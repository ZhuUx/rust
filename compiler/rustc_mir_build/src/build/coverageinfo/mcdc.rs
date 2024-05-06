use std::collections::VecDeque;

use rustc_middle::mir::coverage::{
    BlockMarkerId, ConditionId, ConditionInfo, MCDCBranchMarkers, MCDCBranchSpan, MCDCDecisionSpan,
};
use rustc_middle::mir::BasicBlock;
use rustc_middle::thir::LogicalOp;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::build::Builder;
use crate::errors::MCDCExceedsConditionNumLimit;

/// The MCDC bitmap scales exponentially (2^n) based on the number of conditions seen,
/// So llvm sets a maximum value prevents the bitmap footprint from growing too large without the user's knowledge.
/// This limit may be relaxed if the [upstream change](https://github.com/llvm/llvm-project/pull/82448) is merged.
const MAX_CONDITIONS_NUM_IN_DECISION: usize = 6;

struct MCDCDecisionCtx {
    /// To construct condition evaluation tree.
    decision_info: MCDCDecisionSpan,
    decision_stack: VecDeque<ConditionInfo>,
    conditions: Vec<MCDCBranchSpan>,
}

impl MCDCDecisionCtx {
    fn new(decision_depth: u16) -> Self {
        Self {
            decision_stack: VecDeque::new(),
            decision_info: MCDCDecisionSpan {
                span: Span::default(),
                conditions_num: 0,
                end_markers: vec![],
                decision_depth,
            },
            conditions: vec![],
        }
    }

    // At first we assign ConditionIds for each sub expression.
    // If the sub expression is composite, re-assign its ConditionId to its LHS and generate a new ConditionId for its RHS.
    //
    // Example: "x = (A && B) || (C && D) || (D && F)"
    //
    //      Visit Depth1:
    //              (A && B) || (C && D) || (D && F)
    //              ^-------LHS--------^    ^-RHS--^
    //                      ID=1              ID=2
    //
    //      Visit LHS-Depth2:
    //              (A && B) || (C && D)
    //              ^-LHS--^    ^-RHS--^
    //                ID=1        ID=3
    //
    //      Visit LHS-Depth3:
    //               (A && B)
    //               LHS   RHS
    //               ID=1  ID=4
    //
    //      Visit RHS-Depth3:
    //                         (C && D)
    //                         LHS   RHS
    //                         ID=3  ID=5
    //
    //      Visit RHS-Depth2:              (D && F)
    //                                     LHS   RHS
    //                                     ID=2  ID=6
    //
    //      Visit Depth1:
    //              (A && B)  || (C && D)  || (D && F)
    //              ID=1  ID=4   ID=3  ID=5   ID=2  ID=6
    //
    // A node ID of '0' always means MC/DC isn't being tracked.
    //
    // If a "next" node ID is '0', it means it's the end of the test vector.
    //
    // As the compiler tracks expression in pre-order, we can ensure that condition info of parents are always properly assigned when their children are visited.
    // - If the op is AND, the "false_next" of LHS and RHS should be the parent's "false_next". While "true_next" of the LHS is the RHS, the "true next" of RHS is the parent's "true_next".
    // - If the op is OR, the "true_next" of LHS and RHS should be the parent's "true_next". While "false_next" of the LHS is the RHS, the "false next" of RHS is the parent's "false_next".
    fn record_conditions(&mut self, op: LogicalOp) {
        let parent_condition = self.decision_stack.pop_back().unwrap_or_default();
        let lhs_id = if parent_condition.condition_id == ConditionId::NONE {
            self.decision_info.conditions_num += 1;
            ConditionId::from(self.decision_info.conditions_num)
        } else {
            parent_condition.condition_id
        };

        self.decision_info.conditions_num += 1;
        let rhs_condition_id = ConditionId::from(self.decision_info.conditions_num);

        let (lhs, rhs) = match op {
            LogicalOp::And => {
                let lhs = ConditionInfo {
                    condition_id: lhs_id,
                    true_next_id: rhs_condition_id,
                    false_next_id: parent_condition.false_next_id,
                };
                let rhs = ConditionInfo {
                    condition_id: rhs_condition_id,
                    true_next_id: parent_condition.true_next_id,
                    false_next_id: parent_condition.false_next_id,
                };
                (lhs, rhs)
            }
            LogicalOp::Or => {
                let lhs = ConditionInfo {
                    condition_id: lhs_id,
                    true_next_id: parent_condition.true_next_id,
                    false_next_id: rhs_condition_id,
                };
                let rhs = ConditionInfo {
                    condition_id: rhs_condition_id,
                    true_next_id: parent_condition.true_next_id,
                    false_next_id: parent_condition.false_next_id,
                };
                (lhs, rhs)
            }
        };
        // We visit expressions tree in pre-order, so place the left-hand side on the top.
        self.decision_stack.push_back(rhs);
        self.decision_stack.push_back(lhs);
    }

    fn finish_two_way_branch(
        &mut self,
        span: Span,
        true_marker: BlockMarkerId,
        false_marker: BlockMarkerId,
    ) {
        let condition_info = self.decision_stack.pop_back().unwrap_or_default();
        if condition_info.true_next_id == ConditionId::NONE {
            self.decision_info.end_markers.push(true_marker);
        }
        if condition_info.false_next_id == ConditionId::NONE {
            self.decision_info.end_markers.push(false_marker);
        }

        self.conditions.push(MCDCBranchSpan {
            span,
            condition_info: Some(condition_info),
            markers: MCDCBranchMarkers::Boolean(true_marker, false_marker),
            decision_depth: self.decision_info.decision_depth,
        });
        // In case this decision had only one condition
        self.decision_info.conditions_num = self.decision_info.conditions_num.max(1);
    }

    fn finished(&self) -> bool {
        self.decision_stack.is_empty()
    }
}

pub struct MCDCInfoBuilder {
    branch_spans: Vec<MCDCBranchSpan>,
    decision_spans: Vec<MCDCDecisionSpan>,
    decision_ctx_stack: Vec<MCDCDecisionCtx>,
    base_depth: u16,
}

impl MCDCInfoBuilder {
    pub fn new() -> Self {
        Self {
            branch_spans: vec![],
            decision_spans: vec![],
            decision_ctx_stack: vec![],
            base_depth: 0,
        }
    }

    fn next_decision_depth(&self) -> u16 {
        u16::try_from(self.decision_ctx_stack.len()).expect(
            "decision depth did not fit in u16, this is likely to be an instrumentation error",
        )
    }

    fn ensure_decision(&mut self, span: Span) -> &mut MCDCDecisionCtx {
        if self.base_depth == self.next_decision_depth() {
            let depth = self.next_decision_depth();
            self.decision_ctx_stack.push(MCDCDecisionCtx::new(depth));
        } else {
            assert!(
                self.base_depth <= self.next_decision_depth(),
                "expected depth shall not skip next decision depth"
            );
        }
        let ctx = self.decision_ctx_stack.last_mut().expect("ensured above");

        if ctx.decision_info.span == Span::default() {
            ctx.decision_info.span = span;
        } else {
            ctx.decision_info.span = ctx.decision_info.span.to(span);
        }
        ctx
    }

    fn try_finish_decision(&mut self, tcx: TyCtxt<'_>) {
        if !self.decision_ctx_stack.last().is_some_and(|decision| decision.finished()) {
            return;
        }
        let MCDCDecisionCtx { decision_info, decision_stack: _, conditions } =
            self.decision_ctx_stack.pop().expect("has checked above");

        self.append_mcdc_info(tcx, decision_info, conditions);
    }

    fn append_mcdc_info(
        &mut self,
        tcx: TyCtxt<'_>,
        decision: MCDCDecisionSpan,
        mut conditions: Vec<MCDCBranchSpan>,
    ) {
        // take_condition() returns Some for decision_result when the decision stack
        // is empty, i.e. when all the conditions of the decision were instrumented,
        // and the decision is "complete".
        match decision.conditions_num {
            0 => {
                unreachable!("Decision with no condition is not expected");
            }
            2..=MAX_CONDITIONS_NUM_IN_DECISION => {
                self.decision_spans.push(decision);
                self.branch_spans.extend(conditions);
            }
            // MCDC is equivalent to normal branch coverage if number of conditions is 1, so ignore these decisions.
            // See comment of `MAX_CONDITIONS_NUM_IN_DECISION` for why decisions with oversized conditions are ignored.
            _ => {
                // Generate normal branch coverage mappings in such cases.
                conditions.iter_mut().for_each(|branch| branch.condition_info = None);
                self.branch_spans.extend(conditions);
                if decision.conditions_num > MAX_CONDITIONS_NUM_IN_DECISION {
                    tcx.dcx().emit_warn(MCDCExceedsConditionNumLimit {
                        span: decision.span,
                        conditions_num: decision.conditions_num,
                        max_conditions_num: MAX_CONDITIONS_NUM_IN_DECISION,
                    });
                }
            }
        }
    }

    pub fn visit_evaluated_condition(
        &mut self,
        tcx: TyCtxt<'_>,
        span: Span,
        true_block: BasicBlock,
        false_block: BasicBlock,
        mut inject_block_marker: impl FnMut(BasicBlock) -> BlockMarkerId,
    ) {
        let true_marker = inject_block_marker(true_block);
        let false_marker = inject_block_marker(false_block);
        let decision = self.ensure_decision(span);
        decision.finish_two_way_branch(span, true_marker, false_marker);
        self.try_finish_decision(tcx);
    }

    pub fn into_done(self) -> (Vec<MCDCDecisionSpan>, Vec<MCDCBranchSpan>) {
        (self.decision_spans, self.branch_spans)
    }
}

impl Builder<'_, '_> {
    pub(crate) fn visit_coverage_branch_operation(&mut self, logical_op: LogicalOp, span: Span) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            let decision = mcdc_info.ensure_decision(span);
            decision.record_conditions(logical_op);
        }
    }

    pub(crate) fn mcdc_increment_depth_if_enabled(&mut self) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            mcdc_info.base_depth = mcdc_info.next_decision_depth().max(mcdc_info.base_depth + 1);
        };
    }

    pub(crate) fn mcdc_decrement_depth_if_enabled(&mut self) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            mcdc_info.base_depth -= 1;
        };
    }
}
