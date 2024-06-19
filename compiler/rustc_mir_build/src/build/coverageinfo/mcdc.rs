use std::collections::VecDeque;

use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::bug;
use rustc_middle::mir::coverage::{
    BlockMarkerId, ConditionId, ConditionInfo, DecisionId, MCDCBranchSpan, MCDCDecisionSpan,
};
use rustc_middle::mir::BasicBlock;
use rustc_middle::thir::LogicalOp;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::build::Builder;
use crate::errors::{MCDCExceedsConditionLimit, MCDCExceedsDecisionDepth};

/// The MCDC bitmap scales exponentially (2^n) based on the number of conditions seen,
/// So llvm sets a maximum value prevents the bitmap footprint from growing too large without the user's knowledge.
/// This limit may be relaxed if the [upstream change](https://github.com/llvm/llvm-project/pull/82448) is merged.
const MAX_CONDITIONS_IN_DECISION: usize = 6;

/// MCDC allocates an i32 variable on stack for each depth. Ignore decisions nested too much to prevent it
/// consuming excessive memory.
const MAX_DECISION_DEPTH: u16 = 0x3FFF;

#[derive(Debug)]
struct BooleanDecisionCtx {
    id: DecisionId,
    decision_info: MCDCDecisionSpan,
    /// To construct condition evaluation tree.
    decision_stack: VecDeque<ConditionInfo>,
    conditions: Vec<MCDCBranchSpan>,
}

impl BooleanDecisionCtx {
    fn new(id: DecisionId) -> Self {
        Self {
            id,
            decision_info: MCDCDecisionSpan {
                span: Span::default(),
                num_conditions: 0,
                end_markers: vec![],
                decision_depth: 0,
            },
            decision_stack: VecDeque::new(),
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
            self.decision_info.num_conditions += 1;
            ConditionId::from(self.decision_info.num_conditions)
        } else {
            parent_condition.condition_id
        };

        self.decision_info.num_conditions += 1;
        let rhs_condition_id = ConditionId::from(self.decision_info.num_conditions);

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
            true_marker,
            false_marker,
            decision_depth: 0,
        });
        // In case this decision had only one condition
        self.decision_info.num_conditions = self.decision_info.num_conditions.max(1);
    }

    fn is_finished(&self) -> bool {
        self.decision_stack.is_empty()
    }

    fn into_done(self) -> (DecisionId, MCDCDecisionSpan, Vec<MCDCBranchSpan>) {
        (self.id, self.decision_info, self.conditions)
    }
}

#[derive(Debug)]
enum DecisionCtx {
    Boolean(BooleanDecisionCtx),
    #[allow(unused)]
    Matching,
}

impl DecisionCtx {
    fn new_boolean(id: DecisionId) -> Self {
        Self::Boolean(BooleanDecisionCtx::new(id))
    }
}

struct MCDCState {
    current_ctx: Option<DecisionCtx>,
    nested_decision_records: Vec<DecisionId>,
    ctx_stash: Vec<(Option<DecisionCtx>, Vec<DecisionId>)>,
}

impl MCDCState {
    fn new() -> Self {
        Self { current_ctx: None, ctx_stash: vec![], nested_decision_records: vec![] }
    }

    fn current_depth(&self) -> usize {
        self.ctx_stash.len()
    }

    fn increment_depth(&mut self) {
        self.ctx_stash
            .push((self.current_ctx.take(), std::mem::take(&mut self.nested_decision_records)));
    }

    fn decrement_depth(&mut self) {
        assert!(self.current_ctx.is_none(), "still has processing decision");
        let (parent_ctx, parent_nested) = self.ctx_stash.pop().expect("ensured in the if guard");
        self.current_ctx = parent_ctx;
        // The processed ctx might produce no decision but still have nested decisions, which can happen on code like `if foo(bar(a || b))`.
        // These nested decisions should be taken as the parent's nested ones. By this way we can eliminate unused mcdc parameters.
        self.inherit_nested_decisions(parent_nested);
    }

    fn ensure_ctx(&mut self, constructor: impl FnOnce() -> DecisionCtx) -> &mut DecisionCtx {
        self.current_ctx.get_or_insert_with(constructor)
    }

    fn take_ctx(&mut self) -> Option<(DecisionCtx, Vec<DecisionId>)> {
        let ctx = self.current_ctx.take()?;
        let nested_decisions_id = std::mem::take(&mut self.nested_decision_records);

        Some((ctx, nested_decisions_id))
    }

    // Return `true` if there is no ctx to be processed.
    fn is_empty(&self) -> bool {
        self.current_ctx.is_none() && self.current_depth() == 0
    }

    fn inherit_nested_decisions(&mut self, nested_decisions_id: Vec<DecisionId>) {
        self.nested_decision_records.extend(nested_decisions_id);
    }

    fn take_current_nested_decisions(&mut self) -> Vec<DecisionId> {
        std::mem::take(&mut self.nested_decision_records)
    }

    // Return `true` if the decision can be nested in another decision and record it,
    // otherwise return `false`.
    fn record_nested_decision(&mut self, id: DecisionId) {
        if !self.is_empty() {
            self.nested_decision_records.push(id);
        }
    }
}

#[derive(Debug)]
struct MCDCTargetInfo {
    decision: MCDCDecisionSpan,
    conditions: Vec<MCDCBranchSpan>,
    nested_decisions_id: Vec<DecisionId>,
}

impl MCDCTargetInfo {
    fn set_depth(&mut self, depth: u16) {
        self.decision.decision_depth = depth;
        self.conditions.iter_mut().for_each(|branch| branch.decision_depth = depth);
    }
}

#[derive(Default)]
struct DecisionIdGen(usize);
impl DecisionIdGen {
    fn next_decision_id(&mut self) -> DecisionId {
        let id = DecisionId::from_usize(self.0);
        self.0 += 1;
        id
    }
}

pub(crate) struct MCDCInfoBuilder {
    normal_branch_spans: Vec<MCDCBranchSpan>,
    mcdc_targets: FxIndexMap<DecisionId, MCDCTargetInfo>,
    state: MCDCState,
    decision_id_gen: DecisionIdGen,
}

impl MCDCInfoBuilder {
    pub(crate) fn new() -> Self {
        Self {
            normal_branch_spans: vec![],
            mcdc_targets: FxIndexMap::default(),
            state: MCDCState::new(),
            decision_id_gen: DecisionIdGen::default(),
        }
    }

    fn ensure_boolean_decision(&mut self, condition_span: Span) -> &mut BooleanDecisionCtx {
        let DecisionCtx::Boolean(ctx) = self
            .state
            .ensure_ctx(|| DecisionCtx::new_boolean(self.decision_id_gen.next_decision_id()))
        else {
            unreachable!("ensured above");
        };

        if ctx.decision_info.span == Span::default() {
            ctx.decision_info.span = condition_span;
        } else {
            ctx.decision_info.span = ctx.decision_info.span.to(condition_span);
        }
        ctx
    }

    fn append_normal_branches(&mut self, mut branches: Vec<MCDCBranchSpan>) {
        branches.iter_mut().for_each(|branch| branch.condition_info = None);
        self.normal_branch_spans.extend(branches);
    }

    fn append_mcdc_info(
        &mut self,
        tcx: TyCtxt<'_>,
        id: DecisionId,
        decision: MCDCDecisionSpan,
        conditions: Vec<MCDCBranchSpan>,
    ) -> Option<&mut MCDCTargetInfo> {
        let num_conditions = conditions.len();
        match num_conditions {
            0 => {
                unreachable!("Decision with no condition is not expected");
            }
            // Ignore decisions with only one condition given that mcdc for them is completely equivalent to branch coverage.
            2..=MAX_CONDITIONS_IN_DECISION => {
                let info = MCDCTargetInfo { decision, conditions, nested_decisions_id: vec![] };
                Some(self.mcdc_targets.entry(id).or_insert(info))
            }
            _ => {
                self.append_normal_branches(conditions);
                if num_conditions > MAX_CONDITIONS_IN_DECISION {
                    tcx.dcx().emit_warn(MCDCExceedsConditionLimit {
                        span: decision.span,
                        num_conditions,
                        max_conditions: MAX_CONDITIONS_IN_DECISION,
                    });
                }
                None
            }
        }
    }

    fn normalize_depth_from(&mut self, tcx: TyCtxt<'_>, id: DecisionId) {
        let Some(entry_decision) = self.mcdc_targets.get_mut(&id) else {
            bug!("unknown mcdc decision");
        };
        let mut next_nested_records = entry_decision.nested_decisions_id.clone();
        let mut depth = 0;
        while !next_nested_records.is_empty() {
            depth += 1;
            for id in std::mem::take(&mut next_nested_records) {
                let Some(nested_target) = self.mcdc_targets.get_mut(&id) else {
                    continue;
                };
                nested_target.set_depth(depth);
                next_nested_records.extend(nested_target.nested_decisions_id.iter().copied());
                if depth > MAX_DECISION_DEPTH {
                    tcx.dcx().emit_warn(MCDCExceedsDecisionDepth {
                        span: nested_target.decision.span,
                        max_decision_depth: MAX_DECISION_DEPTH.into(),
                    });
                    let branches = std::mem::take(&mut nested_target.conditions);
                    self.append_normal_branches(branches);
                    self.mcdc_targets.swap_remove(&id);
                }
            }
        }
    }

    // If `entry_decision_id` is some, there must be at least one mcdc decision being produced.
    // The "entry decision" will be taken as the root if these decisions were nested in others.
    fn on_ctx_finished(&mut self, tcx: TyCtxt<'_>, entry_decision_id: Option<DecisionId>) {
        match (self.state.is_empty(), entry_decision_id) {
            // Can not be nested in other decisions, depth is accumulated starting from this decision.
            (true, Some(id)) => self.normalize_depth_from(tcx, id),
            // May be nested in other decisions, record it.
            (false, Some(id)) => self.state.record_nested_decision(id),
            // No decision is produced this time and no other parent decision to be processing.
            // All "nested decisions" now get zero depth and then calculate depth of their children.
            (true, None) => {
                for root_decision in self.state.take_current_nested_decisions() {
                    self.normalize_depth_from(tcx, root_decision);
                }
            }
            (false, None) => {}
        }
    }

    pub(crate) fn visit_evaluated_condition(
        &mut self,
        tcx: TyCtxt<'_>,
        span: Span,
        true_block: BasicBlock,
        false_block: BasicBlock,
        mut inject_block_marker: impl FnMut(BasicBlock) -> BlockMarkerId,
    ) {
        let true_marker = inject_block_marker(true_block);
        let false_marker = inject_block_marker(false_block);
        let decision = self.ensure_boolean_decision(span);
        decision.finish_two_way_branch(span, true_marker, false_marker);

        if !decision.is_finished() {
            return;
        }

        let Some((DecisionCtx::Boolean(ctx), nested_decisions_id)) = self.state.take_ctx() else {
            unreachable!("ensured boolean ctx above");
        };

        let (id, decision, conditions) = ctx.into_done();
        if let Some(target_info) = self.append_mcdc_info(tcx, id, decision, conditions) {
            target_info.nested_decisions_id = nested_decisions_id;
            self.on_ctx_finished(tcx, Some(id));
        } else {
            self.state.inherit_nested_decisions(nested_decisions_id);
            self.on_ctx_finished(tcx, None)
        }
    }

    pub(crate) fn into_done(
        self,
    ) -> (Vec<MCDCBranchSpan>, Vec<(MCDCDecisionSpan, Vec<MCDCBranchSpan>)>) {
        let MCDCInfoBuilder { normal_branch_spans, mcdc_targets, state: _, decision_id_gen: _ } =
            self;

        let mcdc_spans = mcdc_targets
            .into_values()
            .map(|MCDCTargetInfo { decision, conditions, nested_decisions_id: _ }| {
                (decision, conditions)
            })
            .collect();

        (normal_branch_spans, mcdc_spans)
    }
}

impl Builder<'_, '_> {
    pub(crate) fn visit_coverage_branch_operation(&mut self, logical_op: LogicalOp, span: Span) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            let decision = mcdc_info.ensure_boolean_decision(span);
            decision.record_conditions(logical_op);
        }
    }

    pub(crate) fn mcdc_increment_depth_if_enabled(&mut self) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            mcdc_info.state.increment_depth();
        };
    }

    pub(crate) fn mcdc_decrement_depth_if_enabled(&mut self) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            mcdc_info.state.decrement_depth();
        };
    }
}
