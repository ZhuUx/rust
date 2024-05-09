use std::collections::{BTreeMap, BTreeSet, VecDeque};

use rustc_middle::mir::coverage::{
    BlockMarkerId, ConditionId, ConditionInfo, MCDCBranchSpan, MCDCDecisionSpan,
};
use rustc_middle::mir::{BasicBlock, SourceInfo};
use rustc_middle::thir::LogicalOp;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::build::{Builder, CFG};
use crate::errors::MCDCExceedsConditionNumLimit;

/// The MCDC bitmap scales exponentially (2^n) based on the number of conditions seen,
/// So llvm sets a maximum value prevents the bitmap footprint from growing too large without the user's knowledge.
/// This limit may be relaxed if the [upstream change](https://github.com/llvm/llvm-project/pull/82448) is merged.
const MAX_CONDITIONS_NUM_IN_DECISION: usize = 6;

struct BooleanDecisionCtx {
    /// To construct condition evaluation tree.
    decision_info: MCDCDecisionSpan,
    decision_stack: VecDeque<ConditionInfo>,
    conditions: Vec<MCDCBranchSpan>,
}

impl BooleanDecisionCtx {
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
        test_marker: BlockMarkerId,
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
            test_markers: vec![test_marker],
            true_markers: vec![true_marker],
            decision_depth: self.decision_info.decision_depth,
        });
        // In case this decision had only one condition
        self.decision_info.conditions_num = self.decision_info.conditions_num.max(1);
    }

    fn finished(&self) -> bool {
        self.decision_stack.is_empty()
    }
}

#[derive(Default)]
struct MatchArmRecord {
    true_next_pattern: Option<Span>,
    false_next_pattern: Option<Span>,
    test_blocks: Vec<BasicBlock>,
    matched_blocks: Vec<BasicBlock>,
}
struct PatternDecisionCtx {
    decision_span: Span,
    decision_depth: u16,
    // All patterns leading to branch.
    matching_arms: BTreeMap<Span, MatchArmRecord>,
    // Patterns unknown for their predecessors yet.
    start_tests: BTreeMap<BasicBlock, Span>,
    // Patterns ending the process once they are matched.
    end_tests: BTreeMap<BasicBlock, Span>,
}

impl PatternDecisionCtx {
    fn new(decision_span: Span, decision_depth: u16) -> Self {
        Self {
            decision_span,
            decision_depth,
            matching_arms: BTreeMap::new(),
            start_tests: BTreeMap::new(),
            end_tests: BTreeMap::new(),
        }
    }

    // This method is valid when following invariants hold:
    // 1. In same decision, patterns called this in different time shall be matched alltogether.
    // 2. Targets passed to this method in same time are joint with `|`
    fn visit_matching_arms(
        &mut self,
        test_block: BasicBlock,
        pattern_targets: impl Iterator<Item = (Span, BasicBlock)>,
    ) {
        let mut targets = pattern_targets.collect::<Vec<_>>();

        let mut visiting_arms: BTreeMap<_, _> =
            targets.iter().filter_map(|(span, _)| self.matching_arms.remove_entry(&span)).collect();

        let entry_span = targets.first().expect("targets mut be non empty").0;

        let mut false_next_arm = None;

        // Tranverse conditions in reverse order.
        while let Some((span, matched_block)) = targets.pop() {
            // LLVM whether the decision dominates the condition by checking if span of the decision cover that of the condition,
            // thus we should ensure the decision span covering all conditions span.
            self.decision_span = self.decision_span.to(span);
            let record = visiting_arms.entry(span).or_default();
            // Same pattern test might appear at different blocks as successors of different tests.
            // Thus always update `start_tests` even though the `next_test` of the record has already been known.
            let next_test = self.start_tests.remove(&matched_block);
            assert!(
                record.true_next_pattern.is_none() || record.true_next_pattern == next_test,
                "only has one next test pattern"
            );
            record.true_next_pattern = record.true_next_pattern.or(next_test);
            record.false_next_pattern = false_next_arm.take();
            if record.true_next_pattern.is_some() {
                // By here it has known its successor.
                self.end_tests.remove(&matched_block);
            } else {
                self.end_tests.insert(matched_block, span);
            }
            record.test_blocks.push(test_block);
            record.matched_blocks.push(matched_block);
            false_next_arm = Some(span);
        }
        // There are only one of two occasions when we visit this test:
        // 1. The direct predecessor has been visited before. In this case, the predecessor
        //    must be in `end_tests` and should set its true next to the test entry.
        // 2. Its direct predecessor has not been visited yet. Then we insert the test entry to `start_tests`.
        if let Some(span) = self.end_tests.remove(&test_block) {
            let predecessor = self
                .matching_arms
                .get_mut(&span)
                .expect("this collection must contain 'end' conditions");
            predecessor.true_next_pattern = Some(entry_span);
        } else {
            self.start_tests.insert(test_block, entry_span);
        }

        self.matching_arms.append(&mut visiting_arms);
    }

    // Gaps appear when the matched value is ignored. For example, `Some(_) | Ok(_), IpAddr::V4(_) | IpAddr::V6(_)`.
    // In such cases the matched blocks of `Some(_) | Ok(_)` will have empty successors which converge
    // to the unique test block of  `IpAddr::V4(_) | IpAddr::V6(_)`. Thus the test block cannot find its direct
    // predecessors, which are not matched blocks of any patterns, at `visit_matching_arms`
    // (in fact they were not connected at that moment).
    fn link_condition_gaps(&mut self, cfg: &mut CFG<'_>) {
        if self.start_tests.len() < 2 {
            return;
        }
        let mut linked_starts = BTreeSet::new();
        for (&end, span) in &self.end_tests {
            let mut successor = Some(end);
            while let Some(block) = successor.take() {
                let next_blocks =
                    cfg.block_data(block).terminator().successors().collect::<Vec<_>>();
                match next_blocks.as_slice() {
                    &[unique_successor] => {
                        if let Some(&next_span) = self.start_tests.get(&unique_successor) {
                            let end_record = self
                                .matching_arms
                                .get_mut(span)
                                .expect("end tests must be recorded");
                            end_record.true_next_pattern = Some(next_span);
                            linked_starts.insert(unique_successor);
                        } else {
                            successor = Some(unique_successor);
                        }
                    }
                    _ => break,
                }
            }
        }

        self.start_tests.retain(|block, _| !linked_starts.contains(block));

        assert_eq!(self.start_tests.len(), 1, "still some gaps exist in mcdc pattern decision");
    }

    fn finish(
        mut self,
        cfg: &mut CFG<'_>,
        matching_block: BasicBlock,
        failure_block: BasicBlock,
        mut inject_block_marker: impl FnMut(&mut CFG<'_>, Span, BasicBlock) -> BlockMarkerId,
    ) -> (MCDCDecisionSpan, Vec<MCDCBranchSpan>) {
        self.link_condition_gaps(cfg);

        let Self { decision_span, decision_depth, mut matching_arms, start_tests, end_tests: _ } =
            self;

        let mut into_block_markers = |span: Span, blocks: &[BasicBlock]| {
            blocks.into_iter().map(|&block| inject_block_marker(cfg, span, block)).collect()
        };

        let decision = MCDCDecisionSpan {
            span: decision_span,
            decision_depth,
            conditions_num: matching_arms.len(),
            end_markers: into_block_markers(decision_span, &[matching_block, failure_block]),
        };

        let mut branch_spans = vec![];

        // LLVM implementation requires the entry condition should be assigned id 1.
        // See https://github.com/rust-lang/rust/issues/79649#issuecomment-2099808951 for detail.
        // We assign condition id at last stage because the entry test could appear
        // in any order in recording.
        let mut condition_id_counter: usize = 0;
        let mut next_condition_id = || {
            condition_id_counter += 1;
            ConditionId::from(condition_id_counter)
        };
        let mut test_entries = VecDeque::from_iter(
            start_tests.into_values().zip(std::iter::once(next_condition_id())),
        );

        let mut assigned_entries = BTreeMap::from_iter(test_entries.iter().copied());
        while let Some((span, condition_id)) = test_entries.pop_back() {
            let MatchArmRecord {
                true_next_pattern,
                false_next_pattern,
                test_blocks,
                matched_blocks,
            } = matching_arms.remove(&span).expect("entries must have been recorded");
            let mut condition_info = ConditionInfo {
                condition_id,
                true_next_id: ConditionId::NONE,
                false_next_id: ConditionId::NONE,
            };

            if let Some(true_next) = true_next_pattern {
                // Multiple patterns joint with `|` may or may not share same `true_next`.
                // That's why `assigned_entries` is used to trace the conditions already assigned a condition id.
                condition_info.true_next_id =
                    assigned_entries.get(&true_next).copied().unwrap_or_else(|| {
                        let id = next_condition_id();
                        test_entries.push_back((true_next, id));
                        assigned_entries.insert(true_next, id);
                        id
                    });
            }

            if let Some(false_next) = false_next_pattern {
                condition_info.false_next_id = next_condition_id();
                assigned_entries.insert(false_next, condition_info.false_next_id);
                test_entries.push_back((false_next, condition_info.false_next_id));
            }

            branch_spans.push(MCDCBranchSpan {
                span,
                decision_depth,
                condition_info: Some(condition_info),
                test_markers: into_block_markers(span, &test_blocks),
                true_markers: into_block_markers(span, &matched_blocks),
            });
        }
        assert_eq!(branch_spans.len(), decision.conditions_num, "conditions num is not correct");
        branch_spans.sort_by(|lhs, rhs| {
            if lhs.span.contains(rhs.span) {
                std::cmp::Ordering::Less
            } else {
                lhs.span.cmp(&rhs.span)
            }
        });

        // Suppose patterns like `A(Some(_))` generate two conditions: `A` and `Some`. The span of
        // `A` would be `A(Some(_))`, including the span of `Some`. To make it look nicer we extract span of sub patterns
        // so that span of `A` would be `A(` while `Some` is `Some(_)`.
        for idx in 0..branch_spans.len().saturating_sub(1) {
            let mut span = branch_spans[idx].span;
            for sub_branch in branch_spans.iter().skip(idx + 1) {
                if span.contains(sub_branch.span) {
                    span = span.until(sub_branch.span);
                } else {
                    break;
                }
            }
            branch_spans[idx].span = span;
        }

        (decision, branch_spans)
    }
}

enum DecisionCtx {
    Boolean(BooleanDecisionCtx),
    Pattern(PatternDecisionCtx),
}

pub struct MCDCInfoBuilder {
    branch_spans: Vec<MCDCBranchSpan>,
    decision_spans: Vec<MCDCDecisionSpan>,
    decision_ctx_stack: Vec<DecisionCtx>,
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

    fn ensure_boolean_decision(&mut self, span: Span) -> &mut BooleanDecisionCtx {
        if self.base_depth == self.next_decision_depth()
            || self
                .decision_ctx_stack
                .last()
                .is_some_and(|ctx| !matches!(ctx, DecisionCtx::Boolean(_)))
        {
            let depth = self.next_decision_depth();
            self.decision_ctx_stack.push(DecisionCtx::Boolean(BooleanDecisionCtx::new(depth)));
        } else {
            assert!(
                self.base_depth <= self.next_decision_depth(),
                "expected depth shall not skip next decision depth"
            );
        }
        let Some(DecisionCtx::Boolean(ctx)) = self.decision_ctx_stack.last_mut() else {
            unreachable!("ensured above")
        };

        if ctx.decision_info.span == Span::default() {
            ctx.decision_info.span = span;
        } else {
            ctx.decision_info.span = ctx.decision_info.span.to(span);
        }
        ctx
    }

    fn try_finish_boolean_decision(&mut self, tcx: TyCtxt<'_>) {
        if !self.decision_ctx_stack.last().is_some_and(|decision| match decision {
            DecisionCtx::Boolean(ctx) => ctx.finished(),
            _ => false,
        }) {
            return;
        }
        let Some(DecisionCtx::Boolean(BooleanDecisionCtx {
            decision_info,
            decision_stack: _,
            conditions,
        })) = self.decision_ctx_stack.pop()
        else {
            unreachable!("has checked above");
        };
        self.append_mcdc_info(tcx, decision_info, conditions);
    }

    fn create_pattern_decision(&mut self, span: Span) {
        if self
            .decision_ctx_stack
            .last()
            .is_some_and(|decision| matches!(decision, DecisionCtx::Pattern(_)))
        {
            bug!("has been processing a pattern decision");
        }
        let depth = self.next_decision_depth();
        self.decision_ctx_stack.push(DecisionCtx::Pattern(PatternDecisionCtx::new(span, depth)));
    }

    fn current_pattern_decision(&mut self) -> Option<&mut PatternDecisionCtx> {
        self.decision_ctx_stack.last_mut().and_then(|decision| match decision {
            DecisionCtx::Pattern(ctx) => Some(ctx),
            _ => None,
        })
    }

    fn finish_pattern_decision(
        &mut self,
        cfg: &mut CFG<'_>,
        tcx: TyCtxt<'_>,
        matching_block: BasicBlock,
        failure_block: BasicBlock,
        inject_block_marker: impl FnMut(&mut CFG<'_>, Span, BasicBlock) -> BlockMarkerId,
    ) {
        if !self
            .decision_ctx_stack
            .last()
            .is_some_and(|decision| matches!(decision, DecisionCtx::Pattern(_)))
        {
            bug!("no processing pattern decision");
        }
        let Some(DecisionCtx::Pattern(decision_ctx)) = self.decision_ctx_stack.pop() else {
            unreachable!("has checked above");
        };

        let (decision, conditions) =
            decision_ctx.finish(cfg, matching_block, failure_block, inject_block_marker);
        self.append_mcdc_info(tcx, decision, conditions);
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
            // MCDC is equivalent to normal branch coverage if number of conditions is less than 1, so ignore these decisions.
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
        test_block: BasicBlock,
        true_block: BasicBlock,
        false_block: BasicBlock,
        mut inject_block_marker: impl FnMut(BasicBlock) -> BlockMarkerId,
    ) {
        let test_marker = inject_block_marker(test_block);
        let true_marker = inject_block_marker(true_block);
        let false_marker = inject_block_marker(false_block);
        let decision = self.ensure_boolean_decision(span);
        decision.finish_two_way_branch(span, test_marker, true_marker, false_marker);
        self.try_finish_boolean_decision(tcx);
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
            let decision = mcdc_info.ensure_boolean_decision(span);
            decision.record_conditions(logical_op);
        }
    }

    pub(crate) fn visit_mcdc_pattern_matching_conditions(
        &mut self,
        test_block: BasicBlock,
        pattern_targets: impl Iterator<Item = (Span, BasicBlock)>,
    ) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
            && let Some(decision_ctx) = mcdc_info.current_pattern_decision()
        {
            decision_ctx.visit_matching_arms(test_block, pattern_targets);
        }
    }

    pub(crate) fn mcdc_prepare_pattern_matching_decision(&mut self, span: Span) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            mcdc_info.create_pattern_decision(span);
        }
    }

    pub(crate) fn mcdc_finish_pattern_matching_decision(
        &mut self,
        matching_block: BasicBlock,
        failure_block: BasicBlock,
    ) {
        if let Some(branch_info) = self.coverage_branch_info.as_mut()
            && let Some(mcdc_info) = branch_info.mcdc_info.as_mut()
        {
            let inject_block_marker = |cfg: &mut CFG<'_>, span, block| {
                branch_info.markers.inject_block_marker(
                    cfg,
                    SourceInfo { span, scope: self.source_scope },
                    block,
                )
            };
            mcdc_info.finish_pattern_decision(
                &mut self.cfg,
                self.tcx,
                matching_block,
                failure_block,
                inject_block_marker,
            );
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
