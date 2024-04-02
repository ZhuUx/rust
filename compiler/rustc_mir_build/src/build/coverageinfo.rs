use std::assert_matches::assert_matches;
use std::collections::hash_map::Entry;
use std::collections::VecDeque;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::coverage::{
    BlockMarkerId, BranchSpan, ConditionId, ConditionInfo, CoverageKind, DecisionInfo, DecisionSpan,
};
use rustc_middle::mir::{self, BasicBlock, UnOp};
use rustc_middle::thir::{ExprId, ExprKind, LogicalOp, Thir};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

use crate::build::Builder;

pub(crate) struct BranchInfoBuilder {
    /// Maps condition expressions to their enclosing `!`, for better instrumentation.
    nots: FxHashMap<ExprId, NotInfo>,

    num_block_markers: usize,
    branch_spans: Vec<BranchSpan>,

    mcdc_state: Option<MCDCState>,
}

#[derive(Clone, Copy)]
struct NotInfo {
    /// When visiting the associated expression as a branch condition, treat this
    /// enclosing `!` as the branch condition instead.
    enclosing_not: ExprId,
    /// True if the associated expression is nested within an odd number of `!`
    /// expressions relative to `enclosing_not` (inclusive of `enclosing_not`).
    is_flipped: bool,
}

impl BranchInfoBuilder {
    /// Creates a new branch info builder, but only if branch coverage instrumentation
    /// is enabled and `def_id` represents a function that is eligible for coverage.
    pub(crate) fn new_if_enabled(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<Self> {
        if tcx.sess.instrument_coverage_branch() && tcx.is_eligible_for_coverage(def_id) {
            Some(Self {
                nots: FxHashMap::default(),
                num_block_markers: 0,
                branch_spans: vec![],
                mcdc_state: MCDCState::new_if_enabled(tcx),
            })
        } else {
            None
        }
    }

    /// Unary `!` expressions inside an `if` condition are lowered by lowering
    /// their argument instead, and then reversing the then/else arms of that `if`.
    ///
    /// That's awkward for branch coverage instrumentation, so to work around that
    /// we pre-emptively visit any affected `!` expressions, and record extra
    /// information that [`Builder::visit_coverage_branch_condition`] can use to
    /// synthesize branch instrumentation for the enclosing `!`.
    pub(crate) fn visit_unary_not(&mut self, thir: &Thir<'_>, unary_not: ExprId) {
        assert_matches!(thir[unary_not].kind, ExprKind::Unary { op: UnOp::Not, .. });

        self.visit_with_not_info(
            thir,
            unary_not,
            // Set `is_flipped: false` for the `!` itself, so that its enclosed
            // expression will have `is_flipped: true`.
            NotInfo { enclosing_not: unary_not, is_flipped: false },
        );
    }

    fn visit_with_not_info(&mut self, thir: &Thir<'_>, expr_id: ExprId, not_info: NotInfo) {
        match self.nots.entry(expr_id) {
            // This expression has already been marked by an enclosing `!`.
            Entry::Occupied(_) => return,
            Entry::Vacant(entry) => entry.insert(not_info),
        };

        match thir[expr_id].kind {
            ExprKind::Unary { op: UnOp::Not, arg } => {
                // Invert the `is_flipped` flag for the contents of this `!`.
                let not_info = NotInfo { is_flipped: !not_info.is_flipped, ..not_info };
                self.visit_with_not_info(thir, arg, not_info);
            }
            ExprKind::Scope { value, .. } => self.visit_with_not_info(thir, value, not_info),
            ExprKind::Use { source } => self.visit_with_not_info(thir, source, not_info),
            // All other expressions (including `&&` and `||`) don't need any
            // special handling of their contents, so stop visiting.
            _ => {}
        }
    }

    fn get_mcdc_state_mut(&mut self) -> Option<&mut MCDCState> {
        self.mcdc_state.as_mut()
    }

    fn next_block_marker_id(&mut self) -> BlockMarkerId {
        let id = BlockMarkerId::from_usize(self.num_block_markers);
        self.num_block_markers += 1;
        id
    }

    pub(crate) fn into_done(self) -> Option<Box<mir::coverage::BranchInfo>> {
        let Self { nots: _, num_block_markers, branch_spans, mcdc_state } = self;

        if num_block_markers == 0 {
            assert!(branch_spans.is_empty());
            return None;
        }
        let decision_spans = mcdc_state.map(|state| state.decisions).unwrap_or_default();
        let mcdc_bitmap_bytes_num = decision_spans
            .last()
            .map(|decision| {
                decision
                    .mcdc_params
                    .bitmap_idx
                    .saturating_add((1 << decision.mcdc_params.conditions_num).max(8))
                    / 8
            })
            .unwrap_or_default();

        Some(Box::new(mir::coverage::BranchInfo {
            num_block_markers,
            branch_spans,
            mcdc_bitmap_bytes_num,
            decision_spans,
        }))
    }
}

struct MCDCState {
    /// To construct condition evaluation tree.
    decision_stack: VecDeque<ConditionInfo>,
    next_condition_id: usize,
    decisions: Vec<DecisionSpan>,
}

impl MCDCState {
    fn new_if_enabled(tcx: TyCtxt<'_>) -> Option<Self> {
        tcx.sess.instrument_coverage_mcdc().then(|| Self {
            decision_stack: VecDeque::new(),
            next_condition_id: 0,
            decisions: vec![],
        })
    }

    fn record_conditions(&mut self, op: LogicalOp) {
        let parent_condition = self.decision_stack.pop_back().unwrap_or_default();
        let lhs_id = if parent_condition.condition_id == ConditionId::NONE {
            self.next_condition_id += 1;
            ConditionId::from(self.next_condition_id)
        } else {
            parent_condition.condition_id
        };

        self.next_condition_id += 1;
        let rhs_condition_id = ConditionId::from(self.next_condition_id);

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

    fn pop_condition_info(&mut self) -> Option<ConditionInfo> {
        let condition = self.decision_stack.pop_back();
        if condition.is_some() {
            if self.decision_stack.is_empty()
                && let Some(decision) = self.decisions.last_mut()
            {
                decision.mcdc_params.conditions_num = (self.next_condition_id - 1) as u16;
                self.next_condition_id = 0;
            }
        }
        condition
    }
}

impl Builder<'_, '_> {
    /// If branch coverage is enabled, inject marker statements into `then_block`
    /// and `else_block`, and record their IDs in the table of branch spans.
    pub(crate) fn visit_coverage_branch_condition(
        &mut self,
        mut expr_id: ExprId,
        mut then_block: BasicBlock,
        mut else_block: BasicBlock,
    ) {
        // Bail out if branch coverage is not enabled for this function.
        let Some(branch_info) = self.coverage_branch_info.as_ref() else { return };

        // If this condition expression is nested within one or more `!` expressions,
        // replace it with the enclosing `!` collected by `visit_unary_not`.
        if let Some(&NotInfo { enclosing_not, is_flipped }) = branch_info.nots.get(&expr_id) {
            expr_id = enclosing_not;
            if is_flipped {
                std::mem::swap(&mut then_block, &mut else_block);
            }
        }
        let source_info = self.source_info(self.thir[expr_id].span);

        // Now that we have `source_info`, we can upgrade to a &mut reference.
        let branch_info = self.coverage_branch_info.as_mut().expect("upgrading & to &mut");

        let condition_info = branch_info
            .mcdc_state
            .as_mut()
            .and_then(MCDCState::pop_condition_info)
            .unwrap_or_default();

        let mut inject_branch_marker = |block: BasicBlock, value: bool| {
            let id = branch_info.next_block_marker_id();

            let marker_statement = mir::Statement {
                source_info,
                kind: mir::StatementKind::Coverage(CoverageKind::BlockMarker { id }),
            };
            self.cfg.push(block, marker_statement);

            if condition_info.condition_id != ConditionId::NONE {
                let condbitmap_update_statement = mir::Statement {
                    source_info,
                    kind: mir::StatementKind::Coverage(CoverageKind::UpdateCondBitmap {
                        id: condition_info.condition_id,
                        value,
                    }),
                };
                self.cfg.push(block, condbitmap_update_statement);
            }

            id
        };

        let true_marker = inject_branch_marker(then_block, true);
        let false_marker = inject_branch_marker(else_block, false);

        branch_info.branch_spans.push(BranchSpan {
            span: source_info.span,
            condition_info,
            true_marker,
            false_marker,
        });
    }

    pub(crate) fn visit_coverage_decision(&mut self, expr_id: ExprId) {
        if let Some(mcdc_state) =
            self.coverage_branch_info.as_mut().and_then(BranchInfoBuilder::get_mcdc_state_mut)
        {
            let bitmap_idx = mcdc_state
                .decisions
                .last()
                .map(|decision| {
                    decision
                        .mcdc_params
                        .bitmap_idx
                        .saturating_add((1 << decision.mcdc_params.conditions_num).max(8))
                })
                .unwrap_or_default();
            mcdc_state.decisions.push(DecisionSpan {
                span: self.thir[expr_id].span,
                mcdc_params: DecisionInfo { conditions_num: 0, bitmap_idx },
            });
        }
    }

    pub(crate) fn visit_coverage_decision_end(&mut self, join_block: BasicBlock) {
        if let Some((span, bitmap_idx)) = self
            .coverage_branch_info
            .as_mut()
            .and_then(BranchInfoBuilder::get_mcdc_state_mut)
            .and_then(|state| state.decisions.last_mut())
            .map(|end_decision| (end_decision.span, end_decision.mcdc_params.bitmap_idx))
        {
            let statement = mir::Statement {
                source_info: self.source_info(span),
                kind: mir::StatementKind::Coverage(CoverageKind::UpdateTestVector { bitmap_idx }),
            };
            self.cfg.push(join_block, statement);
        }
    }

    pub(crate) fn visit_coverage_branch_operation(&mut self, logical_op: LogicalOp) {
        if let Some(mcdc_state) =
            self.coverage_branch_info.as_mut().and_then(BranchInfoBuilder::get_mcdc_state_mut)
        {
            mcdc_state.record_conditions(logical_op);
        }
    }
}
