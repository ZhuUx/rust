use std::assert_matches::assert_matches;
use std::collections::hash_map::Entry;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::coverage::{BlockMarkerId, BranchSpan, CoverageKind};
use rustc_middle::mir::{self, BasicBlock, SourceInfo, UnOp};
use rustc_middle::thir::{ExprId, ExprKind, Pat, Thir};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

use crate::build::coverageinfo::mcdc::MCDCInfoBuilder;
use crate::build::{Builder, CFG};

mod mcdc;

pub(crate) struct BranchInfoBuilder {
    /// Maps condition expressions to their enclosing `!`, for better instrumentation.
    nots: FxHashMap<ExprId, NotInfo>,

    markers: BlockMarkerGen,
    branch_spans: Vec<BranchSpan>,

    mcdc_info: Option<MCDCInfoBuilder>,
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

#[derive(Default)]
struct BlockMarkerGen {
    num_block_markers: usize,
}

impl BlockMarkerGen {
    fn next_block_marker_id(&mut self) -> BlockMarkerId {
        let id = BlockMarkerId::from_usize(self.num_block_markers);
        self.num_block_markers += 1;
        id
    }

    fn inject_block_marker(
        &mut self,
        cfg: &mut CFG<'_>,
        source_info: SourceInfo,
        block: BasicBlock,
    ) -> BlockMarkerId {
        let id = self.next_block_marker_id();
        let marker_statement = mir::Statement {
            source_info,
            kind: mir::StatementKind::Coverage(CoverageKind::BlockMarker { id }),
        };
        cfg.push(block, marker_statement);

        id
    }
}

impl BranchInfoBuilder {
    /// Creates a new branch info builder, but only if branch coverage instrumentation
    /// is enabled and `def_id` represents a function that is eligible for coverage.
    pub(crate) fn new_if_enabled(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<Self> {
        if tcx.sess.instrument_coverage_branch() && tcx.is_eligible_for_coverage(def_id) {
            Some(Self {
                nots: FxHashMap::default(),
                markers: BlockMarkerGen::default(),
                branch_spans: vec![],
                mcdc_info: tcx.sess.instrument_coverage_mcdc().then(MCDCInfoBuilder::new),
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

    fn add_two_way_branch<'tcx>(
        &mut self,
        cfg: &mut CFG<'tcx>,
        source_info: SourceInfo,
        true_block: BasicBlock,
        false_block: BasicBlock,
    ) {
        let true_marker = self.markers.inject_block_marker(cfg, source_info, true_block);
        let false_marker = self.markers.inject_block_marker(cfg, source_info, false_block);

        self.branch_spans.push(BranchSpan { span: source_info.span, true_marker, false_marker });
    }

    pub(crate) fn into_done(self) -> Option<Box<mir::coverage::BranchInfo>> {
        let Self {
            nots: _,
            markers: BlockMarkerGen { num_block_markers },
            branch_spans,
            mcdc_info,
        } = self;

        if num_block_markers == 0 {
            assert!(branch_spans.is_empty());
            return None;
        }

        let (mcdc_degraded_spans, mcdc_spans) =
            mcdc_info.map(MCDCInfoBuilder::into_done).unwrap_or_default();

        Some(Box::new(mir::coverage::BranchInfo {
            num_block_markers,
            branch_spans,
            mcdc_degraded_spans,
            mcdc_spans,
        }))
    }
}

impl<'tcx> Builder<'_, 'tcx> {
    /// If condition coverage is enabled, inject extra blocks and marker statements
    /// that will let us track the value of the condition in `place`.
    pub(crate) fn visit_coverage_standalone_condition(
        &mut self,
        mut expr_id: ExprId,     // Expression giving the span of the condition
        place: mir::Place<'tcx>, // Already holds the boolean condition value
        block: &mut BasicBlock,
    ) {
        // Bail out if condition coverage is not enabled for this function.
        let Some(branch_info) = self.coverage_branch_info.as_mut() else { return };
        if !self.tcx.sess.instrument_coverage_condition() {
            return;
        };

        // Remove any wrappers, so that we can inspect the real underlying expression.
        while let ExprKind::Use { source: inner } | ExprKind::Scope { value: inner, .. } =
            self.thir[expr_id].kind
        {
            expr_id = inner;
        }
        // If the expression is a lazy logical op, it will naturally get branch
        // coverage as part of its normal lowering, so we can disregard it here.
        if let ExprKind::LogicalOp { .. } = self.thir[expr_id].kind {
            return;
        }

        let source_info = SourceInfo { span: self.thir[expr_id].span, scope: self.source_scope };

        // Using the boolean value that has already been stored in `place`, set up
        // control flow in the shape of a diamond, so that we can place separate
        // marker statements in the true and false blocks. The coverage MIR pass
        // will use those markers to inject coverage counters as appropriate.
        //
        //          block
        //         /     \
        // true_block   false_block
        //  (marker)     (marker)
        //         \     /
        //        join_block

        let true_block = self.cfg.start_new_block();
        let false_block = self.cfg.start_new_block();
        self.cfg.terminate(
            *block,
            source_info,
            mir::TerminatorKind::if_(mir::Operand::Copy(place), true_block, false_block),
        );

        branch_info.add_two_way_branch(&mut self.cfg, source_info, true_block, false_block);

        let join_block = self.cfg.start_new_block();
        self.cfg.goto(true_block, source_info, join_block);
        self.cfg.goto(false_block, source_info, join_block);
        // Any subsequent codegen in the caller should use the new join block.
        *block = join_block;
    }

    /// If branch coverage is enabled, inject marker statements into `then_block`
    /// and `else_block`, and record their IDs in the table of branch spans.
    pub(crate) fn visit_coverage_branch_condition(
        &mut self,
        mut expr_id: ExprId,
        mut then_block: BasicBlock,
        mut else_block: BasicBlock,
    ) {
        // Bail out if branch coverage is not enabled for this function.
        let Some(branch_info) = self.coverage_branch_info.as_mut() else { return };

        // If this condition expression is nested within one or more `!` expressions,
        // replace it with the enclosing `!` collected by `visit_unary_not`.
        if let Some(&NotInfo { enclosing_not, is_flipped }) = branch_info.nots.get(&expr_id) {
            expr_id = enclosing_not;
            if is_flipped {
                std::mem::swap(&mut then_block, &mut else_block);
            }
        }

        let source_info = SourceInfo { span: self.thir[expr_id].span, scope: self.source_scope };

        // Separate path for handling branches when MC/DC is enabled.
        if let Some(mcdc_info) = branch_info.mcdc_info.as_mut() {
            let inject_block_marker =
                |block| branch_info.markers.inject_block_marker(&mut self.cfg, source_info, block);
            mcdc_info.visit_evaluated_condition(
                self.tcx,
                source_info.span,
                then_block,
                else_block,
                inject_block_marker,
            );
            return;
        }

        branch_info.add_two_way_branch(&mut self.cfg, source_info, then_block, else_block);
    }

    /// If branch coverage is enabled, inject marker statements into `true_block`
    /// and `false_block`, and record their IDs in the table of branches.
    ///
    /// Used to instrument let-else and if-let (including let-chains) for branch coverage.
    pub(crate) fn visit_coverage_conditional_let(
        &mut self,
        pattern: &Pat<'tcx>, // Pattern that has been matched when the true path is taken
        true_block: BasicBlock,
        false_block: BasicBlock,
    ) {
        // Bail out if branch coverage is not enabled for this function.
        let Some(branch_info) = self.coverage_branch_info.as_mut() else { return };

        // FIXME(#124144) This may need special handling when MC/DC is enabled.

        let source_info = SourceInfo { span: pattern.span, scope: self.source_scope };
        branch_info.add_two_way_branch(&mut self.cfg, source_info, true_block, false_block);
    }
}
