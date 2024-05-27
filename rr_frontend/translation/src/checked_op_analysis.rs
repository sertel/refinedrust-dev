// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{HashMap, HashSet};

use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::mir::{
    BasicBlock, BasicBlockData, Body, Local, Place, Rvalue, StatementKind, TerminatorKind,
};
use rr_rustc_interface::middle::ty::{Ty, TyCtxt};

/// Analysis for determining which locals are the temporaries used as the result of a checked-op.
pub struct CheckedOpLocalAnalysis<'def, 'tcx> {
    tcx: TyCtxt<'tcx>,
    bb_queue: Vec<BasicBlock>,
    visited_bbs: HashSet<BasicBlock>,
    result: HashMap<Local, Ty<'tcx>>,
    body: &'def Body<'tcx>,
}

impl<'def, 'tcx> CheckedOpLocalAnalysis<'def, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'def Body<'tcx>) -> Self {
        Self {
            tcx,
            bb_queue: Vec::new(),
            visited_bbs: HashSet::new(),
            body,
            result: HashMap::new(),
        }
    }

    const fn is_checked_op(val: &Rvalue<'tcx>) -> bool {
        matches!(*val, Rvalue::CheckedBinaryOp(_, _))
    }

    /// Get the type of a checked-op result.
    /// We discard the second component of the tuple.
    fn get_checked_op_result_type(ty: Ty<'tcx>) -> Ty<'tcx> {
        let fields = ty.tuple_fields();
        *fields.get(0).unwrap()
    }

    /// Get the type of a place expression.
    fn get_type_of_place(&self, pl: &Place<'tcx>) -> PlaceTy<'tcx> {
        pl.ty(&self.body.local_decls, self.tcx)
    }

    /// Get all successors of the basic block (ignoring unwinding).
    fn successors_of_bb(bb: &BasicBlockData<'tcx>) -> Vec<BasicBlock> {
        let mut v = Vec::new();

        let Some(term) = &bb.terminator else {
            return v;
        };

        match &term.kind {
            TerminatorKind::Assert { target, .. }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Goto { target }
            | TerminatorKind::Call {
                target: Some(target),
                ..
            } => v.push(*target),

            TerminatorKind::InlineAsm {
                destination: Some(destination),
                ..
            } => v.push(*destination),

            TerminatorKind::SwitchInt { targets, .. } => {
                for target in targets.all_targets() {
                    v.push(*target);
                }
            },

            TerminatorKind::Yield { resume, .. } => v.push(*resume),

            _ => (),
        }

        v
    }

    pub fn analyze(&mut self) {
        if self.body.basic_blocks.len() > 0 {
            self.bb_queue.push(BasicBlock::from_u32(0));
        }

        while let Some(next_bb) = self.bb_queue.pop() {
            if !self.visited_bbs.contains(&next_bb) {
                self.visited_bbs.insert(next_bb);
                self.visit_bb(next_bb);
            }
        }
    }

    pub fn results(self) -> HashMap<Local, Ty<'tcx>> {
        self.result
    }

    fn visit_bb(&mut self, bb_idx: BasicBlock) {
        let bb = self.body.basic_blocks.get(bb_idx).unwrap();
        // check if a statement is an assignment of a checked op result

        for stmt in &bb.statements {
            let StatementKind::Assign(b) = &stmt.kind else {
                continue;
            };

            let (plc, val) = b.as_ref();

            // if this is a checked op, be sure to remember it
            if Self::is_checked_op(val) {
                // this should be a temporary
                assert!(plc.projection.is_empty());

                // just use the RHS ty
                let ty = self.get_type_of_place(plc);
                let ty = Self::get_checked_op_result_type(ty.ty);

                self.result.insert(plc.local, ty);
            }
        }

        self.bb_queue.append(&mut Self::successors_of_bb(bb));
    }
}
