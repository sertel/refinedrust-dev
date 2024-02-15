// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;

pub trait StatementAsAssign<'tcx> {
    /// If this statement is an assignment, returns the LHS and RHS. If not, returns `None`.
    fn as_assign(&self) -> Option<(mir::Place<'tcx>, &mir::Rvalue<'tcx>)>;
}

impl<'tcx> StatementAsAssign<'tcx> for mir::Statement<'tcx> {
    fn as_assign(&self) -> Option<(mir::Place<'tcx>, &mir::Rvalue<'tcx>)> {
        if let mir::StatementKind::Assign(box (lhs, ref rhs)) = self.kind { Some((lhs, rhs)) } else { None }
    }
}
