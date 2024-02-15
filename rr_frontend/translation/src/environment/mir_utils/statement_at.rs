// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use rustc_middle::mir;

pub trait StatementAt<'tcx> {
    fn statement_at(&self, location: mir::Location) -> Option<&mir::Statement<'tcx>>;
}

impl<'tcx> StatementAt<'tcx> for mir::Body<'tcx> {
    fn statement_at(&self, location: mir::Location) -> Option<&mir::Statement<'tcx>> {
        let block = &self[location.block];
        match location.statement_index.cmp(&block.statements.len()) {
            Ordering::Less => Some(&block.statements[location.statement_index]),
            Ordering::Equal => None,
            Ordering::Greater => {
                unreachable!(
                    "cannot retrieve statement at {:?}, because the basic block is too short",
                    location
                );
            },
        }
    }
}
