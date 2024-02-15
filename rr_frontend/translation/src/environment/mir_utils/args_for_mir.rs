// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_index::Idx;
use rustc_middle::{mir, ty};

pub trait ArgsForMir<'tcx> {
    fn get_args(&self) -> Vec<(mir::Local, ty::Ty<'tcx>)>;
}

impl<'tcx> ArgsForMir<'tcx> for mir::Body<'tcx> {
    fn get_args(&self) -> Vec<(mir::Local, ty::Ty<'tcx>)> {
        (1..=self.arg_count)
            .map(mir::Local::new)
            .map(|l| (l, self.local_decls[l].clone().ty))
            .collect()
    }
}
