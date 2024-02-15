// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir::terminator::Mutability;
use rustc_middle::ty::{Region, Ty, TyKind};

pub trait TyAsRef<'tcx> {
    fn as_ty_ref(&self) -> Option<(Region<'tcx>, Ty<'tcx>, Mutability)>;
}

impl<'tcx> TyAsRef<'tcx> for Ty<'tcx> {
    fn as_ty_ref(&self) -> Option<(Region<'tcx>, Ty<'tcx>, Mutability)> {
        match self.kind() {
            TyKind::Ref(region, ty, mutability) => Some((*region, *ty, *mutability)),
            _ => None,
        }
    }
}
