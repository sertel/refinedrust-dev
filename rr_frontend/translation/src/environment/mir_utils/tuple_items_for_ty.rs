// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty;

pub trait TupleItemsForTy<'tcx> {
    /// Tries to interpret the given `mir::Ty` as a tuple type. If this succeeds, it returns the
    /// nested types making up the tuple. If this failes, it returns `None`.
    fn tuple_items(&self) -> Option<Vec<ty::Ty<'tcx>>>;
}

impl<'tcx> TupleItemsForTy<'tcx> for ty::Ty<'tcx> {
    fn tuple_items(&self) -> Option<Vec<ty::Ty<'tcx>>> {
        if let ty::TyKind::Tuple(items) = self.kind() {
            let types = items.iter().collect();
            Some(types)
        } else {
            None
        }
    }
}
