// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MirPlace<'tcx> {
    pub local: mir::Local,
    pub projection: Vec<mir::PlaceElem<'tcx>>,
}

impl<'tcx> From<mir::Place<'tcx>> for MirPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        MirPlace {
            local: place.local,
            projection: place.projection.to_vec(),
        }
    }
}
