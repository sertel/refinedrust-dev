// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[macro_export]
macro_rules! force_matches {
    ($ex:expr, $patt:pat => $ret:expr, $err:expr) => {
        if let $patt = $ex { $ret } else { unreachable!($err) }
    };
    ($ex:expr, $patt:pat => $ret:expr) => {
        if let $patt = $ex {
            $ret
        } else {
            unreachable!(
                "force_matches: expr {} doesn't match pattern {}",
                stringify!($ex),
                stringify!($patt)
            )
        }
    };
}
