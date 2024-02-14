// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

// declaring a closure like this only works for the unoptimized MIR we use; optimization may remove the unused
// temporary
#[macro_export]
macro_rules! loop_body {
    ( ) => {
        #[rr::only_spec]
        #[allow(unused_variables)]
        let _ = || {};
    };
}
