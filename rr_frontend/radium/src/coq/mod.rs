// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// A collection of types to represent and generate [Rocq] code.
///
/// These types are intended to be used for the purposes of the [RefinedRust project].
/// As such, they may not be suitable for general use.
///
/// This crate is split up in the same way as the [Rocq reference documentation].
///
/// [RefinedRust project]: https://plv.mpi-sws.org/refinedrust/
/// [Rocq]: https://coq.inria.fr
/// [Rocq reference]: https://coq.inria.fr/doc/master/refman/index.html
pub mod command;
pub mod module;
pub mod term;
