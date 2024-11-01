// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [typeclasses] section.
//!
//! [typeclasses]: https://coq.inria.fr/doc/v8.20/refman/addendum/type-classes.html

use derive_more::Display;

use crate::coq::term;

/// The [`Instance`] command.
///
/// [`Instance`]: https://coq.inria.fr/doc/v8.20/refman/addendum/type-classes.html#coq:cmd.Instance
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Instance: {}", _0)]
pub struct Instance(pub term::Type);
