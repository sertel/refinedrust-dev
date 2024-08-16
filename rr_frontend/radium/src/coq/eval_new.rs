// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [eval] section. This module will be renamed `eval`.
//!
//! [eval]: https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#computing-in-a-term-eval-and-eval

use derive_more::{Deref, DerefMut, Display};

use crate::coq::term_new;

/// The [`Compute`] command.
///
/// [`Compute`]: https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#coq:cmd.Compute
#[derive(Clone, Eq, PartialEq, Debug, Display, Deref, DerefMut)]
#[display("Compute {}", _0)]
pub struct Compute(pub term_new::Term);
