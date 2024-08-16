// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [terms] section. This module will be renamed `term`.
//!
//! [terms]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#term-term

use derive_more::Display;
use from_variants::FromVariants;

/// A [term].
///
/// [term]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#grammar-token-term
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Term {
    #[display("\"{}\"", _0)]
    String(String),
}
