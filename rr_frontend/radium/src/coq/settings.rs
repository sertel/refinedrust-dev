// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Mechanisms, called [settings], for changing the behaviour of Rocq.
//!
//! [settings]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#settings

use derive_more::{Display, From};

/// An [attribute].
///
/// [attribute]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#grammar-token-attribute
#[derive(Clone, Eq, PartialEq, Debug, Display, From)]
#[from(forward)]
#[display("{}", _0)]
pub struct Attribute(String);
