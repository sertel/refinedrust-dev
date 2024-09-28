// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [syntax and notations] section.
//!
//! [syntax and notations]: https://coq.inria.fr/doc/v8.20/refman/user-extensions/syntax-extensions.html

use derive_more::{Deref, DerefMut, Display, From};

/// The [`Open Scope`] command.
///
/// [`Open Scope`]: https://coq.inria.fr/doc/v8.20/refman/user-extensions/syntax-extensions.html#coq:cmd.Open-Scope
#[derive(Clone, Eq, PartialEq, Debug, Display, Default, Deref, DerefMut, From)]
#[from(forward)]
#[display("Open Scope {}", _0)]
pub struct OpenScope(pub String);

impl OpenScope {
    pub fn new(scope: impl Into<String>) -> Self {
        Self(scope.into())
    }
}
