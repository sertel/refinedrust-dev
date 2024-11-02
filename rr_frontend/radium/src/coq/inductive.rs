// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [inductive] section.
//!
//! [inductive]: https://coq.inria.fr/doc/v8.20/refman/language/core/inductive.html#inductive-types-and-recursive-functions

use derive_more::{Constructor, Display};
use indent_write::indentable::Indentable;

use crate::coq::binder;
use crate::{display_list, make_indent};

/// An [Inductive] type.
///
/// [`Inductive`]: https://coq.inria.fr/doc/v8.20/refman/language/core/inductive.html#inductive-types
#[derive(Clone, Eq, PartialEq, Debug, Display, Constructor)]
#[display("Inductive {} {} :=\n{}\n",
    name,
    parameters,
    display_list!(variants, "\n| ").indented(&make_indent(1))
)]
pub struct Inductive {
    name: String,
    parameters: binder::BinderList,
    variants: Vec<Variant>,
}

impl Inductive {
    #[must_use]
    pub const fn get_name(&self) -> &String {
        &self.name
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}", name, display_list!(params, " "))]
pub struct Variant {
    name: String,
    params: Vec<binder::Binder>,
}

impl Variant {
    #[must_use]
    pub fn new(name: String, params: Vec<binder::Binder>) -> Self {
        Self { name, params }
    }
}
