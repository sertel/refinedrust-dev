// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// [Sections].
///
/// [Sections]: https://coq.inria.fr/doc/v8.20/refman/language/core/sections.html
use derive_more::Display;

#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
#[display("Section {}", name)]
pub struct Section {
    name: String,
}

impl Section {
    pub fn new(name: String) -> Self {
        Self { name }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}
