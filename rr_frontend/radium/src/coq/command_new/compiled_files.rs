// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;

/// A [dirpath].
///
/// [dirpath]: https://coq.inria.fr/doc/master/refman/proof-engine/vernacular-commands.html#grammar-token-dirpath
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct DirPath(Vec<String>);

/// Either an Import or an Export flag.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Kind {
    Import,
    Export,
}

/// A [`From ... Require`] command.
///
/// [`From ... Require`]: https://coq.inria.fr/doc/master/refman/proof-engine/vernacular-commands.html#coq:cmd.From-%E2%80%A6-Require
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FromRequire {
    pub from: Option<String>,
    pub import: Vec<String>,
    pub kind: Kind,
}

impl FromRequire {
    #[must_use]
    pub fn new(import: Vec<impl Into<String>>, kind: Kind) -> Self {
        let from = None;
        let import = import.into_iter().map(Into::into).collect();

        Self { from, kind, import }
    }

    #[must_use]
    pub fn from(self, from: impl Into<String>) -> Self {
        let from = Some(from.into());

        Self { from, ..self }
    }
}

impl fmt::Display for FromRequire {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "")
    }
}
