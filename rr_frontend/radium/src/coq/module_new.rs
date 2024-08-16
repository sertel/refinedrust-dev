// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [module] section. This module will be renamed `module`.
//!
//! [module]: https://coq.inria.fr/doc/master/refman/language/core/modules.html

use std::fmt;

use derive_more::{Deref, DerefMut, Display, From, Into};

use crate::{display_list, write_list};

/// A [dirpath].
///
/// [dirpath]: https://coq.inria.fr/doc/master/refman/proof-engine/vernacular-commands.html#grammar-token-dirpath
#[derive(Clone, Eq, PartialEq, Debug, Display, Default, Deref, DerefMut)]
#[display("{}", display_list!(_0, "."))]
pub struct DirPath(pub Vec<String>);

impl From<Vec<&str>> for DirPath {
    fn from(v: Vec<&str>) -> Self {
        Self(v.into_iter().map(ToString::to_string).collect())
    }
}

/// Either an Import or an Export flag.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Kind {
    Import,
    Export,
}

/// The [`From ... Require`] command.
///
/// [`From ... Require`]: https://coq.inria.fr/doc/master/refman/proof-engine/vernacular-commands.html#coq:cmd.From-%E2%80%A6-Require
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FromRequire {
    pub from: Option<String>,
    pub import: Vec<DirPath>,
    pub kind: Kind,
}

impl FromRequire {
    #[must_use]
    pub fn new(import: Vec<impl Into<DirPath>>, kind: Kind) -> Self {
        let from = None;
        let import = import.into_iter().map(Into::into).collect();

        Self { from, import, kind }
    }

    #[allow(clippy::same_name_method)]
    #[must_use]
    pub fn from(self, from: impl Into<String>) -> Self {
        let from = Some(from.into());

        Self { from, ..self }
    }
}

impl Display for FromRequire {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(from) = &self.from {
            write!(f, "From {} ", from)?;
        }

        match self.kind {
            Kind::Import => write!(f, "Require Import ")?,
            Kind::Export => write!(f, "Require Export ")?,
        };

        write_list!(f, &self.import, " ")
    }
}

/// A wrapper over [`FromRequire`] to represent an import list.
#[derive(Clone, Eq, PartialEq, Debug, Deref, DerefMut, Into)]
pub struct Import(pub FromRequire);

impl Import {
    pub fn new(import: Vec<impl Into<DirPath>>) -> Self {
        Self(FromRequire::new(import, Kind::Import))
    }

    #[must_use]
    pub fn from(self, from: impl Into<String>) -> Self {
        Self(self.0.from(from))
    }
}

/// A wrapper over [`FromRequire`] to represent an export list.
#[derive(Clone, Eq, PartialEq, Debug, Deref, DerefMut, Into)]
pub struct Export(pub FromRequire);

impl Export {
    pub fn new(import: Vec<impl Into<DirPath>>) -> Self {
        Self(FromRequire::new(import, Kind::Export))
    }

    #[must_use]
    pub fn from(self, from: impl Into<String>) -> Self {
        Self(self.0.from(from))
    }
}
