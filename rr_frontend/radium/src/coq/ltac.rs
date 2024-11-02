// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [LTac] section.
//!
//! [LTac]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/ltac.html#ltac

use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;

use crate::coq::{Attribute, Sentence};

/// A [tactic], with optional attributes.
///
/// [tactic]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/ltac.html#grammar-token-ltac_expr
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct LTacAttrs {
    pub ltac: LTac,
    pub attributes: Option<Attribute>,
}

impl Display for LTacAttrs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(attributes) = &self.attributes {
            write!(f, "{} ", attributes)?;
        }

        write!(f, "{}.", self.ltac)
    }
}

impl LTacAttrs {
    #[must_use]
    pub fn new(ltac: impl Into<LTac>) -> Self {
        Self {
            attributes: None,
            ltac: ltac.into(),
        }
    }

    #[must_use]
    pub fn attributes(self, attributes: impl Into<Attribute>) -> Self {
        let attributes = Some(attributes.into());

        Self { attributes, ..self }
    }
}

/// A [tactic].
///
/// [tactic]: https://coq.inria.fr/doc/v8.20/refman/coq-tacindex.html
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum LTac {
    Literal(String),
}

impl From<LTac> for Sentence {
    fn from(ltac: LTac) -> Self {
        Self::LTacAttrs(LTacAttrs::new(ltac))
    }
}
