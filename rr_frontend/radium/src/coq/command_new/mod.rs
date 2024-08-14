// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

pub mod compiled_files;

use derive_more::Display;
use from_variants::FromVariants;

use crate::coq;
use crate::coq::settings;

/// A [command], with optional attributes.
///
/// [command]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#grammar-token-command
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}.", command, attributes.as_ref().map_or(String::new(), |a| a.to_string()))]
pub struct CommandAttrs {
    pub command: Command,
    pub attributes: Option<settings::Attribute>,
}

impl CommandAttrs {
    #[must_use]
    pub fn new(command: impl Into<Command>) -> Self {
        Self {
            attributes: None,
            command: command.into(),
        }
    }

    #[must_use]
    pub fn attributes(self, attributes: impl Into<settings::Attribute>) -> Self {
        let attributes = Some(attributes.into());

        Self { attributes, ..self }
    }
}

/// A [command].
///
/// [command]: https://coq.inria.fr/doc/master/refman/coq-cmdindex.html#command-index
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Command {
    #[display("{}", _0)]
    FromRequire(compiled_files::FromRequire),

    #[display("Proof")]
    Proof,
}

impl From<Command> for coq::Sentence {
    fn from(command: Command) -> Self {
        Self::CommandAttrs(CommandAttrs::new(command))
    }
}
