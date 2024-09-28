use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;

use crate::coq::{eval, module, syntax, typeclasses, Attribute, Sentence};

/// A [command], with optional attributes.
///
/// [command]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-command
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CommandAttrs {
    pub command: Command,
    pub attributes: Option<Attribute>,
}

impl Display for CommandAttrs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(attributes) = &self.attributes {
            write!(f, "{} ", attributes)?;
        }

        write!(f, "{}.", self.command)
    }
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
    pub fn attributes(self, attributes: impl Into<Attribute>) -> Self {
        let attributes = Some(attributes.into());

        Self { attributes, ..self }
    }
}

/// A [query command], with optional attributes.
///
/// [query command]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-query_command
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct QueryCommandAttrs {
    pub command: QueryCommand,
    pub natural: Option<i32>,
    pub attributes: Option<Attribute>,
}

impl Display for QueryCommandAttrs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(attributes) = &self.attributes {
            write!(f, "{} ", attributes)?;
        }

        if let Some(natural) = &self.natural {
            write!(f, "{}: ", natural)?;
        }

        write!(f, "{}.", self.command)
    }
}

impl QueryCommandAttrs {
    #[must_use]
    pub fn new(command: impl Into<QueryCommand>) -> Self {
        Self {
            attributes: None,
            natural: None,
            command: command.into(),
        }
    }

    #[must_use]
    pub fn attributes(self, attributes: impl Into<Attribute>) -> Self {
        let attributes = Some(attributes.into());

        Self { attributes, ..self }
    }
}

/// A [command].
///
/// [command]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-command
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Command {
    /// The [`From ... Require`] command.
    ///
    /// [`From ... Require`]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#coq:cmd.From-%E2%80%A6-Require
    #[display("{}", _0)]
    FromRequire(module::FromRequire),

    /// The [`Proof`] command.
    ///
    /// [`Proof`]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Proof
    #[display("Proof")]
    Proof,

    /// The [`Open Scope`] command.
    ///
    /// [`Open Scope`]: https://coq.inria.fr/doc/v8.20/refman/user-extensions/syntax-extensions.html#coq:cmd.Open-Scope
    #[display("{}", _0)]
    OpenScope(syntax::OpenScope),
}

impl From<Command> for Sentence {
    fn from(command: Command) -> Self {
        Self::CommandAttrs(CommandAttrs::new(command))
    }
}

/// A [query command].
///
/// [query command]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-query_command
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum QueryCommand {
    #[display("{}", _0)]
    Compute(eval::Compute),
}

impl From<QueryCommand> for Sentence {
    fn from(command: QueryCommand) -> Self {
        Self::QueryCommandAttrs(QueryCommandAttrs::new(command))
    }
}
