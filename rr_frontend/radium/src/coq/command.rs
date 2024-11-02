// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [command] section.
//!
//! [command]: https://coq.inria.fr/doc/v8.20/refman/coq-cmdindex.html

use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;
use indent_write::indentable::Indentable;

use crate::coq::{binder, eval, inductive, module, syntax, term, typeclasses, Attribute, Document, Sentence};
use crate::make_indent;

/// A [command], with optional attributes.
///
/// [command]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-command
#[allow(clippy::module_name_repetitions)]
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

    /// The [`Inductive`] command.
    ///
    /// [`Inductive`]: https://coq.inria.fr/doc/v8.20/refman/language/core/inductive.html#inductive-types
    #[display("{}", _0)]
    Inductive(inductive::Inductive),

    /// The [`Instance`] command.
    ///
    /// [`Instance`]: https://coq.inria.fr/doc/v8.20/refman/addendum/type-classes.html#coq:cmd.Instance
    #[display("{}", _0)]
    Instance(typeclasses::Instance),

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

    /// The [`Qed`] command.
    ///
    /// [`Qed`]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Qed
    #[display("Qed")]
    Qed,

    /* TODO */
    #[display("{}", _0)]
    RecordDecl(term::Record),

    #[display("{}", _0)]
    ContextDecl(ContextDecl),

    #[display("{}", _0)]
    Definition(Definition),

    #[display("Section {}.\n{}End {}.", _0.0, _0.1.to_string().indented(&make_indent(1)), _0.0)]
    Section((String, Document)),
}

impl From<Command> for Sentence {
    fn from(command: Command) -> Self {
        Self::CommandAttrs(CommandAttrs::new(command))
    }
}

/// A [query command].
///
/// [query command]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-query_command
#[allow(clippy::module_name_repetitions)]
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

/* TODO */
/// A Context declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextDecl {
    pub items: binder::BinderList,
}

impl ContextDecl {
    #[must_use]
    pub const fn new(items: binder::BinderList) -> Self {
        Self { items }
    }

    #[must_use]
    pub fn refinedrust() -> Self {
        Self {
            items: binder::BinderList::new(vec![binder::Binder::new_generalized(
                binder::Kind::MaxImplicit,
                Some("RRGS".to_owned()),
                term::Type::Literal("refinedrustGS Σ".to_owned()),
            )]),
        }
    }
}

impl Display for ContextDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.items.0.is_empty() { Ok(()) } else { write!(f, "Context {}", self.items) }
    }
}

/// A Rocq definition
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: Option<term::Type>,
    pub body: term::Gallina,
}

impl Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ty) = &self.ty {
            write!(f, "Definition {} {} : {ty} := {}", self.name, self.params, self.body)
        } else {
            write!(f, "Definition {} {} := {}", self.name, self.params, self.body)
        }
    }
}
