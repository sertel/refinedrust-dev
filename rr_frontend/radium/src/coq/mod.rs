// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! A collection of types for representing and generating [Rocq] code.
//!
//! These types are intended to be used for the purposes of the [RefinedRust project].
//! As such, they may not be suitable for general use.
//!
//! ---
//!
//! This crate defines structures in a similar way to the grammar defined in the [Rocq reference]
//! documentation, but unstructured sentences have been reunited under a single structure, such as
//! `Section`/`End`.
//!
//! The syntax used to create structures is designed to write as little code as possible, with choices
//! explained in the Notes section.
//!
//! Moreover, the crate is divided into several modules but does generally not follow the [Rocq reference].
//!
//! ---
//!
//! Following the [Rocq reference], most of the types can be structured as nested enumerations.
//! However, some types can take optional attributes that will be left empty most of the time:
//!  - Structures wrapping the element are required, suffixed with `Attrs`.
//!  - Consuming builder pattern, without any validation, is used to fill the attributes.
//!
//! ---
//!
//! Each enumeration derives the `From` trait for each variant, and each element wrapped in an `Attr`
//! structure are coerced into the parent enumeration using the same `From` trait.
//!
//! This concept makes sense when each arguments expects a type that can be coerced into the final expected
//! type, allowing the user not to explicitly write `.into()` everywhere.
//!
//! # Examples
//!
//! Let's write the following [Rocq] code:
//! ```text
//! From Coq.Strings Require Import String.
//! Open Scope string_scope.
//! Compute "Hello World".
//! ```
//!
//! This code can be generated with the following Rust code:
//! ```
//! # use radium::coq::{*, eval_new::*, module::*, syntax_new::*, term_new::*};
//! Document(vec![
//!     Sentence::CommandAttrs(CommandAttrs {
//!         attributes: None,
//!         command: Command::FromRequire(FromRequire {
//!             from: Some(DirPath(vec!["Coq".to_owned(), "Strings".to_owned()])),
//!             import: vec!["String".to_owned()],
//!             kind: Kind::Import,
//!         }),
//!     }),
//!     Sentence::CommandAttrs(CommandAttrs {
//!         attributes: None,
//!         command: Command::OpenScope(OpenScope("string_scope".to_owned())),
//!     }),
//!     Sentence::QueryCommandAttrs(QueryCommandAttrs {
//!         attributes: None,
//!         command: QueryCommand::Compute(Compute(Term::String("Hello World".to_owned()))),
//!         natural: None,
//!     }),
//! ]);
//! ```
//!
//! This code can be reduced using coercions in the following Rust code:
//! ```
//! # use radium::coq::{*, eval_new::*, module::*, syntax_new::*, term_new::*};
//! let mut doc = Document::default();
//!
//! doc.push(Command::FromRequire(Import::new(vec!["String"]).from(vec!["Coq", "Strings"]).into()));
//! doc.push(Command::OpenScope(OpenScope::new("string_scope")));
//! doc.push(QueryCommand::Compute(Compute(Term::String("Hello World".to_owned()))));
//! ```
//!
//! # Notes
//!
//! This section explains the various design decisions that have been made.
//! It also allows a developer to understand how to contribute to this crate.
//!
//! Throughout this section, let's take the following example:
//! ```
//! struct FieldAttrs {
//!     field: Field,
//!     attributes: Option<String>,
//! };
//!
//! enum Field {
//!     Foo,
//!     Bar,
//! };
//! ```
//!
//! ## Filling the attributes
//!
//! The following idiomatic code could be used, but it is too verbose as each field must be filled.
//! Also, this syntax is not resilient to future changes in the structure of types:
//! ```
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! FieldAttrs {
//!     field: Field::Foo,
//!     attributes: None,
//! };
//! ```
//!
//! The following idiomatic syntax cannot be used because some types contain an enumeration:
//! ``` compile_fail
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! FieldAttrs {
//!     field: Field::Foo,
//!     ..FieldAttrs::default()   // Error: `Field` is an enumeration without a default value.
//! };
//! ```
//!
//! Instead, the following builder pattern is preferred where mandatory fields are filled on creation, and
//! optional fields are filled with a method call:
//! ```
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! impl FieldAttrs {
//!     fn new(field: Field) -> Self {
//!         let attributes = None;
//!
//!         Self { field, attributes }
//!     }
//!
//!     fn attributes(self, attributes: String) -> Self {
//!         let attributes = Some(attributes);
//!
//!         Self { attributes, ..self }
//!     }
//! }
//!
//! FieldAttrs::new(Field::Foo).attributes("Hello".to_owned());
//! ```
//!
//! There are several builder patterns available, but the owned (_aka consuming_) builder pattern has been
//! chosen:
//!  - It is possible to chain method calls to keep everything concise.
//!  - There is no need to `.copy()`/`.clone()` objects to build the final object.
//!  - No verification is performed, which would be unmaintainable and currently outside the scope of this
//!    crate.
//!  - Therefore, there is no need to `.build()?` the object, as it can be considered built after each step.
//!
//! ## Type coercions
//!
//! Let's take the following code, which is simple but already verbose:
//! ```
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! # impl FieldAttrs {
//! #   fn new(field: Field) -> Self { Self { field, attributes: None } }
//! #   fn attributes(self, attributes: String) -> Self { Self { attributes: Some(attributes), ..self } }
//! # }
//! use derive_more::{Deref, DerefMut};
//!
//! #[derive(Deref, DerefMut)]
//! struct Entries(Vec<Entry>);
//!
//! enum Entry {
//!     FieldAttrs(FieldAttrs),
//! };
//!
//! Entries(vec![
//!     Entry::FieldAttrs(FieldAttrs::new(Field::Foo)),
//!     Entry::FieldAttrs(FieldAttrs::new(Field::Bar).attributes("Hello".to_owned())),
//! ]);
//! ```
//!
//! Writing the attribute structure can be unnecessarily verbose if no attributes are given.
//!
//! To avoid this, the `From<Field>` trait is derived for `Entry`, resulting in the following syntax:
//! ```
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! # impl FieldAttrs {
//! #   fn new(field: Field) -> Self { Self { field, attributes: None } }
//! #   fn attributes(self, attributes: String) -> Self { Self { attributes: Some(attributes), ..self } }
//! # }
//! use derive_more::{Deref, DerefMut};
//!
//! #[derive(Deref, DerefMut)]
//! struct Entries(Vec<Entry>);
//!
//! enum Entry {
//!     FieldAttrs(FieldAttrs),
//! };
//!
//! impl From<Field> for Entry {
//!     fn from(field: Field) -> Self {
//!         Self::FieldAttrs(FieldAttrs::new(field))
//!     }
//! }
//!
//! Entries(vec![
//!     Field::Foo.into(),
//!     Entry::FieldAttrs(FieldAttrs::new(Field::Bar).attributes("Hello".to_owned())),
//! ]);
//! ```
//!
//! Similarly, the `.into()` method can be derived for each enumeration variant using `FromVariant`:
//! ```
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! # impl FieldAttrs {
//! #   fn new(field: Field) -> Self { Self { field, attributes: None } }
//! #   fn attributes(self, attributes: String) -> Self { Self { attributes: Some(attributes), ..self } }
//! # }
//! # impl From<Field> for Entry {
//! #   fn from(field: Field) -> Self { Self::FieldAttrs(FieldAttrs::new(field)) }
//! # }
//! use derive_more::{Deref, DerefMut};
//! use from_variants::FromVariants;
//!
//! #[derive(Deref, DerefMut)]
//! struct Entries(Vec<Entry>);
//!
//! #[derive(FromVariants)]
//! enum Entry {
//!     FieldAttrs(FieldAttrs),
//! };
//!
//! Entries(vec![
//!     Field::Foo.into(),
//!     FieldAttrs::new(Field::Bar).attributes("Hello".to_owned()).into(),
//! ]);
//! ```
//!
//! ## Call-site into
//!
//! With this syntax, the caller will be filled with lots of `.into()`.
//!
//! This can be circumvented with function argument types. Instead of taking `T`, functions should take `impl
//! Into<T>`.
//!
//! <section class="warning">
//!
//! Although concise for user writing, this approach can be seen as a bad practice as monomorphising for each
//! `T` duplicates the function's body. In practice, the methods are tiny and easily inlineable by the
//! compiler.
//!
//! </section>
//!
//! Then, the previous example can be written using this syntax:
//! ```
//! # use from_variants::FromVariants;
//! # struct Entries(Vec<Entry>);
//! # #[derive(FromVariants)] enum Entry { FieldAttrs(FieldAttrs) };
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # impl FieldAttrs {
//! #   fn new(field: Field) -> Self { Self { field, attributes: None } }
//! # }
//! # enum Field { Foo, Bar };
//! # impl From<Field> for Entry {
//! #   fn from(field: Field) -> Self { Self::FieldAttrs(FieldAttrs::new(field)) }
//! # }
//! impl Entries {
//!     pub fn push(mut self, entry: impl Into<Entry>) -> Self {
//!         self.0.push(entry.into());
//!         self
//!     }
//! }
//!
//! impl FieldAttrs {
//!     fn attributes(self, attributes: impl Into<String>) -> Self {
//!         let attributes = Some(attributes.into());
//!         Self { attributes, ..self }
//!     }
//! }
//!
//! Entries(vec![]).push(Field::Foo).push(FieldAttrs::new(Field::Bar).attributes("Hello"));
//! ```
//!
//! <section class="warning">
//!
//! Heterogeneous datatypes do not exist in Rust, and coercions does not apply in the caller.
//! Therefore, the example cannot merge `Field` and `FieldAttrs`, and must use `.push()` instead.
//!
//! However, if there is a homogeneous list, an `impl Into` argument can be used:
//! ```
//! # use from_variants::FromVariants;
//! # struct Entries(Vec<Entry>);
//! # #[derive(FromVariants)] enum Entry { FieldAttrs(FieldAttrs) };
//! # struct FieldAttrs { field: Field, attributes: Option<String> };
//! # enum Field { Foo, Bar };
//! # impl FieldAttrs {
//! #   fn new(field: Field) -> Self { Self { field, attributes: None } }
//! # }
//! # impl From<Field> for Entry {
//! #   fn from(field: Field) -> Self { Self::FieldAttrs(FieldAttrs::new(field)) }
//! # }
//! impl Entries {
//!     fn new(entries: Vec<impl Into<Entry>>) -> Self {
//!         Self(entries.into_iter().map(Into::into).collect())
//!     }
//! }
//!
//! Entries::new(vec![Field::Foo, Field::Bar]);
//! ```
//!
//! In practice, this case is not expected to happen very often.
//!
//! </section>
//!
//! [RefinedRust project]: https://plv.mpi-sws.org/refinedrust/
//! [Rocq]: https://coq.inria.fr
//! [Rocq reference]: https://coq.inria.fr/doc/v8.20/refman/index.html
//! [sections]: https://coq.inria.fr/doc/v8.20/refman/language/core/sections.html

pub mod command;
pub mod eval_new;
pub mod module;
pub mod syntax_new;
pub mod term;
pub mod term_new;

use std::fmt;

use derive_more::{Deref, DerefMut, Display, From};
use from_variants::FromVariants;

use crate::display_list;

/// A [document].
///
/// [document]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-document
#[derive(Clone, Eq, PartialEq, Debug, Display, Default, Deref, DerefMut)]
#[display("{}\n", display_list!(_0, "\n"))]
pub struct Document(pub Vec<Sentence>);

impl Document {
    #[must_use]
    pub fn new(sentences: Vec<impl Into<Sentence>>) -> Self {
        Self(sentences.into_iter().map(Into::into).collect())
    }

    pub fn push(&mut self, sentence: impl Into<Sentence>) {
        self.0.push(sentence.into());
    }
}

/// A [sentence].
///
/// [sentence]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-sentence
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Sentence {
    #[display("{}", _0)]
    CommandAttrs(CommandAttrs),

    #[display("{}", _0)]
    QueryCommandAttrs(QueryCommandAttrs),
}

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

/// A [command].
///
/// [command]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-command
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Command {
    #[display("{}", _0)]
    FromRequire(module::FromRequire),

    #[display("{}", _0)]
    OpenScope(syntax_new::OpenScope),

    #[display("Proof")]
    Proof,
}

impl From<Command> for Sentence {
    fn from(command: Command) -> Self {
        Self::CommandAttrs(CommandAttrs::new(command))
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

/// A [query command].
///
/// [query command]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-query_command
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum QueryCommand {
    #[display("{}", _0)]
    Compute(eval_new::Compute),
}

impl From<QueryCommand> for Sentence {
    fn from(command: QueryCommand) -> Self {
        Self::QueryCommandAttrs(QueryCommandAttrs::new(command))
    }
}

/// An [attribute].
///
/// [attribute]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-attribute
#[derive(Clone, Eq, PartialEq, Debug, Display, From)]
#[from(forward)]
#[display("{}", _0)]
pub struct Attribute(String);

#[cfg(test)]
mod tests {
    use eval_new::Compute;
    use module::{DirPath, FromRequire, Import, Kind};
    use syntax_new::OpenScope;
    use term_new::Term;

    use super::*;

    #[test]
    fn hello_world_compact() {
        let mut doc = Document::default();

        doc.push(Command::FromRequire(Import::new(vec!["String"]).from(vec!["Coq", "Strings"]).into()));
        doc.push(Command::OpenScope(OpenScope::new("string_scope")));
        doc.push(QueryCommand::Compute(Compute(Term::String("Hello World".to_owned()))));

        assert_eq!(doc.to_string(), indoc::indoc! {r#"
            From Coq.Strings Require Import String.
            Open Scope string_scope.
            Compute "Hello World".
        "#});
    }

    #[test]
    fn hello_world_extended() {
        let doc = Document(vec![
            Sentence::CommandAttrs(CommandAttrs {
                attributes: None,
                command: Command::FromRequire(FromRequire {
                    from: Some(DirPath(vec!["Coq".to_owned(), "Strings".to_owned()])),
                    import: vec!["String".to_owned()],
                    kind: Kind::Import,
                }),
            }),
            Sentence::CommandAttrs(CommandAttrs {
                attributes: None,
                command: Command::OpenScope(OpenScope("string_scope".to_owned())),
            }),
            Sentence::QueryCommandAttrs(QueryCommandAttrs {
                attributes: None,
                command: QueryCommand::Compute(Compute(Term::String("Hello World".to_owned()))),
                natural: None,
            }),
        ]);

        assert_eq!(doc.to_string(), indoc::indoc! {r#"
            From Coq.Strings Require Import String.
            Open Scope string_scope.
            Compute "Hello World".
        "#});
    }
}
