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
//! This crate is divided in a similar way to the grammar defined in the [Rocq reference] documentation, but
//! is not followed strictly:
//!  - Unstructured sentences have been reunited under a single structure, such as `Section`/`End`.
//!  - Some cases are unified for simplicity, such as `command`/`control_command`/`query_command`.
//!
//! The syntax used to create structures is designed to write as little code as possible, with choices
//! explained in the Notes section.
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
//! # use radium::coq::*;
//! // Document(vec![
//! //   TODO
//! // ]);
//! ```
//!
//! This code can be reduced using coercions in the following Rust code:
//! ```
//! # use radium::coq::*;
//! // Document::new(vec![
//! //   TODO
//! // ]);
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
//! FieldAttrs::new(Field::Foo).attributes("Hello".to_string());
//! ```
//!
//! There are several builder patterns available, but owned (_aka consuming_) builder pattern has been chosen:
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
//!     Entry::FieldAttrs(FieldAttrs::new(Field::Bar).attributes("Hello".to_string())),
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
//!     Entry::FieldAttrs(FieldAttrs::new(Field::Bar).attributes("Hello".to_string())),
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
//!     FieldAttrs::new(Field::Bar).attributes("Hello".to_string()).into(),
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
//! Heteregeneous does not exist in Rust, and coercion does not apply in the caller.
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
//! [Rocq reference]: https://coq.inria.fr/doc/master/refman/index.html
//! [sections]: https://coq.inria.fr/doc/master/refman/language/core/sections.html

pub mod command;
pub mod command_new;
pub mod module;
pub mod settings;
pub mod term;

use std::fmt;

use derive_more::{Deref, DerefMut, Display, From};
use derive_new::new;
use from_variants::FromVariants;
use indoc::writedoc;

use crate::display_list;

/// A [document].
///
/// [document]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#grammar-token-document
#[derive(Clone, Eq, PartialEq, Debug, Display, Default, Deref, DerefMut)]
#[display("{}", display_list!(_0, "\n"))]
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
/// [sentence]: https://coq.inria.fr/doc/master/refman/language/core/basic.html#grammar-token-sentence
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Sentence {
    #[display("{}", _0)]
    CommandAttrs(command_new::CommandAttrs),
}

#[cfg(test)]
mod tests {
    use command_new::compiled_files::*;
    use command_new::*;

    use super::*;

    #[test]
    fn test_document() {
        let mut doc = Document::new(vec![
            Command::FromRequire(
                FromRequire::new(vec!["nat", "bool"], Kind::Import).from("Coq.Init.Datatypes"),
            ),
            Command::Proof,
        ]);

        doc.push(Command::FromRequire(
            FromRequire::new(vec!["nat", "bool"], Kind::Import).from("Coq.Init.Datatypes"),
        ));
        doc.push(Command::Proof);
        doc.push(CommandAttrs::new(Command::Proof).attributes("Some"));
    }
}
