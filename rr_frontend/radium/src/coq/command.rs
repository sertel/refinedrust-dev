// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Rocq commands.
use std::fmt;
use std::fmt::Write as fmtWrite;

use derive_more::Display;
use indent_write::fmt::IndentWriter;

use crate::coq::term;
use crate::{display_list, BASE_INDENT};

/// A single tactic call.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum ProofItem {
    #[display("{}.", _0)]
    Literal(String),
}

/// A Coq proof script.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}\n", display_list!(_0, "\n"))]
pub struct ProofScript(pub Vec<ProofItem>);

/// A terminator for a proof script
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum ProofScriptTerminator {
    #[display("Qed")]
    Qed,

    #[display("Defined")]
    Defined,

    #[display("Admitted")]
    Admitted,
}

/// A body of a Coq definition
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum DefBody {
    /// a proof script invoking Ltac tactics
    Script(ProofScript, ProofScriptTerminator),

    /// a proof term
    Term(term::Gallina),
}

impl Display for DefBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Script(script, terminator) => {
                write!(f, ".\n")?;
                write!(f, "Proof.\n")?;
                let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
                write!(f2, "{}", script)?;
                write!(f, "{}.", terminator)?;
            },
            Self::Term(term) => {
                write!(f, " := {}.", term)?;
            },
        }
        Ok(())
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Attribute {
    #[display("global")]
    Global,

    #[display("local")]
    Local,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}",
    if attrs.is_empty() { String::new() } else {
        format!("#[ {} ]", display_list!(attrs, ", "))
    }
)]
pub struct Attributes {
    attrs: Vec<Attribute>,
}

impl Attributes {
    #[must_use]
    pub const fn empty() -> Self {
        Self { attrs: vec![] }
    }

    #[must_use]
    pub fn new(attrs: Vec<Attribute>) -> Self {
        Self { attrs }
    }

    #[must_use]
    pub fn singleton(attr: Attribute) -> Self {
        Self { attrs: vec![attr] }
    }
}

/// A Coq typeclass instance declaration
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("#[global] Instance : {}{}", ty, body)]
pub struct InstanceDecl {
    ty: term::Type,
    body: DefBody,
}

impl InstanceDecl {
    #[must_use]
    pub const fn new(ty: term::Type, body: DefBody) -> Self {
        Self { ty, body }
    }
}

#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[display("{} {} : {}", name, params, ty)]
pub struct RecordDeclItem {
    pub name: String,
    pub params: term::ParamList,
    pub ty: term::Type,
}

/// A record declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub name: String,
    pub params: term::ParamList,
    pub ty: term::Type,
    pub constructor: Option<String>,
    pub body: Vec<RecordDeclItem>,
}

impl Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let constructor = self.constructor.clone().unwrap_or_default();
        write!(f, "Record {} {} : {} := {constructor} {{\n", self.name, self.params, self.ty)?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.body {
            write!(f2, "{it};\n")?;
        }
        write!(f, "}}.")
    }
}

/// A Context declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextDecl {
    pub items: term::ParamList,
}

impl ContextDecl {
    #[must_use]
    pub const fn new(items: term::ParamList) -> Self {
        Self { items }
    }

    #[must_use]
    pub fn refinedrust() -> Self {
        Self {
            items: term::ParamList::new(vec![term::Param::new(
                term::Name::Named("RRGS".to_owned()),
                term::Type::Literal("refinedrustGS Σ".to_owned()),
                true,
            )]),
        }
    }
}

impl Display for ContextDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.items.0.is_empty() { Ok(()) } else { write!(f, "Context {}.", self.items) }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub enum DefinitionKind {
    #[display("Definition")]
    Definition,
    #[display("Lemma")]
    Lemma,
}

/// A Coq definition
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub name: String,
    pub params: term::ParamList,
    pub ty: Option<term::Type>,
    pub body: DefBody,
    pub kind: DefinitionKind,
}

impl Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ty) = &self.ty {
            write!(f, "{} {} {} : {ty}{}", self.kind, self.name, self.params, self.body)
        } else {
            write!(f, "{} {} {}{}", self.kind, self.name, self.params, self.body)
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum TopLevelAssertion<'a> {
    /// A declaration of a Coq Inductive
    #[display("{}", _0)]
    InductiveDecl(&'a term::Inductive),

    /// A declaration of a Coq instance
    #[display("{}", _0)]
    InstanceDecl(&'a InstanceDecl),

    /// A declaration of a Coq record
    #[display("{}", _0)]
    RecordDecl(Record),

    /// A declaration of Coq context items
    #[display("{}", _0)]
    ContextDecl(ContextDecl),

    /// A Coq Definition
    #[display("{}", _0)]
    Definition(Definition),

    /// A Coq comment
    #[display("(* {} *)", _0)]
    Comment(&'a str),

    /// A Coq section
    #[display("Section {}.\n{}End{}.", _0, Indented::new(_1), _0)]
    Section(String, TopLevelAssertions<'a>),

    /// A Coq section start
    #[display("Section {}.", _0)]
    SectionStart(String),

    /// A Coq section end
    #[display("End {}.", _0)]
    SectionEnd(String),
}

/// Type for writing contents indented via Display.
struct Indented<T> {
    x: T,
}
impl<T> Indented<T> {
    pub const fn new(x: T) -> Self {
        Self { x }
    }
}
impl<T: Display> Display for Indented<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut indent_writer = IndentWriter::new(BASE_INDENT, f);
        write!(indent_writer, "{}", self.x)
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, "\n"))]
pub struct TopLevelAssertions<'a>(pub Vec<TopLevelAssertion<'a>>);

impl<'a> TopLevelAssertions<'a> {
    #[must_use]
    pub(crate) const fn empty() -> Self {
        Self(vec![])
    }

    pub(crate) fn push(&mut self, a: TopLevelAssertion<'a>) {
        self.0.push(a);
    }
}
