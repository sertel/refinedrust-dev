// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// A collection of types to represent and generate Rocq code.
///
/// These types are intended to be used for the purposes of this project.
use std::fmt;
use std::fmt::Write as fmtWrite;

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;

use crate::{display_list, make_indent, write_list, BASE_INDENT};

/// A Rocq path of the form `A.B.C`.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
#[display("{}", _0)]
pub struct Path(String);

impl Path {
    #[must_use]
    pub const fn new(path: String) -> Self {
        Self(path)
    }

    #[must_use]
    pub fn new_from_segments(segments: &[String]) -> Self {
        Self(segments.join("."))
    }
}

/// A Rocq module that contains a path `A.B.C` and a module name `D`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Module {
    path: Option<Path>,
    module: String,
}

impl Module {
    #[must_use]
    pub const fn new(module: String) -> Self {
        Self { module, path: None }
    }

    #[must_use]
    pub const fn new_with_path(module: String, path: Path) -> Self {
        Self {
            module,
            path: Some(path),
        }
    }

    #[must_use]
    pub fn get_path(&self) -> Option<Path> {
        self.path.as_ref().cloned()
    }
}

/// A Rocq import of the form `From A.B.C Require Import D`.
///
/// If the `path` is empty, it is of the form `Require Import A`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Import(pub Module);

impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.path {
            None => write!(f, "Require Import {}.\n", self.0.module),
            Some(ref path) => write!(f, "From {} Require Import {}.\n", path, self.0.module),
        }
    }
}

impl Import {
    #[must_use]
    pub const fn new(module: Module) -> Self {
        Self(module)
    }
}

/// A Rocq export of the form `From A.B.C Require Export D`.
///
/// If the `path` is empty, it is of the form `Require Export A`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Export(pub Module);

impl fmt::Display for Export {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.path {
            None => write!(f, "Require Export {}.\n", self.0.module),
            Some(ref path) => write!(f, "From {} Require Export {}.\n", path, self.0.module),
        }
    }
}

impl Export {
    #[must_use]
    pub const fn new(module: Module) -> Self {
        Self(module)
    }
}

/// Represents an application of a term to an rhs.
/// (commonly used for layouts and instantiating them with generics).
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct AppTerm<T> {
    pub(crate) lhs: T,
    pub(crate) rhs: Vec<String>,
}

impl<T: Display> Display for AppTerm<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write!(f, "({}", self.lhs)?;
        write_list!(f, &self.rhs, "", " ({})")?;
        write!(f, ")")
    }
}

impl<T> AppTerm<T> {
    pub fn new(lhs: T, rhs: Vec<String>) -> Self {
        Self { lhs, rhs }
    }

    pub fn new_lhs(lhs: T) -> Self {
        Self {
            lhs,
            rhs: Vec::new(),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Name {
    #[display("{}", _0)]
    Named(String),

    #[display("_")]
    Unnamed,
}

/// A Coq pattern, e.g., "x" or "'(x, y)".
pub type Pattern = String;

fn fmt_prod(v: &Vec<Type>) -> String {
    match v.as_slice() {
        [] => "unit".to_string(),
        [t] => t.to_string(),
        _ => format!("({})%type", display_list!(v, " * ")),
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Type {
    /// free variable that is bound, e.g., by a surrounding struct definition
    #[display("#{}", _0)]
    Var(usize),

    /// literal types that are not contained in the grammar
    #[display("{}", _0)]
    Literal(String),

    /// Placeholder that should be inferred by Coq if possible
    #[display("_")]
    Infer,

    /// Coq type `lft`
    #[display("lft")]
    Lft,

    /// Coq type `loc`
    #[display("loc")]
    Loc,

    /// Coq type `layout`
    #[display("layout")]
    Layout,

    /// Coq type `syn_type`
    #[display("syn_type")]
    SynType,

    /// Coq type `struct_layout`
    #[display("struct_layout")]
    StructLayout,

    /// Coq type `Type`
    #[display("Type")]
    Type,

    /// Coq type `type rt`
    #[display("(type {})", &_0)]
    Ttype(Box<Type>),

    /// Coq type `rtype`
    #[display("rtype")]
    Rtype,

    /// the unit type
    #[display("unit")]
    Unit,

    /// the type of integers
    #[display("Z")]
    Z,

    /// the type of booleans
    #[display("bool")]
    Bool,

    /// product types
    #[display("{}", fmt_prod(_0))]
    Prod(Vec<Type>),

    /// place_rfn
    #[display("(place_rfn {})", &_0)]
    PlaceRfn(Box<Type>),

    /// gname
    #[display("gname")]
    Gname,

    /// a plist with a given type constructor over a list of types
    #[display("plist {} [{}]", _0, display_list!(_1, "; ", "{} : Type"))]
    PList(String, Vec<Type>),
}

impl Type {
    /// Check if the `CoqType` contains a free variable `Var(i)`.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        match self {
            Self::Bool
            | Self::Z
            | Self::Unit
            | Self::Gname
            | Self::Infer
            | Self::Layout
            | Self::Lft
            | Self::Literal(..)
            | Self::Loc
            | Self::Rtype
            | Self::StructLayout
            | Self::SynType
            | Self::Type => true,

            Self::PList(_, tys) => tys.iter().all(Self::is_closed),

            Self::PlaceRfn(t) => t.is_closed(),

            Self::Prod(v) => v.iter().all(Self::is_closed),

            Self::Ttype(box ty) => ty.is_closed(),

            Self::Var(_) => false,
        }
    }

    /// Substitute variables `Var` according to the given substitution (variable `i` is mapped to
    /// index `i` in the vector).
    /// The types in `substi` should not contain variables themselves, as this substitution
    /// operation is capture-incurring!
    pub fn subst(&mut self, substi: &Vec<Self>) {
        match self {
            Self::Bool
            | Self::Z
            | Self::Unit
            | Self::Gname
            | Self::Infer
            | Self::Layout
            | Self::Lft
            | Self::Literal(..)
            | Self::Loc
            | Self::Rtype
            | Self::StructLayout
            | Self::SynType
            | Self::Type => (),

            Self::PList(_, tys) => {
                for t in tys.iter_mut() {
                    t.subst(substi);
                }
            },

            Self::PlaceRfn(box t) => {
                t.subst(substi);
            },

            Self::Prod(v) => {
                for t in v.iter_mut() {
                    t.subst(substi);
                }
            },

            Self::Ttype(box t) => t.subst(substi),

            Self::Var(i) => {
                if let Some(ta) = substi.get(*i) {
                    assert!(ta.is_closed());
                    *self = ta.clone();
                }
            },
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", self.format(true))]
pub struct Param {
    /// the name
    pub(crate) name: Name,

    /// the type
    pub(crate) ty: Type,

    /// implicit or not?
    pub(crate) implicit: bool,

    /// does this depend on Σ?
    pub(crate) depends_on_sigma: bool,
}

impl Param {
    #[must_use]
    pub fn new(name: Name, ty: Type, implicit: bool) -> Self {
        let depends_on_sigma = if let Type::Literal(ref lit) = ty { lit.contains('Σ') } else { false };

        Self {
            name,
            ty,
            implicit,
            depends_on_sigma,
        }
    }

    #[must_use]
    pub fn with_name(&self, name: String) -> Self {
        Self::new(Name::Named(name), self.ty.clone(), self.implicit)
    }

    #[allow(clippy::collapsible_else_if)]
    #[must_use]
    pub fn format(&self, make_implicits: bool) -> String {
        if !self.implicit {
            return format!("({} : {})", self.name, self.ty);
        }

        if make_implicits {
            if let Name::Named(ref name) = self.name {
                format!("`{{{} : !{}}}", name, self.ty)
            } else {
                format!("`{{!{}}}", self.ty)
            }
        } else {
            if let Name::Named(ref name) = self.name {
                format!("`({} : !{})", name, self.ty)
            } else {
                format!("`(!{})", self.ty)
            }
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, " "))]
pub struct ParamList(Vec<Param>);

impl ParamList {
    #[must_use]
    pub const fn new(params: Vec<Param>) -> Self {
        Self(params)
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}", name, params)]
pub struct Variant {
    pub name: String,
    pub params: ParamList,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Inductive {} {} :=\n{}\n.", name, parameters,
    display_list!(variants, "\n| ").indented(&make_indent(1))
)]
pub struct Inductive {
    pub name: String,
    pub parameters: ParamList,
    pub variants: Vec<Variant>,
}

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

/// A Coq Gallina term.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum GallinaTerm {
    #[display("{}.", _0)]
    Literal(String),
}

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
    Term(GallinaTerm),
}

impl Display for DefBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Script(script, terminator) => {
                write!(f, ".\n")?;
                write!(f, "Proof.\n")?;
                let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
                write!(f2, "{}", script)?;
                write!(f, "{}.\n", terminator)?;
            },
            Self::Term(term) => {
                write!(f, " := {}.\n", term)?;
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
}

/// A Coq typeclass instance declaration
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct InstanceDecl {
    pub attrs: Attributes,
    pub name: Option<String>,
    pub params: ParamList,
    pub ty: Type,
    pub body: DefBody,
}

impl Display for InstanceDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.name {
            Some(ref name) => {
                write!(f, "{} Instance {} {} : {}{}", self.attrs, name, self.params, self.ty, self.body)
            },
            None => write!(f, "{} Instance {} : {}{}", self.attrs, self.params, self.ty, self.body),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum TopLevelAssertion {
    /// A declaration of a Coq Inductive
    #[display("{}", _0)]
    InductiveDecl(Inductive),

    /// A declaration of a Coq instance
    #[display("{}", _0)]
    InstanceDecl(InstanceDecl),

    /// A Coq comment
    #[display("(* {} *)", _0)]
    Comment(String),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TopLevelAssertions(pub Vec<TopLevelAssertion>);

impl TopLevelAssertions {
    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn push(&mut self, a: TopLevelAssertion) {
        self.0.push(a);
    }
}

impl Display for TopLevelAssertions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for a in &self.0 {
            writeln!(f, "{a}")?;
        }
        Ok(())
    }
}
