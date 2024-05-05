// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;
use std::fmt::Write as fmtWrite;

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;

use crate::{display_list, make_indent, write_list};

pub(crate) const BASE_INDENT: &str = "  ";

/// Represents a Coq path of the form
/// `From A.B.C Import D`
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CoqPath {
    pub path: Option<String>,
    pub module: String,
}

impl fmt::Display for CoqPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.path {
            None => write!(f, "Require Export {}.\n", self.module),
            Some(ref path) => write!(f, "From {} Require Export {}.\n", path, self.module),
        }
    }
}

/// Represents an application of a term to an rhs.
/// (commonly used for layouts and instantiating them with generics).
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CoqAppTerm<T> {
    pub(crate) lhs: T,
    pub(crate) rhs: Vec<String>,
}

impl<T: Display> Display for CoqAppTerm<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write!(f, "({}", self.lhs)?;
        write_list!(f, &self.rhs, "", " ({})")?;
        write!(f, ")")
    }
}

impl<T> CoqAppTerm<T> {
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
pub enum CoqName {
    #[display("{}", _0)]
    Named(String),

    #[display("_")]
    Unnamed,
}

/// A Coq pattern, e.g., "x" or "'(x, y)".
pub type CoqPattern = String;

fn fmt_prod(v: &Vec<CoqType>) -> String {
    match v.as_slice() {
        [] => "unit".to_string(),
        [t] => t.to_string(),
        _ => format!("({})%type", display_list!(v, " * ")),
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum CoqType {
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
    Ttype(Box<CoqType>),

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
    Prod(Vec<CoqType>),

    /// place_rfn
    #[display("(place_rfn {})", &_0)]
    PlaceRfn(Box<CoqType>),

    /// gname
    #[display("gname")]
    Gname,

    /// a plist with a given type constructor over a list of types
    #[display("plist {} [{}]", _0, display_list!(_1, "; ", "{} : Type"))]
    PList(String, Vec<CoqType>),
}

impl CoqType {
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
#[display("{}", display_list!(_0, " ", |(name, ty)| format!("({} : {})", name, ty)))]
pub struct CoqParamList(pub Vec<(CoqName, CoqType)>);

impl CoqParamList {
    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}", name, params)]
pub struct CoqVariant {
    pub name: String,
    pub params: CoqParamList,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Inductive {} {} :=\n{}\n.", name, parameters,
    display_list!(variants, "\n| ").indented(&make_indent(1))
)]
pub struct CoqInductive {
    pub name: String,
    pub parameters: CoqParamList,
    pub variants: Vec<CoqVariant>,
}

/// A single tactic call.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum CoqProofItem {
    #[display("{}.", _0)]
    Literal(String),
}

/// A Coq proof script.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}\n", display_list!(_0, "\n"))]
pub struct CoqProofScript(pub Vec<CoqProofItem>);

/// A Coq Gallina term.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum GallinaTerm {
    #[display("{}.", _0)]
    Literal(String),
}

/// A terminator for a proof script
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum CoqProofScriptTerminator {
    #[display("Qed")]
    Qed,

    #[display("Defined")]
    Defined,

    #[display("Admitted")]
    Admitted,
}

/// A body of a Coq definition
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum CoqDefBody {
    /// a proof script invoking Ltac tactics
    Script(CoqProofScript, CoqProofScriptTerminator),

    /// a proof term
    Term(GallinaTerm),
}

impl Display for CoqDefBody {
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
pub enum CoqAttribute {
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
pub struct CoqAttributes {
    attrs: Vec<CoqAttribute>,
}

impl CoqAttributes {
    #[must_use]
    pub const fn empty() -> Self {
        Self { attrs: vec![] }
    }

    #[must_use]
    pub fn new(attrs: Vec<CoqAttribute>) -> Self {
        Self { attrs }
    }
}

/// A Coq typeclass instance declaration
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqInstanceDecl {
    pub attrs: CoqAttributes,
    pub name: Option<String>,
    pub params: CoqParamList,
    pub ty: CoqType,
    pub body: CoqDefBody,
}

impl Display for CoqInstanceDecl {
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
pub enum CoqTopLevelAssertion {
    /// A declaration of a Coq Inductive
    #[display("{}", _0)]
    InductiveDecl(CoqInductive),

    /// A declaration of a Coq instance
    #[display("{}", _0)]
    InstanceDecl(CoqInstanceDecl),

    /// A Coq comment
    #[display("(* {} *)", _0)]
    Comment(String),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqTopLevelAssertions(pub Vec<CoqTopLevelAssertion>);

impl CoqTopLevelAssertions {
    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn push(&mut self, a: CoqTopLevelAssertion) {
        self.0.push(a);
    }
}

impl Display for CoqTopLevelAssertions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for a in &self.0 {
            writeln!(f, "{a}")?;
        }
        Ok(())
    }
}
