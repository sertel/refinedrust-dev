// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;
use std::fmt::{Display, Formatter, Write};

use indent_write::fmt::IndentWriter;

use crate::write_list;

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

impl<T> fmt::Display for CoqAppTerm<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write!(f, "({}", self.lhs)?;
        for r in &self.rhs {
            write!(f, " ({})", r)?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum CoqName {
    Named(String),
    Unnamed,
}

impl Display for CoqName {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Named(s) => write!(f, "{}", s),
            Self::Unnamed => write!(f, "_"),
        }
    }
}

/// A Coq pattern, e.g., "x" or "'(x, y)".
pub type CoqPattern = String;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum CoqType {
    /// free variable that is bound, e.g., by a surrounding struct definition
    Var(usize),
    /// literal types that are not contained in the grammar
    Literal(String),
    /// Placeholder that should be inferred by Coq if possible
    Infer,
    /// Coq type `lft`
    Lft,
    /// Coq type `loc`
    Loc,
    /// Coq type `layout`
    Layout,
    /// Coq type `syn_type`
    SynType,
    /// Coq type `struct_layout`
    StructLayout,
    /// Coq type `Type`
    Type,
    /// Coq type `type rt`
    Ttype(Box<CoqType>),
    /// Coq type `rtype`
    Rtype,
    /// the unit type
    Unit,
    /// the type of integers
    Z,
    /// the type of booleans
    Bool,
    /// product types
    Prod(Vec<CoqType>),
    /// place_rfn
    PlaceRfn(Box<CoqType>),
    /// gname
    Gname,
    /// a plist with a given type constructor over a list of types
    PList(String, Vec<CoqType>),
}

impl Display for CoqType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::Z => write!(f, "Z"),
            Self::Unit => write!(f, "unit"),

            Self::Gname => write!(f, "gname"),
            Self::Infer => write!(f, "_"),
            Self::Layout => write!(f, "layout"),
            Self::Lft => write!(f, "lft"),
            Self::Literal(s) => write!(f, "{}", s),
            Self::Loc => write!(f, "loc"),
            Self::Rtype => write!(f, "rtype"),
            Self::StructLayout => write!(f, "struct_layout"),
            Self::SynType => write!(f, "syn_type"),
            Self::Type => write!(f, "Type"),

            Self::PList(cons, tys) => {
                write!(f, "plist {} [", cons)?;
                write_list!(f, tys, "; ", "{} : Type")?;
                write!(f, "]")
            },

            Self::PlaceRfn(box t) => write!(f, "(place_rfn {})", t),

            Self::Prod(v) => match v.len() {
                0 => write!(f, "unit"),
                1 => write!(f, "{}", v[0]),
                _ => {
                    write!(f, "(")?;
                    write_list!(f, v, " * ")?;
                    write!(f, ")%type")
                },
            },

            Self::Ttype(box t) => write!(f, "(type {})", t),

            Self::Var(i) => write!(f, "#{}", i),
        }
    }
}

impl CoqType {
    /// Check if the `CoqType` contains a free variable `Var(i)`.
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

            Self::PList(_, tys) => tys.iter().all(|t| t.is_closed()),

            Self::PlaceRfn(t) => t.is_closed(),

            Self::Prod(v) => v.iter().all(|t| t.is_closed()),

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

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqParamList(pub Vec<(CoqName, CoqType)>);

impl CoqParamList {
    pub const fn empty() -> Self {
        Self(vec![])
    }
}

impl Display for CoqParamList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_list!(f, &self.0, " ", |(name, ty)| format!("({name} : {ty})"))
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqVariant {
    pub name: String,
    pub params: CoqParamList,
}

impl Display for CoqVariant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name, self.params)
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqInductive {
    pub name: String,
    pub parameters: CoqParamList,
    pub variants: Vec<CoqVariant>,
}

impl Display for CoqInductive {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Inductive {} {} :=", self.name, self.parameters)?;
        for v in &self.variants {
            writeln!(f, "| {}", v)?;
        }
        write!(f, ".")
    }
}

/// A single tactic call.
#[derive(Clone, Debug)]
pub enum CoqProofItem {
    Literal(String),
}

impl Display for CoqProofItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(lit) => write!(f, "{}.", lit),
        }
    }
}

/// A Coq proof script.
#[derive(Clone, Debug)]
pub struct CoqProofScript(pub Vec<CoqProofItem>);

impl Display for CoqProofScript {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for it in &self.0 {
            writeln!(f, "{}", it)?;
        }
        Ok(())
    }
}

/// A Coq Gallina term.
#[derive(Clone, Debug)]
pub enum GallinaTerm {
    Literal(String),
}

impl Display for GallinaTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(lit) => {
                write!(f, "{}", lit)
            },
        }
    }
}

/// A terminator for a proof script
#[derive(Clone, Debug)]
pub enum CoqProofScriptTerminator {
    Qed,
    Defined,
    Admitted,
}
impl Display for CoqProofScriptTerminator {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Qed => write!(f, "Qed"),
            Self::Defined => write!(f, "Defined"),
            Self::Admitted => write!(f, "Admitted"),
        }
    }
}

/// A body of a Coq definition
#[derive(Clone, Debug)]
pub enum CoqDefBody {
    /// a proof script invoking Ltac tactics
    Script(CoqProofScript, CoqProofScriptTerminator),
    /// a proof term
    Term(GallinaTerm),
}

impl Display for CoqDefBody {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

#[derive(Clone, Debug)]
pub enum CoqAttribute {
    Global,
    Local,
}
impl Display for CoqAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Global => write!(f, "global"),
            Self::Local => write!(f, "local"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CoqAttributes {
    attrs: Vec<CoqAttribute>,
}
impl CoqAttributes {
    pub const fn empty() -> Self {
        Self { attrs: vec![] }
    }

    pub fn new(attrs: Vec<CoqAttribute>) -> Self {
        Self { attrs }
    }
}
impl Display for CoqAttributes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.attrs.is_empty() {
            return Ok(());
        }

        write!(f, "#[ ")?;
        write_list!(f, &self.attrs, ", ")?;
        write!(f, "]")
    }
}

/// A Coq typeclass instance declaration
#[derive(Clone, Debug)]
pub struct CoqInstanceDecl {
    pub attrs: CoqAttributes,
    pub name: Option<String>,
    pub params: CoqParamList,
    pub ty: CoqType,
    pub body: CoqDefBody,
}

impl Display for CoqInstanceDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.name {
            Some(ref name) => {
                write!(f, "{} Instance {} {} : {}{}", self.attrs, name, self.params, self.ty, self.body)
            },
            None => write!(f, "{} Instance {} : {}{}", self.attrs, self.params, self.ty, self.body),
        }
    }
}

#[derive(Clone, Debug)]
pub enum CoqTopLevelAssertion {
    /// A declaration of a Coq Inductive
    InductiveDecl(CoqInductive),
    /// A declaration of a Coq instance
    InstanceDecl(CoqInstanceDecl),
    /// A Coq comment
    Comment(String),
}

impl Display for CoqTopLevelAssertion {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::InductiveDecl(inductive) => write!(f, "{inductive}")?,
            Self::InstanceDecl(decl) => write!(f, "{decl}")?,
            Self::Comment(comm) => write!(f, "(* {comm} *)")?,
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct CoqTopLevelAssertions(pub Vec<CoqTopLevelAssertion>);

impl CoqTopLevelAssertions {
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn push(&mut self, a: CoqTopLevelAssertion) {
        self.0.push(a)
    }
}

impl Display for CoqTopLevelAssertions {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for a in &self.0 {
            writeln!(f, "{a}")?;
        }
        Ok(())
    }
}
