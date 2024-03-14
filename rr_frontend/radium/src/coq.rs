// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;
use std::fmt::{Display, Formatter, Write};

use indent_write::fmt::IndentWriter;

pub(crate) const BASE_INDENT: &'static str = "  ";

/// Represents a Coq path of the form
/// `From A.B.C Import D`
#[derive(Hash, Clone, Debug, Eq, PartialEq)]
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
#[derive(Hash, Clone, Debug, Eq, PartialEq)]
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
        if self.rhs.len() == 0 {
            write!(f, "{}", self.lhs)
        } else {
            write!(f, "({}", self.lhs)?;
            for r in self.rhs.iter() {
                write!(f, " ({})", r)?;
            }
            write!(f, ")")
        }
    }
}

#[derive(PartialOrd, Ord, Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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
            Self::Infer => write!(f, "_"),
            Self::Literal(s) => write!(f, "{}", s),
            Self::Lft => write!(f, "lft"),
            Self::Loc => write!(f, "loc"),
            Self::Layout => write!(f, "layout"),
            Self::SynType => write!(f, "syn_type"),
            Self::StructLayout => write!(f, "struct_layout"),
            Self::Type => write!(f, "Type"),
            Self::Ttype(box t) => write!(f, "(type {})", t),
            Self::Rtype => write!(f, "rtype"),
            Self::Unit => write!(f, "unit"),
            Self::Z => write!(f, "Z"),
            Self::Bool => write!(f, "bool"),
            Self::Prod(v) => {
                if v.len() == 0 {
                    write!(f, "unit")
                } else if v.len() == 1 {
                    v[0].fmt(f)
                } else {
                    write!(f, "(")?;
                    let mut need_sep = false;
                    for t in v.iter() {
                        if need_sep {
                            write!(f, " * ")?;
                        }
                        need_sep = true;

                        t.fmt(f)?;
                    }
                    write!(f, ")%type")
                }
            },
            Self::PlaceRfn(box t) => {
                write!(f, "(place_rfn {})", t)
            },
            Self::Gname => write!(f, "gname"),
            Self::Var(i) => write!(f, "#{}", i),
            Self::PList(cons, tys) => {
                write!(f, "plist {} [", cons)?;
                let mut needs_sep = false;
                for ty in tys.iter() {
                    if needs_sep {
                        write!(f, "; ")?;
                    }
                    needs_sep = true;
                    write!(f, "{} : Type", ty)?;
                }
                write!(f, "]")
            },
        }
    }
}

impl CoqType {
    /// Check if the CoqType contains a free variable `Var(i)`.
    pub fn is_closed(&self) -> bool {
        match self {
            Self::Var(_) => false,
            Self::Prod(v) => {
                for t in v.iter() {
                    if !t.is_closed() {
                        return false;
                    }
                }
                return true;
            },
            Self::PList(_, tys) => {
                for t in tys.iter() {
                    if !t.is_closed() {
                        return false;
                    }
                }
                return true;
            },
            Self::Ttype(box ty) => ty.is_closed(),
            Self::PlaceRfn(t) => t.is_closed(),
            Self::Literal(..) => true,
            Self::Infer => true,
            Self::Lft => true,
            Self::Loc => true,
            Self::Layout => true,
            Self::SynType => true,
            Self::StructLayout => true,
            Self::Type => true,
            Self::Rtype => true,
            Self::Unit => true,
            Self::Z => true,
            Self::Bool => true,
            Self::Gname => true,
        }
    }

    /// Substitute variables `Var` according to the given substitution (variable `i` is mapped to
    /// index `i` in the vector).
    /// The types in `substi` should not contain variables themselves, as this substitution
    /// operation is capture-incurring!
    pub fn subst(&mut self, substi: &Vec<CoqType>) {
        match self {
            Self::Ttype(box t) => t.subst(substi),
            Self::Prod(v) => {
                for t in v.iter_mut() {
                    t.subst(substi);
                }
            },
            Self::PList(_, tys) => {
                for t in tys.iter_mut() {
                    t.subst(substi);
                }
            },
            Self::PlaceRfn(box t) => {
                t.subst(substi);
            },
            Self::Gname => (),
            Self::Var(i) => {
                if let Some(ta) = substi.get(*i) {
                    assert!(ta.is_closed());
                    *self = ta.clone();
                }
            },
            Self::Literal(..) => (),
            Self::Infer => (),
            Self::Lft => (),
            Self::Loc => (),
            Self::Layout => (),
            Self::SynType => (),
            Self::StructLayout => (),
            Self::Type => (),
            Self::Rtype => (),
            Self::Unit => (),
            Self::Z => (),
            Self::Bool => (),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CoqParamList(pub Vec<(CoqName, CoqType)>);

impl CoqParamList {
    pub fn empty() -> Self {
        Self(vec![])
    }
}

impl Display for CoqParamList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut needs_sep = false;
        for (name, ty) in self.0.iter() {
            if needs_sep {
                write!(f, " ")?;
            }
            needs_sep = true;
            write!(f, "({} : {})", name, ty)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CoqVariant {
    pub name: String,
    pub params: CoqParamList,
}

impl Display for CoqVariant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name, self.params)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CoqInductive {
    pub name: String,
    pub parameters: CoqParamList,
    pub variants: Vec<CoqVariant>,
}

impl Display for CoqInductive {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Inductive {} {} :=\n", self.name, self.parameters)?;
        for v in self.variants.iter() {
            write!(f, "| {}\n", v)?;
        }
        write!(f, ".")
    }
}

/// A single tactic call.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
pub struct CoqProofScript(pub Vec<CoqProofItem>);

impl Display for CoqProofScript {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for it in self.0.iter() {
            write!(f, "{}\n", it)?;
        }
        Ok(())
    }
}

/// A Coq Gallina term.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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

/// A Coq typeclass instance declaration
#[derive(Debug, Clone)]
pub struct CoqInstanceDecl {
    pub name: Option<String>,
    pub params: CoqParamList,
    pub ty: CoqType,
    pub body: CoqDefBody,
}

impl Display for CoqInstanceDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.name {
            Some(ref name) => write!(f, "Instance {} {} : {}{}", name, self.params, self.ty, self.body),
            None => write!(f, "Instance {} : {}{}", self.params, self.ty, self.body),
        }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct CoqTopLevelAssertions(pub Vec<CoqTopLevelAssertion>);

impl CoqTopLevelAssertions {
    pub fn empty() -> Self {
        Self(vec![])
    }

    pub fn push(&mut self, a: CoqTopLevelAssertion) {
        self.0.push(a)
    }
}

impl Display for CoqTopLevelAssertions {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for a in self.0.iter() {
            write!(f, "{a}\n")?;
        }
        Ok(())
    }
}
