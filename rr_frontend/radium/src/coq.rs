// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;
use std::fmt::{Display, Formatter, Write};

use indent_write::fmt::IndentWriter;
use itertools::Itertools;

pub(crate) const BASE_INDENT: &'static str = "  ";

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
pub struct CoqAppTerm<T, U> {
    pub(crate) lhs: T,
    pub(crate) rhs: Vec<U>,
}

impl<T, U> CoqAppTerm<T, U> {
    pub fn new(lhs: T, rhs: Vec<U>) -> Self {
        Self { lhs, rhs }
    }

    pub fn new_lhs(lhs: T) -> Self {
        Self {
            lhs,
            rhs: Vec::new(),
        }
    }
}

impl<T, U> fmt::Display for CoqAppTerm<T, U>
where
    T: Display,
    U: Display,
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
    /// the semantic type of a function
    FunctionTy,
    /// the Coq type Prop of propositions
    Prop,
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
            Self::FunctionTy => {
                write!(f, "function_ty")
            },
            Self::Prop => {
                write!(f, "Prop")
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
            Self::FunctionTy => true,
            Self::Prop => true,
        }
    }

    /// Substitute variables `Var` according to the given substitution (variable `i` is mapped to
    /// index `i` in the vector).
    /// The types in `substi` should not contain variables themselves, as this substitution
    /// operation is capture-incurring!
    pub fn subst(&mut self, substi: &Vec<Self>) {
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
            Self::FunctionTy => (),
            Self::Prop => (),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqParam {
    /// the name
    pub name: CoqName,
    /// the type
    pub ty: CoqType,
    /// implicit or not?
    pub implicit: bool,
    /// does this depend on Σ?
    pub depends_on_sigma: bool,
}

impl CoqParam {
    pub fn new(name: CoqName, ty: CoqType, implicit: bool) -> Self {
        let depends_on_sigma = if let CoqType::Literal(ref lit) = ty { lit.contains('Σ') } else { false };
        Self {
            name,
            ty,
            implicit,
            depends_on_sigma,
        }
    }

    pub fn with_name(&self, name: String) -> Self {
        Self::new(CoqName::Named(name), self.ty.clone(), self.implicit)
    }

    pub fn format(&self, f: &mut Formatter, make_implicits: bool) -> fmt::Result {
        if self.implicit {
            if make_implicits {
                if let CoqName::Named(ref name) = self.name {
                    write!(f, "`{{{} : !{}}}", name, self.ty)
                } else {
                    write!(f, "`{{!{}}}", self.ty)
                }
            } else {
                if let CoqName::Named(ref name) = self.name {
                    write!(f, "`({} : !{})", name, self.ty)
                } else {
                    write!(f, "`(!{})", self.ty)
                }
            }
        } else {
            write!(f, "({} : {})", self.name, self.ty)
        }
    }
}

impl Display for CoqParam {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.format(f, true)
    }
}


#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqParamList(pub Vec<CoqParam>);

impl CoqParamList {
    pub const fn empty() -> Self {
        Self(vec![])
    }

    /// Make using terms for this list of binders
    pub fn make_using_terms(&self) -> Vec<GallinaTerm> {
        self.0.iter().map(|x| GallinaTerm::Literal(format!("{}", x.name))).collect()
    }
}

impl Display for CoqParamList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut needs_sep = false;
        for param in self.0.iter() {
            if needs_sep {
                write!(f, " ")?;
            }
            needs_sep = true;
            write!(f, "{}", param)?;
        }
        Ok(())
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
        write!(f, "Inductive {} {} :=\n", self.name, self.parameters)?;
        for v in self.variants.iter() {
            write!(f, "| {}\n", v)?;
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
        for it in self.0.iter() {
            write!(f, "{}\n", it)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct CoqRecordBodyItem {
    pub name: String,
    pub params: CoqParamList,
    pub term: GallinaTerm,
}

impl Display for CoqRecordBodyItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        write!(writer, "{} {} :=\n{};", self.name, self.params, self.term)
    }
}

#[derive(Clone, Debug)]
pub struct RecordBodyTerm {
    pub items: Vec<CoqRecordBodyItem>,
}

impl Display for RecordBodyTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{|\n")?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.items {
            write!(f2, "{}\n", it)?;
        }
        write!(f, "|}}\n")
    }
}

/// A Coq Gallina term.
#[derive(Clone, Debug)]
pub enum GallinaTerm {
    /// a literal
    Literal(String),
    /// Application
    App(Box<CoqAppTerm<GallinaTerm, GallinaTerm>>),
    /// a record body
    RecordBody(RecordBodyTerm),
    /// Projection a.(b) from a record
    RecordProj(Box<GallinaTerm>, String),
    /// Universal quantifiers
    All(CoqParamList, Box<GallinaTerm>),
    /// Existential quantifiers
    Exists(CoqParamList, Box<GallinaTerm>),
    /// Infix operators 
    Infix(String, Vec<GallinaTerm>),
}

impl Display for GallinaTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(lit) => {
                let mut f2 = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
                write!(f2, "{lit}")
            },
            Self::RecordBody(b) => {
                write!(f, "{b}")
            },
            Self::RecordProj(rec, component) => {
                write!(f, "{rec}.({component})")
            },
            Self::App(box a) => write!(f, "{a}"),
            Self::All(binders, box body) => write!(f, "∀ {binders}, {body}"),
            Self::Exists(binders, box body) => write!(f, "∃ {binders}, {body}"),
            Self::Infix(op, terms) => 
                if terms.is_empty() {
                    write!(f, "True")
                } else {
                    write!(f, "{}", terms.iter().format(" {op} "))
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
        if !self.attrs.is_empty() {
            write!(f, "#[ ")?;
            let mut needs_sep = false;
            for attr in self.attrs.iter() {
                if needs_sep {
                    write!(f, ", ")?;
                }
                needs_sep = true;
                write!(f, "{}", attr)?;
            }
            write!(f, "]")?;
        }
        Ok(())
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
pub struct CoqRecordDeclItem {
    pub name: String,
    pub params: CoqParamList,
    pub ty: CoqType,
}

impl Display for CoqRecordDeclItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} : {}", self.name, self.params, self.ty)
    }
}

/// A record declaration.
#[derive(Clone, Debug)]
pub struct CoqRecord {
    pub name: String,
    pub params: CoqParamList,
    pub ty: CoqType,
    pub constructor: Option<String>,
    pub body: Vec<CoqRecordDeclItem>,
}

impl Display for CoqRecord {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let constructor = self.constructor.clone().unwrap_or("".to_string());
        write!(f, "Record {} {} : {} := {constructor} {{\n", self.name, self.params, self.ty)?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in self.body.iter() {
            write!(f2, "{it};\n")?;
        }
        write!(f, "}}.\n")
    }
}

/// A Context declaration.
#[derive(Clone, Debug)]
pub struct CoqContextDecl {
    pub items: CoqParamList,
}

impl Display for CoqContextDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Context {}.\n", self.items)
    }
}

/// A Coq definition
#[derive(Clone, Debug)]
pub struct CoqDefinition {
    pub name: String,
    pub params: CoqParamList,
    pub ty: Option<CoqType>,
    pub body: CoqDefBody,
}

impl Display for CoqDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(ref ty) = self.ty {
            write!(f, "Definition {} {} : {ty}{}", self.name, self.params, self.body)
        }
        else {
            write!(f, "Definition {} {}{}", self.name, self.params, self.body)
        }
    }
}

#[derive(Clone, Debug)]
pub enum CoqTopLevelAssertion {
    /// A declaration of a Coq Inductive
    InductiveDecl(CoqInductive),
    /// A declaration of a Coq instance
    InstanceDecl(CoqInstanceDecl),
    /// A declaration of a Coq record
    RecordDecl(CoqRecord),
    /// A declaration of Coq context items
    ContextDecl(CoqContextDecl),
    /// A Coq Definition
    Definition(CoqDefinition),
    /// A Coq comment
    Comment(String),
}

impl Display for CoqTopLevelAssertion {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::InductiveDecl(inductive) => write!(f, "{inductive}")?,
            Self::InstanceDecl(decl) => write!(f, "{decl}")?,
            Self::RecordDecl(decl) => write!(f, "{decl}")?,
            Self::ContextDecl(decl) => write!(f, "{decl}")?,
            Self::Definition(def) => write!(f, "{def}")?,
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
        for a in self.0.iter() {
            write!(f, "{a}\n")?;
        }
        Ok(())
    }
}
