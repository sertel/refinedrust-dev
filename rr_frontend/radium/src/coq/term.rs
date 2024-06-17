// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Rocq terms.
use std::fmt::{self, Write};

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;
use itertools::Itertools;

use crate::{display_list, make_indent, write_list, BASE_INDENT};

/// Represents an application of a term to an rhs.
/// (commonly used for layouts and instantiating them with generics).
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct App<T, U> {
    pub(crate) lhs: T,
    pub(crate) rhs: Vec<U>,
}

impl<T: Display, U: Display> Display for App<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write_list!(f, &self.rhs, " ", "({})")
    }
}

impl<T, U> App<T, U> {
    pub fn new(lhs: T, rhs: Vec<U>) -> Self {
        Self { lhs, rhs }
    }

    pub fn new_lhs(lhs: T) -> Self {
        Self {
            lhs,
            rhs: Vec::new(),
        }
    }

    pub(crate) const fn get_lhs(&self) -> &T {
        &self.lhs
    }
}

/// A Coq Gallina term.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Gallina {
    /// a literal
    Literal(String),
    /// Application
    App(Box<App<Gallina, Gallina>>),
    /// a record body
    RecordBody(RecordBody),
    /// Projection a.(b) from a record
    RecordProj(Box<Gallina>, String),
    /// Universal quantifiers
    All(ParamList, Box<Gallina>),
    /// Existential quantifiers
    Exists(ParamList, Box<Gallina>),
    /// Infix operators
    Infix(String, Vec<Gallina>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordBodyItem {
    pub name: String,
    pub params: ParamList,
    pub term: Gallina,
}

impl Display for RecordBodyItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        write!(writer, "{} {} :=\n{};", self.name, self.params, self.term)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordBody {
    pub items: Vec<RecordBodyItem>,
}

impl Display for RecordBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{|\n")?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.items {
            write!(f2, "{}\n", it)?;
        }
        write!(f, "|}}\n")
    }
}

impl Display for Gallina {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            Self::All(binders, box body) => {
                if !binders.0.is_empty() {
                    write!(f, "∀ {binders}, ")?;
                }
                write!(f, "{body}")
            },
            Self::Exists(binders, box body) => {
                if !binders.0.is_empty() {
                    write!(f, "∃ {binders}, ")?;
                }
                write!(f, "{body}")
            },
            Self::Infix(op, terms) => {
                if terms.is_empty() {
                    write!(f, "True")
                } else {
                    write!(f, "{}", terms.iter().format(&format!(" {op} ")))
                }
            },
        }
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Display)]
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
        [] => "unit".to_owned(),
        [t] => t.to_string(),
        _ => format!("({})%type", display_list!(v, " * ")),
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Type {
    /// literal types that are not contained in the grammar
    #[display("{}", _0)]
    Literal(String),

    /// function types; the argument vector should be non-empty
    #[display("{} → {}", display_list!(_0, " → ", "({})"), *_1)]
    Function(Vec<Type>, Box<Type>),

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

    /// the semantic type of a function
    #[display("function_ty")]
    FunctionTy,

    /// the Coq type Prop of propositions
    #[display("Prop")]
    Prop,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", self.format(true))]
pub struct Param {
    /// the name
    name: Name,

    /// the type
    ty: Type,

    /// implicit or not?
    implicit: bool,

    /// does this depend on Σ?
    depends_on_sigma: bool,
}

impl Param {
    #[must_use]
    pub fn new(name: Name, ty: Type, implicit: bool) -> Self {
        let depends_on_sigma = if let Type::Literal(lit) = &ty { lit.contains('Σ') } else { false };

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

    #[must_use]
    pub fn get_name_ref(&self) -> Option<&str> {
        match &self.name {
            Name::Named(s) => Some(s),
            Name::Unnamed => None,
        }
    }

    #[allow(clippy::collapsible_else_if)]
    #[must_use]
    fn format(&self, make_implicits: bool) -> String {
        if !self.implicit {
            return format!("({} : {})", self.name, self.ty);
        }

        if make_implicits {
            if let Name::Named(name) = &self.name {
                format!("`{{{} : !{}}}", name, self.ty)
            } else {
                format!("`{{!{}}}", self.ty)
            }
        } else {
            if let Name::Named(name) = &self.name {
                format!("`({} : !{})", name, self.ty)
            } else {
                format!("`(!{})", self.ty)
            }
        }
    }

    pub(crate) const fn get_name(&self) -> &Name {
        &self.name
    }

    pub(crate) const fn is_implicit(&self) -> bool {
        self.implicit
    }

    pub(crate) const fn is_dependent_on_sigma(&self) -> bool {
        self.depends_on_sigma
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, " "))]
pub struct ParamList(pub Vec<Param>);

impl ParamList {
    #[must_use]
    pub const fn new(params: Vec<Param>) -> Self {
        Self(params)
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn append(&mut self, params: Vec<Param>) {
        self.0.extend(params);
    }

    /// Make using terms for this list of binders
    #[must_use]
    pub fn make_using_terms(&self) -> Vec<Gallina> {
        self.0.iter().map(|x| Gallina::Literal(format!("{}", x.name))).collect()
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}", name, params)]
pub struct Variant {
    name: String,
    params: ParamList,
}

impl Variant {
    #[must_use]
    pub fn new(name: &str, params: Vec<Param>) -> Self {
        Self {
            name: name.to_owned(),
            params: ParamList::new(params),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Inductive {} {} :=\n{}\n.", name, parameters,
    display_list!(variants, "\n| ").indented(&make_indent(1))
)]
pub struct Inductive {
    name: String,
    parameters: ParamList,
    variants: Vec<Variant>,
}

impl Inductive {
    #[must_use]
    pub fn new(name: &str, parameters: Vec<Param>, variants: Vec<Variant>) -> Self {
        Self {
            name: name.to_owned(),
            parameters: ParamList::new(parameters),
            variants,
        }
    }

    pub(crate) const fn get_name(&self) -> &String {
        &self.name
    }
}

#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[display("{} {} : {}", name, params, ty)]
pub struct RecordDeclItem {
    pub name: String,
    pub params: ParamList,
    pub ty: Type,
}

/// A record declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub name: String,
    pub params: ParamList,
    pub ty: Type,
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
