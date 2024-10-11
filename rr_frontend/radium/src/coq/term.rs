// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [terms] section.
//!
//! [terms]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#term-term

use std::fmt::{self, Write};

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;
use itertools::Itertools;

use crate::{display_list, make_indent, BASE_INDENT};

/// A [term].
///
/// [term]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-term
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
    All(BinderList, Box<Gallina>),

    /// Existential quantifiers
    Exists(BinderList, Box<Gallina>),

    /// Infix operators
    Infix(String, Vec<Gallina>),
}

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

        write!(f, "({} {})", self.lhs, display_list!(&self.rhs, " ", "({})"))
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordBodyItem {
    pub name: String,
    pub params: BinderList,
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

fn fmt_prod(v: &Vec<Type>) -> String {
    match v.as_slice() {
        [] => "unit".to_owned(),
        [t] => t.to_string(),
        _ => format!("({})%type", display_list!(v, " * ")),
    }
}

/// A [type], limited to specific cases.
///
/// [type]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#grammar-token-type
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Type {
    /// Literal types that are not contained in the grammar
    #[display("{}", _0)]
    Literal(String),

    /// Function types; the argument vector should be non-empty
    #[display("{} → {}", display_list!(_0, " → ", "({})"), *_1)]
    Function(Vec<Type>, Box<Type>),

    /// Placeholder that should be inferred by Coq if possible
    #[display("_")]
    Infer,

    /// Rocq type `lft`
    #[display("lft")]
    Lft,

    /// Rocq type `loc`
    #[display("loc")]
    Loc,

    /// Rocq type `layout`
    #[display("layout")]
    Layout,

    /// Rocq type `syn_type`
    #[display("syn_type")]
    SynType,

    /// Rocq type `struct_layout`
    #[display("struct_layout")]
    StructLayout,

    /// Rocq type `Type`
    #[display("Type")]
    Type,

    /// Rocq type `type rt`
    #[display("(type {})", &_0)]
    Ttype(Box<Type>),

    /// Rocq type `rtype`
    #[display("rtype")]
    Rtype,

    /// Unit type
    #[display("unit")]
    Unit,

    /// Integers
    #[display("Z")]
    Z,

    /// Booleans
    #[display("bool")]
    Bool,

    /// Product type
    #[display("{}", fmt_prod(_0))]
    Prod(Vec<Type>),

    /// place_rfn
    #[display("(place_rfn {})", &_0)]
    PlaceRfn(Box<Type>),

    /// gname
    #[display("gname")]
    Gname,

    /// A plist with a given type constructor over a list of types
    #[display("plist {} [{}]", _0, display_list!(_1, "; ", "{} : Type"))]
    PList(String, Vec<Type>),

    /// The semantic type of a function
    #[display("function_ty")]
    FunctionTy,

    /// The Rocq type Prop of propositions
    #[display("Prop")]
    Prop,
}

/// A Coq pattern, e.g., "x" or "'(x, y)".
pub type Pattern = String;

/// A [binder].
///
/// [binder]: https://coq.inria.fr/doc/v8.20/refman/language/core/assumptions.html#grammar-token-binder
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", self.format(true))]
pub struct Binder {
    name: Option<String>,
    ty: Type,
    is_implicit: bool,
    depends_on_sigma: bool,
}

impl Binder {
    #[must_use]
    pub fn new(name: Option<String>, ty: Type) -> Self {
        let depends_on_sigma = if let Type::Literal(lit) = &ty { lit.contains('Σ') } else { false };

        Self {
            name,
            ty,
            is_implicit: false,
            depends_on_sigma,
        }
    }

    #[must_use]
    pub fn set_implicit(self, is_implicit: bool) -> Self {
        Self {
            is_implicit,
            ..self
        }
    }

    #[must_use]
    pub fn set_name(self, name: String) -> Self {
        Self {
            name: Some(name),
            ..self
        }
    }

    #[must_use]
    pub(crate) fn get_name(&self) -> String {
        let Some(name) = &self.name else { return "_".to_owned() };
        name.clone()
    }

    pub(crate) const fn get_name_ref(&self) -> &Option<String> {
        &self.name
    }

    pub(crate) const fn get_type(&self) -> &Type {
        &self.ty
    }

    pub(crate) const fn is_implicit(&self) -> bool {
        self.is_implicit
    }

    pub(crate) const fn is_dependent_on_sigma(&self) -> bool {
        self.depends_on_sigma
    }

    #[allow(clippy::collapsible_else_if)]
    #[must_use]
    fn format(&self, make_implicits: bool) -> String {
        if !self.is_implicit {
            return format!("({} : {})", self.get_name(), self.ty);
        }

        if make_implicits {
            if let Some(name) = &self.name {
                format!("`{{{} : !{}}}", name, self.ty)
            } else {
                format!("`{{!{}}}", self.ty)
            }
        } else {
            if let Some(name) = &self.name {
                format!("`({} : !{})", name, self.ty)
            } else {
                format!("`(!{})", self.ty)
            }
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, " "))]
pub struct BinderList(pub Vec<Binder>);

impl BinderList {
    #[must_use]
    pub const fn new(params: Vec<Binder>) -> Self {
        Self(params)
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn append(&mut self, params: Vec<Binder>) {
        self.0.extend(params);
    }

    /// Make using terms for this list of binders
    #[must_use]
    pub fn make_using_terms(&self) -> Vec<Gallina> {
        self.0.iter().map(|x| Gallina::Literal(format!("{}", x.get_name()))).collect()
    }
}

/* TODO */
#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[display("{} {} : {}", name, params, ty)]
pub struct RecordDeclItem {
    pub name: String,
    pub params: BinderList,
    pub ty: Type,
}

/// A record declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub name: String,
    pub params: BinderList,
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
