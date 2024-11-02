// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [terms] section.
//!
//! [terms]: https://coq.inria.fr/doc/v8.20/refman/language/core/basic.html#term-term

use std::fmt;

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;
use itertools::Itertools;

use crate::coq::binder;
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
    All(binder::BinderList, Box<Gallina>),

    /// Existential quantifiers
    Exists(binder::BinderList, Box<Gallina>),

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
    pub params: binder::BinderList,
    pub term: Gallina,
}

impl Display for RecordBodyItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

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
        use fmt::Write;

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
        use fmt::Write;

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

/* TODO */
#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[display("{} {} : {}", name, params, ty)]
pub struct RecordDeclItem {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: Type,
}

/// A record declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: Type,
    pub constructor: Option<String>,
    pub body: Vec<RecordDeclItem>,
}

impl Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        let constructor = self.constructor.clone().unwrap_or_default();
        write!(f, "Record {} {} : {} := {constructor} {{\n", self.name, self.params, self.ty)?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.body {
            write!(f2, "{it};\n")?;
        }
        write!(f, "}}.")
    }
}
