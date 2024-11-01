//! The [implicit arguments], and [binders].
//!
//! [implicit arguments]: https://coq.inria.fr/doc/v8.20/refman/language/extensions/implicit-arguments.html#implicit-arguments
//! [binders]: https://coq.inria.fr/doc/v8.20/refman/language/core/assumptions.html#binders

use std::fmt;

use derive_more::Display;

use crate::coq::term;
use crate::display_list;

/// A [binder].
///
/// [binder]: https://coq.inria.fr/doc/v8.20/refman/language/core/assumptions.html#grammar-token-binder
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Binder {
    #[display("({}: {})", self.get_name(), _1)]
    Default(Option<String>, term::Type),

    #[display("{}", _0)]
    Generalizing(Generalizing),
}

impl Binder {
    #[must_use]
    pub const fn new(name: Option<String>, ty: term::Type) -> Self {
        Self::Default(name, ty)
    }

    #[must_use]
    pub const fn new_generalized(kind: Kind, name: Option<String>, ty: term::Type) -> Self {
        Self::Generalizing(Generalizing { kind, name, ty })
    }

    #[must_use]
    pub(crate) fn get_name(&self) -> String {
        match self {
            Self::Default(name, _) => name.clone().unwrap_or_else(|| "_".to_owned()),
            Self::Generalizing(g) => g.name.clone().unwrap_or_else(|| "_".to_owned()),
        }
    }

    pub(crate) const fn get_name_ref(&self) -> &Option<String> {
        match self {
            Self::Default(name, _) => name,
            Self::Generalizing(g) => &g.name,
        }
    }

    pub(crate) const fn get_type(&self) -> &term::Type {
        match self {
            Self::Default(_, ty) => ty,
            Self::Generalizing(g) => &g.ty,
        }
    }

    #[must_use]
    pub(crate) const fn is_implicit(&self) -> bool {
        matches!(self, Self::Generalizing(_))
    }

    #[must_use]
    pub(crate) fn is_dependent_on_sigma(&self) -> bool {
        let term::Type::Literal(lit) = self.get_type() else {
            return false;
        };

        lit.contains('Σ')
    }

    #[must_use]
    pub fn set_name(self, name: String) -> Self {
        match self {
            Self::Default(_, ty) => Self::Default(Some(name), ty),
            Self::Generalizing(g) => Self::Generalizing(Generalizing {
                name: Some(name),
                ..g
            }),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Kind {
    /// `()
    Implicit,

    /// `{}
    MaxImplicit,
}

/// [Implicit generalization] binders.
///
/// [Implicit generalization]: https://coq.inria.fr/doc/v8.20/refman/language/extensions/implicit-arguments.html#grammar-token-generalizing_binder
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Generalizing {
    kind: Kind,
    name: Option<String>,
    ty: term::Type,
}

impl fmt::Display for Generalizing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (&self.kind, &self.name) {
            (Kind::Implicit, Some(name)) => write!(f, "`({} : !{})", name, self.ty),
            (Kind::Implicit, None) => write!(f, "`(!{})", self.ty),
            (Kind::MaxImplicit, Some(name)) => write!(f, "`{{{} : !{}}}", name, self.ty),
            (Kind::MaxImplicit, None) => write!(f, "`{{!{}}}", self.ty),
        }
    }
}

/// A Rocq pattern, e.g., "x" or "'(x, y)".
pub type Pattern = String;

#[allow(clippy::module_name_repetitions)]
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
    pub fn make_using_terms(&self) -> Vec<term::Gallina> {
        self.0.iter().map(|x| term::Gallina::Literal(format!("{}", x.get_name()))).collect()
    }
}
