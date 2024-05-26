// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashSet;

use attribute_parse::{parse, MToken};
use lazy_static::lazy_static;
use parse::{Parse, Peek};
/// This provides some general utilities for RefinedRust-specific attribute parsing.
use radium::{coq, specs};
use regex::{self, Captures, Regex};

/// Parse either a literal string (a term/pattern) or an identifier, e.g.
/// `x`, `z`, `"w"`, `"(a, b)"`
#[derive(Debug)]
pub enum IdentOrTerm {
    Ident(String),
    Term(String),
}

impl<U> parse::Parse<U> for IdentOrTerm
where
    U: ?Sized,
{
    fn parse(input: parse::Stream, meta: &U) -> parse::Result<Self> {
        if let Ok(ident) = parse::Ident::parse(input, meta) {
            // it's an identifer
            Ok(Self::Ident(ident.value()))
        } else {
            parse::LitStr::parse(input, meta).map(|s| Self::Term(s.value()))
        }
    }
}

impl ToString for IdentOrTerm {
    fn to_string(&self) -> String {
        match self {
            Self::Ident(s) | Self::Term(s) => s.to_string(),
        }
    }
}

/// Parse a refinement with an optional type annotation, e.g.
/// `x`, `"y"`, `x @ "int i32"`, `"(a, b)" @ "struct_t ...."`.
#[derive(Debug)]
pub struct LiteralTypeWithRef {
    pub rfn: IdentOrTerm,
    pub ty: Option<String>,
    pub raw: specs::TypeIsRaw,
    pub meta: specs::TypeAnnotMeta,
}

impl<'a> parse::Parse<ParseMeta<'a>> for LiteralTypeWithRef {
    fn parse(input: parse::Stream, meta: &ParseMeta) -> parse::Result<Self> {
        // check if a #raw annotation is present
        let loc = input.pos();
        let mut raw = specs::TypeIsRaw::No;
        if parse::Pound::peek(input) {
            input.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "raw" => {
                    raw = specs::TypeIsRaw::Yes;
                },
                _ => return Err(parse::Error::OtherErr(loc.unwrap(), "Unsupported flag".to_owned())),
            }
        }

        // refinement
        let rfn: IdentOrTerm = input.parse(meta)?;

        // optionally, parse a type annotation (otherwise, use the translated Rust type)
        if parse::At::peek(input) {
            input.parse::<_, MToken![@]>(meta)?;
            let ty: parse::LitStr = input.parse(meta)?;
            let (ty, meta) = process_coq_literal(&ty.value(), *meta);

            Ok(Self {
                rfn,
                ty: Some(ty),
                raw,
                meta,
            })
        } else {
            Ok(Self {
                rfn,
                ty: None,
                raw,
                meta: specs::TypeAnnotMeta::empty(),
            })
        }
    }
}

/// Parse a type annotation.
#[derive(Debug)]
pub struct LiteralType {
    pub ty: String,
    pub meta: specs::TypeAnnotMeta,
}

impl<'a> parse::Parse<ParseMeta<'a>> for LiteralType {
    fn parse(input: parse::Stream, meta: &ParseMeta) -> parse::Result<Self> {
        let ty: parse::LitStr = input.parse(meta)?;
        let (ty, meta) = process_coq_literal(&ty.value(), *meta);

        Ok(Self { ty, meta })
    }
}

pub struct IProp(specs::IProp);

impl From<IProp> for specs::IProp {
    fn from(iprop: IProp) -> Self {
        iprop.0
    }
}

/// Parse an iProp string, e.g. `"P ∗ Q ∨ R"`
impl<'a> parse::Parse<ParseMeta<'a>> for IProp {
    fn parse(input: parse::Stream, meta: &ParseMeta) -> parse::Result<Self> {
        let lit: parse::LitStr = input.parse(meta)?;
        let (lit, _) = process_coq_literal(&lit.value(), *meta);

        Ok(Self(specs::IProp::Atom(lit)))
    }
}

/// Parse a binder declaration with an optional Coq type annotation, e.g.
/// `x : "Z"`,
/// `"y"`,
/// `z`,
/// `w : "(Z * Z)%type"`
#[derive(Debug)]
pub struct RRParam {
    pub name: coq::Name,
    pub ty: coq::Type,
}

impl<'a> parse::Parse<ParseMeta<'a>> for RRParam {
    fn parse(input: parse::Stream, meta: &ParseMeta) -> parse::Result<Self> {
        let name: IdentOrTerm = input.parse(meta)?;
        let name = coq::Name::Named(name.to_string());

        if parse::Colon::peek(input) {
            input.parse::<_, MToken![:]>(meta)?;
            let ty: parse::LitStr = input.parse(meta)?;
            let (ty, _) = process_coq_literal(&ty.value(), *meta);
            let ty = coq::Type::Literal(ty);
            Ok(Self { name, ty })
        } else {
            Ok(Self {
                name,
                ty: coq::Type::Infer,
            })
        }
    }
}

/// Parse a list of comma-separated parameter declarations.
#[derive(Debug)]
pub struct RRParams {
    pub(crate) params: Vec<RRParam>,
}

impl<'a> parse::Parse<ParseMeta<'a>> for RRParams {
    fn parse(input: parse::Stream, meta: &ParseMeta) -> parse::Result<Self> {
        let params: parse::Punctuated<RRParam, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(Self {
            params: params.into_iter().collect(),
        })
    }
}

pub struct CoqModule(coq::Module);

impl From<CoqModule> for coq::Module {
    fn from(path: CoqModule) -> Self {
        path.0
    }
}

/// Parse a `CoqModule`.
impl<U> parse::Parse<U> for CoqModule {
    fn parse(input: parse::Stream, meta: &U) -> parse::Result<Self> {
        let path_or_module: parse::LitStr = input.parse(meta)?;
        let path_or_module = path_or_module.value();

        if parse::Comma::peek(input) {
            input.parse::<_, MToken![,]>(meta)?;
            let module: parse::LitStr = input.parse(meta)?;
            let module = module.value();

            Ok(Self(coq::Module::new_with_path(&module, coq::Path::new(&path_or_module))))
        } else {
            Ok(Self(coq::Module::new(&path_or_module)))
        }
    }
}

/// Parse an assumed Coq context item, e.g.
/// ``"`{ghost_mapG Σ Z Z}"``.
#[derive(Debug)]
pub struct RRCoqContextItem {
    pub item: String,
    /// true if this should be put at the end of the dependency list, e.g. if it depends on type
    /// parameters
    pub at_end: bool,
}
impl<'a> parse::Parse<ParseMeta<'a>> for RRCoqContextItem {
    fn parse(input: parse::Stream, meta: &ParseMeta<'a>) -> parse::Result<Self> {
        let item: parse::LitStr = input.parse(meta)?;
        let (item_str, annot_meta) = process_coq_literal(&item.value(), *meta);

        let at_end = !annot_meta.is_empty();

        //annot_meta.
        Ok(Self {
            item: item_str,
            at_end,
        })
    }
}

/// a variant of `RRCoqContextItem` for module/crate scope
#[derive(Debug)]
pub struct RRGlobalCoqContextItem {
    pub item: String,
}

impl<U> parse::Parse<U> for RRGlobalCoqContextItem {
    fn parse(input: parse::Stream, meta: &U) -> parse::Result<Self> {
        let item: parse::LitStr = input.parse(meta)?;

        Ok(Self { item: item.value() })
    }
}

#[allow(clippy::needless_pass_by_value)]
pub fn str_err(e: parse::Error) -> String {
    format!("{:?}", e)
}

pub type ParseMeta<'a> = (&'a [specs::LiteralTyParam], &'a [(Option<String>, specs::Lft)]);

/// Handle escape sequences in the given string.
pub fn handle_escapes(s: &str) -> String {
    String::from(s).replace("\\\"", "\"")
}

/// Processes a literal Coq term annotated via an attribute.
/// In particular, processes escapes `{...}` and replaces them via their interpretation, see
/// below for supported escape sequences.
///
/// Supported interpretations:
/// - `{{...}}` is replaced by `{...}`
/// - `{T}` is replaced by the type for the type parameter `T`
/// - `{rt_of T}` is replaced by the refinement type of the type parameter `T`
/// - `{st_of T}` is replaced by the syntactic type of the type parameter `T`
/// - `{ly_of T}` is replaced by a term giving the layout of the type parameter `T`'s syntactic type
/// - `{'a}` is replaced by a term corresponding to the lifetime parameter 'a
pub fn process_coq_literal(s: &str, meta: ParseMeta<'_>) -> (String, specs::TypeAnnotMeta) {
    let params = meta.0;
    let lfts = meta.1;

    let mut literal_lfts: HashSet<String> = HashSet::new();
    let mut literal_tyvars: HashSet<specs::LiteralTyParam> = HashSet::new();

    let s = handle_escapes(s);

    /* regexes:
     * - '{\s*rt_of\s+([[:alpha:]])\s*}' replace by lookup of the refinement type name
     * - '{\s*st_of\s+([[:alpha:]])\s*}' replace by lookup of the syntype name
     * - '{\s*ly_of\s+([[:alpha:]])\s*}' replace by "use_layout_alg' st"
     * - '{\s*([[:alpha:]])\s*}' replace by the type name
     * - '{\s*'([[:alpha:]])\s*}' replace by lookup of the lifetime name
     * - '{{(.*)}}' replace by the contents
     */
    // compile these just once, not for every invocation of the method
    lazy_static! {
        static ref RE_RT_OF: Regex = Regex::new(r"([^{]|^)\{\s*rt_of\s+([[:alpha:]])\s*\}").unwrap();
        static ref RE_ST_OF: Regex = Regex::new(r"([^{]|^)\{\s*st_of\s+([[:alpha:]])\s*\}").unwrap();
        static ref RE_LY_OF: Regex = Regex::new(r"([^{]|^)\{\s*ly_of\s+([[:alpha:]])\s*\}").unwrap();
        static ref RE_TY_OF: Regex = Regex::new(r"([^{]|^)\{\s*([[:alpha:]])\s*\}").unwrap();
        static ref RE_LFT_OF: Regex = Regex::new(r"([^{]|^)\{\s*'([[:alpha:]])\s*\}").unwrap();
        static ref RE_LIT: Regex = Regex::new(r"\{(\{.*\})\}").unwrap();
    }

    let lookup_lft_name = |search: &str| {
        for (name, lft) in lfts {
            if let Some(name) = name {
                if name == search {
                    return Some(lft.clone());
                }
            }
        }

        None
    };

    let cs = &s;
    let cs = RE_RT_OF.replace_all(cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}{}", &c[1], &param.refinement_type)
    });

    let cs = RE_ST_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}(ty_syn_type {})", &c[1], &param.type_term)
    });

    let cs = RE_LY_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}(use_layout_alg' (ty_syn_type {}))", &c[1], &param.type_term)
    });

    let cs = RE_TY_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}{}", &c[1], &param.type_term)
    });

    let cs = RE_LFT_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let lft = lookup_lft_name(t);

        let Some(lft) = lft else {
            return "ERR".to_owned();
        };

        literal_lfts.insert(lft.clone());
        format!("{}{}", &c[1], lft)
    });

    let cs = RE_LIT.replace_all(&cs, |c: &Captures<'_>| format!("{}", &c[1]));

    (cs.to_string(), specs::TypeAnnotMeta::new(literal_tyvars, literal_lfts))
}
