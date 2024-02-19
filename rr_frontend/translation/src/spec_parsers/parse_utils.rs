// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashSet;

use attribute_parse as parse;
use lazy_static::lazy_static;
use parse::{MToken, Parse, ParseResult, ParseStream, Peek};
/// This provides some general utilities for RefinedRust-specific attribute parsing.
use radium::specs;
use regex::{self, Captures, Regex};

/// Parse either a literal string (a term/pattern) or an identifier, e.g.
/// `x`, `z`, `"w"`, `"(a, b)"`
#[derive(Debug)]
pub enum IdentOrTerm {
    Ident(String),
    Term(String),
}
impl<'tcx, U> parse::Parse<U> for IdentOrTerm
where
    U: ?Sized,
{
    fn parse(input: parse::ParseStream, meta: &U) -> parse::ParseResult<Self> {
        if let Ok(ident) = parse::Ident::parse(input, meta) {
            // it's an identifer
            Ok(IdentOrTerm::Ident(ident.value()))
        } else {
            parse::LitStr::parse(input, meta).map(|s| IdentOrTerm::Term(s.value()))
        }
    }
}

impl ToString for IdentOrTerm {
    fn to_string(&self) -> String {
        match self {
            IdentOrTerm::Ident(s) => s.to_string(),
            IdentOrTerm::Term(s) => s.to_string(),
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

impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for LiteralTypeWithRef {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        // check if a #raw annotation is present
        let loc = input.pos();
        let mut raw = specs::TypeIsRaw::No;
        if parse::Pound::peek(input) {
            input.parse::<_, parse::MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "raw" => {
                    raw = specs::TypeIsRaw::Yes;
                },
                _ => return Err(parse::ParseError::OtherErr(loc.unwrap(), "Unsupported flag".to_string())),
            }
        }

        // refinement
        let rfn: IdentOrTerm = input.parse(meta)?;

        // optionally, parse a type annotation (otherwise, use the translated Rust type)
        if parse::At::peek(input) {
            input.parse::<_, parse::MToken![@]>(meta)?;
            let ty: parse::LitStr = input.parse(meta)?;
            let (ty, meta) = process_coq_literal(&ty.value(), *meta);

            Ok(LiteralTypeWithRef {
                rfn,
                ty: Some(ty),
                raw,
                meta,
            })
        } else {
            Ok(LiteralTypeWithRef {
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
impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for LiteralType {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        let ty: parse::LitStr = input.parse(meta)?;
        let (ty, meta) = process_coq_literal(&ty.value(), *meta);

        Ok(LiteralType { ty, meta })
    }
}

pub struct IProp(specs::IProp);
impl Into<specs::IProp> for IProp {
    fn into(self) -> specs::IProp {
        self.0
    }
}

/// Parse an iProp string, e.g. `"P ∗ Q ∨ R"`
impl<'a> Parse<ParseMeta<'a>> for IProp {
    fn parse(input: ParseStream, meta: &ParseMeta) -> ParseResult<Self> {
        let lit: parse::LitStr = input.parse(meta)?;
        let (lit, _) = process_coq_literal(&lit.value(), *meta);

        Ok(IProp(specs::IProp::Atom(lit)))
    }
}

/// Parse a binder declaration with an optional Coq type annotation, e.g.
/// `x : "Z"`,
/// `"y"`,
/// `z`,
/// `w : "(Z * Z)%type"`
#[derive(Debug)]
pub struct RRParam {
    pub name: specs::CoqName,
    pub ty: specs::CoqType,
}

impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for RRParam {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        let name: IdentOrTerm = input.parse(meta)?;
        let name = specs::CoqName::Named(name.to_string());

        if parse::Colon::peek(input) {
            input.parse::<_, parse::MToken![:]>(meta)?;
            let ty: parse::LitStr = input.parse(meta)?;
            let (ty, _) = process_coq_literal(&ty.value(), *meta);
            let ty = specs::CoqType::Literal(ty);
            Ok(RRParam { name, ty })
        } else {
            Ok(RRParam {
                name,
                ty: specs::CoqType::Infer,
            })
        }
    }
}

/// Parse a list of comma-separated parameter declarations.
#[derive(Debug)]
pub(crate) struct RRParams {
    pub(crate) params: Vec<RRParam>,
}
impl<'tcx, 'a> Parse<ParseMeta<'a>> for RRParams {
    fn parse(input: ParseStream, meta: &ParseMeta) -> ParseResult<Self> {
        let params: parse::Punctuated<RRParam, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(RRParams {
            params: params.into_iter().collect(),
        })
    }
}

pub(crate) struct CoqPath(specs::CoqPath);
impl Into<specs::CoqPath> for CoqPath {
    fn into(self) -> specs::CoqPath {
        self.0
    }
}

/// Parse a CoqPath.
impl<'a, U> Parse<U> for CoqPath {
    fn parse(input: ParseStream, meta: &U) -> ParseResult<Self> {
        let path_or_module: parse::LitStr = input.parse(meta)?;
        let path_or_module = path_or_module.value();

        if parse::Comma::peek(input) {
            input.parse::<_, parse::MToken![,]>(meta)?;
            let module: parse::LitStr = input.parse(meta)?;
            let module = module.value();

            Ok(CoqPath(specs::CoqPath {
                path: Some(path_or_module.to_string()),
                module,
            }))
        } else {
            Ok(CoqPath(specs::CoqPath {
                path: None,
                module: path_or_module.to_string(),
            }))
        }
    }
}

/// Parse an assumed Coq context item, e.g.
/// `"`{ghost_mapG Σ Z Z}"`.
#[derive(Debug)]
pub struct RRCoqContextItem {
    pub item: String,
    /// true if this should be put at the end of the dependency list, e.g. if it depends on type
    /// parameters
    pub at_end: bool,
}
impl<'a> parse::Parse<ParseMeta<'a>> for RRCoqContextItem {
    fn parse(input: parse::ParseStream, meta: &ParseMeta<'a>) -> parse::ParseResult<Self> {
        let item: parse::LitStr = input.parse(meta)?;
        let (item_str, annot_meta) = process_coq_literal(&item.value(), *meta);

        let mut at_end = false;
        if !annot_meta.is_empty() {
            at_end = true;
        }

        //annot_meta.
        Ok(RRCoqContextItem {
            item: item_str,
            at_end,
        })
    }
}

pub type ParseMeta<'a> = (&'a [specs::LiteralTyParam], &'a [(Option<String>, specs::Lft)]);

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
pub(crate) fn process_coq_literal(s: &str, meta: ParseMeta<'_>) -> (String, specs::TypeAnnotMeta) {
    let params = meta.0;
    let lfts = meta.1;

    let mut literal_lfts: HashSet<String> = HashSet::new();
    let mut literal_tyvars: HashSet<specs::LiteralTyParam> = HashSet::new();

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
        for (name, lft) in lfts.iter() {
            if let Some(name) = name {
                if name == search {
                    return Some(lft.clone());
                }
            }
        }
        return None;
    };

    let cs = s;
    let cs = RE_RT_OF.replace_all(cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);
        match param {
            Some(param) => {
                literal_tyvars.insert(param.clone());
                format!("{}{}", &c[1], &param.refinement_type)
            },
            None => format!("ERR"),
        }
    });

    let cs = RE_ST_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);
        match param {
            Some(param) => {
                literal_tyvars.insert(param.clone());
                format!("{}(ty_syn_type {})", &c[1], &param.type_term)
            },
            None => "ERR".to_string(),
        }
    });
    let cs = RE_LY_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);
        match param {
            Some(param) => {
                literal_tyvars.insert(param.clone());
                format!("{}(use_layout_alg' (ty_syn_type {}))", &c[1], &param.type_term)
            },
            None => "ERR".to_string(),
        }
    });
    let cs = RE_TY_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let param = specs::lookup_ty_param(t, params);
        match param {
            Some(param) => {
                literal_tyvars.insert(param.clone());
                format!("{}{}", &c[1], &param.type_term)
            },
            None => format!("ERR"),
        }
    });
    let cs = RE_LFT_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let lft = lookup_lft_name(t);
        match lft {
            Some(lft) => {
                literal_lfts.insert(lft.clone());
                format!("{}{}", &c[1], lft)
            },
            None => "ERR".to_string(),
        }
    });
    let cs = RE_LIT.replace_all(&cs, |c: &Captures<'_>| format!("{}", &c[1]));

    (cs.to_string(), specs::TypeAnnotMeta::new(literal_tyvars, literal_lfts))
}
