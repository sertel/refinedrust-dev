// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// This provides some general utilities for RefinedRust-specific attribute parsing.
use std::collections::{HashMap, HashSet};

use attribute_parse::{parse, MToken};
use lazy_static::lazy_static;
use log::info;
use parse::{Parse, Peek};
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

impl<T: ParamLookup> parse::Parse<T> for LiteralTypeWithRef {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
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
            let (ty, meta) = process_coq_literal(&ty.value(), meta);

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

impl<T: ParamLookup> parse::Parse<T> for LiteralType {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let ty: parse::LitStr = input.parse(meta)?;
        let (ty, meta) = process_coq_literal(&ty.value(), meta);

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
impl<T: ParamLookup> parse::Parse<T> for IProp {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let lit: parse::LitStr = input.parse(meta)?;
        let (lit, _) = process_coq_literal(&lit.value(), meta);

        Ok(Self(specs::IProp::Atom(lit)))
    }
}

/// Parse a Coq type.
pub struct RRCoqType {
    pub ty: coq::term::Type,
}
impl<T: ParamLookup> parse::Parse<T> for RRCoqType {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let ty: parse::LitStr = input.parse(meta)?;
        let (ty, _) = process_coq_literal(&ty.value(), meta);
        let ty = coq::term::Type::Literal(ty);
        Ok(Self { ty })
    }
}

/// Parse a binder declaration with an optional Coq type annotation, e.g.
/// `x : "Z"`,
/// `"y"`,
/// `z`,
/// `w : "(Z * Z)%type"`
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct RRParam(coq::binder::Binder);

impl From<RRParam> for coq::binder::Binder {
    fn from(param: RRParam) -> Self {
        param.0
    }
}

impl<T: ParamLookup> parse::Parse<T> for RRParam {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let name: IdentOrTerm = input.parse(meta)?;
        let name = name.to_string();

        if parse::Colon::peek(input) {
            input.parse::<_, MToken![:]>(meta)?;
            let ty: RRCoqType = input.parse(meta)?;
            Ok(Self(coq::binder::Binder::new(Some(name), ty.ty)))
        } else {
            Ok(Self(coq::binder::Binder::new(Some(name), coq::term::Type::Infer)))
        }
    }
}

/// Parse a list of comma-separated parameter declarations.
#[derive(Debug)]
pub struct RRParams {
    pub(crate) params: Vec<RRParam>,
}

impl<T: ParamLookup> parse::Parse<T> for RRParams {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let params: parse::Punctuated<RRParam, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(Self {
            params: params.into_iter().collect(),
        })
    }
}

pub struct CoqExportModule(coq::module::Export);

impl From<CoqExportModule> for coq::module::Export {
    fn from(path: CoqExportModule) -> Self {
        path.0
    }
}

/// Parse a `CoqModule`.
impl<U> parse::Parse<U> for CoqExportModule {
    fn parse(input: parse::Stream, meta: &U) -> parse::Result<Self> {
        let path_or_module: parse::LitStr = input.parse(meta)?;
        let path_or_module = path_or_module.value();

        if parse::Comma::peek(input) {
            input.parse::<_, MToken![,]>(meta)?;
            let module: parse::LitStr = input.parse(meta)?;
            let module = module.value();

            Ok(Self(coq::module::Export::new(vec![module]).from(vec![path_or_module])))
        } else {
            Ok(Self(coq::module::Export::new(vec![path_or_module])))
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
impl<T: ParamLookup> parse::Parse<T> for RRCoqContextItem {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        let item: parse::LitStr = input.parse(meta)?;
        let (item_str, annot_meta) = process_coq_literal(&item.value(), meta);

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

/// Lookup of lifetime and type parameters given their Rust source names.
pub trait ParamLookup {
    fn lookup_ty_param(&self, path: &[&str]) -> Option<&specs::LiteralTyParam>;
    fn lookup_lft(&self, lft: &str) -> Option<&specs::Lft>;
    fn lookup_literal(&self, path: &[&str]) -> Option<&str>;
}

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
/// - `{ty_of T}` is replaced by the type for the type parameter `T`
/// - `{rt_of T}` is replaced by the refinement type of the type parameter `T`
/// - `{st_of T}` is replaced by the syntactic type of the type parameter `T`
/// - `{ly_of T}` is replaced by a term giving the layout of the type parameter `T`'s syntactic type
/// - `{'a}` is replaced by a term corresponding to the lifetime parameter 'a
pub fn process_coq_literal<T: ParamLookup>(s: &str, meta: &T) -> (String, specs::TypeAnnotMeta) {
    let mut literal_lfts: HashSet<String> = HashSet::new();
    let mut literal_tyvars: HashSet<specs::LiteralTyParam> = HashSet::new();

    // TODOs:
    // - associated types, we should split them here already. We need to adjust the matching to accept :: and
    //   then split
    // - lookup other literals in ParamLookup

    let s = handle_escapes(s);

    /* regexes:
     * - '{\s*rt_of\s+([[:alpha:]])\s*}' replace by lookup of the refinement type name
     * - '{\s*st_of\s+([[:alpha:]])\s*}' replace by lookup of the syntype name
     * - '{\s*ly_of\s+([[:alpha:]])\s*}' replace by "use_layout_alg' st"
     * - '{\s*ty_of\s+([[:alpha:]])\s*}' replace by the type name
     * - '{\s*'([[:alpha:]])\s*}' replace by lookup of the lifetime name
     * - '{{(.*)}}' replace by the contents
     *
     * Note: the leading regex ([^{]|^) is supposed to rule out leading {, for the RE_LIT rule.
     */
    // compile these just once, not for every invocation of the method
    lazy_static! {
        //(::[[:alpha:]]*)?
        static ref RE_RT_OF: Regex = Regex::new(r"([^{]|^)\{\s*rt_of\s+([[:alpha:]]+)(::([[:alpha:]]+))?\s*\}").unwrap();
        static ref RE_ST_OF: Regex = Regex::new(r"([^{]|^)\{\s*st_of\s+([[:alpha:]]+)(::([[:alpha:]]+))?\s*\}").unwrap();
        static ref RE_LY_OF: Regex = Regex::new(r"([^{]|^)\{\s*ly_of\s+([[:alpha:]]+)(::([[:alpha:]]+))?\s*\}").unwrap();
        static ref RE_TY_OF: Regex = Regex::new(r"([^{]|^)\{\s*ty_of\s+([[:alpha:]]+)(::([[:alpha:]]+))?\s*\}").unwrap();
        static ref RE_LFT_OF: Regex = Regex::new(r"([^{]|^)\{\s*'([[:alpha:]]+)\s*\}").unwrap();

        static ref RE_LIT: Regex = Regex::new(r"([^{]|^)\{\s*([[:alpha:]]+)(::([[:alpha:]]+))?\s*\}").unwrap();

        static ref RE_DIRECT: Regex = Regex::new(r"\{(\{.*\})\}").unwrap();
    }

    let cs = &s;
    let cs = RE_RT_OF.replace_all(cs, |c: &Captures<'_>| {
        let mut path = Vec::new();
        path.push(&c[2]);

        if let Some(t2) = c.get(4) {
            path.push(t2.as_str());
        }

        let param = meta.lookup_ty_param(&path);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}{}", &c[1], &param.refinement_type)
    });

    let cs = RE_ST_OF.replace_all(&cs, |c: &Captures<'_>| {
        let mut path = Vec::new();
        path.push(&c[2]);

        if let Some(t2) = c.get(4) {
            path.push(t2.as_str());
        }
        let param = meta.lookup_ty_param(&path);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}(ty_syn_type {})", &c[1], &param.type_term)
    });

    let cs = RE_LY_OF.replace_all(&cs, |c: &Captures<'_>| {
        let mut path = Vec::new();
        path.push(&c[2]);

        if let Some(t2) = c.get(4) {
            path.push(t2.as_str());
        }
        let param = meta.lookup_ty_param(&path);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}(use_layout_alg' (ty_syn_type {}))", &c[1], &param.type_term)
    });

    let cs = RE_TY_OF.replace_all(&cs, |c: &Captures<'_>| {
        let mut path = Vec::new();
        path.push(&c[2]);

        if let Some(t2) = c.get(4) {
            path.push(t2.as_str());
        }
        let param = meta.lookup_ty_param(&path);

        let Some(param) = param else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(param.clone());
        format!("{}{}", &c[1], &param.type_term)
    });

    let cs = RE_LFT_OF.replace_all(&cs, |c: &Captures<'_>| {
        let t = &c[2];
        let lft = meta.lookup_lft(t);

        let Some(lft) = lft else {
            return "ERR".to_owned();
        };

        literal_lfts.insert(lft.clone());
        format!("{}{}", &c[1], lft)
    });

    let cs = RE_LIT.replace_all(&cs, |c: &Captures<'_>| {
        let mut path = Vec::new();
        path.push(&c[2]);
        if let Some(t2) = c.get(4) {
            path.push(t2.as_str());
        }

        // first lookup literals
        let lit = meta.lookup_literal(&path);

        if let Some(lit) = lit {
            return format!("{}{}", &c[1], lit);
        }

        // else interpret it as ty_of
        let ty = meta.lookup_ty_param(&path);

        let Some(ty) = ty else {
            return "ERR".to_owned();
        };

        literal_tyvars.insert(ty.clone());
        format!("{}{}", &c[1], &ty.type_term)
    });

    let cs = RE_DIRECT.replace_all(&cs, |c: &Captures<'_>| c[1].to_string());

    (cs.to_string(), specs::TypeAnnotMeta::new(literal_tyvars, literal_lfts))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::ParamLookup;

    #[derive(Default)]
    struct TestScope {
        /// conversely, map the declaration name of a lifetime to an index
        pub lft_names: HashMap<String, radium::Lft>,
        /// map types to their index
        pub ty_names: HashMap<String, radium::LiteralTyParam>,

        pub assoc_names: HashMap<(String, String), radium::LiteralTyParam>,

        pub literals: HashMap<Vec<String>, String>,
    }
    impl ParamLookup for TestScope {
        fn lookup_ty_param(&self, path: &[&str]) -> Option<&radium::LiteralTyParam> {
            if path.len() == 1 {
                self.ty_names.get(path[0])
            } else if path.len() == 2 {
                self.assoc_names.get(&(path[0].to_owned(), path[1].to_owned()))
            } else {
                None
            }
        }

        fn lookup_lft(&self, lft: &str) -> Option<&radium::Lft> {
            self.lft_names.get(lft)
        }

        fn lookup_literal(&self, path: &[&str]) -> Option<&str> {
            use std::string::ToString;
            let key: Vec<String> = path.iter().map(ToString::to_string).collect();
            self.literals.get(&key).map(String::as_str)
        }
    }

    #[test]
    fn test_literal1() {
        let lit = "{rt_of T} * {rt_of T}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("T".to_owned(), radium::LiteralTyParam::new("T", "T"));

        let (res, _) = super::process_coq_literal(lit, &scope);
        assert_eq!(res, "T_rt * T_rt");
    }

    #[test]
    fn test_literal2() {
        let lit = "{ty_of T} * {ty_of T}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("T".to_owned(), radium::LiteralTyParam::new("T", "T"));

        let (res, _) = super::process_coq_literal(lit, &scope);
        assert_eq!(res, "T_ty * T_ty");
    }

    #[test]
    fn test_literal3() {
        let lit = "{rt_of Self} * {rt_of Self}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Self".to_owned(), radium::LiteralTyParam::new("Self", "Self"));

        let (res, _) = super::process_coq_literal(lit, &scope);
        assert_eq!(res, "Self_rt * Self_rt");
    }

    #[test]
    fn test_literal4() {
        let lit = "{{rt_of Bla}}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Self".to_owned(), radium::LiteralTyParam::new("Self", "Self"));

        let (res, _) = super::process_coq_literal(lit, &scope);
        assert_eq!(res, "{rt_of Bla}");
    }

    #[test]
    fn test_assoc_1() {
        let lit = "{rt_of Bla::Blub}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Bla".to_owned(), radium::LiteralTyParam::new("Bla", "Bla"));
        scope.assoc_names.insert(
            ("Bla".to_owned(), "Blub".to_owned()),
            radium::LiteralTyParam::new("Bla_Blub", "Bla_Blub"),
        );

        let (res, _) = super::process_coq_literal(lit, &scope);
        assert_eq!(res, "Bla_Blub_rt");
    }

    #[test]
    fn test_lit_1() {
        let lit = "{Size} 4";
        let mut scope = TestScope::default();
        scope.literals.insert(vec!["Size".to_owned()], "(trait_attrs).(size)".to_owned());

        let (res, _) = super::process_coq_literal(lit, &scope);
        assert_eq!(res, "(trait_attrs).(size) 4");
    }
}
