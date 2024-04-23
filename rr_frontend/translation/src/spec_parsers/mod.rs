pub mod const_attr_parser;
pub mod crate_attr_parser;
pub mod enum_spec_parser;
pub mod module_attr_parser;
mod parse_utils;
pub mod struct_spec_parser;
pub mod verbose_function_spec_parser;

use attribute_parse as parse;
use parse::{MToken, Parse};
use rustc_ast::ast::AttrItem;

/// For parsing of RustPaths
pub struct RustPath {
    path: Vec<String>,
}

impl<F> parse::Parse<F> for RustPath {
    fn parse(input: parse::ParseStream, meta: &F) -> parse::ParseResult<Self> {
        let x: parse::Punctuated<parse::Ident, parse::MToken![::]> =
            parse::Punctuated::parse_separated_nonempty(input, meta)?;
        let path = x.into_iter().map(|x| x.value()).collect();
        Ok(Self { path })
    }
}

pub fn get_export_as_attr(attrs: &[&AttrItem]) -> Result<Vec<String>, String> {
    let meta: () = ();
    let meta = &meta;
    for &it in attrs.iter() {
        let ref path_segs = it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
            match seg.ident.name.as_str() {
                "export_as" => {
                    let path = RustPath::parse(&buffer, meta).map_err(parse_utils::str_err)?;
                    return Ok(path.path);
                },
                _ => (),
            }
        }
    }
    Err("Did not find export_as annotation".to_string())
}

/// Parser for getting shim attributes
#[derive(Debug)]
pub struct ShimAnnot {
    pub code_name: String,
    pub spec_name: String,
}

impl<U> parse::Parse<U> for ShimAnnot
where
    U: ?Sized,
{
    fn parse(input: parse::ParseStream, meta: &U) -> parse::ParseResult<Self> {
        let pos = input.pos().unwrap();
        let args: parse::Punctuated<parse::LitStr, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        if args.len() != 2 {
            Err(parse::ParseError::OtherErr(pos, "Expected exactly two arguments to rr::shim".to_string()))
        } else {
            let args: Vec<_> = args.into_iter().collect();
            let x = args[0].value();
            let y = args[1].value();
            Ok(Self {
                code_name: x,
                spec_name: y,
            })
        }
    }
}

/// Extract a shim annotation from a list of annotations of a function or method.
pub fn get_shim_attrs(attrs: &[&AttrItem]) -> Result<ShimAnnot, String> {
    let meta: () = ();
    let meta = &meta;
    for &it in attrs.iter() {
        let ref path_segs = it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
            match seg.ident.name.as_str() {
                "shim" => {
                    let annot = ShimAnnot::parse(&buffer, meta).map_err(parse_utils::str_err)?;
                    return Ok(annot);
                },
                _ => (),
            }
        }
    }
    Err("Did not find shim annotation".to_string())
}

/// Check whether we should propagate this attribute of a method from a surrounding impl.
pub fn propagate_method_attr_from_impl(it: &rustc_ast::ast::AttrItem) -> bool {
    if let Some(ident) = it.path.segments.get(1) {
        match ident.ident.as_str() {
            "context" => true,
            _ => false,
        }
    } else {
        false
    }
}
