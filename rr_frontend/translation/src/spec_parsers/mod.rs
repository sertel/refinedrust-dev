pub mod const_attr_parser;
pub mod crate_attr_parser;
pub mod enum_spec_parser;
pub mod module_attr_parser;
pub mod parse_utils;
pub mod struct_spec_parser;
pub mod trait_attr_parser;
pub mod trait_impl_attr_parser;
pub mod verbose_function_spec_parser;

use attribute_parse::{parse, MToken};
use parse::Parse;
use rr_rustc_interface::ast;
use rr_rustc_interface::ast::ast::AttrItem;

/// For parsing of `RustPaths`
pub struct RustPath {
    path: Vec<String>,
}

impl<F> parse::Parse<F> for RustPath {
    fn parse(input: parse::Stream, meta: &F) -> parse::Result<Self> {
        let x: parse::Punctuated<parse::Ident, MToken![::]> =
            parse::Punctuated::parse_separated_nonempty(input, meta)?;
        let path = x.into_iter().map(|x| x.value()).collect();
        Ok(Self { path })
    }
}

pub fn get_export_as_attr(attrs: &[&AttrItem]) -> Result<Vec<String>, String> {
    for &it in attrs {
        let path_segs = &it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::Buffer::new(&it.args.inner_tokens());

            if seg.ident.name.as_str() == "export_as" {
                let path = RustPath::parse(&buffer, &()).map_err(parse_utils::str_err)?;
                return Ok(path.path);
            }
        }
    }
    Err("Did not find export_as annotation".to_owned())
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
    fn parse(input: parse::Stream, meta: &U) -> parse::Result<Self> {
        let pos = input.pos().unwrap();
        let args: parse::Punctuated<parse::LitStr, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;

        if args.len() != 2 {
            return Err(parse::Error::OtherErr(pos, "Expected exactly two arguments to rr::shim".to_owned()));
        }

        let args: Vec<_> = args.into_iter().collect();

        Ok(Self {
            code_name: args[0].value(),
            spec_name: args[1].value(),
        })
    }
}

/// Extract a shim annotation from a list of annotations of a function or method.
pub fn get_shim_attrs(attrs: &[&AttrItem]) -> Result<ShimAnnot, String> {
    for &it in attrs {
        let path_segs = &it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::Buffer::new(&it.args.inner_tokens());

            if seg.ident.name.as_str() == "shim" {
                let annot = ShimAnnot::parse(&buffer, &()).map_err(parse_utils::str_err)?;
                return Ok(annot);
            }
        }
    }
    Err("Did not find shim annotation".to_owned())
}

/// Check whether we should propagate this attribute of a method from a surrounding impl.
pub fn propagate_method_attr_from_impl(it: &ast::ast::AttrItem) -> bool {
    if let Some(ident) = it.path.segments.get(1) {
        matches!(ident.ident.as_str(), "context") || matches!(ident.ident.as_str(), "verify")
    } else {
        false
    }
}
