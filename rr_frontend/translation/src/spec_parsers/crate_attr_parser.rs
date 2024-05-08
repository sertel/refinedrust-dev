// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse as parse;
use radium::{coq, specs};
use rustc_ast::ast::AttrItem;

use crate::spec_parsers::parse_utils::{self, str_err};

/// Parse attributes on a crate.
/// Permitted attributes:
/// - `rr::import("A.B.C`", "D"), which will import the Coq path "A.B.C.D"
pub trait CrateAttrParser {
    fn parse_crate_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<CrateAttrs, String>;
}

#[derive(Clone, Debug)]
pub struct CrateAttrs {
    pub imports: Vec<coq::Path>,
    pub prefix: Option<String>,
    pub includes: Vec<String>,
    pub package: Option<String>,
    pub context_params: Vec<coq::Param>,
}

pub struct VerboseCrateAttrParser {}

impl VerboseCrateAttrParser {
    pub const fn new() -> Self {
        Self {}
    }
}

impl CrateAttrParser for VerboseCrateAttrParser {
    fn parse_crate_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<CrateAttrs, String> {
        let meta = ();
        let mut imports: Vec<coq::Path> = Vec::new();
        let mut includes: Vec<String> = Vec::new();
        let mut prefix: Option<String> = None;
        let mut package: Option<String> = None;
        let mut context_params = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
                match seg.ident.name.as_str() {
                    "import" => {
                        let path: parse_utils::CoqPath = buffer.parse(&meta).map_err(str_err)?;
                        imports.push(path.into());
                    },
                    "include" => {
                        let name: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                        includes.push(name.value());
                    },
                    "coq_prefix" => {
                        let path: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                        if prefix.is_some() {
                            return Err(format!("multiple rr::coq_prefix attributes have been provided"));
                        }
                        prefix = Some(path.value().to_string());
                    },
                    "package" => {
                        let path: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                        if package.is_some() {
                            return Err(format!("multiple rr::package attributes have been provided"));
                        }
                        package = Some(path.value().to_string());
                    },
                    "context" => {
                        let param: parse_utils::RRGlobalCoqContextItem =
                            buffer.parse(&meta).map_err(str_err)?;
                        context_params.push(coq::Param::new(
                            coq::Name::Unnamed,
                            coq::Type::Literal(param.item),
                            true,
                        ));
                    },
                    _ => {
                        return Err(format!("unknown attribute for crate specification: {:?}", args));
                    },
                }
            }
        }
        Ok(CrateAttrs {
            imports,
            prefix,
            includes,
            package,
            context_params,
        })
    }
}
