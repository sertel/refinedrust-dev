// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse::parse;
use radium::coq;
use rr_rustc_interface::ast::ast::AttrItem;
use rr_rustc_interface::hir::def_id::LocalDefId;

use crate::spec_parsers::parse_utils::{self, str_err};

/// Parse attributes on a module.
/// Permitted attributes:
/// - `rr::import("A.B.C`", "D"), which will import the Coq path "A.B.C.D"
pub trait ModuleAttrParser {
    fn parse_module_attrs<'a>(
        &'a mut self,
        did: LocalDefId,
        attrs: &'a [&'a AttrItem],
    ) -> Result<ModuleAttrs, String>;
}

#[derive(Clone, Debug)]
pub struct ModuleAttrs {
    pub exports: Vec<coq::module::Export>,
    pub includes: Vec<String>,
    pub context_params: Vec<coq::binder::Binder>,
}

#[allow(clippy::module_name_repetitions)]
pub struct VerboseModuleAttrParser;

impl VerboseModuleAttrParser {
    pub const fn new() -> Self {
        Self {}
    }
}

impl ModuleAttrParser for VerboseModuleAttrParser {
    fn parse_module_attrs<'a>(
        &'a mut self,
        _did: LocalDefId,
        attrs: &'a [&'a AttrItem],
    ) -> Result<ModuleAttrs, String> {
        let mut exports: Vec<coq::module::Export> = Vec::new();
        let mut includes: Vec<String> = Vec::new();
        let mut context_params = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());
            match seg.ident.name.as_str() {
                "import" => {
                    let path: parse_utils::CoqExportModule = buffer.parse(&()).map_err(str_err)?;
                    exports.push(path.into());
                },
                "include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
                    includes.push(name.value());
                },
                "context" => {
                    let param: parse_utils::RRGlobalCoqContextItem = buffer.parse(&()).map_err(str_err)?;
                    context_params.push(coq::binder::Binder::new_generalized(
                        coq::binder::Kind::MaxImplicit,
                        None,
                        coq::term::Type::Literal(param.item),
                    ));
                },
                _ => {
                    return Err(format!("unknown attribute for module specification: {:?}", args));
                },
            }
        }

        Ok(ModuleAttrs {
            exports,
            includes,
            context_params,
        })
    }
}
