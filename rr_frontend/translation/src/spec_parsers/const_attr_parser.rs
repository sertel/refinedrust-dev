// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse::parse;
use rr_rustc_interface::ast::ast::AttrItem;
use rr_rustc_interface::hir::def_id::LocalDefId;

use crate::spec_parsers::parse_utils::str_err;

/// Parse attributes on a const.
/// Permitted attributes:
/// - `rr::name("x`"), which will introduce the name x to refer to the const in other specs
pub trait ConstAttrParser {
    fn parse_const_attrs<'a>(
        &'a mut self,
        did: LocalDefId,
        attrs: &'a [&'a AttrItem],
    ) -> Result<ConstAttrs, String>;
}

#[derive(Clone, Debug)]
pub struct ConstAttrs {
    pub name: String,
}

#[allow(clippy::module_name_repetitions)]
pub struct VerboseConstAttrParser;

impl VerboseConstAttrParser {
    pub const fn new() -> Self {
        Self {}
    }
}

impl ConstAttrParser for VerboseConstAttrParser {
    fn parse_const_attrs<'a>(
        &'a mut self,
        _did: LocalDefId,
        attrs: &'a [&'a AttrItem],
    ) -> Result<ConstAttrs, String> {
        let mut name: Option<String> = None;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());

            match seg.ident.name.as_str() {
                "name" => {
                    let parsed_name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
                    if name.is_some() {
                        return Err("name attribute has already been specified".to_owned());
                    }
                    name = Some(parsed_name.value());
                },
                _ => {
                    return Err(format!("unknown attribute for const specification: {:?}", args));
                },
            }
        }

        let Some(name) = name else {
            return Err("no name attribute specified on const".to_owned());
        };

        Ok(ConstAttrs { name })
    }
}
