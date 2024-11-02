// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use attribute_parse::{parse, MToken};
use derive_more::Constructor;
use radium::coq;
use rr_rustc_interface::ast::ast::AttrItem;
use rr_rustc_interface::hir::def_id::LocalDefId;

use crate::spec_parsers::parse_utils::*;

/// Parse attributes on a trait.
/// Permitted attributes:
/// - `rr::exists("x" : "Prop")`, which will declare a specification attribute "x" of the given type "Prop"
pub trait TraitAttrParser {
    fn parse_trait_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<TraitAttrs, String>;
}

#[derive(Constructor)]
struct TraitAttrScope<'a, T> {
    inner_scope: &'a T,
    // spec attrs that were parsed so far mapped to the record item name
    literals: HashMap<String, String>,
}
impl<'a, T: ParamLookup> ParamLookup for TraitAttrScope<'a, T> {
    fn lookup_ty_param(&self, path: &[&str]) -> Option<&radium::LiteralTyParam> {
        self.inner_scope.lookup_ty_param(path)
    }

    fn lookup_lft(&self, lft: &str) -> Option<&radium::Lft> {
        self.inner_scope.lookup_lft(lft)
    }

    fn lookup_literal(&self, path: &[&str]) -> Option<&str> {
        if path.len() == 1 {
            if let Some(lit) = self.literals.get(path[0]) {
                return Some(lit);
            }
        }
        self.inner_scope.lookup_literal(path)
    }
}

#[derive(Clone, Debug)]
pub struct TraitAttrs {
    pub attrs: radium::TraitSpecAttrsDecl,
    pub context_items: Vec<coq::binder::Binder>,
}

#[allow(clippy::module_name_repetitions)]
pub struct VerboseTraitAttrParser<'a, T, F> {
    scope: TraitAttrScope<'a, T>,
    make_record_id: F,
}

impl<'a, T: ParamLookup, F> VerboseTraitAttrParser<'a, T, F>
where
    F: Fn(&str) -> String,
{
    pub fn new(scope: &'a T, make_record_id: F) -> Self {
        let scope = TraitAttrScope::new(scope, HashMap::new());
        Self {
            scope,
            make_record_id,
        }
    }
}

impl<'b, T: ParamLookup, F> TraitAttrParser for VerboseTraitAttrParser<'b, T, F>
where
    F: Fn(&str) -> String,
{
    fn parse_trait_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<TraitAttrs, String> {
        let mut context_items = Vec::new();
        let mut trait_attrs = HashMap::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());

            match seg.ident.name.as_str() {
                "exists" => {
                    let parsed_name: IdentOrTerm = buffer.parse(&()).map_err(str_err)?;
                    buffer.parse::<_, MToken![:]>(&()).map_err(str_err)?;
                    // add the new identifier to the scope
                    self.scope.literals.insert(
                        parsed_name.to_string(),
                        self.make_record_id.call((&parsed_name.to_string(),)),
                    );
                    let parsed_type: RRCoqType = buffer.parse(&self.scope).map_err(str_err)?;
                    if trait_attrs.insert(parsed_name.to_string(), parsed_type.ty).is_some() {
                        return Err(format!(
                            "attribute {} has been declared multiple times",
                            parsed_name.to_string()
                        ));
                    }
                },
                "context" => {
                    let context_item: RRCoqContextItem = buffer.parse(&self.scope).map_err(str_err)?;
                    let param = coq::binder::Binder::new_generalized(
                        coq::binder::Kind::MaxImplicit,
                        None,
                        coq::term::Type::Literal(context_item.item),
                    );
                    context_items.push(param);
                },
                "export_as" => (),
                _ => {
                    return Err(format!("unknown attribute for trait specification: {:?}", args));
                },
            }
        }

        Ok(TraitAttrs {
            attrs: radium::TraitSpecAttrsDecl::new(trait_attrs),
            context_items,
        })
    }
}
