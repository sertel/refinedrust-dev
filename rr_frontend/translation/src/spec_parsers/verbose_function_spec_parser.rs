// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{info};
use parse::{MToken, Parse, ParseResult, ParseStream, Peek};
use radium::specs;
use rustc_ast::ast::AttrItem;
use {attribute_parse as parse, radium};

use crate::spec_parsers::parse_utils::{ParseMeta, *};

pub trait FunctionSpecParser<'def> {
    /// Parse a set of attributes into a function spec.
    /// The implementation can assume the `attrs` to be prefixed by the tool prefix (e.g. `rr`) and
    /// that it does not need to deal with any other attributes.
    fn parse_function_spec<'a>(
        &'a mut self,
        attrs: &'a [&'a AttrItem],
        spec: &'a mut radium::FunctionBuilder<'def>,
    ) -> Result<(), String>;
}

/// A sequence of refinements with optional types, e.g.
/// `"42" @ "int i32", "1337", "(a, b)"`
#[derive(Debug)]
struct RRArgs {
    args: Vec<LiteralTypeWithRef>,
}
impl<'a> Parse<ParseMeta<'a>> for RRArgs {
    fn parse(input: ParseStream, meta: &ParseMeta) -> ParseResult<Self> {
        let args: parse::Punctuated<LiteralTypeWithRef, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(RRArgs {
            args: args.into_iter().collect(),
        })
    }
}

/// Representation of the IProps that can appear in a requires or ensures clause.
enum MetaIProp {
    /// #[rr::requires("..")] or #[rr::requires("Ha" : "..")]
    Pure(String, Option<String>),
    /// #[rr::requires(#iris "..")]
    Iris(specs::IProp),
    /// #[rr::requires(#type "l" : "rfn" @ "ty")]
    Type(specs::TyOwnSpec),
    /// #[rr::ensures(#observe "γ" : "2 * x")]
    Observe(String, String),
}

impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for MetaIProp {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        if parse::Pound::peek(input) {
            input.parse::<_, parse::MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "type" => {
                    let loc_str: parse::LitStr = input.parse(meta)?;
                    let (loc_str, mut annot_meta) = process_coq_literal(&loc_str.value(), *meta);

                    input.parse::<_, parse::MToken![:]>(meta)?;

                    let rfn_str: parse::LitStr = input.parse(meta)?;
                    let (rfn_str, annot_meta2) = process_coq_literal(&rfn_str.value(), *meta);

                    annot_meta.join(&annot_meta2);

                    input.parse::<_, parse::MToken![@]>(meta)?;

                    let type_str: parse::LitStr = input.parse(meta)?;
                    let (type_str, annot_meta3) = process_coq_literal(&type_str.value(), *meta);
                    annot_meta.join(&annot_meta3);

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, false, annot_meta);
                    Ok(MetaIProp::Type(spec))
                },
                "iris" => {
                    let prop: IProp = input.parse(meta)?;
                    Ok(MetaIProp::Iris(prop.into()))
                },
                "observe" => {
                    let gname: parse::LitStr = input.parse(meta)?;
                    input.parse::<_, parse::MToken![:]>(meta)?;

                    let term: parse::LitStr = input.parse(meta)?;
                    let (term, _meta) = process_coq_literal(&term.value(), *meta);

                    Ok(MetaIProp::Observe(gname.value().to_string(), term))
                },
                _ => {
                    panic!("invalid macro command: {:?}", macro_cmd.value());
                },
            }
        } else {
            let name_or_prop_str: parse::LitStr = input.parse(meta)?;
            if parse::Colon::peek(input) {
                // this is a name
                let name_str = name_or_prop_str.value();

                input.parse::<_, parse::MToken![:]>(meta)?;

                let pure_prop: parse::LitStr = input.parse(meta)?;
                let (pure_str, _annot_meta) = process_coq_literal(&pure_prop.value(), *meta);
                // TODO: should we use annot_meta?

                Ok(MetaIProp::Pure(pure_str, Some(name_str)))
            } else {
                // this is a
                let (lit, _) = process_coq_literal(&name_or_prop_str.value(), *meta);
                Ok(MetaIProp::Pure(lit, None))
            }
        }
    }
}

impl Into<specs::IProp> for MetaIProp {
    fn into(self) -> specs::IProp {
        match self {
            Self::Pure(p, name) => match name {
                None => specs::IProp::Pure(p),
                Some(n) => specs::IProp::PureWithName(p, n),
            },
            Self::Iris(p) => p,
            Self::Type(spec) => {
                let lit = spec.fmt_owned("π");
                specs::IProp::Atom(lit)
            },
            Self::Observe(name, term) => specs::IProp::Atom(format!("gvar_pobs {name} ({term})")),
        }
    }
}

/// The main parser.
pub struct VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    /// argument types with substituted type parameters
    arg_types: &'a [specs::Type<'def>],
    /// return types with substituted type parameters
    ret_type: &'a specs::Type<'def>,
    make_literal: F,
}

impl<'a, 'def, F> VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    /// Type parameters must already have been substituted in the given types.
    pub fn new(arg_types: &'a [specs::Type<'def>], ret_type: &'a specs::Type<'def>, make_literal: F) -> Self {
        VerboseFunctionSpecParser {
            arg_types,
            ret_type,
            make_literal,
        }
    }

    /// Given a type annotation (either `r` or `r @ ty0`) and a translated Rust type `ty`, get the
    /// full type with refinement and, optionally, a Coq refinement type hint that will be used
    /// for the refinement `r`.
    fn make_type_with_ref(
        &self,
        lit: &LiteralTypeWithRef,
        ty: &specs::Type<'def>,
    ) -> (specs::TypeWithRef<'def>, Option<specs::CoqType>) {
        if let Some(ref lit_ty) = lit.ty {
            // literal type given, we use this literal type as the RR semantic type
            // just use the syntype from the Rust type
            let st = ty.get_syn_type();

            // TODO: get CoqType for refinement. maybe have it as an annotation? the Infer is currently a
            // placeholder.

            let lit_ty = specs::LiteralType {
                rust_name: None,
                type_term: lit_ty.to_string(),
                refinement_type: specs::CoqType::Infer,
                syn_type: st,
            };
            let lit_ref = (&self.make_literal)(lit_ty);
            let lit_ty_use = specs::LiteralTypeUse::new_with_annot(lit_ref, vec![], lit.meta.clone());

            (specs::TypeWithRef::new(specs::Type::Literal(lit_ty_use), lit.rfn.to_string()), None)
        } else {
            // no literal type given, just a refinement
            // we use the translated Rust type with the given refinement
            let mut ty = ty.clone();
            let rt = ty.get_rfn_type(&[]);
            if lit.raw == specs::TypeIsRaw::Yes {
                ty.make_raw();
            }
            (specs::TypeWithRef::new(ty, lit.rfn.to_string()), Some(rt))
        }
    }
}

fn str_err(e: parse::ParseError) -> String {
    format!("{:?}", e)
}

impl<'a, 'def, F> FunctionSpecParser<'def> for VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    fn parse_function_spec(
        &mut self,
        attrs: &[&AttrItem],
        spec: &mut radium::FunctionBuilder<'def>,
    ) -> Result<(), String> {
        if attrs.len() > 0 {
            spec.spec.have_spec();
        }

        // clone to be able to mutably borrow later
        let builder = spec;
        let lfts: Vec<(Option<String>, specs::Lft)> = builder.get_lfts();

        let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
        let meta: ParseMeta = (&meta, &lfts);
        info!("ty params: {:?}", meta);

        for &it in attrs.iter() {
            let ref path_segs = it.path.segments;
            let ref args = it.args;

            let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
            let meta: ParseMeta = (&meta, &lfts);

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
                match &*seg.ident.name.as_str() {
                    "params" => {
                        let params = RRParams::parse(&buffer, &meta).map_err(str_err)?;
                        for p in params.params {
                            builder.spec.add_param(p.name, p.ty)?;
                        }
                    },
                    "param" => {
                        let param = RRParam::parse(&buffer, &meta).map_err(str_err)?;
                        builder.spec.add_param(param.name, param.ty)?;
                    },
                    "args" => {
                        let args = RRArgs::parse(&buffer, &meta).map_err(str_err)?;
                        if self.arg_types.len() != args.args.len() {
                            return Err("wrong number of function arguments given".to_string());
                        }
                        for (arg, ty) in args.args.into_iter().zip(self.arg_types) {
                            let (ty, hint) = self.make_type_with_ref(&arg, ty);
                            builder.spec.add_arg(ty)?;
                            if let Some(cty) = hint {
                                // potentially add a typing hint to the refinement
                                if let IdentOrTerm::Ident(ref i) = arg.rfn {
                                    info!("Trying to add a typing hint for {}", i);
                                    builder
                                        .spec
                                        .add_param_type_annot(&specs::CoqName::Named(i.clone()), cty)?;
                                }
                            }
                        }
                    },
                    "requires" => {
                        let iprop = MetaIProp::parse(&buffer, &meta).map_err(str_err)?;
                        builder.spec.add_precondition(iprop.into())?;
                    },
                    "ensures" => {
                        let iprop = MetaIProp::parse(&buffer, &meta).map_err(str_err)?;
                        builder.spec.add_postcondition(iprop.into())?;
                    },
                    "observe" => {
                        let m = || {
                            let gname: parse::LitStr = buffer.parse(&meta)?;
                            buffer.parse::<_, parse::MToken![:]>(&meta)?;

                            let term: parse::LitStr = buffer.parse(&meta)?;
                            let (term, _) = process_coq_literal(&term.value(), meta);
                            Ok(MetaIProp::Observe(gname.value().to_string(), term))
                        };
                        let m = m().map_err(str_err)?;
                        builder.spec.add_postcondition(m.into())?;
                    },
                    "returns" => {
                        let tr = LiteralTypeWithRef::parse(&buffer, &meta).map_err(str_err)?;
                        // convert to type
                        let (ty, _) = self.make_type_with_ref(&tr, self.ret_type);
                        builder.spec.set_ret_type(ty)?;
                    },
                    "exists" => {
                        let params = RRParams::parse(&buffer, &meta).map_err(str_err)?;
                        for param in params.params.into_iter() {
                            builder.spec.add_existential(param.name, param.ty)?;
                        }
                    },
                    "tactics" => {
                        let tacs = parse::LitStr::parse(&buffer, &meta).map_err(str_err)?;
                        let tacs = tacs.value();
                        builder.add_manual_tactic(&tacs);
                    },
                    "context" => {
                        let context_item = RRCoqContextItem::parse(&buffer, &meta).map_err(str_err)?;
                        if context_item.at_end {
                            builder.spec.add_late_coq_param(
                                specs::CoqName::Unnamed,
                                specs::CoqType::Literal(context_item.item),
                                true,
                            )?;
                        } else {
                            builder.spec.add_coq_param(
                                specs::CoqName::Unnamed,
                                specs::CoqType::Literal(context_item.item),
                                true,
                            )?;
                        }
                    },
                    _ => {
                        info!("ignoring function attribute: {:?}", args);
                    },
                }
            }
        }
        Ok(())
    }
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
            Ok(ShimAnnot {
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
            match &*seg.ident.name.as_str() {
                "shim" => {
                    let annot = ShimAnnot::parse(&buffer, meta).map_err(str_err)?;
                    return Ok(annot);
                },
                _ => (),
            }
        }
    }
    Err("Did not find shim annotation".to_string())
}

/// For parsing of RustPaths
pub struct RustPath {
    path: Vec<String>,
}
impl<'tcx, F> parse::Parse<F> for RustPath {
    fn parse(input: parse::ParseStream, meta: &F) -> parse::ParseResult<Self> {
        let x: parse::Punctuated<parse::Ident, parse::MToken![::]> =
            parse::Punctuated::parse_separated_nonempty(input, meta)?;
        let path = x.into_iter().map(|x| x.value()).collect();
        Ok(RustPath { path })
    }
}
pub fn get_export_as_attr(attrs: &[&AttrItem]) -> Result<Vec<String>, String> {
    let meta: () = ();
    let meta = &meta;
    for &it in attrs.iter() {
        let ref path_segs = it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
            match &*seg.ident.name.as_str() {
                "export_as" => {
                    let path = RustPath::parse(&buffer, meta).map_err(str_err)?;
                    return Ok(path.path);
                },
                _ => (),
            }
        }
    }
    Err("Did not find export_as annotation".to_string())
}
