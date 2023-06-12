// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{debug, info};

use rustc_ast::ast::AttrItem;
use crate::caesium::specs as specs;
use crate::caesium as caesium;

use crate::parse as parse;
use crate::parse::{Peek, Parse, ParseStream, MToken, ParseResult};
use crate::parse_utils::{*, ParseMeta};

pub trait FunctionSpecParser<'def> {
    /// Parse a set of attributes into a function spec.
    /// The implementation can assume the `attrs` to be prefixed by the tool prefix (e.g. `rr`) and
    /// that it does not need to deal with any other attributes.
    fn parse_function_spec<'a>(&'a mut self, attrs: &'a[&'a AttrItem], spec: &'a mut caesium::FunctionBuilder<'def>) -> Result<(), String>;
}

/// Parse an assumed Coq context item, e.g.
/// `"`{ghost_mapG Σ Z Z}"`.
#[derive(Debug)]
struct RRCoqContextItem {
    item: String,
}
impl<U> parse::Parse<U> for RRCoqContextItem where U: ?Sized {
    fn parse(input: parse::ParseStream, meta: &U) -> parse::ParseResult<Self> {
        let item: parse::LitStr = input.parse(meta)?;
        Ok (RRCoqContextItem {item: item.value()})
    }
}


/// A sequence of refinements with optional types, e.g.
/// `"42" @ "int i32", "1337", "(a, b)"`
#[derive(Debug)]
struct RRArgs {
    args: Vec<LiteralTypeWithRef>,
}
impl<'a> Parse<ParseMeta<'a>> for RRArgs {
    fn parse(input: ParseStream, meta: &ParseMeta) -> ParseResult<Self> {
        let args: parse::Punctuated<LiteralTypeWithRef, MToken![,]> = parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(RRArgs {args: args.into_iter().collect()})
    }
}


/// Parse a list of comma-separated lifetimes.
struct RRELfts {
    lfts: Vec<specs::Lft>,
}
impl<U> Parse<U> for RRELfts where U: ?Sized {
    fn parse(input: ParseStream, meta: &U) -> ParseResult<Self> {
        let elfts: parse::Punctuated<parse::LitStr, MToken![,]> = parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(RRELfts {lfts: elfts.into_iter().map(|s| s.value()).collect() })
    }
}

/// Representation of the IProps that can appear in a requires or ensures clause.
enum MetaIProp {
    /// #[rr::requires("..")]
    Plain(specs::IProp),
    /// #[rr::requires(#type "l" : "rfn" @ "ty")]
    Type(specs::TyOwnSpec),
}

impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for MetaIProp {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        if parse::Pound::peek(input) {
            input.parse::<_, parse::MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "type" => {
                    let loc_str: parse::LitStr = input.parse(meta)?;
                    let loc_str = process_coq_literal(&loc_str.value(), *meta);

                    input.parse::<_, parse::MToken![:]>(meta)?;

                    let rfn_str: parse::LitStr = input.parse(meta)?;
                    let rfn_str = process_coq_literal(&rfn_str.value(), *meta);

                    input.parse::<_, parse::MToken![@]>(meta)?;

                    let type_str: parse::LitStr = input.parse(meta)?;
                    let type_str = process_coq_literal(&type_str.value(), *meta);

                    // TODO: have an option to specify a later here
                    let with_later = false;
                    let spec = specs::TyOwnSpec::new(loc_str, with_later, rfn_str, type_str);
                    Ok(MetaIProp::Type(spec))
                },
                _ => {
                    panic!("invalid macro command: {:?}", macro_cmd.value());
                },
            }
        }
        else {
            let prop: specs::IProp = input.parse(meta)?;
            Ok(MetaIProp::Plain(prop))
        }
    }
}

impl Into<specs::IProp> for MetaIProp {
    fn into(self) -> specs::IProp {
        match self {
            Self::Plain(p) => p,
            Self::Type(spec) => {
                let lit = spec.fmt_owned("π");
                specs::IProp::Atom(lit)
            },
        }
    }
}

/// The main parser.
pub struct VerboseFunctionSpecParser<'a, 'def> {
    /// argument types with substituted type parameters
    arg_types: &'a [specs::Type<'def>],
    /// return types with substituted type parameters
    ret_type: &'a specs::Type<'def>,

    /// environment for rfn type identifiers for generics
    rfnty_scope: &'a [Option<specs::CoqType>],
}

impl<'a, 'def> VerboseFunctionSpecParser<'a, 'def> {
    /// Type parameters must already have been substituted in the given types.
    pub fn new(arg_types: &'a [specs::Type<'def>], ret_type: &'a specs::Type<'def>, rfnty_scope : &'a [Option<specs::CoqType>]) -> Self {
        VerboseFunctionSpecParser {
            arg_types,
            ret_type,
            rfnty_scope
        }
    }

    /// Given a type annotation (either `r` or `r @ ty0`) and a translated Rust type `ty`, get the
    /// full type with refinement and, optionally, a Coq refinement type hint that will be used
    /// for the refinement `r`.
    fn make_type_with_ref(&self, lit: &LiteralTypeWithRef, ty: &specs::Type<'def>) -> (specs::TypeWithRef<'def>, Option<specs::CoqType>) {
        if let Some(ref lit_ty) = lit.ty {
            // literal type given, we use this literal type as the RR semantic type
            // just use the syntype from the Rust type
            let st = ty.get_syn_type();

            // TODO: get CoqType for refinement. maybe have it as an annotation? the Infer is currently a placeholder.

            (specs::TypeWithRef::new(
                specs::Type::Literal(None, specs::CoqAppTerm::new_lhs(lit_ty.to_string()), specs::CoqType::Infer, st),
                lit.rfn.to_string()),
             None)
        }
        else {
            // no literal type given, just a refinement
            // we use the translated Rust type with the given refinement
            let mut ty = ty.clone();
            let rt = ty.get_rfn_type(self.rfnty_scope);
            if lit.raw == specs::TypeIsRaw::Yes {
                ty.make_raw();
            }
            (specs::TypeWithRef::new(ty, lit.rfn.to_string()), Some(rt))
        }
    }
}

fn str_err(e : parse::ParseError) -> String {
    format!("{:?}", e)
}

impl<'a, 'def> FunctionSpecParser<'def> for VerboseFunctionSpecParser<'a, 'def> {
    fn parse_function_spec(&mut self, attrs: &[&AttrItem], spec: &mut caesium::FunctionBuilder<'def>) -> Result<(), String> {
        if attrs.len() > 0 {
            spec.spec.have_spec();
        }

        // clone to be able to mutably borrow later
        let meta: Vec<specs::TyParamNames> = spec.get_ty_params();
        let lfts: Vec<(Option<String>, specs::Lft)> = spec.get_lfts();
        let meta: ParseMeta = (&meta, &lfts);
        info!("ty params: {:?}", meta);

        let builder = spec;

        for &it in attrs.iter() {
            let ref path_segs = it.path.segments;
            let ref args = it.args;

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
                            return Err("wrong number of function arguments given".to_string())
                        }
                        for (arg, ty) in args.args.into_iter().zip(self.arg_types) {
                            let (ty, hint) = self.make_type_with_ref(&arg, ty);
                            builder.spec.add_arg(ty)?;
                            if let Some(cty) = hint {
                                // potentially add a typing hint to the refinement
                                if let IdentOrTerm::Ident(ref i) = arg.rfn {
                                    info!("Trying to add a typing hint for {}", i);
                                    builder.spec.add_param_type_annot(&specs::CoqName::Named(i.clone()), cty)?;
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
                    // TODO do we need this anymore?
                    "lifetimes" => {
                        let lfts = RRELfts::parse(&buffer, &meta).map_err(str_err)?;
                        for lft in lfts.lfts.iter() {
                            builder.spec.add_param(specs::CoqName::Named(lft.clone()), specs::CoqType::Lft)?;
                        }
                    },
                    "context" => {
                        let context_item = RRCoqContextItem::parse(&buffer, &meta).map_err(str_err)?;
                        builder.spec.add_coq_param(specs::CoqName::Unnamed, specs::CoqType::Literal(context_item.item), true)?;
                        //spec.add_coq_context_item(context_item.item);
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
impl<U> parse::Parse<U> for ShimAnnot where U: ?Sized {
    fn parse(input: parse::ParseStream, meta: &U) -> parse::ParseResult<Self> {
        let pos = input.pos().unwrap();
        let args: parse::Punctuated<parse::LitStr, MToken![,]> = parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        if args.len() != 2 {
            Err(parse::ParseError::OtherErr(pos, "Expected exactly two arguments to rr::shim".to_string()))
        }
        else {
            let args: Vec<_> = args.into_iter().collect();
            let x = args[0].value();
            let y = args[1].value();
            Ok(ShimAnnot{code_name: x, spec_name: y})
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
                }
                _ => (),
            }
        }
    }
    Err("Did not find shim annotation".to_string())
}
