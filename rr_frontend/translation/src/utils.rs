// Except for the exceptions specified below, this code is © 2019, ETH Zurich
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// The following functions have been adapted from Miri (https://github.com/rust-lang/miri/blob/31fb32e49f42df19b45baccb6aa80c3d726ed6d5/src/helpers.rs#L48) under the MIT license;
// - `try_resolve_did`

//! Various helper functions for working with `mir::Place`.

use std::mem;

use log::{info, trace};
use rr_rustc_interface::ast::ast;
use rr_rustc_interface::data_structures::fx::FxHashSet;
use rr_rustc_interface::hir::def_id::{DefId, CRATE_DEF_INDEX};
use rr_rustc_interface::middle::mir;
use rr_rustc_interface::middle::ty::{self, TyCtxt};
use rr_rustc_interface::{hir, middle, span};
use serde::{Deserialize, Serialize};

use crate::spec_parsers::get_export_as_attr;
use crate::type_translator::normalize_in_function;
use crate::{force_matches, Environment};

/// An item path that receives generic arguments.
#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub struct PathWithArgs {
    path: Vec<String>,
    /// An encoding of the GenericArgs for this definition.
    /// This is `Some(ty)` if:
    /// - the argument represents a type (not a constant or region)
    /// - and the arg is not the trivial identity arg (in case of ADTs)
    args: Vec<Option<FlatType>>,
}

impl PathWithArgs {
    pub fn to_item<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Option<(DefId, Vec<Option<ty::GenericArg<'tcx>>>)> {
        let did = try_resolve_did(tcx, self.path.as_slice())?;

        let mut ty_args = Vec::new();

        for arg in &self.args {
            if let Some(arg) = arg {
                let ty = arg.to_type(tcx)?;
                ty_args.push(Some(ty::GenericArg::from(ty)));
            } else {
                ty_args.push(None);
            }
        }

        Some((did, ty_args))
    }

    /// `args` should be normalized already.
    pub fn from_item<'tcx>(
        env: &Environment<'tcx>,
        did: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> Option<Self> {
        let path = get_export_path_for_did(env, did);
        let mut flattened_args = Vec::new();
        // TODO: how to represent type variables in case the definition is open?
        let mut index = 0;
        info!("flattening args {:?}", args);
        for arg in args {
            if let Some(ty) = arg.as_type() {
                // TODO not quite right yet (see above)
                if !ty.is_param(index) {
                    let flattened_ty = convert_ty_to_flat_type(env, ty)?;
                    flattened_args.push(Some(flattened_ty));
                }
                index += 1;
            } else {
                flattened_args.push(None);
            }
        }
        Some(Self {
            path,
            args: flattened_args,
        })
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "ty::IntTy")]
pub enum IntTyDef {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}
#[derive(Serialize, Deserialize)]
#[serde(remote = "ty::UintTy")]
pub enum UintTyDef {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
/// A "flattened" representation of types that should be suitable serialized storage, and should be
/// stable enough to resolve to the same actual type across compilations.
/// Currently mostly geared to our trait resolution needs.
pub enum FlatType {
    /// Path + generic args
    /// empty args represents the identity substitution
    Adt(PathWithArgs),
    #[serde(with = "IntTyDef")]
    Int(ty::IntTy),
    #[serde(with = "UintTyDef")]
    Uint(ty::UintTy),
    Char,
    Bool,
    // TODO: more cases
}

impl FlatType {
    /// Try to convert a flat type to a type.
    pub fn to_type<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Option<ty::Ty<'tcx>> {
        match self {
            Self::Adt(path_with_args) => {
                let (did, flat_args) = path_with_args.to_item(tcx)?;

                let ty: ty::EarlyBinder<ty::Ty<'tcx>> = tcx.type_of(did);
                let ty::TyKind::Adt(_, args) = ty.skip_binder().kind() else {
                    return None;
                };

                // build substitution
                let mut substs = Vec::new();
                for (ty_arg, flat_arg) in args.iter().zip(flat_args.into_iter()) {
                    match ty_arg.unpack() {
                        ty::GenericArgKind::Type(_) => {
                            if let Some(flat_arg) = flat_arg {
                                substs.push(flat_arg);
                            }
                        },
                        _ => {
                            substs.push(ty_arg);
                        },
                    }
                }

                // substitute
                info!("substituting {:?} with {:?}", ty, substs);
                let subst_ty =
                    if substs.is_empty() { ty.instantiate_identity() } else { ty.instantiate(tcx, &substs) };

                Some(subst_ty)
            },
            Self::Bool => Some(tcx.mk_ty_from_kind(ty::TyKind::Bool)),
            Self::Char => Some(tcx.mk_ty_from_kind(ty::TyKind::Char)),
            Self::Int(it) => Some(tcx.mk_ty_from_kind(ty::TyKind::Int(it.to_owned()))),
            Self::Uint(it) => Some(tcx.mk_ty_from_kind(ty::TyKind::Uint(it.to_owned()))),
        }
    }
}

/// Try to convert a type to a flat type. Assumes the type has been normalized already.
pub fn convert_ty_to_flat_type<'tcx>(env: &Environment<'tcx>, ty: ty::Ty<'tcx>) -> Option<FlatType> {
    match ty.kind() {
        ty::TyKind::Adt(def, args) => {
            let did = def.did();
            // TODO: if this is downcast to a variant, this might not work
            let path_with_args = PathWithArgs::from_item(env, did, args.as_slice())?;
            Some(FlatType::Adt(path_with_args))
        },
        ty::TyKind::Bool => Some(FlatType::Bool),
        ty::TyKind::Char => Some(FlatType::Char),
        ty::TyKind::Int(it) => Some(FlatType::Int(it.to_owned())),
        ty::TyKind::Uint(it) => Some(FlatType::Uint(it.to_owned())),
        _ => None,
    }
}

pub fn get_cleaned_def_path(tcx: TyCtxt<'_>, did: DefId) -> Vec<String> {
    let def_path = tcx.def_path_str(did);
    // we clean this up a bit and segment it
    let mut components = Vec::new();
    for i in def_path.split("::") {
        if i.starts_with('<') && i.ends_with('>') {
            // this is a generic specialization, skip
            continue;
        }
        components.push(i.to_owned());
    }
    info!("split def path {:?} to {:?}", def_path, components);

    components
}

// Alternative implementation of `get_cleaned_def_path`, but this doesn't always yield a rooted
// path (but only a suffix of the full path)
fn extract_def_path(path: &hir::definitions::DefPath) -> Vec<String> {
    let mut components = Vec::new();
    for p in &path.data {
        if let Some(name) = p.data.get_opt_name() {
            components.push(name.as_str().to_owned());
        }
    }
    components
}

/// Get the path we should export an item at.
pub fn get_export_path_for_did(env: &Environment, did: DefId) -> Vec<String> {
    let attrs = env.get_attributes(did);

    if has_tool_attr(attrs, "export_as") {
        let filtered_attrs = filter_tool_attrs(attrs);

        return get_export_as_attr(filtered_attrs.as_slice()).unwrap();
    }

    // Check for an annotation on the surrounding impl
    if let Some(impl_did) = env.tcx().impl_of_method(did) {
        let attrs = env.get_attributes(impl_did);

        if has_tool_attr(attrs, "export_as") {
            let filtered_attrs = filter_tool_attrs(attrs);
            let mut path_prefix = get_export_as_attr(filtered_attrs.as_slice()).unwrap();

            // push the last component of this path
            //let def_path = env.tcx().def_path(did);
            let mut this_path = get_cleaned_def_path(env.tcx(), did);
            path_prefix.push(this_path.pop().unwrap());

            return path_prefix;
        }
    }

    get_cleaned_def_path(env.tcx(), did)
}

/// Gets an instance for a path.
/// Taken from Miri <https://github.com/rust-lang/miri/blob/31fb32e49f42df19b45baccb6aa80c3d726ed6d5/src/helpers.rs#L48>.
pub fn try_resolve_did_direct<T>(tcx: TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    tcx.crates(())
        .iter()
        .find(|&&krate| tcx.crate_name(krate).as_str() == path[0].as_ref())
        .and_then(|krate| {
            let krate = DefId {
                krate: *krate,
                index: CRATE_DEF_INDEX,
            };

            let mut items: &[middle::metadata::ModChild] = tcx.module_children(krate);
            let mut path_it = path.iter().skip(1).peekable();

            while let Some(segment) = path_it.next() {
                for item in mem::take(&mut items) {
                    let item: &middle::metadata::ModChild = item;
                    if item.ident.name.as_str() == segment.as_ref() {
                        if path_it.peek().is_none() {
                            return Some(item.res.def_id());
                        }

                        items = tcx.module_children(item.res.def_id());
                        break;
                    }
                }
            }
            None
        })
}

pub fn try_resolve_did<T>(tcx: TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    if let Some(did) = try_resolve_did_direct(tcx, path) {
        return Some(did);
    }

    // if the first component is "std", try if we can replace it with "alloc" or "core"
    if path[0].as_ref() == "std" {
        let mut components: Vec<_> = path.iter().map(|x| x.as_ref().to_owned()).collect();
        components[0] = "core".to_owned();
        if let Some(did) = try_resolve_did_direct(tcx, &components) {
            return Some(did);
        }
        // try "alloc"
        components[0] = "alloc".to_owned();
        try_resolve_did_direct(tcx, &components)
    } else {
        None
    }
}

/// Determine whether the two argument lists match for the type positions (ignoring consts and regions).
/// The first argument is the authority determining which argument positions are types.
/// The second argument may contain `None` for non-type positions.
fn args_match_types<'tcx>(
    reference: &[ty::GenericArg<'tcx>],
    compare: &[Option<ty::GenericArg<'tcx>>],
) -> bool {
    if reference.len() != compare.len() {
        return false;
    }

    for (arg1, arg2) in reference.iter().zip(compare.iter()) {
        if let Some(ty1) = arg1.as_type() {
            if let Some(arg2) = arg2 {
                if let Some(ty2) = arg2.as_type() {
                    if ty1 != ty2 {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
    }
    true
}

// Useful queries:
//tcx.trait_id_of_impl
//tcx.associated_items
//tcx.impl_trait_parent
//tcx.implementations_of_trait
//tcx.trait_impls_of
//tcx.trait_impls_in_crate
/// Try to resolve the `DefId` of an implementation of a trait for a particular type.
/// Note that this does not, in general, find a unique solution, in case there are complex things
/// with different where clauses going on.
pub fn try_resolve_trait_impl_did<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_did: DefId,
    trait_args: &[Option<ty::GenericArg<'tcx>>],
    for_type: ty::Ty<'tcx>,
) -> Option<DefId> {
    // get all impls of this trait
    let impls: &ty::trait_def::TraitImpls = tcx.trait_impls_of(trait_did);

    let simplified_type =
        middle::ty::fast_reject::simplify_type(tcx, for_type, ty::fast_reject::TreatParams::AsCandidateKey)?;
    let defs = impls.non_blanket_impls().get(&simplified_type)?;
    info!("found implementations: {:?}", impls);

    let mut solution = None;
    for did in defs {
        let impl_self_ty: ty::Ty<'tcx> = tcx.type_of(did).instantiate_identity();
        let impl_self_ty = normalize_in_function(*did, tcx, impl_self_ty).unwrap();

        // check if this is an implementation for the right type
        // TODO: is this the right way to compare the types?
        if impl_self_ty == for_type {
            let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> = tcx.impl_trait_ref(did);

            if let Some(impl_ref) = impl_ref {
                let impl_ref = normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

                let this_impl_args = impl_ref.args;
                // filter by the generic instantiation for the trait
                info!("found impl with args {:?}", this_impl_args);
                // args has self at position 0 and generics of the trait at position 1..

                // check if the generic argument types match up
                if !args_match_types(&this_impl_args.as_slice()[1..], trait_args) {
                    continue;
                }

                info!("found impl {:?}", impl_ref);
                if solution.is_some() {
                    println!(
                        "Warning: Ambiguous resolution for impl of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                        trait_did,
                        for_type,
                        solution.unwrap(),
                        impl_ref.def_id,
                    );
                } else {
                    solution = Some(*did);
                }
            }
        }
    }

    solution
}

/// Try to resolve the `DefId` of a method in an implementation of a trait for a particular type.
/// Note that this does not, in general, find a unique solution, in case there are complex things
/// with different where clauses going on.
pub fn try_resolve_trait_method_did<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_did: DefId,
    trait_args: &[Option<ty::GenericArg<'tcx>>],
    method_name: &str,
    for_type: ty::Ty<'tcx>,
) -> Option<DefId> {
    // get all impls of this trait
    let impls: &ty::trait_def::TraitImpls = tcx.trait_impls_of(trait_did);

    let simplified_type =
        middle::ty::fast_reject::simplify_type(tcx, for_type, ty::fast_reject::TreatParams::AsCandidateKey)?;
    let defs = impls.non_blanket_impls().get(&simplified_type)?;
    info!("found implementations: {:?}", impls);

    let mut solution = None;
    for did in defs {
        let impl_self_ty: ty::Ty<'tcx> = tcx.type_of(did).instantiate_identity();
        let impl_self_ty = normalize_in_function(*did, tcx, impl_self_ty).unwrap();

        // check if this is an implementation for the right type
        // TODO: is this the right way to compare the types?
        if impl_self_ty == for_type {
            let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> = tcx.impl_trait_ref(did);

            if let Some(impl_ref) = impl_ref {
                let impl_ref = normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

                let this_impl_args = impl_ref.args;
                // filter by the generic instantiation for the trait
                info!("found impl with args {:?}", this_impl_args);
                // args has self at position 0 and generics of the trait at position 1..

                // check if the generic argument types match up
                if !args_match_types(&this_impl_args.as_slice()[1..], trait_args) {
                    continue;
                }

                let impl_assoc_items: &ty::AssocItems = tcx.associated_items(did);
                // find the right item
                if let Some(item) = impl_assoc_items.find_by_name_and_kind(
                    tcx,
                    span::symbol::Ident::from_str(method_name),
                    ty::AssocKind::Fn,
                    trait_did,
                ) {
                    info!("found impl {:?} with item {:?}", impl_ref, item);
                    if solution.is_some() {
                        println!(
                            "Warning: Ambiguous resolution for method {method_name} of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                            trait_did,
                            for_type,
                            solution.unwrap(),
                            item.def_id
                        );
                    } else {
                        solution = Some(item.def_id);
                    }
                }
            }
        }
    }

    solution
}

/// Try to get a defid of a method at the given path.
/// This does not handle trait methods.
/// This also does not handle overlapping method definitions/specialization well.
pub fn try_resolve_method_did_direct<T>(tcx: TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    tcx.crates(())
        .iter()
        .find(|&&krate| tcx.crate_name(krate).as_str() == path[0].as_ref())
        .and_then(|krate| {
            let krate = DefId {
                krate: *krate,
                index: CRATE_DEF_INDEX,
            };

            let mut items: &[middle::metadata::ModChild] = tcx.module_children(krate);
            let mut path_it = path.iter().skip(1).peekable();

            while let Some(segment) = path_it.next() {
                //info!("items to look at: {:?}", items);
                for item in mem::take(&mut items) {
                    let item: &middle::metadata::ModChild = item;

                    if item.ident.name.as_str() != segment.as_ref() {
                        continue;
                    }

                    info!("taking path: {:?}", segment.as_ref());
                    if path_it.peek().is_none() {
                        return Some(item.res.def_id());
                    }

                    // just the method remaining
                    if path_it.len() != 1 {
                        items = tcx.module_children(item.res.def_id());
                        break;
                    }

                    let did: DefId = item.res.def_id();
                    let impls: &[DefId] = tcx.inherent_impls(did);
                    info!("trying to find method among impls {:?}", impls);

                    let find = path_it.next().unwrap();
                    for impl_did in impls {
                        //let ty = tcx.type_of(*impl_did);
                        //info!("type of impl: {:?}", ty);
                        let items: &ty::AssocItems = tcx.associated_items(impl_did);
                        //info!("items here: {:?}", items);
                        // TODO more robust error handling if there are multiple matches.
                        for item in items.in_definition_order() {
                            //info!("comparing: {:?} with {:?}", item.name.as_str(), find);
                            if item.name.as_str() == find.as_ref() {
                                return Some(item.def_id);
                            }
                        }
                        //info!("impl items: {:?}", items);
                    }

                    //info!("inherent impls for {:?}: {:?}", did, impls);
                    return None;
                }
            }

            None
        })
}

pub fn try_resolve_method_did<T>(tcx: TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    if let Some(did) = try_resolve_method_did_direct(tcx, path) {
        return Some(did);
    }

    // if the first component is "std", try if we can replace it with "alloc" or "core"
    if path[0].as_ref() == "std" {
        let mut components: Vec<_> = path.iter().map(|x| x.as_ref().to_owned()).collect();
        components[0] = "core".to_owned();
        if let Some(did) = try_resolve_method_did_direct(tcx, &components) {
            return Some(did);
        }
        // try "alloc"
        components[0] = "alloc".to_owned();
        try_resolve_method_did_direct(tcx, &components)
    } else {
        None
    }
}

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// + `is_prefix(x.f, x.f) == true`
/// + `is_prefix(x.f.g, x.f) == true`
/// + `is_prefix(x.f, x.f.g) == false`
pub fn is_prefix<'tcx>(place: &mir::Place<'tcx>, potential_prefix: &mir::Place<'tcx>) -> bool {
    if place.local != potential_prefix.local || place.projection.len() < potential_prefix.projection.len() {
        false
    } else {
        place.projection.iter().zip(potential_prefix.projection.iter()).all(|(e1, e2)| e1 == e2)
    }
}

/// Expands a place `x.f.g` of type struct into a vector of places for
/// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
/// `without_field` is not `None`, then omits that field from the final
/// vector.
pub fn expand_struct_place<'tcx>(
    place: &mir::Place<'tcx>,
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    without_field: Option<usize>,
) -> Vec<mir::Place<'tcx>> {
    let mut places = Vec::new();
    let typ = place.ty(mir, tcx);

    if typ.variant_index.is_some() {
        // Downcast is a no-op.
        return places;
    }

    match typ.ty.kind() {
        ty::Adt(def, substs) => {
            assert!(def.is_struct(), "Only structs can be expanded. Got def={:?}.", def);
            let variant = def.non_enum_variant();
            for (index, field_def) in variant.fields.iter().enumerate() {
                if Some(index) != without_field {
                    let field_place = tcx.mk_place_field(*place, index.into(), field_def.ty(tcx, substs));
                    places.push(field_place);
                }
            }
        },

        ty::Tuple(slice) => {
            for (index, arg) in slice.iter().enumerate() {
                if Some(index) != without_field {
                    let field_place = tcx.mk_place_field(*place, index.into(), arg);
                    places.push(field_place);
                }
            }
        },

        ty::Ref(_, _, _) => match without_field {
            Some(without_field) => {
                assert_eq!(without_field, 0, "References have only a single “field”.");
            },
            None => {
                places.push(tcx.mk_place_deref(*place));
            },
        },

        ty => {
            unimplemented!("ty={:?}", &ty);
        },
    }

    places
}

/// Expand `current_place` one level down by following the `guide_place`.
/// Returns the new `current_place` and a vector containing other places that
/// could have resulted from the expansion.
pub fn expand_one_level<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    current_place: mir::Place<'tcx>,
    guide_place: mir::Place<'tcx>,
) -> (mir::Place<'tcx>, Vec<mir::Place<'tcx>>) {
    let index = current_place.projection.len();
    match guide_place.projection[index] {
        mir::ProjectionElem::Field(projected_field, field_ty) => {
            let places = expand_struct_place(&current_place, mir, tcx, Some(projected_field.index()));
            let new_current_place = tcx.mk_place_field(current_place, projected_field, field_ty);
            (new_current_place, places)
        },
        mir::ProjectionElem::Downcast(_symbol, variant) => {
            let kind = &current_place.ty(mir, tcx).ty.kind();
            force_matches!(kind, ty::TyKind::Adt(adt, _) =>
                (tcx.mk_place_downcast(current_place, *adt, variant), Vec::new())
            )
        },
        mir::ProjectionElem::Deref => (tcx.mk_place_deref(current_place), Vec::new()),
        mir::ProjectionElem::Index(idx) => (tcx.mk_place_index(current_place, idx), Vec::new()),
        elem => {
            unimplemented!("elem = {:?}", elem);
        },
    }
}

/// Pop the last projection from the place and return the new place with the popped element.
pub fn try_pop_one_level<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
) -> Option<(mir::PlaceElem<'tcx>, mir::Place<'tcx>)> {
    if place.projection.is_empty() {
        return None;
    }

    let last_index = place.projection.len() - 1;
    let new_place = mir::Place {
        local: place.local,
        projection: tcx.mk_place_elems(&place.projection[..last_index]),
    };

    Some((place.projection[last_index], new_place))
}

/// Pop the last element from the place if it is a dereference.
pub fn try_pop_deref<'tcx>(tcx: TyCtxt<'tcx>, place: mir::Place<'tcx>) -> Option<mir::Place<'tcx>> {
    try_pop_one_level(tcx, place)
        .and_then(|(elem, base)| (elem == mir::ProjectionElem::Deref).then_some(base))
}

/// Subtract the `subtrahend` place from the `minuend` place. The
/// subtraction is defined as set minus between `minuend` place replaced
/// with a set of places that are unrolled up to the same level as
/// `subtrahend` and the singleton `subtrahend` set. For example,
/// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
/// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
/// subtracting `{x.f.g.h}` from it, which results into `{x.g, x.h,
/// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`.
pub fn expand<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    minuend: &mir::Place<'tcx>,
    subtrahend: &mir::Place<'tcx>,
) -> Vec<mir::Place<'tcx>> {
    assert!(is_prefix(subtrahend, minuend), "The minuend must be the prefix of the subtrahend.");
    trace!("[enter] expand minuend={:?} subtrahend={:?}", minuend, subtrahend);
    let mut place_set = Vec::new();
    let mut minuend = *minuend;
    while minuend.projection.len() < subtrahend.projection.len() {
        let (new_minuend, places) = expand_one_level(mir, tcx, minuend, *subtrahend);
        minuend = new_minuend;
        place_set.extend(places);
    }
    trace!("[exit] expand minuend={:?} subtrahend={:?} place_set={:?}", minuend, subtrahend, place_set);
    place_set
}

/// Try to collapse all places in `places` by following the
/// `guide_place`. This function is basically the reverse of
/// `expand_struct_place`.
pub fn collapse<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    places: &mut FxHashSet<mir::Place<'tcx>>,
    guide_place: &mir::Place<'tcx>,
) {
    fn recurse<'tcx>(
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        places: &mut FxHashSet<mir::Place<'tcx>>,
        current_place: mir::Place<'tcx>,
        guide_place: mir::Place<'tcx>,
    ) {
        if current_place == guide_place {
            return;
        }

        let (new_current_place, mut expansion) = expand_one_level(mir, tcx, current_place, guide_place);

        recurse(mir, tcx, places, new_current_place, guide_place);
        expansion.push(new_current_place);

        if expansion.iter().all(|place| places.contains(place)) {
            for place in expansion {
                places.remove(&place);
            }
            places.insert(current_place);
        }
    }

    recurse(mir, tcx, places, guide_place.local.into(), *guide_place);
}

#[derive(Debug)]
pub struct VecPlaceComponent<'tcx> {
    place: mir::Place<'tcx>,
}

impl<'tcx> VecPlaceComponent<'tcx> {
    pub const fn get_mir_place(&self) -> &mir::Place<'tcx> {
        &self.place
    }
}

/// A different way to represent a place that is more similar to the one
/// mentioned in the issue <https://github.com/rust-lang/rust/issues/52708>.
#[derive(Debug)]
pub struct VecPlace<'tcx> {
    components: Vec<VecPlaceComponent<'tcx>>,
}

impl<'tcx> VecPlace<'tcx> {
    pub fn new(mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>, place: &mir::Place<'tcx>) -> VecPlace<'tcx> {
        let mut vec_place = Self {
            components: Vec::new(),
        };
        let mut prefix: mir::Place = place.local.into();
        vec_place.components.push(VecPlaceComponent { place: prefix });
        while prefix.projection.len() < place.projection.len() {
            let (new_prefix, _) = expand_one_level(mir, tcx, prefix, *place);
            prefix = new_prefix;
            vec_place.components.push(VecPlaceComponent { place: prefix });
        }
        vec_place
    }

    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = &'a VecPlaceComponent<'tcx>> {
        self.components.iter()
    }

    pub fn component_count(&self) -> usize {
        self.components.len()
    }
}

/// Check if `<tool>::<name>` is among the attributes, where `tool` is determined by the
/// `spec_hotword` config.
/// Any arguments of the attribute are ignored.
pub fn has_tool_attr(attrs: &[ast::Attribute], name: &str) -> bool {
    get_tool_attr(attrs, name).is_some()
}

/// Get the arguments for a tool attribute, if it exists.
pub fn get_tool_attr<'a>(attrs: &'a [ast::Attribute], name: &str) -> Option<&'a ast::AttrArgs> {
    attrs.iter().find_map(|attr| match &attr.kind {
        ast::AttrKind::Normal(na) => {
            let segments = &na.item.path.segments;
            let args = &na.item.args;
            (segments.len() == 2
                && segments[0].ident.as_str() == rrconfig::spec_hotword().as_str()
                && segments[1].ident.as_str() == name)
                .then_some(args)
        },
        _ => None,
    })
}

/// Check if `<tool>::name` is among the filtered attributes.
pub fn has_tool_attr_filtered(attrs: &[&ast::AttrItem], name: &str) -> bool {
    attrs.iter().any(|item| {
        let segments = &item.path.segments;
        segments.len() == 2
            && segments[0].ident.as_str() == rrconfig::spec_hotword().as_str()
            && segments[1].ident.as_str() == name
    })
}

/// Check if any attribute starting with `<tool>` is among the attributes.
pub fn has_any_tool_attr(attrs: &[ast::Attribute]) -> bool {
    attrs.iter().any(|attr| match &attr.kind {
        ast::AttrKind::Normal(na) => {
            let segments = &na.item.path.segments;
            segments[0].ident.as_str() == rrconfig::spec_hotword().as_str()
        },
        _ => false,
    })
}

/// Get all tool attributes, i.e. attributes of the shape `<tool>::attr`, where `tool` is
/// determined by the `spec_hotword` config.
pub fn filter_tool_attrs(attrs: &[ast::Attribute]) -> Vec<&ast::AttrItem> {
    attrs
        .iter()
        .filter_map(|attr| match &attr.kind {
            ast::AttrKind::Normal(na) => {
                let item = &na.item;

                let seg = item.path.segments.get(0)?;

                (seg.ident.name.as_str() == rrconfig::spec_hotword()).then_some(item)
            },
            _ => None,
        })
        .collect()
}
