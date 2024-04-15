/// Inspired by (in terms of rustc APIs used) by
/// https://github.com/xldenis/creusot/blob/9d8b1822cd0c43154a6d5d4d05460be56710399c/creusot/src/translation/traits.rs
use log::info;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty;
use rustc_middle::ty::{
    AssocItem, AssocItemContainer, GenericArgsRef, ParamEnv, TraitRef, TyCtxt, TypeVisitableExt,
};
use rustc_trait_selection::traits::{ImplSource, NormalizeExt};

pub(crate) fn associated_items(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = &AssocItem> {
    tcx.associated_items(def_id).in_definition_order()
}

/// Normalize a type in the given environment.
pub fn normalize_type<'tcx, T>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: T,
) -> Result<T, Vec<rustc_trait_selection::traits::FulfillmentError<'tcx>>>
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let infer_ctx = tcx.infer_ctxt().build();
    rustc_trait_selection::traits::fully_normalize(
        &infer_ctx,
        rustc_middle::traits::ObligationCause::dummy(),
        param_env,
        ty,
    )
}

/// Resolve an implementation of a trait using codegen candidate selection.
/// `did` can be the id of a trait, or the id of an associated item of a trait.
pub fn resolve_impl_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    did: DefId,
    substs: GenericArgsRef<'tcx>,
) -> Option<&'tcx ImplSource<'tcx, ()>> {
    let substs = tcx.normalize_erasing_regions(param_env, substs);

    // Check if the `did` is an associated item
    let trait_ref;
    if let Some(item) = tcx.opt_associated_item(did) {
        match item.container {
            AssocItemContainer::TraitContainer =>
            // this is part of a trait declaration
            {
                trait_ref = TraitRef::new(tcx, item.container_id(tcx), substs)
            },
            AssocItemContainer::ImplContainer =>
            // this is part of an implementation of a trait
            {
                trait_ref = tcx.impl_trait_ref(item.container_id(tcx))?.instantiate(tcx, substs)
            },
        }
    } else {
        // Otherwise, check if it's a reference to a trait itself
        if tcx.is_trait(did) {
            trait_ref = TraitRef::new(tcx, did, substs)
        } else {
            return None;
        }
    };

    let source = tcx.codegen_select_candidate((param_env, trait_ref));
    source.map_or_else(|_| None, |x| Some(x))
}

pub fn resolve_trait_or_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>, TraitResolutionKind)> {
    if tcx.is_trait(def_id) {
        resolve_trait(tcx, param_env, def_id, substs)
    } else {
        resolve_assoc_item(tcx, param_env, def_id, substs)
    }
}

/// Resolve a reference to a trait using codegen trait selection.
/// `did` should be the id of a trait.
pub fn resolve_trait<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    did: DefId,
    substs: GenericArgsRef<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>, TraitResolutionKind)> {
    if tcx.is_trait(did) {
        let impl_source = resolve_impl_source(tcx, param_env, did, substs);
        info!("trait impl_source for {:?}: {:?}", did, impl_source);
        match impl_source? {
            ImplSource::UserDefined(impl_data) => {
                Some((impl_data.impl_def_id, impl_data.args, TraitResolutionKind::UserDefined))
            },
            ImplSource::Param(_) => Some((did, substs, TraitResolutionKind::Param)),
            ImplSource::Builtin(_, _) => None,
        }
    } else {
        None
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum TraitResolutionKind {
    Param,
    UserDefined,
    Closure,
}

/// Resolve a reference to a trait item using codegen trait selection.
/// `did` should be the id of a trait item.
pub fn resolve_assoc_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    did: DefId,
    substs: GenericArgsRef<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>, TraitResolutionKind)> {
    let assoc = tcx.opt_associated_item(did)?;

    /*
    // If we're given an associated item that is already on an instance,
    // we don't need to resolve at all!
    //
    // FIXME: not true given specialization!
    if let AssocItemContainer::ImplContainer = assoc.container {
        return None;
    }
    */

    let trait_ref = TraitRef::from_method(tcx, tcx.trait_of_item(did).unwrap(), substs);

    let impl_source = resolve_impl_source(tcx, param_env, did, substs)?;
    info!("trait impl_source for {:?}: {:?}", did, impl_source);

    match impl_source {
        ImplSource::UserDefined(impl_data) => {
            // this is a user-defined trait, and we found the right impl
            // now map back to the item we were looking for
            let trait_did = tcx.trait_id_of_impl(impl_data.impl_def_id).unwrap();
            let trait_def: &'tcx rustc_middle::ty::TraitDef = tcx.trait_def(trait_did);

            // Find the id of the actual associated method we will be running
            let ancestors = trait_def.ancestors(tcx, impl_data.impl_def_id).unwrap();
            // find the item we were looking for
            let leaf_def = ancestors.leaf_def(tcx, assoc.def_id).unwrap_or_else(|| {
                panic!("{:?} not found in {:?}", assoc, impl_data.impl_def_id);
            });

            if !leaf_def.is_final() && trait_ref.still_further_specializable() {
                // return the original id to call
                return Some((did, substs, TraitResolutionKind::UserDefined));
            }

            // Translate the original substitution into one on the selected impl method
            let infcx = tcx.infer_ctxt().build();

            let param_env = param_env.with_reveal_all_normalized(tcx);
            let substs = substs.rebase_onto(tcx, trait_did, impl_data.args);
            let substs = rustc_trait_selection::traits::translate_args(
                &infcx,
                param_env,
                impl_data.impl_def_id,
                substs,
                leaf_def.defining_node,
            );
            let leaf_substs = substs;
            //let leaf_substs = infcx.tcx.erase_regions(substs);

            Some((leaf_def.item.def_id, leaf_substs, TraitResolutionKind::UserDefined))
        },
        ImplSource::Param(_) => Some((did, substs, TraitResolutionKind::Param)),
        ImplSource::Builtin(_, _) =>
        // the 0-th parameter should be self
        // if this is a closure, we want to call that closure
        {
            match *substs[0].as_type().unwrap().kind() {
                // try to get the body
                rustc_middle::ty::Closure(closure_def_id, closure_substs) => {
                    Some((closure_def_id, closure_substs, TraitResolutionKind::Closure))
                },
                _ => unimplemented!(),
            }
        },
    }
}
