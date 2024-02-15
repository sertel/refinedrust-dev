// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{HashMap, HashSet};

use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use ty::TypeSuperFoldable;

use crate::base::*;

/// A `TypeFolder` that gathers all the type variables.
pub struct TyVarFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    tyvars: HashSet<ty::ParamTy>,
}

impl<'tcx> TyVarFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyVarFolder {
            tcx,
            tyvars: HashSet::new(),
        }
    }

    pub fn get_result(self) -> HashSet<ty::ParamTy> {
        self.tyvars
    }
}

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for TyVarFolder<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        match t.kind() {
            TyKind::Param(param) => {
                self.tyvars.insert(param.clone());
                t
            },
            _ => t.super_fold_with(self),
        }
    }
}

struct TyVarRenameFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// the generated substitution to get back the original type
    new_subst: Vec<ty::ParamTy>,
    /// maps old names to new names
    name_map: HashMap<ty::ParamTy, ty::ParamTy>,
}

impl<'tcx> TyVarRenameFolder<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyVarRenameFolder {
            tcx,
            new_subst: Vec::new(),
            name_map: HashMap::new(),
        }
    }

    /// Obtain the substitution for getting back the old type.
    fn get_subst(self) -> Vec<ty::ParamTy> {
        self.new_subst
    }
}

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for TyVarRenameFolder<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        match t.kind() {
            TyKind::Param(param) => {
                if let Some(new_param) = self.name_map.get(&param) {
                    Ty::new_param(self.interner(), new_param.index, new_param.name)
                } else {
                    // create another type param
                    let new_index = self.new_subst.len() as u32;
                    // reuse the name
                    let name = param.name;
                    let new_ty = Ty::new_param(self.interner(), new_index, name);
                    let new_param = ty::ParamTy::new(new_index, name);

                    self.name_map.insert(*param, new_param);
                    self.new_subst.push(*param);

                    new_ty
                }
            },
            _ => t.super_fold_with(self),
        }
    }
}

/// A TypeFolder that erases all regions.
pub struct TyRegionEraseFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
}
impl<'tcx> TyRegionEraseFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyRegionEraseFolder { tcx }
    }
}
impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for TyRegionEraseFolder<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_region(&mut self, _: ty::Region<'tcx>) -> ty::Region<'tcx> {
        ty::Region::new_from_kind(self.interner(), ty::RegionKind::ReErased)
    }
}

/// A TypeFolder that finds all regions occurring in a type.
pub struct TyRegionCollectFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    regions: Vec<Region>,
}
impl<'tcx> TyRegionCollectFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyRegionCollectFolder {
            tcx,
            regions: Vec::new(),
        }
    }

    pub fn get_regions(self) -> Vec<Region> {
        self.regions
    }
}
impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for TyRegionCollectFolder<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // TODO: handle the case that we pass below binders
    fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
    where
        T: ty::TypeFoldable<TyCtxt<'tcx>>,
    {
        t.super_fold_with(self)
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match r.kind() {
            ty::RegionKind::ReVar(r) => {
                self.regions.push(r);
            },
            _ => {},
        }
        r
    }
}
