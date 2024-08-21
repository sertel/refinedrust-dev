// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::hir::intravisit::Visitor;
use rr_rustc_interface::middle::ty::TyCtxt;
use rr_rustc_interface::{hir, middle};

use crate::environment::Environment;

pub struct CollectPrustiSpecVisitor<'a, 'tcx: 'a> {
    env: &'a Environment<'tcx>,
    tcx: TyCtxt<'tcx>,
    functions: Vec<LocalDefId>,
    modules: Vec<LocalDefId>,
    statics: Vec<LocalDefId>,
    consts: Vec<LocalDefId>,
    traits: Vec<LocalDefId>,
    trait_impls: Vec<LocalDefId>,
}

impl<'a, 'tcx> CollectPrustiSpecVisitor<'a, 'tcx> {
    pub fn new(env: &'a Environment<'tcx>) -> Self {
        CollectPrustiSpecVisitor {
            env,
            tcx: env.tcx(),
            functions: Vec::new(),
            modules: Vec::new(),
            statics: Vec::new(),
            consts: Vec::new(),
            traits: Vec::new(),
            trait_impls: Vec::new(),
        }
    }

    pub fn get_results(
        self,
    ) -> (Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>) {
        (self.functions, self.modules, self.statics, self.consts, self.traits)
    }

    pub fn get_trait_impls(self) -> Vec<LocalDefId> {
        self.trait_impls
    }

    pub fn run(&mut self) {
        //self.tcx.hir().visit_all_item_likes_in_crate
        let it: &middle::hir::ModuleItems = self.tcx.hir_crate_items(());
        for id in it.items() {
            self.visit_item(self.tcx.hir().item(id));
        }
        for id in it.impl_items() {
            self.visit_impl_item(self.tcx.hir().impl_item(id));
        }
        for id in it.trait_items() {
            self.visit_trait_item(self.tcx.hir().trait_item(id));
        }
        //for id in it.foreign_items() {

        //}
    }
}

impl<'a, 'tcx> Visitor<'tcx> for CollectPrustiSpecVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        //let attrs = self.tcx.get_attrs(item.def_id.to_def_id());
        if let hir::ItemKind::Fn(..) = item.kind {
            let def_id = item.hir_id().owner.def_id;
            let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
            trace!("Add fn item {} to result", item_def_path);
            self.functions.push(def_id);
        } else if let hir::ItemKind::Const(_, _, _) = item.kind {
            let def_id = item.hir_id().owner.def_id;
            let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
            trace!("Add const {} to result", item_def_path);
            self.consts.push(def_id);
        } else if let hir::ItemKind::Static(..) = item.kind {
            let def_id = item.hir_id().owner.def_id;
            let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
            trace!("Add static {} to result", item_def_path);
            self.statics.push(def_id);
        } else if let hir::ItemKind::Mod(..) = item.kind {
            let def_id = item.hir_id().owner.def_id;
            let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
            trace!("Add module {} to result", item_def_path);
            self.modules.push(def_id);
        } else if let hir::ItemKind::Trait(..) = item.kind {
            let def_id = item.hir_id().owner.def_id;
            let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
            trace!("Add trait {} to result", item_def_path);
            self.traits.push(def_id);
        } else if let hir::ItemKind::Impl(i) = item.kind {
            let def_id = item.hir_id().owner.def_id;
            if i.of_trait.is_some() {
                let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
                trace!("Add trait impl {} to result", item_def_path);
                self.trait_impls.push(def_id);
            }
        }
    }

    /// Visit trait items which are default impls of methods.
    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
        //let attrs = self.tcx.get_attrs(trait_item.def_id.to_def_id());

        // Skip associated types and other non-methods items
        if let hir::TraitItemKind::Fn(..) = trait_item.kind {
            // continue
        } else {
            return;
        }

        // Skip body-less trait methods
        if let hir::TraitItemKind::Fn(_, hir::TraitFn::Required(_)) = trait_item.kind {
            return;
        }
        let def_id = trait_item.hir_id().owner.def_id;

        let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
        trace!("Add trait-fn-item {} to result", item_def_path);
        self.functions.push(def_id);
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
        //let attrs = self.tcx.get_attrs(impl_item.def_id.to_def_id());

        // Skip associated types and other non-methods items
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            // continue
        } else {
            return;
        }

        let def_id = impl_item.hir_id().owner.def_id;

        let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
        trace!("Add impl-fn-item {} to result", item_def_path);
        self.functions.push(def_id);
    }

    fn visit_foreign_item(&mut self, _foreign_item: &hir::ForeignItem) {
        // Nothing
    }
}
