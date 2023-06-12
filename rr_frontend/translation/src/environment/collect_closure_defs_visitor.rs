use rustc_hir::intravisit::{Visitor, walk_expr};
use rustc_hir as hir;
use rustc_middle::hir::map::Map;
use crate::environment::Environment;
use log::trace;
use rustc_hir::def_id::LocalDefId;

pub struct CollectClosureDefsVisitor<'env, 'tcx: 'env> {
    env: &'env Environment<'tcx>,
    map: Map<'tcx>,
    result: Vec<LocalDefId>,
}

impl<'env, 'tcx> CollectClosureDefsVisitor<'env, 'tcx> {
    pub fn new(env: &'env Environment<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            env,
            map: env.tcx().hir(),
            result: Vec::new(),
        }
    }
    pub fn get_closure_defs(self) -> Vec<LocalDefId> {
        self.result
    }

    pub fn run(&mut self) {

    }
}

impl<'env, 'tcx> Visitor<'tcx> for CollectClosureDefsVisitor<'env, 'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = rr_rustc_interface::middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.map
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(_) = expr.kind {
            let _tcx = self.env.tcx();
            let def_id = self.map.local_def_id(expr.hir_id);
            let item_def_path = self.env.get_item_def_path(def_id.to_def_id());
            trace!("Add {} to result", item_def_path);
            self.result.push(def_id);
        }

        walk_expr (self, expr)
    }
}
