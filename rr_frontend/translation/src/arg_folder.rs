use rustc_middle::ty::visit::*;
use rustc_middle::ty::{self, GenericArg, GenericArgKind, ParamConst, Ty, TyCtxt, TypeFolder};
pub use rustc_type_ir::fold::{TypeFoldable, TypeSuperFoldable};
pub use rustc_type_ir::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor};

/// A version of the `ArgFolder` in rustc_middle::src::ty::generic_args that skips over `ReVar`
/// (instead of triggering a bug).

struct ArgFolder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    args: &'a [GenericArg<'tcx>],

    /// Number of region binders we have passed through while doing the substitution
    binders_passed: u32,
}

impl<'a, 'tcx> TypeFolder<TyCtxt<'tcx>> for ArgFolder<'a, 'tcx> {
    #[inline]
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T> {
        self.binders_passed += 1;
        let t = t.super_fold_with(self);
        self.binders_passed -= 1;
        t
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        #[cold]
        #[inline(never)]
        fn region_param_out_of_range(data: ty::EarlyBoundRegion, args: &[GenericArg<'_>]) -> ! {
            panic!(
                "Region parameter out of range when substituting in region {} (index={}, args = {:?})",
                data.name, data.index, args,
            )
        }

        #[cold]
        #[inline(never)]
        fn region_param_invalid(data: ty::EarlyBoundRegion, other: GenericArgKind<'_>) -> ! {
            panic!(
                "Unexpected parameter {:?} when substituting in region {} (index={})",
                other, data.name, data.index
            )
        }

        // Note: This routine only handles regions that are bound on
        // type declarations and other outer declarations, not those
        // bound in *fn types*. Region substitution of the bound
        // regions that appear in a function signature is done using
        // the specialized routine `ty::replace_late_regions()`.
        match *r {
            ty::ReEarlyBound(data) => {
                let rk = self.args.get(data.index as usize).map(|k| k.unpack());
                match rk {
                    Some(GenericArgKind::Lifetime(lt)) => self.shift_region_through_binders(lt),
                    Some(other) => region_param_invalid(data, other),
                    None => region_param_out_of_range(data, self.args),
                }
            },
            ty::ReLateBound(..)
            | ty::ReFree(_)
            | ty::ReStatic
            | ty::RePlaceholder(_)
            | ty::ReErased
            | ty::ReError(_)
            | ty::ReVar(_) => r,
        }
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        if !t.has_param() {
            return t;
        }

        match *t.kind() {
            ty::Param(p) => self.ty_for_param(p, t),
            _ => t.super_fold_with(self),
        }
    }

    fn fold_const(&mut self, c: ty::Const<'tcx>) -> ty::Const<'tcx> {
        if let ty::ConstKind::Param(p) = c.kind() {
            self.const_for_param(p, c)
        } else {
            c.super_fold_with(self)
        }
    }
}

impl<'a, 'tcx> ArgFolder<'a, 'tcx> {
    fn ty_for_param(&self, p: ty::ParamTy, source_ty: Ty<'tcx>) -> Ty<'tcx> {
        // Look up the type in the args. It really should be in there.
        let opt_ty = self.args.get(p.index as usize).map(|k| k.unpack());
        let ty = match opt_ty {
            Some(GenericArgKind::Type(ty)) => ty,
            Some(kind) => self.type_param_expected(p, source_ty, kind),
            None => self.type_param_out_of_range(p, source_ty),
        };

        self.shift_vars_through_binders(ty)
    }

    #[cold]
    #[inline(never)]
    fn type_param_expected(&self, p: ty::ParamTy, ty: Ty<'tcx>, kind: GenericArgKind<'tcx>) -> ! {
        panic!(
            "expected type for `{:?}` ({:?}/{}) but found {:?} when substituting, args={:?}",
            p, ty, p.index, kind, self.args,
        )
    }

    #[cold]
    #[inline(never)]
    fn type_param_out_of_range(&self, p: ty::ParamTy, ty: Ty<'tcx>) -> ! {
        panic!(
            "type parameter `{:?}` ({:?}/{}) out of range when substituting, args={:?}",
            p, ty, p.index, self.args,
        )
    }

    fn const_for_param(&self, p: ParamConst, source_ct: ty::Const<'tcx>) -> ty::Const<'tcx> {
        // Look up the const in the args. It really should be in there.
        let opt_ct = self.args.get(p.index as usize).map(|k| k.unpack());
        let ct = match opt_ct {
            Some(GenericArgKind::Const(ct)) => ct,
            Some(kind) => self.const_param_expected(p, source_ct, kind),
            None => self.const_param_out_of_range(p, source_ct),
        };

        self.shift_vars_through_binders(ct)
    }

    #[cold]
    #[inline(never)]
    fn const_param_expected(&self, p: ty::ParamConst, ct: ty::Const<'tcx>, kind: GenericArgKind<'tcx>) -> ! {
        panic!(
            "expected const for `{:?}` ({:?}/{}) but found {:?} when substituting args={:?}",
            p, ct, p.index, kind, self.args,
        )
    }

    #[cold]
    #[inline(never)]
    fn const_param_out_of_range(&self, p: ty::ParamConst, ct: ty::Const<'tcx>) -> ! {
        panic!(
            "const parameter `{:?}` ({:?}/{}) out of range when substituting args={:?}",
            p, ct, p.index, self.args,
        )
    }

    /// It is sometimes necessary to adjust the De Bruijn indices during substitution. This occurs
    /// when we are substituting a type with escaping bound vars into a context where we have
    /// passed through binders. That's quite a mouthful. Let's see an example:
    ///
    /// ```
    /// type Func<A> = fn(A);
    /// type MetaFunc = for<'a> fn(Func<&'a i32>);
    /// ```
    ///
    /// The type `MetaFunc`, when fully expanded, will be
    /// ```ignore (illustrative)
    /// for<'a> fn(fn(&'a i32))
    /// //      ^~ ^~ ^~~
    /// //      |  |  |
    /// //      |  |  DebruijnIndex of 2
    /// //      Binders
    /// ```
    /// Here the `'a` lifetime is bound in the outer function, but appears as an argument of the
    /// inner one. Therefore, that appearance will have a DebruijnIndex of 2, because we must skip
    /// over the inner binder (remember that we count De Bruijn indices from 1). However, in the
    /// definition of `MetaFunc`, the binder is not visible, so the type `&'a i32` will have a
    /// De Bruijn index of 1. It's only during the substitution that we can see we must increase the
    /// depth by 1 to account for the binder that we passed through.
    ///
    /// As a second example, consider this twist:
    ///
    /// ```
    /// type FuncTuple<A> = (A, fn(A));
    /// type MetaFuncTuple = for<'a> fn(FuncTuple<&'a i32>);
    /// ```
    ///
    /// Here the final type will be:
    /// ```ignore (illustrative)
    /// for<'a> fn((&'a i32, fn(&'a i32)))
    /// //          ^~~         ^~~
    /// //          |           |
    /// //   DebruijnIndex of 1 |
    /// //               DebruijnIndex of 2
    /// ```
    /// As indicated in the diagram, here the same type `&'a i32` is substituted once, but in the
    /// first case we do not increase the De Bruijn index and in the second case we do. The reason
    /// is that only in the second case have we passed through a fn binder.
    fn shift_vars_through_binders<T: TypeFoldable<TyCtxt<'tcx>>>(&self, val: T) -> T {
        if self.binders_passed == 0 || !val.has_escaping_bound_vars() {
            return val;
        }

        let result = ty::fold::shift_vars(TypeFolder::interner(self), val, self.binders_passed);

        result
    }

    fn shift_region_through_binders(&self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if self.binders_passed == 0 || !region.has_escaping_bound_vars() {
            return region;
        }
        ty::fold::shift_region(self.tcx, region, self.binders_passed)
    }
}

pub fn ty_instantiate<'tcx>(x: Ty<'tcx>, tcx: TyCtxt<'tcx>, args: &[GenericArg<'tcx>]) -> Ty<'tcx> {
    let mut folder = ArgFolder {
        tcx,
        args,
        binders_passed: 0,
    };
    x.fold_with(&mut folder)
}
