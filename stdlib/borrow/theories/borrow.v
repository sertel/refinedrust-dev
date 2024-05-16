From refinedrust Require Import typing.


Section borrow.
  Context `{!typeGS Σ}.

  (* this is what monomorphizations of functions taking a generic of this constraint take *)
  Record Borrow_phys := {
    Borrow_borrow_loc : loc;
    Borrow_borrow_arg_sts : list syn_type;
  }.
End borrow.

Section rr.
Context `{!typeGS Σ}.

Context {Borrowed_rt : Type}.
Context (Borrowed_ty : type Borrowed_rt).

Class Borrowable {Self_rt} (self_ty : type Self_rt) := {
  borrowable_to : Self_rt → Borrowed_rt;
  (*borrowable_from : Borrowed_rt → Self_rt;*)
}.
Global Arguments borrowable_to {_ _ _}.

Record Borrow_spec := {
  Borrow_borrow_spec : sigT (λ lfts, sigT (λ A, prod_vec lft lfts → A → fn_params));
}.

Definition Borrow_base_spec {Self_rt} (self_ty : type Self_rt) `{!Borrowable self_ty} : Borrow_spec := {|
  Borrow_borrow_spec :=
  existT _ $ existT _ $ (fn(∀ (((), ulft_a)) : 1 | (x) : Self_rt, (λ _, []); #x @ shr_ref (self_ty) ulft_a; (λ π, True)) → ∃ z : (), #(borrowable_to x) @ shr_ref Borrowed_ty ulft_a; (λ π, True))
|}.

Definition Borrow_has_spec (π : thread_id) (impl: Borrow_phys) (spec: Borrow_spec) : iProp Σ :=
  impl.(Borrow_borrow_loc) ◁ᵥ{π} impl.(Borrow_borrow_loc) @ function_ptr impl.(Borrow_borrow_arg_sts) (projT2 $ projT2 spec.(Borrow_borrow_spec)) ∗
  True.

End rr.
