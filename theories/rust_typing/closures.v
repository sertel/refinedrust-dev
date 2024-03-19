From refinedrust Require Import typing.
From iris Require Import options.

Section function_subsume.
  Context `{!typeGS Σ}.

  (* If I have f ◁ F1, then f ◁ F2. *)
  (* I can strengthen the precondition and weaken the postcondition *)
  (*elctx_sat*)
  (* TODO: think about how closures capture lifetimes in their environment.
     lifetimes in the capture shouldn't really show up in their spec at trait-level (a purely safety spec).
     I guess once I want to know something about the captured values (to reason about their functional correctness), I might need to know about lifetimes. However, even then, they should not pose any constraints -- they should just be satisfied, with us only knowing that they live at least as long as the closure body.

     The point is that I want to say that as long as the closure lifetime is alive, all is fine.


     How does the justification that this is fine work?
     Do I explicitly integrate some existential abstraction?
      i.e. functions can pose the existence of lifetimes, as long as they are alive under the function lifetime


     I don't think I can always just subtype that to use the lifetime of the closure. That would definitely break ghostcell etc. And also not everything might be covariant in the lifetime.
  *)
  Lemma subsume_function_ptr π v l1 l2 sts1 sts2 lfts {A B : Type} (F1 : prod_vec lft lfts → A → fn_params) (F2 : prod_vec lft lfts → B → fn_params) T : 
    subsume (v ◁ᵥ{π} l1 @ function_ptr sts1 F1) (v ◁ᵥ{π} l2 @ function_ptr sts2 F2) T :-
    and:
    | drop_spatial;
        (* TODO could also just require that the layouts are compatible *)
        exhale ⌜sts1 = sts2⌝;
        ∀ (κs : prod_vec lft lfts),
        (* NOTE: this is more restrictive than necessary *)
        exhale ⌜∀ a b ϝ, (F1 κs a).(fp_elctx) ϝ = (F2 κs b).(fp_elctx) ϝ⌝;
        ∀ (b : B),
        inhale (fp_Pa (F2 κs b) π);
        ls ← iterate: fp_atys (F2 κs b) with [] {{ ty T ls,
               ∀ l : loc,
                inhale (l ◁ₗ[π, Owned false] #(projT2 ty).2 @ ◁ (projT2 ty).1); return T (ls ++ [l]) }};
        ∃ (a : A),
        exhale ⌜length (fp_atys (F1 κs a)) = length (fp_atys (F2 κs b))⌝%I;
        iterate: zip ls (fp_atys (F1 κs a)) {{ e T, exhale (e.1 ◁ₗ[π, Owned false] #(projT2 e.2).2 @ ◁ (projT2 e.2).1); return T }};
        exhale (fp_Pa (F1 κs a) π);
        (* show that F1.ret implies F2.ret *)
        ∀ (vr : val) a2,
        inhale ((F1 κs a).(fp_fr) a2).(fr_R) π;
        inhale (vr ◁ᵥ{π} ((F1 κs a).(fp_fr) a2).(fr_ref) @ ((F1 κs a).(fp_fr) a2).(fr_ty));
        ∃ b2,
        exhale ((F2 κs b).(fp_fr) b2).(fr_R) π;
        exhale (vr ◁ᵥ{π} ((F2 κs b).(fp_fr) b2).(fr_ref) @ ((F2 κs b).(fp_fr) b2).(fr_ty));
        done
    | exhale ⌜l1 = l2⌝; return T. 
  Proof.
    iIntros "(#Ha & (-> & HT))".
    iIntros "Hv". iFrame.
    iDestruct "Ha" as "(-> & Ha)".
    iEval (rewrite /ty_own_val/=) in "Hv".
    iDestruct "Hv" as "(%fn & %local_sts & -> & Hen & %Halg1 & %Halg2 & #Htf)".
    iEval (rewrite /ty_own_val/=). 
    iExists fn, local_sts. iR. iFrame. 
    iSplitR. { done. }
    iR. 
    iNext. 
    
    rewrite /typed_function.
    iIntros (κs b ϝ) "!>".
    iIntros (Hargly Hlocally lsa lsv).
    iIntros "(Hcred & Hargs & Hlocals & Hpre)".
    iSpecialize ("Ha" $! κs).
    iDestruct "Ha" as "(%Helctx & Ha)".
    iSpecialize ("Ha" $! b with "Hpre").
    (*Locate "|".*)
    (*
    Search Z.divide.
    Search aligned_to
    is_aligned_to
    iterate_elim0
    Locate "iterate:".
    iDestruct ("Ha" with "[Hargs]") as "(%a & %Hlen & Hargs & Hpre & Ha)".
     *)


  Admitted.
  Definition subsume_function_ptr_inst := [instance subsume_function_ptr].
  Global Existing Instance subsume_function_ptr_inst  | 10.
  (* TODO: maybe also make this a subsume_full instance *)
End function_subsume.


(*
trait MyAdd {
    type Output;

    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    #[rr::exists("z")]
    #[rr::returns("z")]
    fn my_add(x: Self, y: Self) -> Self::Output;
}

impl MyAdd for usize {
    type Output = usize;

    #[rr::trust_me]
    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    #[rr::returns("x + y")]
    fn my_add(x: usize, y: usize) -> usize {
        x + y
    }
}
 *)

(* this is what monomorphizations of functions taking a generic of this constraint take *)
Record MyAdd_phys := {
  MyAdd_Output_st : syn_type;

  MyAdd_my_add_loc : loc;
  MyAdd_my_add_arg_sts : list syn_type;
}.

Section rr.
Context `{!typeGS Σ}.

Record MyAdd_spec := {
  MyAdd_Output_ty : sigT (λ rt : Type, type rt);
  MyAdd_my_add_spec : sigT (λ lfts, sigT (λ A, prod_vec lft lfts → A → fn_params));
}.

Definition MyAdd_base_spec {Self_rt} (self_ty : type Self_rt) {Output_rt} (Output_ty : type Output_rt) : MyAdd_spec := {|
  MyAdd_Output_ty := existT _ Output_ty;
  MyAdd_my_add_spec :=
    existT _ $ existT _ $ (fn(∀ (()) : 0 | (x, y) : Self_rt * Self_rt, (λ _, []); x @ (self_ty), y @ self_ty ; (λ π, True)) → ∃ z : Output_rt, z @ Output_ty ; (λ π, True))
|}.

Definition MyAdd_has_spec (π : thread_id) (impl: MyAdd_phys) (spec: MyAdd_spec) : iProp Σ :=
  ⌜ty_syn_type (projT2 spec.(MyAdd_Output_ty)) = impl.(MyAdd_Output_st)⌝ ∗
  impl.(MyAdd_my_add_loc) ◁ᵥ{π} impl.(MyAdd_my_add_loc) @ function_ptr impl.(MyAdd_my_add_arg_sts) (projT2 $ projT2 spec.(MyAdd_my_add_spec)) ∗
  True.

End rr.


(* impl for usize *)
Section rr.
Context `{!typeGS Σ}.

Definition type_of_usizeastraits_MyAdd_my_add  :=
  fn(∀ (()) : 0 | (x, y) : (_ * _), (λ ϝ, []); x @ (int USize), y @ (int USize); (λ π : thread_id, True))
    → ∃ _ : unit, x + y @ (int USize); (λ π : thread_id, True).

Definition MyAdd_usize_spec : MyAdd_spec := {|
  MyAdd_Output_ty := existT _ (int usize_t);
  MyAdd_my_add_spec := existT _ (existT _ type_of_usizeastraits_MyAdd_my_add);
|}.

(* Now I need to show: a concrete specification implies the general specification. *)
Lemma MyAdd_usize_spec_implies_general_spec π impl :
  MyAdd_has_spec π impl (MyAdd_usize_spec) -∗
  MyAdd_has_spec π impl (MyAdd_base_spec (int usize_t) (projT2 $ MyAdd_usize_spec.(MyAdd_Output_ty))).
Proof.
  iIntros "(%Houtput & Hmyadd & _)".
  iSplit; first done.
  iSplitL; last done.
  simpl.
  (* TODO use function subtyping *)
Abort.

End rr.

(** Q: How do we automate this? 

  i.e. when we assume a generic thing implementing a trait, we would generally assume that it's implementing the base spec. 
  So we should probably have some lemmas that do a subsumption to the general spec.
    these should just do subtyping on the function specs.

  Note: In general, we should also have the option for a function to assume a stronger spec, i.e. specify the spec it assumes manually. In particular, this will be quite useful for closures: for functional specs we will want to assume some things about how closures behave.
*)




(** Closures *)
Record FnOnce_phys := {
  FnOnce_Output_st : syn_type;
  FnOnce_call_once_loc : loc;
  FnOnce_call_once_arg_sts : list syn_type;
}.
Record Fn_phys := {
  Fn_Output_st : syn_type;
  Fn_call_loc : loc;
  Fn_call_arg_sts : list syn_type;
}.
Record FnMut_phys := {
  FnMut_Output_st : syn_type;
  FnMut_call_mut_loc : loc;
  FnMut_call_mut_arg_sts : list syn_type;
}.

Section rr.
Context `{!typeGS Σ}.

(** FnOnce *)
Record FnOnce_spec := {
  FnOnce_Output_ty : sigT (λ rt : Type, type rt);
  FnOnce_call_once_spec : sigT (λ lfts, sigT (λ A, prod_vec lft lfts → A → fn_params));
}.
Definition FnOnce_base_spec {Self_rt} (self_ty : type Self_rt) {Args_rt} (args_ty : type Args_rt) {Output_rt} (Output_ty : type Output_rt) : FnOnce_spec := {|
  FnOnce_Output_ty := existT _ Output_ty;
  FnOnce_call_once_spec :=
    existT _ $ existT _ $ (fn(∀ (()) : 0 | (x, y) : Self_rt * Args_rt, (λ _, []); x @ (self_ty), y @ args_ty ; (λ π, True)) → ∃ z : Output_rt, z @ Output_ty ; (λ π, True));
|}.
Definition FnOnce_has_spec (π : thread_id) (impl: FnOnce_phys) (spec: FnOnce_spec) : iProp Σ :=
  ⌜ty_syn_type (projT2 spec.(FnOnce_Output_ty)) = impl.(FnOnce_Output_st)⌝ ∗
  impl.(FnOnce_call_once_loc) ◁ᵥ{π} impl.(FnOnce_call_once_loc) @ function_ptr impl.(FnOnce_call_once_arg_sts) (projT2 $ projT2 spec.(FnOnce_call_once_spec)) ∗
  True.

(** Fn *)
Record Fn_spec := {
  Fn_Output_ty : sigT (λ rt : Type, type rt);
  Fn_call_spec : sigT (λ lfts, sigT (λ A, prod_vec lft lfts → A → fn_params));
}.
Definition Fn_base_spec {Self_rt} (self_ty : type Self_rt) {Args_rt} (args_ty : type Args_rt) {Output_rt} (Output_ty : type Output_rt) : Fn_spec := {|
  Fn_Output_ty := existT _ Output_ty;
  Fn_call_spec :=
    existT _ $ existT _ $ (fn(∀ ((), κ) : 1 | (x, y) : Self_rt * Args_rt, (λ _, []); #x @ (shr_ref self_ty κ), y @ args_ty ; (λ π, True)) → ∃ z : Output_rt, z @ Output_ty ; (λ π, True));
|}.
Definition Fn_has_spec (π : thread_id) (impl: Fn_phys) (spec: Fn_spec) : iProp Σ :=
  ⌜ty_syn_type (projT2 spec.(Fn_Output_ty)) = impl.(Fn_Output_st)⌝ ∗
  impl.(Fn_call_loc) ◁ᵥ{π} impl.(Fn_call_loc) @ function_ptr impl.(Fn_call_arg_sts) (projT2 $ projT2 spec.(Fn_call_spec)) ∗
  True.

(** FnMut *)
Record FnMut_spec := {
  FnMut_Output_ty : sigT (λ rt : Type, type rt);
  FnMut_call_mut_spec : sigT (λ lfts, sigT (λ A, prod_vec lft lfts → A → fn_params));
}.
Definition FnMut_base_spec {Self_rt} (self_ty : type Self_rt) {Args_rt} (args_ty : type Args_rt) {Output_rt} (Output_ty : type Output_rt) : FnMut_spec := {|
  FnMut_Output_ty := existT _ Output_ty;
  FnMut_call_mut_spec :=
    existT _ $ existT _ $ (fn(∀ ((), κ) : 1 | (x, y, γ) : Self_rt * Args_rt * gname, (λ _, []); (#x, γ) @ (mut_ref self_ty κ), y @ args_ty ; (λ π, True)) → ∃ (z, x') : Output_rt * Self_rt, z @ Output_ty ; (λ π, gvar_pobs γ x'));
|}.
Definition FnMut_has_spec (π : thread_id) (impl: FnMut_phys) (spec: FnMut_spec) : iProp Σ :=
  ⌜ty_syn_type (projT2 spec.(FnMut_Output_ty)) = impl.(FnMut_Output_st)⌝ ∗
  impl.(FnMut_call_mut_loc) ◁ᵥ{π} impl.(FnMut_call_mut_loc) @ function_ptr impl.(FnMut_call_mut_arg_sts) (projT2 $ projT2 spec.(FnMut_call_mut_spec)) ∗
  True.

End rr.
