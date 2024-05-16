From refinedrust Require Import typing shims.
From iris Require Import options.


(*

trait Foo<T> {
    type Output;
    
    #[rr::params("a", "b")]
    #[rr::args("#a", "b")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn bar<U> (&self, x: U) -> (Self::Output, T, U);
}

impl Foo<u32> for i32 {
    
    type Output = i32;
    
    fn bar<U> (&self, x: U) -> (i32, u32, U) {
        ( *self, 42, x)
    }
}

#[rr::params("w")]
#[rr::args("#w")]
fn foobar<W, T> (x: &W) where W: Foo<T> {
    x.bar(true);
}

fn call_foobar() {
    foobar(&0);
}

*)

Definition type_ty `{!typeGS Σ} := sigT type.



(* Ideas for simplifying: 
   - have a record of specs for a trait, so that it's clearer that stuff is bundled by trait. 
*)

(** trait Foo *)
Section rr.
Context `{!typeGS Σ}.

Record Foo_spec : Type := {
  Foo_bar_spec (U_rt : Type) (U_st : syn_type) : function_ty;
}.

Definition Foo_spec_incl (spec1 spec2 : Foo_spec) : Prop :=
  (* one entry for every method *)
  (∀ U_rt U_st, function_subtype (spec1.(Foo_bar_spec) U_rt U_st) (spec2.(Foo_bar_spec) U_rt U_st)).

(*Definition Foo_bar_spec_ty {U_rt : Type} (U_st : syn_type) :=*)
  (*sigT (λ lfts, sigT (λ A, prod_vec lft lfts → A → fn_params)).*)

Context {Self_rt} (Self_ty : type Self_rt) {T_rt} (T_ty : type T_rt) {Output_rt} (Output_ty : type Output_rt).

Definition Foo_base_spec : Foo_spec := {|
  Foo_bar_spec U_rt U_st := 
    existT _ $ existT _ $ fn(∀ ((), ulft_1) : 1 | (a, b, U_ty) : Self_rt * U_rt * type U_rt, (λ _, [(* ? *) ]); #a @ (shr_ref Self_ty ulft_1), b @ U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (ty_syn_type Output_ty) (ty_syn_type T_ty) (ty_syn_type U_ty)) +[ Output_ty; T_ty; U_ty] ; (λ π, True);
|}.

End rr.

(** impl *)
Definition Foo_i32_u32_bar_U_def (U_st : syn_type) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

  Definition type_of_Foo_i32_u32_bar_U (U_rt : Type) (U_st : syn_type) :=
    (fn(∀ ((), ulft_1) : 1 | (a, b, U_ty) : Z * U_rt * type U_rt, (λ _, [(* ? *) ]); #a @ (shr_ref (int i32) ulft_1), b @ U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (IntSynType i32) (IntSynType u32) (ty_syn_type U_ty)) +[ int i32; int i32; U_ty] ; (λ π, True)).

  Lemma Foo_i32_u32_bar_U_has_type π :
    ∀ (U_rt : Type) (U_st : syn_type),
    ⊢ typed_function π (Foo_i32_u32_bar_U_def U_st) [(* TODO *)] (type_of_Foo_i32_u32_bar_U U_rt U_st).
  Proof.
  Admitted.

  Definition Foo_i32_u32_spec : Foo_spec := {|
    Foo_bar_spec U_rt U_st := existT _ $ existT _ $ type_of_Foo_i32_u32_bar_U U_rt U_st;
  |}.

  Lemma Foo_i32_u32_incl : 
    Foo_spec_incl (Foo_i32_u32_spec) (Foo_base_spec (int i32) (int u32) (int i32)).
  Proof.
  Admitted.
End rr.

(** foobar *)
Definition foobar_def (W_st : syn_type) (T_st : syn_type) (Foo_W_T_Output_st : syn_type) (Foo_W_T_bar_bool_loc : loc) : function.
Proof.

Admitted.

Section rr.
Context `{!typeGS Σ}.

(* what about the arg syntype? 
    Since the semantic types are not fixed, I need to pass them as parameters.
    I know which arguments this takes modulo generics. 
    For generics, I need to substitute both the ones from self/the trait and from the method, then I should be good. 

*)

Definition type_of_foobar 
  (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
  (* we also need to quantify over the associated types here *)
  (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
  (* we quantify over the specification for Foo *)
  (Foo_W_T_spec : Foo_spec) :=
  fn(∀ ((), ulft_1) : 1 | (a, W_ty, T_ty, Foo_W_T_Output_ty) : W_rt * type W_rt * type T_rt * type Foo_W_T_Output_rt, (λ _, [(* ? *) ]); #a @ (shr_ref W_ty ulft_1) ; (λ π, ⌜ty_syn_type W_ty = W_st⌝ ∗ ⌜ty_syn_type T_ty = T_st⌝ ∗ ⌜ty_syn_type Foo_W_T_Output_ty = Foo_W_T_Output_st⌝ ∗ 
      (* we require that the specification we quantified over satisfies the expected specification (Foo_base_spec is the specification we expect here, but this could also be an overridden specification we assume) *)
      ⌜Foo_spec_incl Foo_W_T_spec (Foo_base_spec W_ty T_ty Foo_W_T_Output_ty)⌝
    )) → ∃ y : _, y @ unit_t ; (λ π, True).

Lemma foobar_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (Foo_W_T_spec : Foo_spec)
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_T_bar_bool_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_T_bar_bool_loc ◁ᵥ{π} Foo_W_T_bar_bool_loc @ function_ptr [PtrSynType; BoolSynType] (proj_function_ty $ Foo_W_T_spec.(Foo_bar_spec) bool BoolSynType) -∗
  typed_function π (foobar_def W_st T_st Foo_W_T_Output_st Foo_W_T_bar_bool_loc) [(* TODO *)] (type_of_foobar W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st Foo_W_T_spec). 
Proof.
Admitted.

End rr.


(** call_foobar *)
Definition call_foobar_def (foobar_i32_u32_i32_loc : loc) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

Definition type_of_call_foobar :=
  fn(∀ (()) : 0 | () : (), (λ _, []); (λ π, True)) → ∃ y : _, y @ unit_t ; (λ π, True).


Lemma call_foobar_has_type π :
  ∀ (foobar_i32_u32_i32_loc : loc), 
  foobar_i32_u32_i32_loc ◁ᵥ{π} foobar_i32_u32_i32_loc @ function_ptr [(* TODO *)] (type_of_foobar Z (IntSynType i32) Z (IntSynType u32) Z (IntSynType i32)
    (* we have to provide the spec we have for the trait impl we give it *)
    (Foo_base_spec (int i32) (int u32) (int i32))) -∗
  typed_function π (call_foobar_def foobar_i32_u32_i32_loc) [(* TODO *)] (type_of_call_foobar).
Proof.
Admitted.

End rr.

(* Adequacy (linking all this together) *)

(* 
  1. Allocate location for Foo_i32_u32_bar_bool. By Foo_i32_u32_bar_U_has_type, this is well-typed
  2. Allocate location for foobar instantiated to W = i32, T = u32, Output = i32 and the preceding location. 
    We instantiate foobar_has_type with these + Foo_base_spec instantiated to these types.
    Thus, it has type type_of_foobar ...
  3. Allocate location for call_foobar, using the preceding location.
      Use call_foobar_has_type with the preceding assumption. 
      It's important that the specification here lines up (in step 2 we picked Foo_base_spec to instantiate foobar, which needs to be the specification we actually have proved and assume now)
      Now we have a closed typing proof for call_foobar.
 *)


(* How does this change the design?
    - a trait has: a spec record, a base spec record, and a subsumption definition for the spec record; no more phys record; no more phys_has_spec
    - we introduce associated types similarly to other generics
      + add this to the localtraitscope
    - we assume a spec record for every trait impl
      + add this to the localtraitscope
    - we assume in the spec of a function using a trait that the spec record subsumes the necessary function impl
    - we require an instance of a function as usual when we use it.
      However, this is a bit different, since we project out the spec from the spec record
      
 *)



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

(* if I assume an implementation for a generic:
    - should I explicitly close under subsumed specs? i.e. quantify over a spec?
    - or should I just quantify over the associated types, and require that I have the base_spec (potentially with an override)?
      + I prefer this. 
  
*)

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
