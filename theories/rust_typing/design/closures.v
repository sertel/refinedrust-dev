From refinedrust Require Import typing.
From iris Require Import options.

(** Tuple defs *)
(* Since the frontend doesn't generate them for now, we just provide a few pre-defined ones for reasonable sizes. *)
Definition tuple1_sls (T0_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple1" [("0", T0_st)] StructReprRust.
Definition tuple1_st (T0_st : syn_type) : syn_type := tuple1_sls T0_st.
Definition tuple1_rt (T0_rt : Type) : Type :=
  plist place_rfn [T0_rt].
Definition tuple1_ty `{!refinedrustGS Σ} {T0_rt : Type} (T0_ty : type T0_rt) : type (tuple1_rt _) :=
  struct_t (tuple1_sls (st_of T0_ty)) +[T0_ty].

Definition tuple2_sls (T0_st T1_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple2" [("0", T0_st); ("1", T1_st)] StructReprRust.
Definition tuple2_st (T0_st T1_st : syn_type) : syn_type := tuple2_sls T0_st T1_st.
Definition tuple2_rt (T0_rt : Type) (T1_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt].
Definition tuple2_ty `{!refinedrustGS Σ} {T0_rt T1_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) : type (tuple2_rt _ _) :=
  struct_t (tuple2_sls (st_of T0_ty) (st_of T1_ty)) +[T0_ty; T1_ty].

Definition tuple3_sls (T0_st T1_st T2_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple3" [("0", T0_st); ("1", T1_st); ("2", T2_st)] StructReprRust.
Definition tuple3_st (T0_st T1_st T2_st : syn_type) : syn_type := tuple3_sls T0_st T1_st T2_st.
Definition tuple3_rt (T0_rt : Type) (T1_rt : Type) (T2_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt; T2_rt].
Definition tuple3_ty `{!refinedrustGS Σ} {T0_rt T1_rt T2_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) (T2_ty : type T2_rt) : type (tuple3_rt _ _ _) :=
  struct_t (tuple3_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty)) +[T0_ty; T1_ty; T2_ty].

Definition tuple4_sls (T0_st T1_st T2_st T3_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple4" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st)] StructReprRust.
Definition tuple4_st (T0_st T1_st T2_st T3_st : syn_type) : syn_type := tuple4_sls T0_st T1_st T2_st T3_st.
Definition tuple4_rt (T0_rt : Type) (T1_rt : Type) (T2_rt : Type) (T3_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt; T2_rt; T3_rt].
Definition tuple4_ty `{!refinedrustGS Σ} {T0_rt T1_rt T2_rt T3_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) (T2_ty : type T2_rt) (T3_ty : type T3_rt) : type (tuple4_rt _ _ _ _) :=
  struct_t (tuple4_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty) (st_of T3_ty)) +[T0_ty; T1_ty; T2_ty; T3_ty].

Definition tuple5_sls (T0_st T1_st T2_st T3_st T4_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple5" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st); ("4", T4_st)] StructReprRust.
Definition tuple5_st (T0_st T1_st T2_st T3_st T4_st : syn_type) : syn_type := tuple5_sls T0_st T1_st T2_st T3_st T4_st.
Definition tuple5_rt (T0_rt : Type) (T1_rt : Type) (T2_rt : Type) (T3_rt : Type) (T4_rt : Type) : Type :=
  plist place_rfn [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt].
Definition tuple5_ty `{!refinedrustGS Σ} {T0_rt T1_rt T2_rt T3_rt T4_rt : Type} (T0_ty : type T0_rt) (T1_ty : type T1_rt) (T2_ty : type T2_rt) (T3_ty : type T3_rt) (T4_ty : type T4_rt) : type (tuple5_rt _ _ _ _ _) :=
  struct_t (tuple5_sls (st_of T0_ty) (st_of T1_ty) (st_of T2_ty) (st_of T3_ty) (st_of T4_ty)) +[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty].

Definition spec_instantiated `{!typeGS Σ} {SPEC : Type} (F : prod_vec lft 0 → plist type [] → SPEC) : SPEC :=
  F -[] -[]. 

Definition spec_as `{!typeGS Σ} {SPEC : Type} {lfts : nat} (rts : list Type) (F : prod_vec lft lfts → plist type rts → SPEC) : 
  prod_vec lft lfts → plist type rts → SPEC :=
  F.
Notation "x '<TY>' T" := (spec_instantiate_typaram_fst _ _ T x) (left associativity, at level 81) : stdpp_scope.
Notation "x '<LFT>' T" := (spec_instantiate_lft_fst _ T x) (left associativity, at level 81) : stdpp_scope.
(*Notation "x '<LFT>@{' R '}' T" := (spec_instantiate_lft_fst R T x) (left associativity, at level 81) : stdpp_scope.*)
(*Notation "x '<TY>@{' R '}' T" := (spec_instantiate_typaram_fst _ R T x) (left associativity, at level 81) : stdpp_scope.*)
Notation "x '<INST!>'" := (spec_instantiated x) (left associativity, at level 81) : stdpp_scope.

Notation "x '<MERGE!>@{' R '}'" := (spec_collapse_params _ R x) (left associativity, at level 181) : stdpp_scope.

Notation "x '<TY>' T" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rt → _ => 
        let rts := eval simpl in rt in
        match rts with
        | (?rt :: ?rts) =>
          refine (spec_instantiate_typaram_fst rt rts T x)
        end
    end))
     (left associativity, at level 81, only parsing) : stdpp_scope.
Notation "x '<LFT>' T" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rts → _ => 
        refine (spec_instantiate_lft_fst rts T x)
    end))
     (left associativity, at level 81, only parsing) : stdpp_scope.
Notation "x '<MERGE!>'" := (
  ltac:(
    match type of x%function with
    | prod_vec _ _ → plist type ?rts1 → prod_vec _ _ → plist type ?rts2 → _ => 
        refine (spec_collapse_params rts1 rts2 x)
    end))
     (left associativity, at level 181, only parsing) : stdpp_scope.

(** We should always simpl this, otherwise our definitions won't typecheck *)
Arguments unpack_function_ty {_ _} _ /.
Notation "<SIMPL> x" := (ltac:(let __x := eval simpl in (x) in refine __x)) (right associativity, at level 180, only parsing).
(*Notation unpack_function_ty x := (<SIMPL> (functions.unpack_function_ty (x))) (only parsing, at level 40).*)



(*



impl<'a, T> Foo<&'a mut T> for u32 {
    type Output = i32;

    fn bar<U>(&self, x : U) -> (Self::Output, &'a mut T, U) {
        unimplemented!();
    }
}


*)

Definition type_ty `{!typeGS Σ} := sigT type.

Notation "'spec!' κs ':' n '|' tys ':' rts ',' S" :=
  ((fun κs tys => S) : prod_vec lft n → plist type rts → _) (at level 99, S at level 180, κs pattern, tys pattern) : stdpp_scope.

(** trait Foo *)
(* 
trait Foo<T> {
    type Output;

    #[rr::params("a", "b")]
    #[rr::args("#a", "b")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn bar<U> (&self, x: U) -> (Self::Output, T, U);
}
 *)
Section rr.
Context `{!typeGS Σ}.

Record Foo_spec : Type := {
  Foo_bar_spec (U_rt : Type) (U_st : syn_type) : function_ty;
}.


(* if I have an instance of spec1, I should also get an instance of spec2 *)

(* Specification inclusion works on fully instantiated specs. *)
Definition Foo_spec_incl (spec1 spec2 : Foo_spec) : Prop :=
  (* one entry for every method *)
  (∀ U_rt U_st, function_subtype (spec1.(Foo_bar_spec) U_rt U_st) (spec2.(Foo_bar_spec) U_rt U_st)).

(* Can I push down the outer quantifiers? No, because the same existentials shoudl work for all the functions. *)
Definition Foo_spec_incl_lifted (spec1 spec2 : packed_spec Foo_spec) : Prop :=
  ∀ κs1 tys1, ∃ κs2 tys2, Foo_spec_incl (unpack_spec spec1 κs1 tys1) (unpack_spec spec2 κs2 tys2).

(* For the base spec, we introduce the refinement types *)
Context (Self_rt : Type) (T_rt : Type) (Output_rt : Type).


Definition Foo_base_spec :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty; Output_ty]) : [Self_rt; T_rt; Output_rt],
  {|
    Foo_bar_spec U_rt U_st :=
    pack_function_ty [U_rt] $ fn(∀ ( *[ulft_1] ) : 1 | ( *[U_ty]) : [(U_rt, U_st)] | (a, b) : Self_rt * U_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref Self_ty ulft_1), b :@: U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (ty_syn_type Output_ty) (ty_syn_type T_ty) (ty_syn_type U_ty)) +[ Output_ty; T_ty; U_ty] ; (λ π, True);
  |}.

(* NOTE: for exists components this doesn't really work. Because we need to know that the other thigns are independent of the generics. I guess it's okay if it depends on the typarams (we might even need this for some specs).
But lifetime parameters are not nice. 

Are there cases where the exists components can legitimately depend on lifetime generics? 
I guess this is not really compatible with how we deal with lifetimes/how we need to be able to instantiate lifetimes.
 *)

(* Consider again: maybe we should push down lifetime parameters directly. 
  - base specs should directly push down lifetime parameters.
  - more specific specs also directly push down their lifetime parameters. If I use a component of the base spec, I need to introduce sufficient quantifiers.
*)

(* 
  How are extra components (rr::exists) handled for base specs?
   - We cannot add them to the record, because we don't have an instantiation for the abstract base spec.
   - Maybe we should have two records, one only for instances and one for the base spec?
     (function specs are nested below)

   Instance function specs need to be able to refer to the exists though.
   Even the base spec needs to be able to refer to the things. 

  Conclusion: We put them as a parameter of the base spec.
 *)

Context (U_rt : Type) (U_st : syn_type).
Definition Foo_push_down (lfts : nat) (rts : list Type) (F : prod_vec lft lfts → plist type rts → Foo_spec)
  (*: *)
  (*prod_vec lft 0 → plist type rts → Foo_spec :=*)
  :=
  λ (_ : prod_vec lft 0) tys,
  (*{|*)
    (*Foo_bar_spec U_rt U_st :=*)
       (*pack_function_ty _ $ *)
       (
        (* quantify over all the lifetimes of the trait *)
        (<SIMPL>(λ (κs : prod_vec lft lfts) (_ : plist type []),
        (* get the base spec by lifting it from under the quantifiers *)
        unpack_function_ty ((F κs tys).(Foo_bar_spec) U_rt U_st) )
        (* finally, we merge with the lifetime quantifiers of the trait *)
        ) )
 
        (*;*)
  (*|}.*)
        .

(* NOTE : This definition does not work. *)




End rr.

(** impl for Self=i32 T=u32 Output=i32 *)
(* 
impl Foo<u32> for i32 {

    type Output = i32;

    fn bar<U> (&self, x: U) -> (i32, u32, U) {
        ( *self, 42, x)
    }
}
 *)
Definition Foo_i32_u32_bar_U_def (U_st : syn_type) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

  Definition type_of_Foo_i32_u32_bar_U (U_rt : Type) (U_st : syn_type) :=
    (fn(∀ ( *[ulft_1]) : 1 | ( *[U_ty]) : [(U_rt, U_st)] | (a, b) : Z * U_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref (int i32) ulft_1), b :@: U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (IntSynType i32) (IntSynType u32) (ty_syn_type U_ty)) +[ int i32; int i32; U_ty] ; (λ π, True)).

  Lemma Foo_i32_u32_bar_U_has_type π :
    ∀ (U_rt : Type) (U_st : syn_type),
    ⊢ typed_function π [U_rt] (Foo_i32_u32_bar_U_def U_st) [(* TODO *)] (type_of_Foo_i32_u32_bar_U U_rt U_st).
  Proof.
  Admitted.

  Definition Foo_i32_u32_spec : Foo_spec := 
  {|
    Foo_bar_spec U_rt U_st := pack_function_ty [_] $ type_of_Foo_i32_u32_bar_U U_rt U_st;
  |}.

  Definition specialized_base_spec :=
    spec! ( *[]) : 0 | ( *[]) : [],
    Foo_base_spec Z Z Z <TY> int i32 <TY> int u32 <TY> int i32 <MERGE!> <INST!>.
  
  Lemma Foo_i32_u32_incl :
    Foo_spec_incl (Foo_i32_u32_spec) (specialized_base_spec).
  Proof.
  Admitted.
End rr.

(** foobar *)
(* 
#[rr::params("w")]
#[rr::args("#w")]
fn foobar<W, T> (x: &W) where W: Foo<T> {
    x.bar(true);
}
 *)
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

  fn(∀ ( *[ulft_1]) : 1 | ( *[W_ty; T_ty; Foo_W_T_Output_ty]) : [(W_rt, W_st); (T_rt, T_st); (Foo_W_T_Output_rt, Foo_W_T_Output_st)] | (a) : W_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref W_ty ulft_1) ; (λ π,
      (* we require that the specification we quantified over satisfies the expected specification (Foo_base_spec is the specification we expect here, but this could also be an overridden specification we assume) *)
      ⌜Foo_spec_incl Foo_W_T_spec ((Foo_base_spec W_rt T_rt Foo_W_T_Output_rt <TY> W_ty <TY> T_ty <TY> Foo_W_T_Output_ty <INST!>))⌝
    )) → ∃ y : _, y @ unit_t ; (λ π, True).

(* In the proof of this function, I should assume that generics are alredy instantiated. 
  e.g. a type variable T might actually be a reference. 

  But in the linking theorem, when I apply this lemma, I don't know the lifetime yet.
   I later on need to be able to instantiate this lemma for various lifetimes. 
   
  Maybe I should provide a specification which is abstracted to this functions's generics? 
   PROBLEM: I can't fully abstract, because the instance relies on these parameters having a particular shape.
   i.e. I can't establish the appearance that it works for all instantiations of this function.
   Rather, for different instantiations of the function, I have to pick a different trait instance, with a different spec.


   Should I do the part where I pass the specs in the precond, after all? 
   No. Then I leak which generics of the function it instantiates with.

  
   If I push this down here in the function assumption, I cannot use the spec_incl assumption anymore (cause the instantiation isn't in scope).

   Adding these parameters to the spec in the assumption also does NOT make any sense.

   The problem is: I'm assuming a single specification, and afterwards I'm getting arbitrary semantic types this specification needs to work for.
    But for different types I actually have a differnet specification.
   In practice this is not really a problem, as type variables lead to different monomorphizations, and lifetimes do not distinguish instances.



  What if I partially monomorphize a type of a function when assuming it as part of another function?
   i.e. I instantiate a generic function with a reference type.
   Currently, I'm saying that it works for all types with a particular syntype.
   But maybe I should also partially monomorphize the semantic type? 
    
    
   
*)

Lemma foobar_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (Foo_W_T_spec : Foo_spec)
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_T_bar_bool_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_T_bar_bool_loc ◁ᵥ{π} Foo_W_T_bar_bool_loc @ function_ptr [PtrSynType; BoolSynType] _ (
    unpack_function_ty $ Foo_W_T_spec.(Foo_bar_spec) bool BoolSynType) -∗
  typed_function π [_; _; _] (foobar_def W_st T_st Foo_W_T_Output_st Foo_W_T_bar_bool_loc) [(* TODO *)] (type_of_foobar W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st Foo_W_T_spec).
Proof.
Admitted.
End rr.

(** call_foobar *)
(*
fn call_foobar() {
    foobar(&0);
}
*)
Definition call_foobar_def (foobar_i32_u32_i32_loc : loc) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

Definition type_of_call_foobar :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : (), (λ _, []); (λ π, True)) → ∃ y : _, y @ unit_t ; (λ π, True).


Lemma call_foobar_has_type π :
  ∀ (foobar_i32_u32_i32_loc : loc),
  foobar_i32_u32_i32_loc ◁ᵥ{π} foobar_i32_u32_i32_loc @ function_ptr [(* TODO *)] [_; _; _] (type_of_foobar Z (IntSynType i32) Z (IntSynType u32) Z (IntSynType i32)
    (* we have to provide the spec we have for the trait impl we give it *)
    (* NOTE: I give it a fully instantiated spec here *) 
    (Foo_base_spec Z Z Z <TY> (int i32) <TY> (int u32) <TY> (int i32) <INST!>)) -∗
  typed_function π [] (call_foobar_def foobar_i32_u32_i32_loc) [(* TODO *)] (type_of_call_foobar).
Proof.
Admitted.

End rr.


(*
impl<'a, T> Foo<&'a mut T> for u32
{
    type Output = i32;

    fn bar<U>(&self, x : U) -> (Self::Output, &'a mut T, U) {
        unimplemented!();
    }
}
 *)
Definition Foo_u32_mut_ref_T_bar_U_def (T_st : syn_type) (U_st : syn_type) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

  (*
  Definition type_of_Foo_i32_u32_bar_U (U_rt : Type) (U_st : syn_type) :=
    (fn(∀ ( *[ulft_1]) : 1 | ( *[U_ty]) : [(U_rt, U_st)] | (a, b) : Z * U_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref (int i32) ulft_1), b :@: U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (IntSynType i32) (IntSynType u32) (ty_syn_type U_ty)) +[ int i32; int i32; U_ty] ; (λ π, True)).

  Lemma Foo_i32_u32_bar_U_has_type π :
    ∀ (U_rt : Type) (U_st : syn_type),
    ⊢ typed_function π [U_rt] (Foo_i32_u32_bar_U_def U_st) [(* TODO *)] (type_of_Foo_i32_u32_bar_U U_rt U_st).
  Proof.
  Admitted.

  Definition Foo_i32_u32_spec : Foo_spec := {|
    Foo_bar_spec U_rt U_st := pack_function_ty [_] $ type_of_Foo_i32_u32_bar_U U_rt U_st;
  |}.
  *)

  (*Definition specialized_base_spec_ref (T_rt : Type) :=*)
    (*spec! ( *[ ulft_a]) : 1 | ( *[ T_ty]) : [ T_rt ],*)
      (*(Foo_base_spec Z (place_rfn T_rt * gname) Z) <TY> int u32 <TY> mut_ref T_ty ulft_a <TY> int i32 <MERGE!>.*)

  (*Definition bla T_rt U_rt U_st := *)
    (*spec! ( *[ ulft_a]) : 1 | ( *[ T_ty]) : [ T_rt ],*)
      (*<SIMPL> unpack_function_ty ((specialized_base_spec_ref T_rt <LFT> ulft_a <TY> T_ty <INST!>).(Foo_bar_spec) U_rt U_st) <MERGE!>*)
      (*.*)

  Definition Foo_u32_mut_ref_T_spec (T_rt : Type) := 
    (* quantify over all the type variables of the instance *)
    spec! ( *[ ]) : 0 | ( *[ T_ty]) : [ T_rt ],
    {|
      Foo_bar_spec U_rt U_st := pack_function_ty [_] $ 
        (* quantify over all the lifetimes of the instance *)
        spec! ( *[ ulft_a]) : 1 | ( *[]) : [],
        (* get the base spec by lifting it from under the quantifiers *)
        <SIMPL> unpack_function_ty (
          (* base spec applied to all the parameters *)
          (Foo_base_spec Z (place_rfn T_rt * gname) Z <TY> int u32 <TY> mut_ref T_ty ulft_a <TY> int i32 <INST!>)
          (* project out the spec for this function *)
          .(Foo_bar_spec) U_rt U_st) 
        (* if there were lifetime parameters of the trait, we'd instantiate them here *)
        (* <LFT> ... *)

        (* finally, we merge with the lifetime quantifiers of the trait *)
        <MERGE!>
    |}.

  (* How do I prove it has this spec when there are no annotations? *)
  
  (* Problem: how do I formulate the base spec it should have?
      for this, I'd need to introduce new lifetime parameters at the function level *)
  (* Solution: maybe we should universally quantify the lifetimes of the RHS here.
     i.e. I show that for an instantiation at the top-level with known but arbitrary types, I can make the subsumption work... *)
  Lemma Foo__incl T_rt (T_ty : type T_rt) ulft_a :
    Foo_spec_incl
      (Foo_u32_mut_ref_T_spec T_rt <TY> T_ty <INST!>)
      (Foo_base_spec Z (place_rfn T_rt * gname) Z <TY> int u32 <TY> mut_ref T_ty ulft_a <TY> int i32 <INST!>).
  Proof.
  Admitted.
End rr.



(*
#[rr::params("w")]
#[rr::args("w")]
fn foobar_ref<'a, W>(x: W) where W: Foo<&'a mut i32> {
    x.bar(32); 
}
*)
Definition foobar_ref_def (W_st : syn_type) (Foo_W_mut_ref_i32_Output_st : syn_type) (Foo_W_mut_ref_i32_bar_i32_loc : loc) : function.
Proof.
Admitted.

Section rr.
Context `{!typeGS Σ}.

Definition type_of_foobar_ref
  (W_rt : Type) (W_st : syn_type)
  (* we also need to quantify over the associated types here *)
  (Foo_W_mut_ref_i32_Output_rt : Type) (Foo_W_mut_ref_i32_Output_st : syn_type)

  (* we quantify over the specification for Foo *)
  (Foo_W_mut_ref_i32_spec : Foo_spec) :=

  fn(∀ ( *[ulft_a]) : 1 | ( *[W_ty; Foo_W_mut_ref_i32_Output_ty]) : [(W_rt, W_st); (Foo_W_mut_ref_i32_Output_rt, Foo_W_mut_ref_i32_Output_st)] | (a) : W_rt, (λ _, [(* ? *) ]); a :@: W_ty ; (λ π,
      (* require that it satisfies the spec we need *)
      (* Crucial: here we can exactly specify the lifetime instantiation we need the spec to work for. *)
      ⌜Foo_spec_incl Foo_W_mut_ref_i32_spec (Foo_base_spec W_rt (place_rfn Z * gname) Foo_W_mut_ref_i32_Output_rt <TY> W_ty <TY> mut_ref (int i32) ulft_a <TY> Foo_W_mut_ref_i32_Output_ty <INST!>)⌝
    )) → ∃ y : _, y @ unit_t ; (λ π, True).

Lemma foobar_ref_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_mut_ref_i32_Output_rt : Type) (Foo_W_mut_ref_i32_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (Foo_W_mut_ref_i32_spec : Foo_spec)
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_mut_ref_i32_bar_i32_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_mut_ref_i32_bar_i32_loc ◁ᵥ{π} Foo_W_mut_ref_i32_bar_i32_loc @ function_ptr [PtrSynType; IntSynType i32] _ (unpack_function_ty $ Foo_W_mut_ref_i32_spec.(Foo_bar_spec) Z (IntSynType i32)) -∗
  typed_function π [_; _] (foobar_ref_def W_st Foo_W_mut_ref_i32_Output_st Foo_W_mut_ref_i32_bar_i32_loc) [(* TODO *)] (type_of_foobar_ref W_rt W_st Foo_W_mut_ref_i32_Output_rt Foo_W_mut_ref_i32_Output_st Foo_W_mut_ref_i32_spec).
Proof.
Admitted.
End rr.

(*
#[rr::verify]
fn call_foobar_ref<'a>(x: &'a u32) {
    foobar_ref::<'a, u32>( *x);
}
*)

Definition call_foobar_ref_def (foobar_ref_u32_loc : loc) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

Definition type_of_call_foobar_ref :=
  fn(∀ ( *[ulft_a]) : 1 | ( *[]) : [] | (x) : (_), (λ _, []); #x :@: shr_ref (int u32) ulft_a; (λ π, True)) → ∃ y : _, y @ unit_t ; (λ π, True).


(* I instantiate the spec here. How do I push the lifetime parameter down? *)
Lemma call_foobar_ref_has_type π :
  ∀ (foobar_ref_u32_loc : loc),
  foobar_ref_u32_loc ◁ᵥ{π} foobar_ref_u32_loc @ function_ptr [(* TODO *)] [_; _] (type_of_foobar_ref Z (IntSynType u32) Z (IntSynType i32)
    (* NOTE: For this to work, it is important that we push down the lifetime parameters *)
    (* In a sense, foobar_ref assumes that the trait instance function is still polymorphic in the lifetime and then subsumes to the instantiated version via spec_incl *)
    (Foo_u32_mut_ref_T_spec Z <TY> (int i32) <INST!>)) -∗
  typed_function π [] (call_foobar_def foobar_ref_u32_loc) [(* TODO *)] (type_of_call_foobar).
Proof.
Admitted.

(* Options for instances with lifetime parameters:
   - we directly push the lifetime parameters down to the individual functions in the definition.
      i.e. avoid having lifetime parameters in non-function objects.
      I don't think this works, as we might have to specialize these.
   - we push it down when using the spec, i.e. in the lemma above.
   - 
 *)

End rr.

(*
  #[rr::params("w")]
  #[rr::args("#w")]
  fn foobar_ref2<W, T>(x: W, a: T) where W: Foo<T> {
      x.bar(32); 
  }
 *)
Definition foobar_ref2_def (W_st T_st : syn_type) (Foo_W_T_Output_st : syn_type) (Foo_W_T_bar_i32_loc : loc) : function.
Proof.
Admitted.

Section rr.
Context `{!typeGS Σ}.

Definition type_of_foobar_ref2
  (W_rt : Type) (W_st : syn_type)
  (T_rt : Type) (T_st : syn_type)
  (* we also need to quantify over the associated types here *)
  (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
  (* we quantify over the specification for Foo *)
  (Foo_W_T_spec : Foo_spec) :=

  fn(∀ ( *[]) : 0 | ( *[W_ty; T_ty; Foo_W_T_Output_ty]) : [(W_rt, W_st); (T_rt, T_st); (Foo_W_T_Output_rt, Foo_W_T_Output_st)] | (a, b) : W_rt * T_rt, (λ _, [(* ? *) ]); a :@: W_ty, b :@: T_ty ; (λ π,
      (* require that it satisfies the spec we need *)
      ⌜Foo_spec_incl Foo_W_T_spec (Foo_base_spec W_rt T_rt Foo_W_T_Output_rt <TY> W_ty <TY> T_ty <TY> Foo_W_T_Output_ty <INST!>)⌝
    )) → ∃ y : _, y @ unit_t ; (λ π, True).

Lemma foobar_ref2_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (Foo_W_T_spec : Foo_spec)
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_T_bar_i32_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_T_bar_i32_loc ◁ᵥ{π} Foo_W_T_bar_i32_loc @ function_ptr [PtrSynType; IntSynType i32] _ (unpack_function_ty $ Foo_W_T_spec.(Foo_bar_spec) Z (IntSynType i32)) -∗
  typed_function π [_; _; _] (foobar_ref2_def W_st T_st Foo_W_T_Output_st Foo_W_T_bar_i32_loc) [(* TODO *)] (type_of_foobar_ref2 W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st Foo_W_T_spec).
Proof.
Admitted.
End rr.

(*
  // Here, I do not know which lifetime to instantiate the instance with statically.
  // Still, I can monomorphize it up to lifetimes (which are irrelevant for monomorphization).
  fn call_foobar_ref2() {
      let mut x = 43;
      foobar_ref2::<u32, &'_ mut i32>(43, &mut x);
  }
 *)

(* TODO *)
Definition call_foobar_ref2_def (foobar_ref2_u32_mut_ref_i32_loc : loc) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

Definition type_of_call_foobar_ref2 :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : (), (λ _, []); (λ π, True)) → ∃ y : _, y @ unit_t ; (λ π, True).


Lemma call_foobar_ref2_has_type π :
  ∀ (foobar_ref2_u32_mut_ref_i32_loc : loc),
  foobar_ref2_u32_mut_ref_i32_loc ◁ᵥ{π} foobar_ref2_u32_mut_ref_i32_loc @ function_ptr [(* TODO *)] [_; _; _] (type_of_foobar_ref2 Z (IntSynType u32) (place_rfn Z * gname) PtrSynType Z (IntSynType i32)
    (* NOTE we might also have cases where we need to quantify over new lifetimes here.
        i.e. I have an instance and monomorphize it to a reference type.
       Here, this works because there's an instance for mutable references. 
       See Note below. *)
    (Foo_u32_mut_ref_T_spec Z <TY> (int i32) <INST!>)) -∗
  typed_function π [] (call_foobar_def foobar_ref2_u32_mut_ref_i32_loc) [(* TODO *)] (type_of_call_foobar).
Proof.
Admitted.
End rr.
(* NOTE Problem: What if we have to monomorphize an instance to a reference type? 

   We cannot define an operation for pushing down lifetime parameters to a spec in a generic way.
   We can only do this for concrete things we are specializing.
    see the def of Foo_push_down above: we cannot be sure that the dependence on the parameters doesn't leak down. 


   One solution: for each use of an instance, we could generate a new record for that instantiation.
   
   Then we need to know that  it is actually a subspec of the original instance spec.
   i.e. from the instance spec, we can get the function spec. 
    spec_incl f1 f2 means that if I satisfy f1, I can use it as f2
    I prove the instance against the instance_spec.
    I want to use it at the specialized_instance_spec
    So I have to prove spec_incl instance_spec specialized_instance_spec.
   Problem: If I have quantification pushed down in the specialized_instance_spec, I can't do this proof.
   (We are doing things in the reverse direction compared to the base spec proof)
   If I needed the base spec instantiated to something with more lifetime parameters, the instance inclusion proof also wouldnt' work, because we quantify things at the toplevel.
    
   i.e., Problem: for even stating that, we face the same problem; i.e. we have a problem with the order of quantifiers.
    We cannot pick one instantiation of the type parameters that works for all the functions, because they might use different lifetime parameters.
   TODO: think about this more. This indicates that how we quantify isn't right yet.
      "Pushing down" quantifiers to the function level should be easier.
    I guess logically we should maek this instantiation at the call time, and then it's fixed.
      We're kinda doing that, but with a weird quirk.
      Maybe what the function spec is parameterized over should get some lifetime parameters.
        but then we can't project the spec directly. Maybe projection should push down the quantifier. 
          But no! at that point in the function, it should already be resolved. We should not push this quantifier inside the function.
      => No.
     
    

   Maybe this isn't sound evne.
*)

(* What if I handled traits without being generic over their spec? *)
(* Then I would push generics down. But for a particular instance that another function assumes, I think I'd still need to partially instantiate etc. 
   I think the problem is a bit because this is kinda higher-order, being generic over other trait instances.

  The other case where we encounter similar things are closures with lifetime generics, for<'a> ... 
   Difference: There, the receiver site is generic. Here, most of the complication arises at the caller site.

  One fundamental thing that complicates this here also: at the place where I assume a trait instance, I don't know how the concretely picked instance has been monomorphized to get there.
    At the specification level, we are essentially handling dynamic dispatch things.

  I think in our case, we should always collapse excess lifetime parameters.
    We could also instantiate the lifetime parameters at the call site. 
    I guess that's what we're effectively doing by proving the spec_incl sidecondition. In that proof, we need to instantiate the lifetime parameters.

  Receiver site protocol:
   - we get a fully instantiated spec. We can rely on type parameters having been fully instantiated, and for lifetime parameters instantiation can happen dynamically.


 *)


(* Steps to implementation:

1. Change generation and instantiation of the base spec
2. Change order in which we process trait instances in order to allo wto use the default spec.
3. Generate more specific instances
4. Change export of specs in rrlib files.
5. Generate proofs for subsumption. Can we leverage these proofs also for sideconditions? 

6. Add support for declaring rr::exists components for spec records
7. Add support for rr::instantiate

 *)
