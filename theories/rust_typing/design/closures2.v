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

(* *)
Record Foo_spec_params : Type := {
  Foo_bar_spec_params (U_rt : Type) : Type;
}.

Record Foo_spec {P : Foo_spec_params} : Type := {
  Foo_bar_spec (U_rt : Type) (U_st : syn_type) : 
    spec_with 1 [U_rt] (P.(Foo_bar_spec_params) U_rt → fn_params);
}.
Global Arguments Foo_spec : clear implicits.


(* if I have an instance of spec1, I should also get an instance of spec2 *)

(* Specification inclusion works on fully instantiated specs. *)
Definition Foo_spec_incl {P1 P2} (spec1 : Foo_spec P1) (spec2 : Foo_spec P2) : Prop :=
  (* one entry for every method *)
  (∀ U_rt U_st, function_subtype (spec1.(Foo_bar_spec) U_rt U_st) (spec2.(Foo_bar_spec) U_rt U_st)).

(* For the base spec, we introduce the refinement types *)
Context (Self_rt : Type) (Self_st : syn_type) (T_rt : Type) (T_st : syn_type) (Output_rt : Type) (Output_st : syn_type).

(* We also introduce the trait's type variables here. *)
Definition Foo_bar_base_spec U_rt U_st :=
  (fn(∀ ( *[ulft_1] ) : 1 | ( *[Self_ty; T_ty; Output_ty; U_ty]) : [(Self_rt, Self_st); (T_rt, T_st); (Output_rt, Output_st); (U_rt, U_st)] | (a, b) : Self_rt * U_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref Self_ty ulft_1), b :@: U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (ty_syn_type Output_ty) (ty_syn_type T_ty) (ty_syn_type U_ty)) +[ Output_ty; T_ty; U_ty] ; (λ π, True)).

(* Now we can infer the parameter signature *)
Definition Foo_base_spec_params := {|
  Foo_bar_spec_params U_rt := <get_params_of> Foo_bar_base_spec U_rt;
|}.
Definition Foo_base_spec :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty; Output_ty]) : [Self_rt; T_rt; Output_rt],
  {|
    Foo_bar_spec U_rt U_st := Foo_bar_base_spec U_rt U_st <TY> Self_ty <TY> T_ty <TY> Output_ty
     : (spec_with 1 [U_rt] (_ Foo_base_spec_params _ → _));
  |}.
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

  (* Type of a function of an instance. This has all the type parameters of the instance *)
  Definition type_of_Foo_i32_u32_bar_U (U_rt : Type) (U_st : syn_type) :=
    (fn(∀ ( *[ulft_1]) : 1 | ( *[U_ty]) : [(U_rt, U_st)] | (a, b) : Z * U_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref (int i32) ulft_1), b :@: U_ty ; (λ π, True)) → ∃ y : _, y @ struct_t (tuple3_sls (IntSynType i32) (IntSynType u32) (ty_syn_type U_ty)) +[ int i32; int i32; U_ty] ; (λ π, True)).

  Lemma Foo_i32_u32_bar_U_has_type π :
    ∀ (U_rt : Type) (U_st : syn_type),
    ⊢ typed_function π (Foo_i32_u32_bar_U_def U_st) [(* TODO *)] (<tag_type> type_of_Foo_i32_u32_bar_U U_rt U_st).
  Proof.
  Admitted.

  Definition Foo_i32_u32_spec_params : Foo_spec_params :=
  {|
    Foo_bar_spec_params U_rt := <get_params_of> type_of_Foo_i32_u32_bar_U U_rt;
  |}.
  Definition Foo_i32_u32_spec : spec_with _ _ _ :=
    (* Introduce type parameters of the instance *)
    spec! ( *[]) : 0 | ( *[]) : [],
    {|
      Foo_bar_spec U_rt U_st := (type_of_Foo_i32_u32_bar_U U_rt U_st)
        : spec_with 1 [U_rt] (Foo_i32_u32_spec_params.(Foo_bar_spec_params) U_rt → _);
    |}.

  (* The lemma quantifies over all instance parameters and then instantiates *)
  Lemma Foo_i32_u32_incl :
    Foo_spec_incl
      (* Insantiate with the instance's parameters *)
      (Foo_i32_u32_spec <INST!>)
      (* Instantiate with the trait's parameters *)
      (Foo_base_spec Z (IntSynType i32) Z (IntSynType u32) Z (IntSynType i32) <TY> int i32 <TY> int u32 <TY> int i32 <INST!>).
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

Definition type_of_foobar
  (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
  (* we also need to quantify over the associated types here *)
  (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
  {Foo_W_T_spec_params : Foo_spec_params}

  (* we quantify over the specification for Foo *)
  (* The specification is parametric in the lifetimes occurring in the type signature, but never parametric in any lifetimes *)
  (Foo_W_T_spec : Foo_spec Foo_W_T_spec_params) :=

  fn(∀ ( *[ulft_1]) : 1 | ( *[W_ty; T_ty; Foo_W_T_Output_ty]) : [(W_rt, W_st); (T_rt, T_st); (Foo_W_T_Output_rt, Foo_W_T_Output_st)] | (a) : W_rt, (λ _, [(* ? *) ]); #a :@: (shr_ref W_ty ulft_1) ; (λ π,
      (* we require that the specification we quantified over satisfies the expected specification (Foo_base_spec is the specification we expect here, but this could also be an overridden specification we assume) *)
      ⌜Foo_spec_incl Foo_W_T_spec ((Foo_base_spec W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st <TY> W_ty <TY> T_ty <TY> Foo_W_T_Output_ty <INST!>))⌝
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

   For this, we need to have a well-defined contract of which type parameters a particular function is supposed to have.
    This does not working when we are pushing lifetime parameters of instances, because these are not formal parameters of the function.

   So does this approach also solve that?
    i.e. I have an instance (of a trait) which is parametric in a lifetime.
    Now I use this instance. On calling, it should be instantiated with a particular lifetime.
    The callee might expect the instance to be parametric in some things, so let's make it parametric.
    But then when we project the function types we get issues.
    Point: at this point the generics should already have been determined.

*)

Lemma foobar_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (Foo_W_T_spec_params : Foo_spec_params)
    (Foo_W_T_spec : Foo_spec Foo_W_T_spec_params)
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_T_bar_bool_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_T_bar_bool_loc ◁ᵥ{π} Foo_W_T_bar_bool_loc @ function_ptr [PtrSynType; BoolSynType] (<tag_type>
    spec! ( *[]) : 0 | ( *[]) : [],
    (* I want to  instantiate this with Bool. *)
    (Foo_W_T_spec.(Foo_bar_spec) bool BoolSynType <TY> bool_t) <MERGE!>) -∗
  typed_function π (foobar_def W_st T_st Foo_W_T_Output_st Foo_W_T_bar_bool_loc) [(* TODO *)] (<tag_type> type_of_foobar W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st Foo_W_T_spec).
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
  foobar_i32_u32_i32_loc ◁ᵥ{π} foobar_i32_u32_i32_loc @ function_ptr [(* TODO *)] (<tag_type>
    spec! ( *[]) : 0 | ( *[]) : [],
    type_of_foobar Z (IntSynType i32) Z (IntSynType u32) Z (IntSynType i32)
    (* we have to provide the spec we have for the trait impl we give it *)
    (* diff to before: we have to give all the rts and syntys, and then use type specialization. 
       This includes self, args, and assocs.
    *)
    (Foo_base_spec Z (IntSynType i32) Z (IntSynType u32) Z (IntSynType i32) <TY> (int i32) <TY> (int u32) <TY> (int i32) <INST!>)
    (* TODO: also instantiate the function? *)
    <TY> (int i32) <TY> (int u32) <TY> (int i32)
    <MERGE!>
  ) -∗
  typed_function π (call_foobar_def foobar_i32_u32_i32_loc) [(* TODO *)] (<tag_type> type_of_call_foobar).
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

  (* We use the base_spec here *)
  Definition Foo_u32_mut_ref_T_bar_spec (T_rt : Type) (U_rt : Type) (T_st : syn_type) (U_st : syn_type) :=
    (* quantify over the generics of the instance *)
    fnspec! ( *[ ulft_a]) : 1 | ( *[ T_ty]) : [ (T_rt, T_st) ],
    (* then instantiate the base spec *)
    (Foo_base_spec Z (IntSynType u32) (place_rfn T_rt * gname) PtrSynType Z (IntSynType i32) <TY> int u32 <TY> mut_ref T_ty ulft_a <TY> int i32 <INST!>)
    (* project out the spec for this function *)
    .(Foo_bar_spec) U_rt U_st <MERGE!>.

  Context (T_rt : Type) (T_st : syn_type).

  (* NOTE: for this, we need to always first quantify over all rts and then over all sts *)
  Definition Foo_u32_mut_ref_T_spec_params : Foo_spec_params :=
  {|
    Foo_bar_spec_params U_rt := <get_params_of> (Foo_u32_mut_ref_T_bar_spec T_rt U_rt);
  |}.
  Definition Foo_u32_mut_ref_T_spec :=
    (* quantify over all the type variables of the instance *)
    spec! ( *[ ulft_a]) : 1 | ( *[ T_ty]) : [ T_rt ],
    (* This is a record decl because we might have overrides for some of the fields *)
    {|
      Foo_bar_spec U_rt U_st := Foo_u32_mut_ref_T_bar_spec T_rt U_rt T_st U_st <TY> T_ty <LFT> ulft_a : spec_with 1 [_] (Foo_bar_spec_params (Foo_u32_mut_ref_T_spec_params) U_rt → _)
    |}.

  Lemma Foo__incl (T_ty : type T_rt) ulft_a :
    Foo_spec_incl
      (* instantiation of the instance's parameters *)
      (Foo_u32_mut_ref_T_spec <TY> T_ty <LFT> ulft_a <INST!>)
      (* instantiation of the trait's parameters *)
      (Foo_base_spec Z (IntSynType u32) (place_rfn T_rt * gname) PtrSynType Z (IntSynType i32) <TY> int u32 <TY> mut_ref T_ty ulft_a <TY> int i32 <INST!>).
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
  {Foo_W_T_mut_ref_i32_spec_params : Foo_spec_params}
  (Foo_W_mut_ref_i32_spec : (Foo_spec Foo_W_T_mut_ref_i32_spec_params)) :=

  fn(∀ ( *[ulft_a]) : 1 | ( *[W_ty; Foo_W_mut_ref_i32_Output_ty]) : [(W_rt, W_st); (Foo_W_mut_ref_i32_Output_rt, Foo_W_mut_ref_i32_Output_st)] | (a) : W_rt, (λ _, [(* ? *) ]); a :@: W_ty ; (λ π,
      (* require that it satisfies the spec we need *)
      (* Crucial: here we can exactly specify the lifetime instantiation we need the spec to work for. *)
      ⌜Foo_spec_incl Foo_W_mut_ref_i32_spec (Foo_base_spec W_rt W_st (place_rfn Z * gname) PtrSynType Foo_W_mut_ref_i32_Output_rt Foo_W_mut_ref_i32_Output_st <TY> W_ty <TY> mut_ref (int i32) ulft_a <TY> Foo_W_mut_ref_i32_Output_ty <INST!>)⌝
    )) → ∃ y : _, y @ unit_t ; (λ π, True).


Lemma foobar_ref_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_mut_ref_i32_Output_rt : Type) (Foo_W_mut_ref_i32_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (* this is still polymorphic in the lifetimes appearing in the instantiation *)
    (Foo_W_T_mut_ref_i32_spec_params : Foo_spec_params)
    (Foo_W_mut_ref_i32_spec : (Foo_spec Foo_W_T_mut_ref_i32_spec_params))
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_mut_ref_i32_bar_i32_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_mut_ref_i32_bar_i32_loc ◁ᵥ{π} Foo_W_mut_ref_i32_bar_i32_loc @ function_ptr [PtrSynType; IntSynType i32] (<tag_type>
    (* Explicitly abstract over all lifetimes *)
    (spec! ( *[]) : 0 | ( *[]) : [],
    (* Instantiate the the spec with the lifetimes, and instantiate the method with its types *)
    Foo_W_mut_ref_i32_spec.(Foo_bar_spec) Z (IntSynType i32) <TY> (int i32) <MERGE!>)) -∗
  typed_function π (foobar_ref_def W_st Foo_W_mut_ref_i32_Output_st Foo_W_mut_ref_i32_bar_i32_loc) [(* TODO *)] (<tag_type> type_of_foobar_ref W_rt W_st Foo_W_mut_ref_i32_Output_rt Foo_W_mut_ref_i32_Output_st Foo_W_mut_ref_i32_spec).
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
  foobar_ref_u32_loc ◁ᵥ{π} foobar_ref_u32_loc @ function_ptr [(* TODO *)] (<tag_type>
    spec! ( *[ulft_a]) : 1 | ( *[]) : [],
    type_of_foobar_ref Z (IntSynType u32) Z (IntSynType i32)
    (Foo_u32_mut_ref_T_spec Z (IntSynType i32) <TY> (int i32) <LFT> ulft_a <INST!>)
    <LFT> ulft_a <MERGE!>) -∗
  typed_function π (call_foobar_def foobar_ref_u32_loc) [(* TODO *)] (<tag_type> type_of_call_foobar).
Proof.
Admitted.
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
  {Foo_W_T_spec_params : Foo_spec_params}
  (Foo_W_T_spec : (Foo_spec Foo_W_T_spec_params)) :=

  fn(∀ ( *[]) : 0 | ( *[W_ty; T_ty; Foo_W_T_Output_ty]) : [(W_rt, W_st); (T_rt, T_st); (Foo_W_T_Output_rt, Foo_W_T_Output_st)] | (a, b) : W_rt * T_rt, (λ _, [(* ? *) ]); a :@: W_ty, b :@: T_ty ; (λ π,
      (* require that it satisfies the spec we need *)
      ⌜Foo_spec_incl Foo_W_T_spec (Foo_base_spec W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st <TY> W_ty <TY> T_ty <TY> Foo_W_T_Output_ty <INST!>)⌝
    )) → ∃ y : _, y @ unit_t ; (λ π, True).

Lemma foobar_ref2_has_type π :
  ∀ (W_rt : Type) (W_st : syn_type) (T_rt : Type) (T_st : syn_type)
    (* also quantify over the Output (per trait instance we require) *)
    (Foo_W_T_Output_rt : Type) (Foo_W_T_Output_st : syn_type)
    (* also quantify over the specification of the trait (per trait instance) *)
    (Foo_W_T_spec_params : Foo_spec_params)
    (Foo_W_T_spec : (Foo_spec Foo_W_T_spec_params))
    (* quantify over the method locs (per generic instance per method per trait instance) *)
    (Foo_W_T_bar_i32_loc : loc),
  (* require type assignment for methods, instantiating the generics in the spec accordingly *)
  Foo_W_T_bar_i32_loc ◁ᵥ{π} Foo_W_T_bar_i32_loc @ function_ptr [PtrSynType; IntSynType i32] (<tag_type>
    spec! ( *[]) : 0 | ( *[]) : [],
    Foo_W_T_spec.(Foo_bar_spec) Z (IntSynType i32) <MERGE!>) -∗
  typed_function π (foobar_ref2_def W_st T_st Foo_W_T_Output_st Foo_W_T_bar_i32_loc) [(* TODO *)] (<tag_type> type_of_foobar_ref2 W_rt W_st T_rt T_st Foo_W_T_Output_rt Foo_W_T_Output_st Foo_W_T_spec).
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

Definition call_foobar_ref2_def (foobar_ref2_u32_mut_ref_i32_loc : loc) : function.
Proof.
Admitted.

Section rr.
  Context `{!typeGS Σ}.

Definition type_of_call_foobar_ref2 :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : (), (λ _, []); (λ π, True)) → ∃ y : _, y @ unit_t ; (λ π, True).

Lemma call_foobar_ref2_has_type π :
  ∀ (foobar_ref2_u32_mut_ref_i32_loc : loc),
  foobar_ref2_u32_mut_ref_i32_loc ◁ᵥ{π} foobar_ref2_u32_mut_ref_i32_loc @ function_ptr [(* TODO *)] (<tag_type>
    spec! ( *[ulft_1]) : 1 | ( *[]) : [],
    type_of_foobar_ref2 Z (IntSynType u32) (place_rfn Z * gname) PtrSynType Z (IntSynType i32)
    (Foo_u32_mut_ref_T_spec Z (IntSynType i32) <TY> (int i32) <LFT> ulft_1 <INST!>)
    <TY> int u32 <TY> mut_ref (int i32) ulft_1 <TY> int i32 <MERGE!>) -∗
  typed_function π (call_foobar_def foobar_ref2_u32_mut_ref_i32_loc) [(* TODO *)] (<tag_type> type_of_call_foobar).
Proof.
Admitted.
End rr.

(* Should we really always explicitly abstract over all lifetimes?
  This does not seem necessary.
   Does it suffice to just lift the quantifiers of a function up when we specify assumptions?

  btw: We should also lift all the quantifiers over type parameters, because instances might also need them.
   (which are still present in the monomorphized version)

  Q: is this ultimately sound? I guess at the place where everything is monomorphic, yeah.
*)


(* This approach seems to work.

  Some questions:

  1) When do we have remaining type variables that are not instantiated in the assumptions?
    -> certainly for type variables of our own function.
    Effectively, we want to instantiate each function assumption as far as possible, while keeping it parametric in the things we are ourselves parametric in.

   What do we NEED to instantiate? (I would like to keep things as simple as possible)
   - If I introduce a new lifetime

   What new lifetimes do we NEED to introduce?
   - we need to check

  2) Does spec inclusion now behave as expected?
    Is it okay that I introduce new lifetime parameters to function specs I assume?
    Can I always instantiate these in adequacy?


  3) Can I simplify the spec param inference?
     In order to infer param types, I usually rely on Coq's inference.
      So declaring them ahead of time is not possible.
    => This is okay now.

  4) At which point do I handle specs?
    - I could generate the name for trait specs ahead of time
    - then generate all the functions
    - and then assemble the instances (like we do currently)
    - for unannotated functions in an instance, we should use the default spec.
      Should we still generate a definition for that?
      I think that's a good idea, probably. Then we can have consistent handling when generating the instance.

    It also makes sense to include all generics from the instance / trait, I think, since that is how we currently handle things.

  5) Where do we add the sidecondition for generics to function types?
      What I need in the verification of a function is that all of its direct generics are wellformed.
      Later instantiation does not matter.
      So maybe we leave it as-is?

  6) Do I need to requantify over late-bound lifetimes as well?
     TODO

  Implementation steps:
  - add infrastructure for quantifying over lifetimes in spec assumptions [done]
  - change instantiation to the new interface [done]
  - generate _spec_params and add it everywhere
  - generate trait impls which are parametric
  - export them correctly from modules
  - add rr::exists. Handle as a record which is passed as a parameter to the specs.

 *)

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
