From caesium Require Import lang notation tactics.
From lithium Require Export tactics.
From refinedrust Require Import functions programs int references uninit automation products.

Section lithium.
  Context {Σ : gFunctors}.
Context (named_lfts' : gmap Z Z → iProp Σ).
Lemma foo : 
  True -∗ named_lfts' ∅ -∗ True.
Proof. 
  iStartProof. 
  liEnforceInvariantAndUnfoldInstantiatedEvars.
  liStep.
  liStep. liStep. liStep. 
Abort.
End lithium.


Section rectype.


End rectype.


(** Generics *) 
Definition target `{LayoutAlg} (T_st : syn_type) : function := {|
 f_args := [
  ("abc", use_layout_alg' T_st)
 ];
 f_local_vars := [
  ("__0", it_layout i32);
  ("abc2", use_layout_alg' T_st)
 ];
 f_code :=
  <["_bb0" :=
  "abc2" <-{UntypedOp (use_layout_alg' T_st)} use{UntypedOp (use_layout_alg' T_st)} "abc";
   "__0" <-{ IntOp i32 } I2v (42) I32;
   Return (use{ IntOp i32 } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition source (target_loc : loc) : function := {|
 f_args := [];
 f_local_vars := [
  ("__0", it_layout i32 : layout)
 ];
 f_code :=
  <["_bb0" :=
   expr: Call target_loc [Val(I2v (42) I32)];
   "__0" <-{ IntOp i32 } I2v (42) I32;
   Return (use{ IntOp i32 } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.


(* call it with a mutable reference *)
Definition source_ref (target_loc : loc) : function := {|
 f_args := [];
 f_local_vars := [
  ("__0", it_layout i32 : layout);
  ("a", it_layout i32 : layout);
  ("b", void* : layout)
 ];
 f_code :=
  <["_bb0" :=
   "a" <-{IntOp i32} I2v (42) I32;
   annot: (StartLftAnnot "κ" []);
   "b" <-{PtrOp} &ref{Mut, Some (RSTInt I32), "κ"} "a";
   expr: Call target_loc [use{PtrOp} "b"];
   annot: (EndLftAnnot "κ");
   "__0" <-{ IntOp i32 } I2v (42) I32;
   annot: (StratifyContextAnnot); 
   Return (use{ IntOp i32 } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Module attempt2.
  Context `{!typeGS Σ}.
  Definition type_of_source := 
    fn(∀ () : unit, (λ ϝ, []); λ π, True)
      → ∃ (x) : (Z), x @ int i32; (λ π, True).
  (* NOTE fixing the refinement type ahead. That is still fine, since it is already lifetime-invariant. *)
  (* NOTE: We don't parameterize the type over the layout, since that will be resolved at call time.
      But we parameterize over the syn_type, so that we can instantiate it with the same one in the [typed_function] proof. *)
  Definition type_of_target (T_rt : Type) (T_st : syn_type) :=
    fn(∀ (T_ty, r) : type T_rt * T_rt, (λ ϝ, []); r @ T_ty; λ π, ⌜T_ty.(ty_syn_type) = T_st⌝ ∗ True)
      → ∃ () : unit, 42 @ int i32; (λ π, True).

  Lemma source_typed π target_loc :  
    (* the function_ptr type is monomorphic in the layout and requires a concrete instantiation *)
    (* this also means that, if we call the same function with different instantiations, we will need multiple linking assumptions *)
    target_loc ◁ᵥ{π} target_loc @ function_ptr [IntSynType i32] (type_of_target Z (IntSynType i32)) -∗
    typed_function π (source target_loc) [IntSynType i32] type_of_source.
  Proof.
    iStartProof.
    start_function "source" ( () ) => local_0. 
    intros.
    init_tyvars (∅).
    init_lfts (∅).
    repeat liRStep; liShow.
    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  Qed.

  Lemma source_ref_typed π target_loc :  
    (* the function_ptr type is monomorphic in the layout and requires a concrete instantiation *)
    (* this also means that, if we call the same function with different instantiations, we will need multiple linking assumptions *)
    (* for a mutable reference to an i32 *)
    target_loc ◁ᵥ{π} target_loc @ function_ptr [PtrSynType] (type_of_target (place_rfn Z * gname) (PtrSynType) ) -∗
    (* for a shared reference to an i32 *)
    (*target_loc ◁ᵥ{π} target_loc @ function_ptr [void* : layout] (type_of_target (place_rfn Z)) -∗*)
    typed_function π (source_ref target_loc) [IntSynType i32; IntSynType i32; PtrSynType] type_of_source.
  Proof.
    iStartProof.
    start_function "source" ( () ) => local_0 local_a local_b. 
    intros.
    init_tyvars (∅).
    init_lfts (∅).
    repeat liRStep; liShow.

    (* TODO: subtyping here should ideally hold. Currently it doesn't because of syntypes in return. *)

    (* Now I didn't get any drop information on the ghost var.
        In principle, I should get drop information from target, phrased generically. *)
    
    (* TODO *)
    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  Abort.
  
  Lemma target_typed π (T_rt : Type) T_st T_ly : 
    syn_type_has_layout T_st T_ly →
    ⊢ typed_function π (target T_st) [IntSynType i32; T_st] (type_of_target T_rt T_st).
  Proof.
    intros.
    start_function "target" ( (T_ty & r) ) => arg_abc local_0 local_a. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.
    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.

  (* TODO : for the first one, we will anyways need a property here that needs to be satisfied by all types (?)
        - every type should be MCId and MCCopy at UntypedOp, because an UntypedOp memcast does nothing
        - possibly: also also give each syntyep a canonical optype and require that types are compatible at MCCopy with that. (see notes on Ipad; would enable to use proper optypes on generic functions)

        
      The latter point pertains in interesting ways to validity invariants.
      The non-trivial optypes essentially check validity invariants. if our translation just uses Untyped for generics, we remove these validity checks (eg on loads) that Rust has.
       But can they ever fail on generics anyways? And where would that error happen? 
       - if a value at generic type fails to satisfy a validity invariant, this should be an error of the context, because a generic function cannot make up such a thing out of thin air (?)
         No: this does not hold true once I consider unsafe stuff like transmutation (but this is really sketchy, because I will not know anything about the generic..)
       - everything that enters from the context is probably checked for validity at the call boundary already (doing a write to arguments, etc)
       => The main issue I get from Untyped seems to be that I can do really sketchy casts and this is not caught by the semantics.
       => This is just one more thing in our model that we don't handle, maybe. 

       But what would be the right way to verify it generically?
       - one verification per syntactic type is clearly infeasible (there's an unbounded number due to structs)
       - phrase a general condition (like I sketched above) and use proper optypes. Main difficulty: making sure that we can satisfy this condition for all the sematypes we are interested in. TODO;


       Other thing: optypes for enums? What are valid bitpatterns for enums? 

     *)
  Abort.

  (* Now, can we actually instantiate the assumption on target that source poses? 
      - We assume that we have linked against the layout-monomorphic version, with the given argument layouts.
        We get a corresponding [fntbl_entry f_loc (target (IntSynType i32))].
        We can show that the arg_layouts of that match with what is assumed by function_ptr.
        (because the layout alg will be successful)
      - Then we need to show typed_function for that. This is easy and directly follows from [target_typed].
        We need to show that the syntypes of the arg match with the layout, which we essentially already showed in the previous step.
        We also need to show that the layout alg is successful on allthe locally used stuff.
        It doesn't require establishing any connection between the layout and the type.
          (which is good, because at that time, I may not know the full type).
   *)
End attempt2.
 *)

Section structs2.
  Context `{typeGS Σ}.

  (* Goal: translate the following code:

      struct foostruct<T> {
        x : i32, 
        y : T
      }

      struct barstruct<T> {
        z : i32,    
        w : foostruct<T>,
      }


      fn foo<T>(a : foostruct<T>) {
         
      }

      fn bar<T>(b : barstruct<T>) {
        foo(b.w);   
      }


      fn foobar() {
        let x: foostruct<i32>;
        x = foostruct {x: 43, y: 53};

        let y: barstruct<i32>;
        y = barstruct {z : 42, w : x};

        bar(y);
      }

      fn foobaz() {
        let x: foostruct<i32>;
        x = foostruct {x: 43, y: 53};

        // this is not valid
        let y: barstruct<foostruct<i32>>;
        y = barstruct {z : 432, w: foostruct {x : 342, y : foostruct {x : 34, y : 90 }}};
      }
   *)

  Section foostruct_spec.
    Context (T_st : syn_type).
    Definition foostruct_sls : struct_layout_spec := mk_sls "foostruct" [("x", IntSynType i32); ("y", T_st)].
  End foostruct_spec.

  Section barstruct_spec.
    Context (T_st : syn_type).
    Definition barstruct_sls : struct_layout_spec := mk_sls "barstruct" [("z", IntSynType i32); ("w", foostruct_sls T_st : syn_type)].
  End barstruct_spec.

  Section foo_code.
    Definition foo (T_st : syn_type) : function := {|
     f_args := [
      ("abc", use_layout_alg' (foostruct_sls T_st))
     ];
     f_local_vars := [
      ("__0", use_layout_alg' (IntSynType i32))
     ];
     f_code :=
      <["_bb0" :=
       "__0" <-{ IntOp i32 } I2v (42) I32;
       Return (use{ IntOp i32 } ("__0"))
      ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
  End foo_code.

  Section bar_code.
    (* let's assume that bar also uses (T, T) *)
    Definition bar (T_st : syn_type) (foo_loc : loc) : function := {|
     f_args := [
      ("b", use_layout_alg' (barstruct_sls T_st))
     ];
     f_local_vars := [
      ("__0", use_layout_alg' UnitSynType);
      ("a", use_layout_alg' (foostruct_sls T_st))
     ];
     f_code :=
      <["_bb0" :=
      "a" <-{use_op_alg' (foostruct_sls T_st)} use{use_op_alg' (foostruct_sls T_st)} ("b" at{barstruct_sls T_st} "w");
      annot: StopAnnot;
       expr: Call foo_loc [use{use_op_alg' (foostruct_sls T_st)} "a"];
       "__0" <-{ IntOp i32 } I2v (42) I32;
       Return (use{ IntOp i32 } ("__0"))
      ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
  End bar_code.

  Section foobar_code.
    Definition foobar (bar_loc : loc) : function := {|
     f_args := [
      ("x", use_layout_alg' (foostruct_sls (IntSynType i32)));
      ("y", use_layout_alg' (barstruct_sls (IntSynType i32)))
     ];
     f_local_vars := [
      ("__0", use_layout_alg' UnitSynType)
     ];
     f_code :=
      <["_bb0" :=
      "x" at{foostruct_sls (IntSynType i32)} "x" <-{IntOp i32} (I2v 43 I32);
      "x" at{foostruct_sls (IntSynType i32)} "y" <-{IntOp i32} (I2v 53 I32);
      "y" at{barstruct_sls (IntSynType i32)} "z" <-{IntOp i32} (I2v 42 I32);
      "y" at{barstruct_sls (IntSynType i32)} "w" <-{use_op_alg' (foostruct_sls (IntSynType i32))} use{use_op_alg' (foostruct_sls (IntSynType i32))} "x";
       expr: Call bar_loc [use{use_op_alg' (barstruct_sls (IntSynType i32))} "y"];
       "__0" <-{ IntOp i32 } I2v (42) I32;
       Return (use{ IntOp i32 } ("__0"))
      ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
  End foobar_code.

  Section specs.
    (* TODO: I don't think that the syntype sidecondition should be part of the precondition -- it should rather be hidden / explicitly a part of a function spec. *)
    Definition type_of_foo (T_rt : Type) T_st :=
      fn(∀ (T, r, z) : (type T_rt * T_rt * Z), (λ ϝ, []); -[#z; #r] @ (struct_t (foostruct_sls T.(ty_syn_type)) +[int i32; T]); λ π, ⌜T.(ty_syn_type) = T_st⌝)
        → ∃ () : (), 42 @ int i32; (λ π, ⌜True⌝).

    Definition type_of_bar (T_rt : Type) T_st :=
      fn(∀ (T, r, z1, z2) : (type T_rt * T_rt * Z * Z), (λ ϝ, []); 
      -[#z1; #(-[#z2; #r])] @ (struct_t (barstruct_sls T.(ty_syn_type)) +[int i32; struct_t (foostruct_sls T.(ty_syn_type)) +[int i32; T]]); λ π, ⌜T.(ty_syn_type) = T_st⌝)
        → ∃ () : (), () @ unit_t; (λ π, ⌜True⌝).

    Definition type_of_foobar :=
      fn(∀ () : (), (λ ϝ, []); λ π, True)
        → ∃ () : (), () @ unit_t; (λ π, ⌜True⌝).
  End specs.

  Section proofs.
    
    Lemma foo_typed π (T_rt : Type) T_st : 
      syn_type_is_layoutable (foostruct_sls T_st) →
      ⊢ typed_function π (foo T_st) [IntSynType i32] (type_of_foo T_rt T_st).
    Proof.
      start_function "source" ( [[T_ty r] z] ) => arg_abc local_0. 
      intros.
      init_lfts (∅).
      init_tyvars (<["T" := existT _ T_ty]> ∅).
      repeat liRStep; liShow.
      Unshelve. all: li_unshelve_sidecond; sidecond_hook.
    Qed.


    Lemma bar_typed π (T_rt : Type) (T_st : syn_type) (foo_loc : loc) :
      (* assumption for foostruct *)
      syn_type_is_layoutable (foostruct_sls T_st) →
      (* assumption for barstruct *)
      syn_type_is_layoutable (barstruct_sls T_st) →
      (* assumption for foo *)
      foo_loc ◁ᵥ{π} foo_loc @ function_ptr [foostruct_sls T_st : syn_type] (type_of_foo T_rt T_st) -∗
      typed_function π (bar T_st foo_loc) [UnitSynType; foostruct_sls T_st : syn_type] (type_of_bar T_rt T_st).
    Proof.
      start_function "source" ( [[[T_ty r] z1] z2] ) => arg_abc local_0 local_a. 
      init_lfts (∅).

      simpl in *. 
      repeat liRStep; liShow.
      iApply program_rules.typed_stmt_annot_skip.
      do 49 liRStep; liShow.
      repeat liRStep; liShow. 

      (* 
         coercing StructLtype to uninit..
          difficulty: some parts might be blocked for a reborrow below, so we cannot require to be able to fold to ofty.
          instead: need to structurally go through it. 
          coerce all the components to uninit.
          This should work via subsume, since it is fully owned.
         Should we instead explicitly have owned, non-persistent subtyping? Essentially subsume_loc + syn_type_eq + sidecond maybe
        
         coercion to uninit only needs to work for Owned. For Uniq, we are below a mutref, which we should never need to deinitialize (and we can't).
       *)

      liRStep. liRStep. liRStep. liRStep. 
      liRStep; liShow.
      liRStep. 
      (* evar instantiation strategy: 
         - need an instance for the case that the sls is different / contains an evar. 
         - after that, the struct instance should fire and we should be fine by recursion.
       *)

      iApply typed_stmt_annot_skip.

      liRStep. 
      cbn. 
      simpl.
      Set Printing All. 

      (* this is probably an issue with the plist  *)
      Global Typeclasses Opaque struct_t.
      Arguments struct_t : simpl never.

      (*refine (tac_fast_apply (place_ofty_struct (rts := [_ ; _]) _ _ _ _ _ _ _ _ _ _ _) _).*)
      iApply (place_ofty_struct (rts := [_ ; _])).
      liRStep. 

      Unshelve. all: li_unshelve_sidecond; sidecond_hook.
    Abort.

    (*
    Lemma foobar_typed π (foostruct_i32_sl barstruct_i32_sl : struct_layout) (bar_loc : loc) :
      (* assumption for bar *)
      bar_loc ◁ᵥ{π} bar_loc @ function_ptr [foostruct_i32_sl : layout_spec; barstruct_i32_sl : layout_spec] (type_of_bar Z foostruct_i32_sl barstruct_i32_sl) -∗
      typed_function π (foobar foostruct_i32_sl barstruct_i32_sl bar_loc) (type_of_foobar foostruct_i32_sl barstruct_i32_sl). 
    Proof.
      (* TODO: need lemma to convert uninit to uninit struct *)
    Abort.
    *)
    
  End proofs.
End structs2.
