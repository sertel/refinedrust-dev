From refinedrust.automation Require Import ident_to_string.
From iris.proofmode Require Import string_ident.
From refinedrust Require Import typing.

(** Some loop experiments *)

Section loop1.
Context `{!typeGS Σ}.

(** Example 1 *)

(*
  fn loop1() {
    let mut x = 1;
    let mut y = 1;
    loop {
      #[invariant(x = y)]
      x += 1;
      y += 1;
    }
   }
*)


Definition loop1_def : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("x", (it_layout i32) : layout);
  ("y", (it_layout i32) : layout);
  ("__3", (layout_of unit_sl) : layout);
  ("__4", (layout_of unit_sl) : layout)
 ];
 f_code :=
  <["_bb1" :=
   Goto "_bb2"
  ]>%E $
  <["_bb0" :=
   "x" <-{ IntOp i32 } i2v (1) i32;
   "y" <-{ IntOp i32 } i2v (1) i32;
   (* put loop invariant annotation here *)
   (*annot: (InitLoopAnnot loop1_bb1_invariant loop1_bb1_EL_invariant);*)
   annot: InitLoopAnnot;
   Goto "_bb1"
  ]>%E $
  <["_bb2" :=
   "x" <-{ IntOp i32 } (use{ IntOp i32 } ("x")) +{ IntOp i32 , IntOp i32 } (i2v (1) i32);
   "y" <-{ IntOp i32 } (use{ IntOp i32 } ("y")) +{ IntOp i32 , IntOp i32 } (i2v (1) i32);
   "__4" <-{ UntypedOp ((layout_of unit_sl)) } zst_val;
   Goto "_bb1"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition type_of_loop1  :=
  fn(∀ _ : unit, (λ ϝ, []); True)
    → ∃ _ : unit, () @ unit_t; True.

(* functional invariant to establish at the start of bb1 *)
(* TODO: initialization status changes the refinement type.
  Check whether we should try to infer that in the frontend, or whether we should just deinitialize everything that might not be needed beforehand via annotations (this seems easier to determine in the frontend);
   point in particular: this may differ depending on which branch we took beforehand.
   StorageDead instructions may be useful for that.
*)
Definition loop1_bb1_invariant (l_0 : place_rfn unit) (x : place_rfn Z) (y : place_rfn Z) (l_3 : place_rfn unit) (l_4 : place_rfn unit) : iProp Σ :=
  ∃ x' y', ⌜x = PlaceIn x'⌝ ∗ ⌜y = PlaceIn y'⌝ ∗ ⌜x' = y'⌝.

Definition loop1_bb1_EL_invariant (E : elctx) (L : llctx) :=
  True.

Definition loop1_inv_map : bb_inv_map_t :=
  PolyCons ("_bb1", (wrap_inv loop1_bb1_invariant, wrap_inv loop1_bb1_EL_invariant)) (PolyNil).


Lemma loop1_dummy_context π :
  ⊢ typed_function π loop1_def type_of_loop1.
Proof.
  intros.

  set (loop_inv_map := BB_INV_MAP loop1_inv_map).

  iStartProof.
  start_function "loop1" ( ? ).
  intros local___0 local_x local_y local___3 local___4.
  prepare_parameters ( ).
  init_lfts ( ∅ ).
  repeat liRStep; liShow.
  iApply typed_stmt_annot_skip.
  do 1 liRStep; liShow.
  rewrite {1}/Hinv__bb1.
  do 9 liRStep.
  liShow.
  (* TODO need instances for subltype *)

  (* TODO: check if the invariant may be too strong, in the sense that after one iteration we have something weaker? *)

  (* TODO: add the named_lfts and the credit_store. *)


Abort.

(* Typing rule design: 
  - have a lemma 




(**
  How can we get subtyping to work? 
  - I don't want to put subtyping directly in the invariant, which would be the straightforward way to establish it.
    This would require inverting subtyping in the loop, which would be really nasty.
  - Can we say: subtype E L (my_loop_inv E L) or so? 
      i.e. formulate it as: we can do subtyping and then have to show the invariant.
    ideally would like some commuting rules here, i.e. 
      - first instantiate the existentials below the subtype with evars,
      - then distribute the subtype over the the separating conj, 
        so that we can then apply the normal rules. 


    subtype E L P := 
       elctx_interp E -∗ llctx_interp L -∗ P ∗ llctx_interp L


    
 *)
