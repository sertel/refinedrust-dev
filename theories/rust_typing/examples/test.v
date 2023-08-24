From iris.proofmode Require Import coq_tactics reduction string_ident.
From caesium Require Import lang notation tactics.
From refinedrust Require Import functions programs int references automation uninit arrays.

Section test.
  Arguments ltype_own : simpl never.
  Context `{typeGS Σ}.

  (** OnEndlft tests *)
  Lemma endlft_test_1 E L κ s fn R π ϝ :
    L = [κ ⊑ₗ{0} []] →
    named_lfts (<["κ" := κ]> ∅) -∗
    typed_stmt π E L (annot: (EndLftAnnot "κ"); s) fn R ϝ.
  Proof.
    intros ->.
    iStartProof.
    repeat liRStep; liShow.
  Abort.

  Lemma endlft_test_2 E L κ s fn R π ϝ κ2 :
    L = [κ ⊑ₗ{0} []; κ2 ⊑ₗ{1} []] →
    Inherit κ InheritDynIncl (llft_elt_toks [κ2]) -∗
    named_lfts (<["κ" := κ]> ∅) -∗
    typed_stmt π E L (annot: (EndLftAnnot "κ"); s) fn R ϝ.
  Proof.
    intros ->.
    iStartProof.
    repeat liRStep; liShow.
  Abort.

  Lemma endlft_test_3 E L κ s fn R π ϝ :
    L = [κ ⊑ₗ{0} []] →
    named_lfts (<["κ1" := κ]> ∅) -∗
    typed_stmt π E L (annot: (EndLftAnnot "κ2"); s) fn R ϝ.
  Proof.
    intros ->. iStartProof.
    repeat liRStep; liShow.
  Abort.

  (** CopyLftName tests *)
  Lemma copy_lft_name_test_1 π E L κ s fn R ϝ :
    L = [κ ⊑ₗ{0} []] →
    named_lfts (<["κ" := κ]> ∅) -∗
    typed_stmt π E L (annot: (CopyLftNameAnnot "κ2" "κ"); s) fn R ϝ.
  Proof.
    intros ->. iStartProof.
    repeat liRStep; liShow.
  Abort.

  (** DynInclude tests *)
  Lemma dyn_include_test_1 π E L κ1 κ2 s fn R ϝ :
    L = [κ1 ⊑ₗ{0} []; κ2 ⊑ₗ{0} []] →
    named_lfts (<["κ1" := κ1]> $ <["κ2" := κ2]> $ ∅) -∗
    typed_stmt π E L (
      annot: (DynIncludeLftAnnot "κ1" "κ2");
      annot: (EndLftAnnot "κ1");
      annot: (EndLftAnnot "κ2");
      s) fn R ϝ.
  Proof.
    intros ->. iStartProof.
    repeat liRStep; liShow.
  Abort.

  (** ExtendLft tests *)
  Lemma extendlft_test_1 π E L κ1 κ2 s fn R ϝ :
    L = [κ1 ⊑ₗ{1} [κ2]; κ2 ⊑ₗ{0} []] →
    named_lfts (<["κ1" := κ1]> $ <["κ2" := κ2]> $ ∅) -∗
    typed_stmt π E L (
      annot: (ExtendLftAnnot "κ1");
      annot: (EndLftAnnot "κ2");
      s) fn R ϝ.
  Proof.
    intros ->. iStartProof.
    repeat liRStep; liShow.
  Abort.

  (** AliasLft tests *)
  Lemma aliaslft_test_1 π E L κ1 κ2 s fn R ϝ :
    L = [κ1 ⊑ₗ{0} [κ2]; κ2 ⊑ₗ[]] →
    named_lfts (<["κ1" := κ1]> $ <["κ2" := κ2]> $ ∅) -∗
    typed_stmt π E L (
      annot: (AliasLftAnnot "κ3" ["κ1"; "κ2"]);
      s) fn R ϝ.
  Proof.
    intros ->. iStartProof.
    repeat liRStep; liShow.
  Abort.

  (** AssertType tests *)
  Lemma assert_type_test1 π E L (T : (llctx → val → ∀ rt : Type, type rt → rt → iProp Σ)) : 
    named_lfts ∅ -∗
    T L (I2v 42 I32) Z (int i32) 42%Z -∗
    typed_val_expr π E L (AnnotExpr 0 (AssertTypeAnnot (Int i32)) (I2v 42 I32)) T.
  Proof.
    iStartProof.
    init_tyvars ∅.
    repeat liRStep; liShow.
    done.
  Abort.

  Lemma assert_type_test2 π E (T : (llctx → val → ∀ rt : Type, type rt → rt → iProp Σ)) κ1 κ2 v γ : 
    named_lfts (<["κ1" := κ1]> $ <["κ2" := κ2]> ∅) -∗
    v ◁ᵥ{π} (#42%Z, γ) @ mut_ref (int i32) κ2 -∗
    T [κ1 ⊑ₗ{ 0} [κ2]] v (place_rfn Z * gname)%type (mut_ref (int i32) κ1) (# 42%Z, γ) -∗
    typed_val_expr π E [κ1 ⊑ₗ{0} [κ2]] (AnnotExpr 0 (AssertTypeAnnot (annotations.Ref Mut "κ1" (Int i32))) v) T.
  Proof.
    iStartProof.
    init_tyvars ∅.
    repeat liRStep; liShow.
    done.
    Unshelve. li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  (** prove_with_subtype tests *)

  Lemma prove_with_subtype_1 E L ( P Q : iProp Σ) T : 
    ⊢ prove_with_subtype E L (P ∗ Q) T.
  Proof.
    iStartProof.
    repeat liRStep.
  Abort.

  Lemma prove_with_subtype_2 π E L T l z : 
    T L -∗
    (l ◁ₗ[π, Owned false] PlaceIn z @ ◁ int i32)%I -∗
    prove_with_subtype E L (l ◁ₗ[π, Owned false] PlaceIn z @ ◁ int i32) T.
  Proof.
    iStartProof. repeat liRStep. liShow. done.
  Abort.

  Lemma prove_with_subtype_3 π E L T v z : 
    T L -∗
    (v ◁ᵥ{π} z @ int i32)%I -∗
    prove_with_subtype E L (v ◁ᵥ{π} z @ int i32) T.
  Proof.
    iStartProof. repeat liRStep. liShow. done.
  Abort.

  (** Subtyping for mut refs *)
  Lemma sub_test_evar1 κ1 γ1 z1: 
   ⊢ ∃ ty2, weak_subltype [] [κ1 ⊑ₗ{0} []] (Owned false) #(#z1, γ1) #(#z1, γ1) (MutLtype (◁ int i32) κ1) (◁ty2) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  Lemma sub_test_evar2 κ1 γ1 z1: 
   ⊢ ∃ ty2, weak_subltype [] [κ1 ⊑ₗ{0} []] (Owned false) #(#z1, γ1) #(#z1, γ1) (MutLtype (◁ int i32) κ1) (◁(mut_ref (ty2) κ1)) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  Lemma sub_test_evar3 κ1 γ1 z1: 
   ⊢ ∃ ty2 κ2, weak_subltype [] [κ1 ⊑ₗ{0} []] (Owned false) #(#z1, γ1) #(#z1, γ1) (MutLtype (◁ int i32) κ1) (◁(mut_ref (ty2) κ2)) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  Lemma sub_test_evar4 κ1 γ1 z1: 
   ⊢ ∃ (ty2 : type Z) κ2 r2, weak_subltype [] [κ1 ⊑ₗ{0} []] (Owned false) #(#z1, γ1) #r2 (MutLtype (◁ int i32) κ1) (◁(mut_ref (ty2) κ2)) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  (** Subtyping for arrays *)
  Lemma sub_test_array1 r1 len1 : 
    ⊢ ∃ (ty2 : type Z) len2, weak_subtype [] [] r1 r1 (array_t (int i32) len1) (array_t ty2 len2) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  Lemma sub_test_array2 r1 len1 : 
    ⊢ ∃ (ty2 : type Z) len2 lts2, weak_subltype [] [] (Owned false) r1 r1 (◁ array_t (int i32) len1) (ArrayLtype ty2 len2 lts2) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  Lemma sub_test_array3 r1 len1 : 
    ⊢ weak_subltype [] [] (Owned false) r1 r1 (ArrayLtype (int i32) len1 []) (◁ array_t (int i32) len1) True.
  Proof.
    iStartProof. repeat liRStep; solve [fail].
  Abort.

  Lemma sub_test_array4 r1 len1 i : 
    i < len1 →
    ⊢ weak_subltype [] [] (Owned false) r1 r1 (ArrayLtype (int i32) len1 [(i, ◁ int i32)]) (◁ array_t (int i32) len1) True.
  Proof.
    intros.
    iStartProof. repeat liRStep; solve [fail].
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma sub_test_array5 r1 len1 i : 
    i < len1 →
    ⊢ ∃ r2, weak_subltype [] [] (Owned false) #(<[i := #42%Z]> r1) #(<[i := #r2]> r1) (ArrayLtype (int i32) len1 [(i, ◁ int i32)]) (◁ array_t (int i32) len1) True.
  Proof.
    intros.
    iStartProof. repeat liRStep; solve [fail].
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma sub_test_array6 r1 len1 i : 
    i < len1 →
    ⊢ ∃ r2, weak_subltype [] [] (Owned false) #(<[i := #42%Z]> r1) #(<[i := #r2]> r1) (ArrayLtype (int i32) len1 [(i, ◁ int i32)]) (ArrayLtype (int i32) len1 []) True.
  Proof.
    intros.
    iStartProof. repeat liRStep; solve [fail].
    Unshelve. all: li_unshelve_sidecond; sidecond_hook.
    (* TODO: ideally we should get some additional knowledge from the fact the own the array -- however, this doesn't quite work because of the order of quantifiers.
       Can we add this to the context before initiating the subtyping? 

       In principle, it is learnable just from the type interpretation, so we should not need to add it as a precondition.
       We could add it as a hook to the subsume_full -> weak_subtype rule?
     *)
  Abort.

  (* subsume interaction: 
     - when proving something in the goal, look for related_to
     - related_to will trigger a find_in_context.
     - afterwards, will trigger a subsume between the found item and the goal.

    But: will not trigger for prove_with_subtype in the goal, since that is not an atom.
     -> for prove_with_subtype, need custom instances that emulate this sequence.

    currently: 
     do find_in_context, then weak_subltype.
     instead, of weak_subltype, I would rather trigger something else -- a subsume_full

   *)


  (** Misc tests *)
  Lemma subsume_test l π :
    l ◁ₗ[π, Owned false] PlaceIn 42%Z @ (◁ int i32) -∗
    (l ◁ₗ[π, Owned false] PlaceIn () @ ◁ uninit (IntSynType i32)) ∗ True.
  Proof.
    iStartProof.
    Set Typeclasses Debug.
    liRStep. liRStep. 
    liRStep. liShow.
    repeat liRStep.
  Qed.

  Lemma gvar_test γ (z : Z):
    gvar_pobs γ z -∗
    gvar_pobs γ z ∗ True.
  Proof.
    iStartProof.
    repeat liRStep; liShow.
  Qed.

  Lemma gvar_test' γ (z : Z):
    True -∗
    gvar_pobs γ z -∗
    find_in_context (FindOptGvarPobs γ) (λ a,
      match a with
      | inl (existT rt r) => gvar_pobs γ r -∗ gvar_pobs γ r ∗ True
      | _ => True
      end%I).
  Proof.
    iStartProof.
    repeat liRStep.
  Qed.

  Lemma gvar_test'' γ (z : Z):
    True -∗
    find_in_context (FindOptGvarPobs γ) (λ a,
      match a with
      | inl (existT rt r) => gvar_pobs γ r -∗ gvar_pobs γ r ∗ True
      | _ => True
      end%I).
  Proof.
    iStartProof.
    repeat liRStep.
  Qed.

  Lemma llctx_kill_lft_test L κ :
    L = [κ ⊑ₗ{0} []] →
    ⊢@{iPropI Σ} (tactic_hint (llctx_kill_llft_goal L κ) (λ L',
      ⌜L' = []⌝ ∗ True))%I.
  Proof.
    intros ->. iStartProof.
    repeat liRStep; solve[fail].
  Abort.

  Lemma lctx_lft_alive_count_test E L κ κ0 κ' :
    L = [κ ⊑ₗ{2} [κ']; κ' ⊑ₗ{3} []] →
    E = [κ' ⊑ₑ κ0] →
    (* doing a roundtrip *)
    ⊢@{iPropI Σ} (tactic_hint (lctx_lft_alive_count_goal E L κ) (λ '(κs, L'),
      tactic_hint (llctx_release_toks_goal L' κs) (λ L'', ⌜L = L''⌝ ∗  True)))%I.
  Proof.
    intros -> ->. iStartProof.
    repeat liRStep; solve[fail].
  Abort.

  (** Tests for credit tracking *)
  Lemma test1 :
    ⊢@{iPropI Σ} let n := 4 + 4 in True -∗ True.
  Proof.
    iStartProof.
    (* unfortunately, this doesn't work. We'll need some more heavy lifting to introduce abstractions. *)
    assert_fails liStep.
    (* one option:
      - have a judgment [introduce_credits n m] that wraps the wand,
          add a rule for that to liRIntroduceLetInGoal,
          then have an intro rule for that that adds the credit assertion to the context again.
     *)
  Abort.


  (** Stratify context *)
  Lemma unblock_test_none E L π s fn ls R Q ϝ l :
    l ◁ₗ[π, Owned false] PlaceIn 32%Z @ (◁ int i32) -∗
    typed_pre_context_fold π E L (CtxFoldStratifyAllInit) s fn ls R Q ϝ.
  Proof.
    iStartProof.
    repeat liRStep.
    liShow.
  Abort.

  Lemma unblock_test_none2 E L π s fn ls R Q ϝ l :
    l ◁ₗ[π, Owned false] PlaceIn 32%Z @ (◁ int i32) -∗
    typed_pre_context_fold π E L (CtxFoldStratifyAllInit) s fn ls R Q ϝ.
  Proof.
    iStartProof.
    repeat liRStep. liShow.
  Abort.

  Lemma unblock_test_obs E L π κ s fn ls R Q l γ ϝ :
    (□ [† κ]) -∗
    (□ gvar_pobs γ (42%Z)) -∗
    l ◁ₗ[π, Owned false] PlaceGhost γ @ (BlockedLty (int i32) κ) -∗
    typed_stmt π E L s fn ls R Q ϝ -∗
    typed_pre_context_fold π E L (CtxFoldStratifyAllInit) s fn ls R Q ϝ.
  Proof.
    iStartProof.
    repeat liRStep. liShow.
    done.
  Abort.



  Lemma subtype_test E L :
    ⊢ weak_subtype E L (int i32) (int i32) True ∗ True.
  Proof.
    iStartProof. repeat liRStep; solve[fail].
  Abort.

  Lemma subtype_test2 E κ κ' c :
    ⊢ weak_subtype E [κ ⊑ₗ{c} [κ']] (mut_ref (int i32) κ') (mut_ref (int i32) κ) True ∗ True.
  Proof.
    iStartProof. unshelve (repeat liRStep).
    all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma shorten_lft_mut_test E κ κ' v γ π fn ls R Q s c ϝ :
    v ◁ᵥ{π} (PlaceIn 42%Z, γ) @ mut_ref (int i32) κ -∗
    named_lfts (<["κ" := κ]> (<["κ'" := κ']> ∅)) -∗
    typed_stmt π E ([κ' ⊑ₗ{c} [κ]]) (ExprS (AnnotExpr 0 (ShortenLftAnnot ["κ'"]) v) s) fn ls R Q ϝ.
  Proof.
    iStartProof. repeat liRStep;  liShow.
    Unshelve.
    all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma shorten_lft_shr_test E κ κ' v π fn ls R Q ϝ s c :
    v ◁ᵥ{π} PlaceIn 42%Z @ shr_ref (int i32) κ -∗
    named_lfts (<["κ" := κ]> (<["κ'" := κ']> ∅)) -∗
    typed_stmt π E ([κ' ⊑ₗ{c} [κ]]) (ExprS (AnnotExpr 0 (ShortenLftAnnot ["κ'"]) v) s) fn ls R Q ϝ.
  Proof.
    iStartProof. repeat liRStep;  liShow.
    Unshelve.
    all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_box E L π (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) :
    (∀ l : loc, T L (val_of_loc l) (place_rfn unit) (box (uninit i32)) (PlaceIn ())) -∗
    typed_val_expr π E L (box{i32}) T.
  Proof.
    iStartProof. repeat liRStep. liShow. done; solve[fail].
  Abort.

  (** ** Read tests *)
  Lemma test_read1 E L (l : loc) γ π κ (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) :
    lctx_lft_alive E L κ →
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn 42%Z, γ) @ (◁ mut_ref (int i32) κ ) -∗
    (*(∀ v, l ◁ₗ[π, Owned false] 42 @ (◁ mut_ref i32) -∗ T v Z (int i32) 42) -∗*)
    typed_read π E L (!{PtrOp} l)%E (IntOp i32) T.
  Proof.
    iIntros (?) "?". repeat liRStep; liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read2 E L (l : loc) π (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) :
    l ◁ₗ[π, Owned false] (PlaceIn 42%Z) @ (◁ int i32) -∗
    (∀ v, l ◁ₗ[π, Owned false] PlaceIn 42%Z @ (◁ int i32) -∗ T L v Z (int i32) 42) -∗
    typed_read π E L (l) (IntOp i32) T.
  Proof.
    iIntros "Hl HT".
    repeat liRStep; liShow.
    iApply "HT"; done; solve[fail].
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read3 E L (l : loc) π fn ϝ (s : stmt) (T : val → ∀ rt, type rt → rt → iProp Σ) :
    l ◁ₗ[π, Owned false] PlaceIn 42%Z @ (◁ int i32) -∗
    typed_stmt π E L (ExprS (use{IntOp i32} (l)) s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros "Hl".
    repeat liRStep. liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read4 E L (l : loc) π fn ϝ (s : stmt) T :
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn 42%Z) @ (◁ box (int i32)) -∗
    (∀ v, v ◁ᵥ{π} PlaceIn 42%Z @ box (int i32) -∗ l ◁ₗ[π, Owned false] PlaceIn () @ (◁ uninit void*) -∗ typed_stmt π E L s fn [] T ∅ ϝ) -∗
    typed_stmt π E L (ExprS (use{PtrOp} l) s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros "Hl Hc".
    (* we move the box out *)
    repeat liRStep. liShow.
    iApply ("Hc" with "[$] [$]").
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read5 E L (l : loc) π fn ϝ (s : stmt) T κ γ :
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn(PlaceIn 42%Z, γ)) @ (◁ box (mut_ref (int i32) κ)) -∗
    (∀ v, v ◁ᵥ{π} (PlaceIn 42%Z, γ) @ mut_ref (int i32) κ -∗ l ◁ₗ[π, Owned false] PlaceIn (PlaceIn ()) @ (BoxLty (◁ uninit void*)) -∗ typed_stmt π E L s fn [] T ∅ ϝ) -∗
    typed_stmt π E L (ExprS (use{PtrOp} (!{PtrOp} l)) s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros "Hl Hc".
    (* we move out of the box *)
    repeat liRStep. liShow.
    iApply ("Hc" with "[$] [$]").
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read_unblock1 E L (l : loc) π fn ϝ s T γ :
    gvar_pobs γ 42%Z -∗
    l ◁ₗ[π, Owned false] PlaceGhost γ @ (◁ int i32) -∗
    typed_stmt π E L (ExprS (use{IntOp i32} l)%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros "Hobs Hl". repeat liRStep; liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read_unblock2 E L (l : loc) π fn ϝ s T γ :
    gvar_pobs γ (PlaceIn 42%Z) -∗
    l ◁ₗ[π, Owned false] PlaceGhost γ @ BoxLty (◁ int i32) -∗
    typed_stmt π E L (ExprS (use{IntOp i32} (!{PtrOp} l)%E)%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros "Hobs Hl". repeat liRStep; liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_read_unblock3 E (l : loc) π fn ϝ s T γ (γ' : gname) κ :
    gvar_pobs γ (PlaceIn 42%Z, γ') -∗
    l ◁ₗ[π, Owned false] PlaceGhost γ @ MutLty (◁ int i32) κ -∗
    typed_stmt π E [κ ⊑ₗ{0} []] (ExprS (use{IntOp i32} (!{PtrOp} l)%E)%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros "Hobs Hl". repeat liRStep; liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  (** ** Write tests *)
  Lemma test_write1 E L (l : loc) π fn ϝ (s : stmt) (T : val → ∀ rt, type rt → rt → iProp Σ) :
    l ◁ₗ[π, Owned false] PlaceIn 1337%Z @ (◁ int i32) -∗
    typed_stmt π E L (l <-{IntOp i32} (i2v 42 i32); s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros "Hl".
    repeat liRStep; liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  (* does a strong write *)
  Lemma test_write2 E L (l : loc) π fn ϝ (s : stmt) (T : val → ∀ rt, type rt → rt → iProp Σ) :
    l ◁ₗ[π, Owned false] PlaceIn () @ (◁ uninit i32) -∗
    typed_stmt π E L (l <-{IntOp i32} (i2v 42 i32); s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros "Hl".
    repeat liRStep; liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; solve[fail].
  Abort.

  Lemma test_write3 E L (l : loc) π fn γ κ ϝ (s : stmt) (T : val → ∀ rt, type rt → rt → iProp Σ) c :
    L = [κ ⊑ₗ{c} []] →
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn 1337%Z, γ) @ (◁ (mut_ref (int i32) κ)) -∗
    typed_stmt π E L ((!{PtrOp} l) <-{IntOp i32} (i2v 42 i32); s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros (->) "Hl".
    repeat liRStep. liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Abort.

  Lemma test_write_unblock1 E L (l : loc) π fn ϝ (γ γ' : gname) κ (s : stmt) (T : val → ∀ rt, type rt → rt → iProp Σ) c :
    L = [κ ⊑ₗ{c} []] →
    gvar_pobs γ (PlaceIn 1337%Z, γ') -∗
    l ◁ₗ[π, Owned false] PlaceGhost γ  @ (◁ (mut_ref (int i32) κ)) -∗
    typed_stmt π E L ((!{PtrOp} l) <-{IntOp i32} (i2v 42 i32); s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros (->) "Hl".
    repeat liRStep. liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Abort.

  (** ** Borrow tests *)
  Lemma test_borrow1 E L l s fn ϝ T π κ :
    lctx_lft_alive E L κ →
    named_lfts (<["κ" := κ]> ∅) -∗
    l ◁ₗ[π, Owned false] (PlaceIn 1337%Z) @ (◁ (int i32)) -∗
    typed_stmt π E L (ExprS (&ref{Mut, "κ"} l)%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros (Hal) "Hlfts Hl".
    repeat liRStep; liShow.
    Unshelve.
    all: li_unshelve_sidecond; sidecond_hook.
  Abort.

  Lemma test_borrow2 E L l s fn ϝ T π κ κ' γ :
    lctx_lft_alive E L κ →
    lctx_lft_alive E L κ' →
    lctx_lft_incl E L κ κ' →
    named_lfts (<["κ" := κ]> ∅) -∗
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn 1337%Z, γ) @ (◁ (mut_ref (int i32) κ')) -∗
    typed_stmt π E L (ExprS (&ref{Mut, "κ"} (!{PtrOp} l))%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros (Halκ Halκ' Hincl) "Hlfts Hl".
    repeat liRStep. liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Abort.

  Lemma test_borrow3 E L l s fn ϝ T π κ :
    lctx_lft_alive E L κ →
    named_lfts (<["κ" := κ]> ∅) -∗
    l ◁ₗ[π, Owned false] (PlaceIn 1337%Z) @ (◁ ((int i32))) -∗
    typed_stmt π E L (ExprS (&ref{Shr, "κ"} l)%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros (Hal) "Hlfts Hl".
    repeat liRStep. liShow.
    Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Abort.

  (** ** Subtyping *)
  Lemma test_shortenlft E L l s fn ϝ T π κ κ' c :
    L = [κ' ⊑ₗ{c} [κ]] →
    named_lfts (<["κ" := κ]> (<["κ'" := κ']> ∅)) -∗
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn 1337%Z) @ (◁ (shr_ref (int i32) κ)) -∗
    typed_stmt π E L (ExprS (AnnotExpr 0 (ShortenLftAnnot ["κ'"]) (use{PtrOp} l))%E s) fn [] T ∅ ϝ.
  Proof.
    iIntros (->) "Hlfts Hl".
    repeat liRStep; liShow.
    (* somehow, the typeclass search diverges.. *)
    (*
    notypeclasses refine (apply_simpl_and _ _ _ _ _).
    { Set Typeclasses Debug.
      eapply simpland_simplunsafe.
      eapply simpl_and_both_inst.
      eapply simpl_both_rel_inst1.
      (*apply simpl_lookup_insert_map_neq. *)
      refine _.
    }
    *)
    (* using the vm_compute hack in [solve_protected_eq_unfold_tac] makes it work *)
    (*repeat liRStep. liShow.*)
    Unshelve. all: li_unshelve_sidecond; sidecond_hook.
  Abort.

  (* test subtyping on writes below references *)
  Lemma test_subtype1 E L (l l' : loc) π fn ϝ γ γ' γ'' κ κ' κ'' (s : stmt) (T : val → ∀ rt, type rt → rt → iProp Σ) c1 c2 c3:
    L = [κ ⊑ₗ{c1} [κ''; κ']; κ' ⊑ₗ{c2} [κ'']; κ'' ⊑ₗ{c3} []] →
    l ◁ₗ[π, Owned false] PlaceIn (PlaceIn (PlaceIn 1337%Z, γ), γ') @ (◁ (mut_ref (mut_ref (int i32) κ) κ' )) -∗
    l' ◁ₗ[π, Owned false] PlaceIn (PlaceIn 42%Z, γ'') @ (◁ (mut_ref (int i32) κ'')) -∗
    typed_stmt π E L ((!{PtrOp} l) <-{PtrOp} (use{PtrOp} l'); s)%E fn [] T ∅ ϝ.
  Proof.
    iIntros (->) "Hl Hl'".
    do 24 liRStep. liShow.
    (* successfully moves out the reference *)
    repeat liRStep. liShow.
    Unshelve.
    all: li_unshelve_sidecond; sidecond_hook.
  Abort.


  (* TODO unblocking tests *)


End test.
