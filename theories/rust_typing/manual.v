From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Import programs arrays automation value.


(** * Proofmode support for manual proofs *)

Section updateable.
  Context `{!typeGS Σ}.

  Definition updateable (E : elctx) (L : llctx) (T : llctx → iProp Σ) : iProp Σ :=
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={⊤}=∗
    ∃ L2, llctx_interp L2 ∗ T L2.
  Class Updateable (P : iProp Σ) := {
    updateable_E : elctx;
    updateable_L : llctx;
    updateable_core : elctx → llctx → iProp Σ;
    updateable_prove E L : updateable E L (λ L2, updateable_core E L2) -∗ updateable_core E L;
    updateable_eq : updateable_core updateable_E updateable_L ⊣⊢ P
  }.

  Lemma updateable_mono E L T1 T2 :
    updateable E L T1 -∗
    (∀ L, T1 L -∗ T2 L) -∗
    updateable E L T2.
  Proof.
    iIntros "HT Hw".
    iIntros "#CTX #HE HL".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iSpecialize ("Hw" with "HT").
    iExists L2. by iFrame.
  Qed.
  Lemma updateable_intro E L T :
    T L ⊢ updateable E L T.
  Proof.
    iIntros "HT #CTX HE HL".
    iExists L. by iFrame.
  Qed.

  Lemma add_updateable P `{!Updateable P} :
    updateable updateable_E updateable_L (λ L2, updateable_core updateable_E L2) ⊢ P.
  Proof.
    iIntros "HT".
    iApply updateable_eq.
    iApply updateable_prove.
    iApply (updateable_mono with "HT").
    eauto.
  Qed.

  Global Program Instance updateable_typed_val_expr π E L e T :
    Updateable (typed_val_expr π E L e T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := typed_val_expr π E L e T;
  |}.
  Next Obligation.
    iIntros (π _ _ e T E L).
    rewrite /typed_val_expr.
    iIntros "HT" (?) "#CTX #HE HL Hc".
    iApply fupd_wp. iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL Hc").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.

  Global Program Instance updateable_typed_call π E L κs v (P : iProp Σ) vl tys T :
    Updateable (typed_call π E L κs v P vl tys T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := typed_call π E L κs v P vl tys T;
  |}.
  Next Obligation.
    iIntros (π _ _ ? ? ? ? ? ? E L).
    rewrite /typed_call.
    iIntros "HT HP Ha".
    unshelve iApply add_updateable; first apply _.
    iApply (updateable_mono with "HT").
    iIntros (L2) "Hb".
    iApply ("Hb" with "HP Ha").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.


  Global Program Instance updateable_typed_stmt E L s rf R ϝ :
    Updateable (typed_stmt E L s rf R ϝ) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := typed_stmt E L s rf R ϝ;
  |}.
  Next Obligation.
    iIntros (_ _ ? ? ? ? E L).
    iIntros "HT". rewrite /typed_stmt.
    iIntros (?) "#CTX #HE HL Hcont".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL Hcont").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.

  Global Program Instance updateable_updateable E L T :
    Updateable (updateable E L T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := updateable E L T;
    |}.
  Next Obligation.
    iIntros (_ _ ? ? ?) "HT".
    rewrite /updateable.
    iIntros "#CTX #HE HL".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL").
  Qed.
  Next Obligation.
    eauto.
  Qed.

  Lemma fupd_typed_val_expr `{!typeGS Σ} π E L e T :
    (|={⊤}=> typed_val_expr π E L e T) -∗ typed_val_expr π E L e T.
  Proof.
    rewrite /typed_val_expr.
    iIntros "HT" (?) "CTX HE HL Hc".
    iApply fupd_wp. iMod ("HT") as "HT". iApply ("HT" with "CTX HE HL Hc").
  Qed.
  Lemma fupd_typed_call `{!typeGS Σ} π E L κs v (P : iProp Σ) vl tys T :
    (|={⊤}=> typed_call π E L κs v P vl tys T) -∗ typed_call π E L κs v P vl tys T.
  Proof.
    rewrite /typed_call.
    iIntros "HT HP Ha".
    iApply fupd_typed_val_expr. iMod "HT" as "HT". iApply ("HT" with "HP Ha").
  Qed.

  Lemma fupd_typed_stmt `{!typeGS Σ} E L s rf R ϝ :
    ⊢ (|={⊤}=> typed_stmt E L s rf R ϝ) -∗ typed_stmt E L s rf R ϝ.
  Proof.
    iIntros "HT". rewrite /typed_stmt. iIntros (?) "CTX HE HL Hcont".
    iMod ("HT") as "HT". iApply ("HT" with "CTX HE HL Hcont").
  Qed.
End updateable.

Section updateable_rules.
  Context `{!typeGS Σ} {P} `{!Updateable P}.

  Lemma updateable_typed_array_access π l off st :
    find_in_context (FindLoc l π) (λ '(existT _ (lt, r, k)),
      typed_array_access π updateable_E updateable_L l off st lt r k (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        l ◁ₗ[π, k2] #rs2 @ ArrayLtype ty2 len2 iml2 -∗
        (l offsetst{st}ₗ off) ◁ₗ[π, k2] re @ lte -∗
        updateable_core updateable_E L2))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context/=.
    iDestruct "HT" as ([rt [[lt r] k]]) "(Ha & Hb)".
    rewrite /typed_array_access.
    iMod ("Hb" with "[] [] CTX HE HL Ha") as "(%L2 & %k2 & %rt2 & %ty2 & %len & %iml & %rs2 & %rte & %re & %lte & Hl & He & HL & HT)";
    [set_solver.. | ].
    iPoseProof ("HT" with "Hl He") as "Ha".
    iModIntro. iExists _. iFrame.
  Qed.

  Lemma updateable_extract_value π l :
    find_in_context (FindLoc l π) (λ '(existT rt (lt, r, bk)),
      ∃ wl ty r', ⌜bk = Owned wl⌝ ∗ ⌜lt = ◁ty⌝ ∗ ⌜r = #r'⌝ ∗
      prove_with_subtype updateable_E updateable_L false ProveDirect (£ (Nat.b2n wl)) (λ L2 κs R, R -∗
      li_tactic (compute_layout_goal ty.(ty_syn_type)) (λ ly,
      (∀ v3, v3 ◁ᵥ{π} r' @ ty -∗
        l ◁ₗ[π, Owned wl] #v3 @ (◁ value_t (UntypedSynType ly)) -∗
        updateable_core updateable_E L2))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[lt r] bk]]) "(Ha & Hb)"; simpl.
    iDestruct "Hb" as "(%wl & %ty & %r' & -> & -> & -> & HT)".
    rewrite /compute_layout_goal. simpl.
    rewrite /prove_with_subtype.
    iMod ("HT" with "[] [] CTX HE HL") as "(%L2 & %κs & %R & HR & HL & HT)"; [solve_ndisj.. | ].
    iMod ("HR") as "(Hcred & HR)".
    iDestruct ("HT" with "HR") as "(%ly & %Hst & HT)".
    iMod (ofty_own_split_value_untyped_lc with "Hcred Ha") as "Ha"; [done.. | ].
    iDestruct "Ha" as "(%v & Hv & Hl)".
    iPoseProof ("HT" with "Hv Hl") as "HT".
    iModIntro. iExists _. iFrame. 
  Qed.

  (* TODO: add lemma for unfolding / subtyping? *)
End updateable_rules.

Ltac add_updateable :=
  match goal with
  | |- envs_entails _ ?P =>
      unshelve notypeclasses refine (tac_fast_apply (add_updateable P) _);
      [ apply _ | apply _ | ]
  end.
Tactic Notation "apply_update" uconstr(H) :=
  refine (tac_fast_apply H _).

Section test.
  Context `{!typeGS Σ}.

  Lemma updateable_updateable_b (π: thread_id) E L (l : loc) (off : Z) (st : syn_type) :
    ⊢ updateable E L (λ _, True).
  Proof.
    iStartProof.
    add_updateable.
    add_updateable.
    unshelve iApply (updateable_typed_array_access π l off st).
    idtac.
  Abort.

  Lemma typed_s_updateable (π: thread_id) E L s rf R ϝ (l : loc) (off : Z) (st : syn_type) :
    ⊢ typed_stmt E L s rf R ϝ.
  Proof.
    iStartProof.
    unshelve apply_update (updateable_typed_array_access π l off st).
    idtac.
  Abort.
End test.

Lemma tac_typed_val_expr_bind' `{!typeGS Σ} π E L K e T :
  typed_val_expr π E L (W.to_expr e) (λ L' v rt ty r,
    v ◁ᵥ{π} r @ ty -∗ typed_val_expr π E L' (W.to_expr (W.fill K (W.Val v))) T) -∗
  typed_val_expr π E L (W.to_expr (W.fill K e)) T.
Proof.
  iIntros "He".
  rewrite /typed_val_expr.
  iIntros (Φ) "#CTX #HE HL Hcont".
  iApply tac_wp_bind'.
  iApply ("He" with "CTX HE HL").
  iIntros (L' v rt ty r) "HL Hv Hcont'".
  iApply ("Hcont'" with "Hv CTX HE HL"). done.
Qed.
Lemma tac_typed_val_expr_bind `{!typeGS Σ} π E L e Ks e' T :
  W.find_expr_fill e false = Some (Ks, e') →
  typed_val_expr π E L (W.to_expr e') (λ L' v rt ty r,
    if Ks is [] then T L' v rt ty r else
      v ◁ᵥ{π} r @ ty -∗ typed_val_expr π E L' (W.to_expr (W.fill Ks (W.Val v))) T) -∗
  typed_val_expr π E L (W.to_expr e) T.
Proof.
  move => /W.find_expr_fill_correct ->. move: Ks => [|K Ks] //.
  { auto. }
  move: (K::Ks) => {K}Ks. by iApply tac_typed_val_expr_bind'.
Qed.

Tactic Notation "typed_val_expr_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (typed_val_expr ?π ?E ?L ?e ?T) =>
    let e' := W.of_expr e in change (typed_val_expr π E L e T) with (typed_val_expr π E L (W.to_expr e') T);
    iApply tac_typed_val_expr_bind; [done |];
    unfold W.to_expr; simpl
  | _ => fail "typed_val_expr_bind: not a 'typed_val_expr'"
  end.

Lemma tac_typed_stmt_bind `{!typeGS Σ} π E L s e Ks fn ϝ T :
  W.find_stmt_fill s = Some (Ks, e) →
  typed_val_expr π E L (W.to_expr e) (λ L' v rt ty r,
    v ◁ᵥ{π} r @ ty -∗ typed_stmt E L' (W.to_stmt (W.stmt_fill Ks (W.Val v))) fn T ϝ) -∗
  typed_stmt E L (W.to_stmt s) fn T ϝ.
Proof.
  move => /W.find_stmt_fill_correct ->. iIntros "He".
  rewrite /typed_stmt.
  iIntros (?) "#CTX #HE HL Hcont".
  rewrite stmt_wp_eq. iIntros (? rf ?) "?".
  have [Ks' HKs']:= W.stmt_fill_correct Ks rf. rewrite HKs'.
  iApply wp_bind.
  iApply (wp_wand with "[He HL]").
  { rewrite /typed_val_expr. iApply ("He" with "CTX HE HL").
    iIntros (L' v rt ty r) "HL Hv Hcont".
    iApply ("Hcont" with "Hv CTX HE HL"). }
  iIntros (v) "HWP".
  rewrite -(HKs' (W.Val _)) /W.to_expr.
  iSpecialize ("HWP" with "Hcont").
  rewrite stmt_wp_eq/stmt_wp_def/=.
  iApply "HWP"; done.
Qed.

Tactic Notation "typed_stmt_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (typed_stmt ?E ?L ?s ?fn ?R ?ϝ) =>
    let s' := W.of_stmt s in change (typed_stmt E L s fn R ϝ) with (typed_stmt E L (W.to_stmt s') fn R ϝ);
    iApply tac_typed_stmt_bind; [done |];
    unfold W.to_expr, W.to_stmt; simpl; unfold W.to_expr; simpl
  | _ => fail "typed_stmt_bind: not a 'typed_stmt'"
  end.

Lemma intro_typed_stmt `{!typeGS Σ} fn R ϝ E L s Φ :
  rrust_ctx -∗
  elctx_interp E -∗
  llctx_interp L -∗
  (∀ (L' : llctx) (v : val), llctx_interp L' -∗ ([∗ list] l ∈ rf_locs fn, l.1 ↦|l.2|) -∗ R v L' -∗ Φ v) -∗
  typed_stmt E L s fn R ϝ -∗
  WPs s {{ f_code (rf_fn fn), Φ }}.
Proof.
  iIntros "#CTX #HE HL Hcont Hs".
  rewrite /typed_stmt.
  iApply ("Hs" with "CTX HE HL Hcont").
Qed.

Ltac to_typed_stmt SPEC :=
  iStartProof;
  lazymatch goal with
  | FN : runtime_function |- envs_entails _ (WPs ?s {{ ?code, ?c }}) =>
    iApply (intro_typed_stmt FN with SPEC)
  end.
