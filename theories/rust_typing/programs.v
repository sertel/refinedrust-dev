From caesium Require Import lang proofmode derived lifting.
From refinedrust Require Export base type ltypes lft_contexts annotations ltype_rules.
Set Default Proof Using "Type".


Section named_lfts.
  Context `{typeGS Σ}.
  (** [named_lfts] is a construct used by the automation to map annotated lifetime names to concrete Coq names.
    This does not have a semantic meaning: we can in principle change this map arbitrarily, the worst thing that
    can happen is that the automation will make the goal unprovable.
    Invariant: there is a global singleton around.
   *)
  (* TODO: find a better way to seal this off and hide it from basic automation. *)
  Definition named_lfts (M : gmap string lft) : iProp Σ := True -∗ True.
  Lemma named_lfts_update M M' : named_lfts M -∗ named_lfts M'.
  Proof. auto. Qed.
  Definition lookup_named_lfts (M : gmap string lft) (lfts : list string) :=
    foldr (λ s oacc, acc ← oacc; κ ← M !! s; Some (κ :: acc)) (Some []) lfts.

  Lemma named_lfts_init (M : gmap string lft) : ⊢ named_lfts M.
  Proof. unfold named_lfts. iIntros "_". done. Qed.

  (* Making it opaque so that simplification doesn't get stuck with it *)
  Definition named_lft_update (name : string) (κ : lft) (M : gmap string lft) :=
    <[name := κ]> (M).

  Definition named_lft_delete (name : string) (M : gmap string lft) :=
    delete name M.
End named_lfts.
(* make opaque so that automation does not do weird things (this should not be persistent, etc.) *)
Global Typeclasses Opaque named_lfts.
Global Opaque named_lfts.
Global Arguments named_lfts : simpl never.
Global Opaque named_lft_update.
Global Opaque named_lft_delete.

Section named_tyvars.
  Context `{!typeGS Σ}.

  Definition TYVAR_MAP (m : gmap string (sigT type)) : Set := unit.
  Arguments TYVAR_MAP : simpl never.
End named_tyvars.

(** Instances for Lithium to put things into the persistent context *)
Section intro_persistent.
  Context `{!typeGS Σ}.

  Global Instance lft_dead_intro_pers κ : IntroPersistent ([† κ]) ([† κ]).
  Proof. constructor. iIntros "#$". Qed.
  Global Instance gvar_pobs_intro_pers {T} γ (x : T) : IntroPersistent (gvar_pobs γ x) (gvar_pobs γ x).
  Proof. constructor. iIntros "#$". Qed.
  Global Instance ty_sidecond_intro_pers {rt} (ty : type rt) : IntroPersistent (ty_sidecond ty) (ty_sidecond ty).
  Proof. constructor. iIntros "#$". Qed.
End intro_persistent.

Section credits.
  Context `{typeGS Σ}.

  (* We require at least one credit here so that the majority of clients does not need any sideconditions.
    We require at least one atime here, as place accesses will use the receipt every step gains for boosting, so we need to have at least one here to regenerate a potential credit we use.
   *)
  Definition credit_store_def (n m : nat) : iProp Σ :=
    £(S n) ∗ atime (S m).
  Definition credit_store_aux : seal (@credit_store_def). by eexists. Qed.
  Definition credit_store := unseal credit_store_aux.
  Definition credit_store_eq : @credit_store = @credit_store_def := seal_eq credit_store_aux.

  Lemma credit_store_acc (n m : nat) :
    credit_store n m -∗
    £ (S n) ∗ atime (S m) ∗ (∀ n' m', £ (S n') -∗ atime (S m') -∗ credit_store n' m').
  Proof.
    rewrite credit_store_eq /credit_store_def.
    iIntros "($ & $)". eauto with iFrame.
  Qed.

  (* allows direct access to one credit, and after regenerating some (usually m' = 0 or m' = 1), we get back *)
  Lemma credit_store_get_reg (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ atime (S m) ∗ (∀ m', £ (1 + m' + m) -∗ atime (1 + m' + m) -∗ credit_store (m' + m + n) (m' + m)).
  Proof.
    iIntros "Hst". iPoseProof (credit_store_acc with "Hst") as "(Hcred & $ & Hcl)".
    rewrite lc_succ. iDestruct "Hcred" as "($ & Hcred)".
    iIntros (m') "Hcred' Hc".
    iPoseProof (lc_split with "[$Hcred' $Hcred]") as "Hcred".
    iApply ("Hcl" with "Hcred Hc").
  Qed.

  (* the two common instantiations of this *)
  Lemma credit_store_get_reg0 (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ atime (S m) ∗ (£ (1 + m) -∗ atime (S m) -∗ credit_store (m + n) (m)).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_get_reg with "Hst") as "($ & $ & Hcl)".
    iApply "Hcl".
  Qed.
  Lemma credit_store_get_reg1 (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ atime (S m) ∗ (£ (S (S m)) -∗ atime (S (S m)) -∗ credit_store (1 + m + n) (1 + m)).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_get_reg with "Hst") as "($ & $ & Hcl)".
    iApply ("Hcl" $! 1%nat).
  Qed.

  Lemma credit_store_borrow_receipt (n m : nat) :
    credit_store n m -∗
    atime 1 ∗ (atime 1 -∗ credit_store n m).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    rewrite additive_time_receipt_succ. iDestruct "Hat" as "(Hat1 & Hat)".
    iFrame. iIntros "Hat1".
    iApply ("Hcl" with "Hcred [Hat1 Hat]").
    iApply additive_time_receipt_succ. iFrame.
  Qed.

  Lemma credit_store_borrow (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ atime 1 ∗ (£ 1 -∗ atime 1 -∗ credit_store n m).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    rewrite additive_time_receipt_succ. iDestruct "Hat" as "(Hat1 & Hat)".
    rewrite lc_succ. iDestruct "Hcred" as "(Hc1 & Hc)".
    iFrame. iIntros "Hc1 Hat1".
    iApply ("Hcl" with "[Hc Hc1] [Hat1 Hat]").
    { iApply lc_succ. iFrame. }
    iApply additive_time_receipt_succ. iFrame.
  Qed.

  (* allows direct access to credits, but without regenerating and instead requires to prove a sidecondition *)
  Lemma credit_store_scrounge (n m k : nat) :
    n ≥ k →
    credit_store n m -∗
    £ k ∗ credit_store (n - k) m.
  Proof.
    iIntros (?) "Hst". iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hc & Hcl)".
    replace (S n)%nat with (S (n - k) + k)%nat by lia.
    rewrite lc_split. iDestruct "Hcred" as "(Hcred & $)".
    iApply ("Hcl" with "Hcred Hc").
  Qed.
  Lemma credit_store_donate n m k :
    credit_store n m -∗ £ k -∗ credit_store (k + n) m.
  Proof.
    iIntros "Hst Hcred0".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    iApply ("Hcl" with "[Hcred0 Hcred] Hat").
    iApply lc_succ. iDestruct "Hcred" as "($ & ?)".
    rewrite lc_split. iFrame.
  Qed.
  Lemma credit_store_donate_atime n m k :
    credit_store n m -∗ atime k -∗ credit_store n (k + m).
  Proof.
    iIntros "Hst Hat0".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    iApply ("Hcl" with "Hcred [Hat Hat0]").
    rewrite -Nat.add_succ_r. rewrite additive_time_receipt_sep. iFrame.
  Qed.

  Lemma credit_store_mono (n m n' m' : nat) :
    n' ≤ n → m' ≤ m → credit_store n m -∗ credit_store n' m'.
  Proof.
    rewrite credit_store_eq/credit_store_def.
    iIntros (??) "(Ha & Hb)".
    iSplitL "Ha". { iApply lc_weaken; last done. lia. }
    iApply additive_time_receipt_mono; last done. lia.
  Qed.
End credits.

Section option_map.
  Context `{!typeGS Σ}.

  Definition option_combine {A B} (a : option A) (b : option B) : option (A * B) :=
    match a, b with
    | Some a, Some b => Some (a, b)
    | _, _ => None
    end.
  Lemma option_combine_Some {A B} (a : option A) (b : option B) c :
    option_combine a b = Some c →
    ∃ a' b', a = Some a' ∧ b = Some b' ∧ c = (a', b').
  Proof.
    rewrite /option_combine. destruct a, b; naive_solver.
  Qed.
  Lemma option_combine_None {A B} (a : option A) (b : option B) :
    option_combine a b = None →
    a = None ∨ b = None.
  Proof.
    rewrite /option_combine. destruct a, b; naive_solver.
  Qed.

  Definition typed_option_map {A R} (o : option A) (Φ : A → (R → iProp Σ) → iProp Σ) (d : R) (T : R → iProp Σ) :=
    match o with
    | Some o => Φ o T
    | None => T d
    end.
  Class TypedOptionMap {A R} (o : option A) (Φ : A → (R → iProp Σ) → iProp Σ) (d : R) :=
    typed_option_map_proof T : iProp_to_Prop (typed_option_map o Φ d T).
  Lemma typed_option_map_some {A R} (a : A) Φ (d : R) T :
    Φ a T ⊢ typed_option_map (Some a) Φ d T.
  Proof. rewrite /typed_option_map. iIntros "$". Qed.
  Global Instance typed_option_map_some_inst {A R} (a : A) Φ (d : R) : TypedOptionMap (Some a) Φ d :=
    λ T, i2p (typed_option_map_some a Φ d T).
  Lemma typed_option_map_none {A R} (Φ : A → (R → iProp Σ) → iProp Σ) (d : R) T :
    T d ⊢ typed_option_map None Φ d T.
  Proof. rewrite /typed_option_map. eauto. Qed.
  Global Instance typed_option_map_none_inst {A R} (Φ : A → (R → iProp Σ) → iProp Σ) d : TypedOptionMap None Φ d :=
    λ T, i2p (typed_option_map_none Φ d T).

  (* If we can find a common predicate [P] that should be satisfied by [r], we can eliminate into that. *)
  Lemma typed_option_map_elim {A R} (o : option A) (d : R) (Φ : A → (R → iProp Σ) → iProp Σ) (P : R → iProp Σ) (F : iProp Σ) T :
    typed_option_map o Φ d T -∗
    (∀ a, ⌜o = Some a⌝ -∗ F -∗ Φ a T -∗ ∃ r, F ∗ P r ∗ T r) -∗
    P d -∗
    F -∗
    (∃ r, F ∗ P r ∗ T r).
  Proof.
    iIntros "Ha Helim1 Helim2 HF".
    rewrite /typed_option_map.
    destruct o as [ a | ].
    - iPoseProof ("Helim1" with "[//] HF Ha") as "(%r & HF & HP & HT)". iExists r. iFrame.
    - iExists d. iFrame.
  Qed.
  Lemma typed_option_map_elim_fupd {A R E} (o : option A) (d : R) (Φ : A → (R → iProp Σ) → iProp Σ) (P : R → iProp Σ) (F : iProp Σ) T :
    lftE ⊆ E →
    typed_option_map o Φ d T -∗
    (∀ a, ⌜o = Some a⌝ -∗ F -∗ Φ a T ={E}=∗ ∃ r, F ∗ P r ∗ T r) -∗
    P d -∗
    F ={E}=∗
    (∃ r, F ∗ P r ∗ T r).
  Proof.
    iIntros (?) "Ha Helim1 Helim2 HF".
    rewrite /typed_option_map.
    destruct o as [ a | ].
    - iMod ("Helim1" with "[//] HF Ha") as "(%r & HF & HP & HT)". iExists r. by iFrame.
    - iModIntro. iExists d. iFrame.
  Qed.
End option_map.
Global Hint Mode TypedOptionMap + + + ! - - : typeclass_instances.

(** find type of val in context *)
Definition FindVal `{!typeGS Σ} (v : val) (π : thread_id) :=
  {| fic_A := @sigT Type (λ rt, type rt * rt)%type; fic_Prop '(existT rt (ty, r)) := (v ◁ᵥ{π} r @ ty)%I; |}.
Global Typeclasses Opaque FindVal.

(** find type of val in context -- also allows to find location assignments by accepting an arbitrary prop [P].
  Thus, this is used mostly for RelatedTo/Subsume *)
Definition FindValP `{!typeGS Σ} (v : val) (π : thread_id) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindValP.

(** find type of val with known rt in context *)
Definition FindValWithRt `{!typeGS Σ} (rt : Type) (v : val) (π : thread_id) :=
  {| fic_A := (type rt * rt)%type; fic_Prop '(ty, r) := (v ◁ᵥ{π} r @ ty)%I; |}.
Global Typeclasses Opaque FindValWithRt.

(** find type of location in context *)
Definition FindLoc `{!typeGS Σ} (l : loc) (π : thread_id) :=
  {| fic_A := @sigT Type (λ rt, ltype rt * (place_rfn rt) * bor_kind)%type; fic_Prop '(existT rt (lt, r, b)) := (l ◁ₗ[π, b] r @ lt)%I; |}.
Global Typeclasses Opaque FindLoc.

Definition FindOptLoc `{!typeGS Σ} (l : loc) (π : thread_id) :=
  {| fic_A := option (@sigT Type (λ rt, ltype rt * (place_rfn rt) * bor_kind)%type); fic_Prop a :=
      match a with Some (existT rt (lt, r, b)) => (l ◁ₗ[π, b] r @ lt)%I | _ => True%I end; |}.
Global Typeclasses Opaque FindOptLoc.

(** Find freeable_nz for a location *)
Definition FindFreeable `{!typeGS Σ} (l : loc) :=
  {| fic_A := (nat * Qp * alloc_kind); fic_Prop '(size, q, kind) := freeable_nz l size q kind |}.
Global Typeclasses Opaque FindFreeable.

(** find type of location in context -- more flexible by accepting an arbitrary prop [P].
  Thus, this is used mostly for RelatedTo/Subsume *)
Definition FindLocP `{!typeGS Σ} (l : loc) (π : thread_id) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindLocP.

(** find type of location with known rt in context *)
Definition FindLocWithRt `{!typeGS Σ} (rt : Type) (l : loc) (π : thread_id) :=
  {| fic_A := (ltype rt * (place_rfn rt) * bor_kind)%type; fic_Prop '(lt, r, b) := (l ◁ₗ[π, b] r @ lt)%I; |}.
Global Typeclasses Opaque FindLocWithRt.

(** find a loc_in_bounds fact for l.
   We also allow other propositions [P], in particular location ownership,
   and will handle them using subsume instances. *)
Definition FindLocInBounds `{!typeGS Σ} (l : loc) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindLocInBounds.

(** find the named lifetime judgment *)
Definition FindNamedLfts `{!typeGS Σ} :=
  {| fic_A := gmap string lft; fic_Prop M := (named_lfts (Σ := Σ) M)%I; |}.
Global Typeclasses Opaque FindNamedLfts.

(** find the credit store *)
Definition FindCreditStore `{!typeGS Σ} :=
  {| fic_A := nat * nat; fic_Prop '(n, m) := credit_store n m; |}.
Global Typeclasses Opaque FindCreditStore.

(** find a lft dead token *)
Definition FindOptLftDead `{!typeGS Σ} (κ : lft) :=
  {| fic_A := bool; fic_Prop b := (if b then [† κ] else True)%I; |}.
Global Typeclasses Opaque FindOptLftDead.

(** attempt to find an observation, or give up if there is none *)
Definition FindOptGvarPobs `{!typeGS Σ} (γ : gname) :=
  {| fic_A := (@sigT Type (λ rt, rt) + unit)%type;
    fic_Prop a :=
      match a with
      | inl (existT rt r) => (gvar_pobs γ r)%I
      | inr _ => True%I
      end
  |}.
Global Typeclasses Opaque FindOptGvarPobs.

(** find an observation on a ghost variable *)
(** NOTE: Ideally, we would also fix the type beforehand.
  However, that leads to universe trouble when using the definition that I have not yet figured out.
*)
Definition FindGvarPobs `{!typeGS Σ} (γ : gname) :=
  {| fic_A := (@sigT Type (λ rt, rt))%type;
    fic_Prop '(existT rt r) := (gvar_pobs γ r)%I
  |}.
Global Typeclasses Opaque FindGvarPobs.
Definition FindGvarPobsP `{!typeGS Σ} (γ : gname) :=
  {| fic_A := iProp Σ;
    fic_Prop P := P
  |}.
Global Typeclasses Opaque FindGvarPobsP.

(** Find a relation with the given gvar on the right hand side. *)
Definition FindOptGvarRel `{!typeGS Σ} (γ : gname) :=
  {| fic_A := (@sigT Type (λ rt, gname * (rt → rt → Prop)) + unit)%type;
    fic_Prop a :=
      match a with
      | inl (existT rt (γ', R)) => (Rel2 γ' γ R)%I
      | inr _ => True%I
      end
  |}.
Global Typeclasses Opaque FindOptGvarRel.



Definition FindInherit `{!typeGS Σ} {K} (κ : lft) (key : K) (P : iProp Σ) :=
  {| fic_A := unit;
     fic_Prop _ := Inherit κ key P;
  |}.
Global Typeclasses Opaque FindInherit.

(** Find a type assignment for a location [l] that may be part of a larger type assignment -- e.g. if [l] offsets into an array, this will find a type assignment for an array whose memory range includes [l].

   Note that the obligation stated here does not require that [l] and the actually found here are in any way related -- rather, this will be enforced by the corresponding [FindHypEqual] with a custom [FICRelated] key, defined in [automation/loc_related.v].
   The client needing this information will have to spawn a sidecondition (re-)proving it.
*)
Definition FindRelatedLoc `{!typeGS Σ} (π : thread_id) :=
  {| fic_A := @sigT Type (λ rt, loc * ltype rt * (place_rfn rt) * bor_kind)%type;
     fic_Prop '(existT rt (l', lt, r, b)) := (l' ◁ₗ[π, b] r @ lt)%I;
  |}.
Global Typeclasses Opaque FindRelatedLoc.


(** A judgment to trigger TC search on [H] for some output [a : A]. *)
Definition trigger_tc `{!typeGS Σ} {A} (H : A → Type) (T : A → iProp Σ) : iProp Σ :=
  ∃ (a : A) (x : H a), T a.

Section judgments.
  Context `{typeGS Σ}.

  Class SimplifyHypPlace (l : loc) (π : thread_id) {rt} (ty : type rt) (r : place_rfn rt) (n : option N) : Type :=
    simplify_hyp_place :: SimplifyHyp (l ◁ₗ[π, Owned false] r @ (◁ ty)%I) n.
  Global Hint Mode SimplifyHypPlace + + + + + - : typeclass_instances.
  Class SimplifyHypVal (v : val) (π : thread_id) {rt} (ty : type rt) (r : rt) (n : option N) : Type :=
    simplify_hyp_val :: SimplifyHyp (v ◁ᵥ{π} r @ ty) n.
  Global Hint Mode SimplifyHypVal + + + + + - : typeclass_instances.

  Class SimplifyGoalPlace (l : loc) π (b : bor_kind) {rt} (lty : ltype rt) (r : place_rfn rt) (n : option N) : Type :=
    simplify_goal_place :: SimplifyGoal (l ◁ₗ[π, b] r @ lty) n.
  Global Hint Mode SimplifyGoalPlace + + + - - - - : typeclass_instances.
  Class SimplifyGoalVal (v : val) π {rt} (ty : type rt) (r : rt) (n : option N) : Type :=
    simplify_goal_val :: SimplifyGoal (v ◁ᵥ{π} r @ ty) n.
  Global Hint Mode SimplifyGoalVal + + - - - - : typeclass_instances.

  (** Notion of [subsume] with support for lifetime contexts + executing updates *)
  Definition subsume_full (E : elctx) (L : llctx) (step : bool) (P : iProp Σ) (Q : iProp Σ) (T : llctx → iProp Σ → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      P -∗ |={F}=>
      ∃ L' R, maybe_logical_step step F (Q ∗ R) ∗ llctx_interp L' ∗ T L' R.
  Class SubsumeFull (E : elctx) (L : llctx) (step : bool) (P Q : iProp Σ) : Type :=
    subsume_full_proof T : iProp_to_Prop (subsume_full E L step P Q T).

  Lemma subsume_full_id E L step P T :
    T L True ⊢ subsume_full E L step P P T.
  Proof.
    iIntros "HT" (???) "CTX HE HL ?".
    iExists L, True%I. iFrame.
    iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance subsume_full_id_inst E L step (P : iProp Σ) : SubsumeFull E L step P P := λ T, i2p (subsume_full_id E L step P T).

  Lemma subsume_full_subsume E L step P Q T :
    subsume P Q (T L True) ⊢
    subsume_full E L step P Q T.
  Proof.
    iIntros "Hsub" (???) "#CTX #HE HL HP". iPoseProof ("Hsub" with "HP") as "(HQ & HT)".
    iExists L, True%I; iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  (* low priority, should not trigger when there are other more specific instances *)
  Global Instance subsume_full_subsume_inst E L step P Q : SubsumeFull E L step P Q | 2000 :=
    λ T, i2p (subsume_full_subsume E L step P Q T).

  Class SubsumeFullPlace (E : elctx) (L : llctx) (step : bool) (l : loc) (π : thread_id) (b : bor_kind) {rt1} (ty1 : ltype rt1) (r1 : place_rfn rt1) {rt2} (ty2 : ltype rt2) (r2 : place_rfn rt2) : Type :=
    subsume_full_place :: SubsumeFull E L step (l ◁ₗ[π, b] r1 @ ty1) (l ◁ₗ[π, b] r2 @ ty2).
  Global Hint Mode SubsumeFullPlace + + + + + + ! ! ! - - - : typeclass_instances.
  Class SubsumeFullVal (π : thread_id) (E : elctx) (L : llctx) (step : bool) (v : val) {rt1} (ty1 : type rt1) (r1 : rt1) {rt2} (ty2 : type rt2) (r2 : rt2) : Type :=
    subsume_full_val :: SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2).
  Global Hint Mode SubsumeFullVal + + + + + ! ! ! - - - : typeclass_instances.

  (** *** Expressions *)

  (** Typing of values *)
  Definition typed_value (v : val) π (T : ∀ rt, type rt → rt → iProp Σ) : iProp Σ :=
    (rrust_ctx -∗ ∃ rt (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T rt ty r).
  Class TypedValue (v : val) π : Type :=
    typed_value_proof T : iProp_to_Prop (typed_value v π T).

  (** Typing of value expressions (unfolding [typed_value] for easier usage) *)
  Definition typed_val_expr_cont_t := llctx → val → ∀ (rt : Type), type rt → rt → iProp Σ.
  Definition typed_val_expr π (E : elctx) (L : llctx) (e : expr) (T : typed_val_expr_cont_t) : iProp Σ :=
    (∀ Φ, rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      (∀ L' v rt (ty : type rt) r, llctx_interp L' -∗ na_own π shrE -∗ v ◁ᵥ{π} r @ ty -∗ T L' v rt ty r -∗ Φ v) -∗
    WP e {{ Φ }}).

  (** Typing of binary op expressions *)
  Definition typed_bin_op (π : thread_id) (E : elctx) (L : llctx) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ)
    (o : bin_op) (ot1 ot2 : op_type) (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr π E L (BinOp o ot1 ot2 v1 v2) T).
  Class TypedBinOp (π : thread_id) (E : elctx) (L : llctx) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_bin_op_proof T : iProp_to_Prop (typed_bin_op π E L v1 P1 v2 P2 o ot1 ot2 T).

  (* class for instances specialized to value ownership *)
  Class TypedBinOpVal (π : thread_id) (E : elctx) (L : llctx) (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1) (v2 : val) {rt2} (ty2 : type rt2) (r2 : rt2) (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_bin_op_val :: TypedBinOp π E L v1 (v1 ◁ᵥ{π} r1 @ ty1) v2 (v2 ◁ᵥ{π} r2 @ ty2) o ot1 ot2.
  Global Hint Mode TypedBinOpVal + + + + + + + + + + + + + + : typeclass_instances.

  (** Typing of unary op expressions *)
  Definition typed_un_op_cont_t := llctx → val → ∀ rt : Type, type rt → rt → iProp Σ.
  Definition typed_un_op (π : thread_id) (E : elctx) (L : llctx) (v : val) (P : iProp Σ) (o : un_op) (ot : op_type)
    (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) : iProp Σ :=
    (P -∗ typed_val_expr π E L (UnOp o ot v) T).
  Class TypedUnOp π (E : elctx) (L : llctx) (v : val) (P : iProp Σ) (o : un_op) (ot : op_type) : Type :=
    typed_un_op_proof T : iProp_to_Prop (typed_un_op π E L v P o ot T).

  (* class for instances specialized to value ownership *)
  Class TypedUnOpVal π (E : elctx) (L : llctx) (v : val) {rt} (ty : type rt) (r : rt) (o : un_op) (ot : op_type) : Type :=
    typed_un_op_val :: TypedUnOp π E L v (v ◁ᵥ{π} r @ ty) o ot.
  Global Hint Mode TypedUnOpVal + + + + + + + + + : typeclass_instances.

  (** Typed call expressions, assuming a list of argument values with given types and refinements.
    [P] may state additional preconditions on the function. *)
  Definition typed_call π E L (eκs : list lft) (v : val) (P : iProp Σ) (vl : list val) (tys : list (sigT (λ rt, type rt * rt)%type)) (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) : iProp Σ :=
    (P -∗
     ([∗ list] v;rt∈vl;tys, let '(existT rt (ty, r)) := rt in v ◁ᵥ{π} r @ ty) -∗
     typed_val_expr π E L (Call v (Val <$> vl)) T)%I.
  Class TypedCall π (E : elctx) (L : llctx) (eκs : list lft) (v : val) (P : iProp Σ) (vl : list val) (tys : list (sigT (λ rt, type rt * rt)%type)) : Type :=
    typed_call_proof T : iProp_to_Prop (typed_call π E L eκs v P vl tys T).

  Definition typed_if (E : elctx) (L : llctx) (v : val) (P T1 T2 : iProp Σ) : iProp Σ :=
    (P -∗ ∃ b, ⌜val_to_bool v = Some b⌝ ∗ (if b then T1 else T2)).
  Class TypedIf E L (v : val) (P : iProp Σ) : Type :=
    typed_if_proof T1 T2 : iProp_to_Prop (typed_if E L v P T1 T2).

  (** Typing of annotated expressions -- annotation determined by the [A]*)
  (* A is the annotation from the code *)
  Definition typed_annot_expr_cont_t := llctx → val → ∀ (rt : Type), type rt → rt → iProp Σ.
  Definition typed_annot_expr (π : thread_id) (E : elctx) (L : llctx) (n : nat) {A} (a : A) (v : val) (P : iProp Σ) (T : typed_annot_expr_cont_t) : iProp Σ :=
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ P ={⊤}[∅]▷=∗^n |={⊤}=> ∃ L2 rt (ty : type rt) r, llctx_interp L2 ∗ v ◁ᵥ{π} r @ ty ∗ T L2 v rt ty r).
  Class TypedAnnotExpr (π : thread_id) (E : elctx) (L : llctx) (n : nat) {A} (a : A) (v : val) (P : iProp Σ) : Type :=
    typed_annot_expr_proof T : iProp_to_Prop (typed_annot_expr π E L n a v P T).

  Definition enter_cache_hint (P : Prop) := P.
  Global Arguments enter_cache_hint : simpl never.
  Global Typeclasses Opaque enter_cache_hint.

  (** Learn from a hypothesis on introduction with [introduce_with_hooks], defined below *)
  Class LearnFromHyp (P : iProp Σ) := {
    learn_from_hyp_Q : iProp Σ;
    learn_from_hyp_pers :: Persistent (learn_from_hyp_Q);
    learn_from_hyp_proof :
      ∀ F, ⌜lftE ⊆ F⌝ -∗ P ={F}=∗ P ∗ learn_from_hyp_Q;
  }.

  Class LearnFromHypVal {rt} (ty : type rt) (r : rt) := {
    learn_from_hyp_val_Q : iProp Σ;
    learn_from_hyp_val_pers :: Persistent (learn_from_hyp_val_Q);
    learn_from_hyp_val_proof :
      ∀ F π v, ⌜lftE ⊆ F⌝ -∗ v ◁ᵥ{π} r @ ty ={F}=∗ v ◁ᵥ{π} r @ ty ∗ learn_from_hyp_val_Q;
  }.
  Global Program Instance learn_hyp_val π v {rt} (ty : type rt) r :
    LearnFromHypVal ty r → LearnFromHyp (v ◁ᵥ{π} r @ ty) :=
    λ H, {| learn_from_hyp_Q := learn_from_hyp_val_Q |}.
  Next Obligation. intros π v rt ty r [Q HQ]. done. Qed.

  Global Program Instance learn_hyp_place_owned π l {rt} (ty : type rt) r :
    LearnFromHypVal ty r → LearnFromHyp (l ◁ₗ[π, Owned false] #r @ (◁ ty))%I | 10 :=
    λ H, {| learn_from_hyp_Q := learn_from_hyp_val_Q ∗ ∃ ly, ⌜use_layout_alg (ty_syn_type ty) = Some ly⌝ ∗ ⌜enter_cache_hint (l `has_layout_loc` ly)⌝ ∗ loc_in_bounds l 0 (ly_size ly) |}.
  Next Obligation.
    intros π l rt ty r [Q ? HQ] F.
    iIntros (?) "Hl". simpl.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & % & ? & #Hlb & ? & %r' & -> & HT)".
    iMod (fupd_mask_mono with "HT") as "(%v & Hl & Hv)"; first done.
    iMod (HQ with "[//] Hv") as "(Hv & #HQ')".
    iSplitL. { iModIntro. iExists _. iFrame. iR. iR. iR. iExists _. iR.
      iModIntro. eauto 8 with iFrame. }
    iModIntro. iFrame "HQ'". iExists _. iFrame "Hlb".
    rewrite /enter_cache_hint. done.
  Qed.

  (* Lower-priority instance for other ownership modes and place types *)
  Global Program Instance learn_hyp_place_layout π l k {rt} (lt : ltype rt) r :
    LearnFromHyp (l ◁ₗ[π, k] r @ lt)%I | 20 :=
    {| learn_from_hyp_Q := ∃ ly, ⌜use_layout_alg (ltype_st lt) = Some ly⌝ ∗ ⌜enter_cache_hint (l `has_layout_loc` ly)⌝ ∗ loc_in_bounds l 0 (ly_size ly)  |}.
  Next Obligation.
    intros π l k rt lt r F.
    iIntros (?) "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst & %Hl)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iModIntro. iFrame. iExists _. iFrame "Hlb".
    rewrite /enter_cache_hint. iPureIntro. eauto.
  Qed.

  Global Program Instance learn_hyp_loc_in_bounds l off1 off2 :
    LearnFromHyp (loc_in_bounds l off1 off2)%I | 10 :=
    {| learn_from_hyp_Q := ⌜enter_cache_hint (0 < l.2 - off1)%Z⌝ ∗ ⌜enter_cache_hint (l.2 + off2 ≤ MaxInt usize_t)%Z⌝ |}.
  Next Obligation.
    iIntros (l off1 off2 ? ?) "Hlb".
    iPoseProof (loc_in_bounds_ptr_in_range with "Hlb") as "%Hinrange".
    iFrame. iModIntro. iPureIntro.
    move: Hinrange. rewrite /min_alloc_start /enter_cache_hint.
    split; first lia.
    rewrite MaxInt_eq.
    specialize (max_alloc_end_le_usize). lia.
  Qed.

  (** * Introduce a proposition containing tokens that we want to directly return *)
  (* TODO also thread na tokens through here *)
  Definition introduce_with_hooks (E : elctx) (L : llctx) (P : iProp Σ) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L -∗ P ={F}=∗ ∃ L', llctx_interp L' ∗ T L'.
  Class IntroduceWithHooks (E : elctx) (L : llctx) (P : iProp Σ) : Type :=
    introduce_with_hooks_proof T : iProp_to_Prop (introduce_with_hooks E L P T).

  Lemma introduce_with_hooks_sep E L P1 P2 T :
    introduce_with_hooks E L P1 (λ L', introduce_with_hooks E L' P2 T) ⊢
    introduce_with_hooks E L (P1 ∗ P2) T.
  Proof.
    iIntros "Ha" (F ?) "#HE HL [HP1 HP2]".
    iMod ("Ha" with "[//] HE HL HP1") as "(%L' & HL & Ha)".
    iApply ("Ha" with "[//] HE HL HP2").
  Qed.
  Global Instance introduce_with_hooks_sep_inst E L P1 P2 : IntroduceWithHooks E L (P1 ∗ P2) :=
    λ T, i2p (introduce_with_hooks_sep E L P1 P2 T).

  Lemma introduce_with_hooks_exists {X} E L (Φ : X → iProp Σ) T :
    (∀ x, introduce_with_hooks E L (Φ x) T) ⊢
    introduce_with_hooks E L (∃ x, Φ x) T.
  Proof.
    iIntros "Ha" (F ?) "#HE HL (%x & HP)".
    iApply ("Ha" with "[//] HE HL HP").
  Qed.
  Global Instance introduce_with_hooks_exists_inst {X} E L (Φ : X → iProp Σ) : IntroduceWithHooks E L (∃ x, Φ x) :=
    λ T, i2p (introduce_with_hooks_exists E L Φ T).

  (* low priority base instances so that other more specialized instances trigger first *)
  Lemma introduce_with_hooks_base_learnable E L P T `{HP : LearnFromHyp P} :
    (P -∗ introduce_with_hooks E L (learn_from_hyp_Q) T) ⊢
    introduce_with_hooks E L P T.
  Proof.
    iIntros "HT" (F ?) "#HE HL HP".
    iMod (learn_from_hyp_proof with "[//] HP") as "(HP & Hlearn)".
    iMod ("HT" with "HP [] HE HL Hlearn") as "Ha"; first done.
    done.
  Qed.
  Global Instance introduce_with_hooks_base_learnable_inst E L P `{!LearnFromHyp P} : IntroduceWithHooks E L P | 100 :=
    λ T, i2p (introduce_with_hooks_base_learnable E L P T).

  Lemma introduce_with_hooks_base E L P T :
    (P -∗ T L) ⊢
    introduce_with_hooks E L P T.
  Proof.
    iIntros "HT" (F ?) "#HE HL HP".
    iSpecialize ("HT" with "HP").
    iModIntro. iExists L. iFrame.
  Qed.
  Global Instance introduce_with_hooks_base_inst E L P : IntroduceWithHooks E L P | 101 :=
    λ T, i2p (introduce_with_hooks_base E L P T).

  Lemma introduce_with_hooks_direct E L P T :
    (P -∗ T L) ⊢
    introduce_with_hooks E L (introduce_direct P) T.
  Proof.
    iApply introduce_with_hooks_base.
  Qed.
  Global Instance introduce_with_hooks_direct_inst E L P : IntroduceWithHooks E L (introduce_direct P) | 1 :=
    λ T, i2p (introduce_with_hooks_direct E L P T).

  (** credit related instances *)
  Lemma introduce_with_hooks_credits E L n T :
    find_in_context (FindCreditStore) (λ '(c, a),
      credit_store (n + c) a -∗ T L) ⊢
    introduce_with_hooks E L (£ n) T.
  Proof.
    rewrite /FindCreditStore. iIntros "Ha".
    iDestruct "Ha" as ([c a]) "(Hstore & HT)". simpl.
    iIntros (??) "#HE HL Hc".
    iPoseProof (credit_store_donate with "Hstore Hc") as "Hstore".
    iExists _. iFrame. iApply ("HT" with "Hstore").
  Qed.
  Global Instance introduce_with_hooks_credits_inst E L n : IntroduceWithHooks E L (£ n) | 10 :=
    λ T, i2p (introduce_with_hooks_credits E L n T).

  Lemma introduce_with_hooks_atime E L n T :
    find_in_context (FindCreditStore) (λ '(c, a),
      credit_store c (n + a) -∗ T L)
    ⊢ introduce_with_hooks E L (atime n) T.
  Proof.
    rewrite /FindCreditStore. iIntros "Ha".
    iDestruct "Ha" as ([c a]) "(Hstore & HT)". simpl.
    iIntros (??) "#HE HL Hc".
    iPoseProof (credit_store_acc with "Hstore") as "(Hcred & Hat & Hcl)".
    iPoseProof ("Hcl" $! _ (n + a)%nat with "Hcred [Hat Hc]") as "Hstore".
    { rewrite -Nat.add_succ_r. rewrite additive_time_receipt_sep. iFrame. }
    iExists _. iFrame. iApply ("HT" with "Hstore").
  Qed.
  Global Instance introduce_with_hooks_atime_inst E L n : IntroduceWithHooks E L (atime n) | 10 :=
    λ T, i2p (introduce_with_hooks_atime E L n T).



  (** *** Statements *)
  (* [fn]: the surrounding function,
     [ls]: stack (list of locations for args and local variables),
  *)
  Definition typed_stmt_R_t := val → llctx → iProp Σ.
  Definition typed_stmt_post_cond (π : thread_id) (L : llctx) (fn : runtime_function) (R : typed_stmt_R_t) (v : val) : iProp Σ :=
    ((* return ownership of the stack *)
     ([∗ list] l ∈ (fn.(rf_locs)), l.1 ↦|l.2|) ∗
     (* return the non-atomic token *)
     na_own π shrE ∗
     (* continuation *)
     R v L)%I.

  (* [Q]: the current function body,
     [ls]: stack
     [ϝ]: the function lifetime

     [R] is a relation on the result value of this statement and its type: we require that the result value is a well-typed [R]-value at this type.
  *)
  Definition typed_stmt (π : thread_id) (E : elctx) (L : llctx) (s : stmt) (fn : runtime_function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (∀ (Φ : val → iProp Σ),
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      (∀ L' (v : val),
        llctx_interp L' -∗
        na_own π shrE -∗
        ([∗ list] l ∈ (fn.(rf_locs)), l.1 ↦|l.2|) -∗
        R v L' -∗
        Φ v) -∗
      (*typed_stmt_post_cond π ϝ fn R L')*)
      WPs s {{fn.(rf_fn).(f_code), Φ}})%I.
  Global Arguments typed_stmt _ _ _ _%E _ _%I _.

  (* [P] is an invariant on the context. *)
  Definition typed_block (π : thread_id) (P : elctx → llctx → iProp Σ) (b : label) (fn : runtime_function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (∀ Φ E L,
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      P E L -∗
      (∀ L' (v : val),
        llctx_interp L' -∗
        na_own π shrE -∗
        ([∗ list] l ∈ (fn.(rf_locs)), l.1 ↦|l.2|) -∗
        R v L' -∗
        Φ v) -∗
      WPs (Goto b) {{ fn.(rf_fn).(f_code), Φ}}).

  (** for all succeeding statements [s], assuming that [v] has type [ty], it can be converted to a non-zero integer *)
  Definition typed_assert (π : thread_id) (E : elctx) (L : llctx) (v : val) {rt} (ty : type rt) (r : rt) (s : stmt) (fn : runtime_function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗ v ◁ᵥ{π} r @ ty -∗ ⌜val_to_bool v = Some true⌝ ∗ llctx_interp L ∗ na_own π shrE ∗ typed_stmt π E L s fn R ϝ)%I.
  Class TypedAssert (π : thread_id) (E : elctx) (L : llctx) (v : val) {rt} (ty : type rt) (r : rt) : Type :=
    typed_assert_proof s fn R ϝ : iProp_to_Prop (typed_assert π E L v ty r s fn R ϝ).


  (** annotated statements are allowed to execute an update and take a step *)
  (* TODO: make this more useful and actually use it *)
  Definition typed_annot_stmt {A} (a : A) (T : iProp Σ) : iProp Σ :=
    (rrust_ctx ={⊤}[∅]▷=∗ T).
  Class TypedAnnotStmt {A} (a : A) : Type :=
    typed_annot_stmt_proof T : iProp_to_Prop (typed_annot_stmt a T).

  Definition typed_switch (π : thread_id) (E : elctx) (L : llctx) (v : val) rt (ty : type rt) (r : rt) (it : int_type) (m : gmap Z nat) (ss : list stmt) (def : stmt) (fn : runtime_function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (v ◁ᵥ{π} r @ ty -∗ ∃ z, ⌜val_to_Z v it = Some z⌝ ∗
      match m !! z with
      | Some i => ∃ s, ⌜ss !! i = Some s⌝ ∗ typed_stmt π E L s fn R ϝ
      | None   => typed_stmt π E L def fn R ϝ
      end).
  Class TypedSwitch (π : thread_id) (E : elctx) (L : llctx) (v : val) rt (ty : type rt) (r : rt) (it : int_type) : Type :=
    typed_switch_proof m ss def fn R ϝ : iProp_to_Prop (typed_switch π E L v rt ty r it m ss def fn R ϝ).



  (** *** Places *)

  (* This defines what place expressions can contain. We cannot reuse
  W.ectx_item because of BinOpPCtx since there the root of the place
  expression is not in evaluation position. *)
  Inductive place_ectx_item :=
  | DerefPCtx (o : lang.order) (ot : op_type) (mc : bool)
  | GetMemberPCtx (sls : struct_layout_spec) (m : var_name)
  | GetMemberUnionPCtx (uls : union_layout_spec) (m : var_name)
  | AnnotExprPCtx (n : nat) {A} (x : A)
    (* for PtrOffsetOp, second ot must be PtrOp *)
  | BinOpPCtx (op : bin_op) (ot : op_type) (v : val) rt (ty : type rt) (r : rt)
    (* for ptr-to-ptr casts, ot must be PtrOp *)
  | UnOpPCtx (op : un_op)
  | EnumDiscriminantPCtx (els : enum_layout_spec)
  | EnumDataPCtx (els : enum_layout_spec) (variant : var_name)
  .

  (* Computes the WP one has to prove for the place ectx_item Ki
  applied to the location l. *)
  Definition place_item_to_wp (π : thread_id) (Ki : place_ectx_item) (Φ : loc → iProp Σ) (l : loc) : iProp Σ :=
    match Ki with
    | DerefPCtx o ot mc => WP !{ot, o, mc} l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberPCtx sls m => WP l at{sls} m {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberUnionPCtx uls m => WP l at_union{uls} m {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | AnnotExprPCtx n x => WP AnnotExpr n x l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    (* we have proved typed_val_expr e1 before so we can use v ◁ᵥ ty here;
      note that the offset is on the left and evaluated first *)
    | BinOpPCtx op ot v rt ty r => v ◁ᵥ{π} r @ ty -∗ WP BinOp op ot PtrOp v l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | UnOpPCtx op => WP UnOp op PtrOp l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | EnumDiscriminantPCtx els => WP EnumDiscriminant els l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | EnumDataPCtx els variant => WP EnumData els variant l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    end%I.
  Definition place_to_wp (π : thread_id) (K : list place_ectx_item) (Φ : loc → iProp Σ) : (loc → iProp Σ) := foldr (place_item_to_wp π) (λ v, |={⊤}=> Φ v)%I K.

  Lemma fupd_place_item_to_wp π Ki Φ l :
    (|={⊤}=> place_item_to_wp π Ki Φ l) -∗ place_item_to_wp π Ki Φ l.
  Proof.
    destruct Ki; simpl; iIntros "Ha"; iIntros; iApply fupd_wp; iMod "Ha"; by iApply "Ha".
  Qed.
  Lemma fupd_place_to_wp π K Φ l:
    (|={⊤}=> place_to_wp π K Φ l) -∗ place_to_wp π K Φ l.
  Proof.
    destruct K as [ | Ki K]; simpl.
    - by iIntros ">>$".
    - iApply fupd_place_item_to_wp.
  Qed.

  Global Instance place_item_to_wp_proper π K :
    Proper (pointwise_relation _ equiv ==> eq ==> equiv)  (place_item_to_wp π K).
  Proof.
    intros Φ1 Φ2 Hequiv l l' <-.
    destruct K; simpl.
    5: f_equiv.
    all: apply wp_proper; solve_proper.
  Qed.
  Lemma place_to_wp_app π (K1 K2 : list place_ectx_item) Φ l :
    place_to_wp π (K1 ++ K2) Φ l ≡ place_to_wp π K1 (place_to_wp π K2 Φ) l.
  Proof.
    induction K1 as [ | Ki K IH] in l |-*.
    - simpl. iSplit; [ by eauto | ].
      iApply fupd_place_to_wp.
    - simpl. apply place_item_to_wp_proper; last done.
      intros l'. by rewrite IH.
  Qed.

  Lemma place_item_to_wp_mono π K Φ1 Φ2 l:
    place_item_to_wp π K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_item_to_wp π K Φ2 l.
  Proof.
    iIntros "HP HΦ". move: K => [o ly mc|sls m|uls m |n A x|op ot v rt ty r|op | els | els variant]//=.
    5: iIntros "Hv".
    1-4,6-8: iApply (@wp_wand with "HP").
    8: iApply (@wp_wand with "[Hv HP]"); first by iApply "HP".
    all: iIntros (?); iDestruct 1 as (l' ->) "HΦ1".
    all: iExists _; iSplit => //; by iApply "HΦ".
  Qed.

  Lemma place_to_wp_mono π K Φ1 Φ2 l:
    place_to_wp π K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_to_wp π K Φ2 l.
  Proof.
    iIntros "HP HΦ".
    iInduction (K) as [] "IH" forall (l) => /=. { by iApply "HΦ". }
    iApply (place_item_to_wp_mono with "HP").
    iIntros (l') "HP". by iApply ("IH" with "HP HΦ").
  Qed.

  Lemma place_to_wp_fupd π K Φ l:
    (place_to_wp π K (λ l, |={⊤}=> Φ l) l) -∗ place_to_wp π K Φ l.
  Proof.
    induction K as [ | Ki K IH] in l |-*; simpl.
    - by iIntros ">>$".
    - iIntros "Ha". iApply (place_item_to_wp_mono with "Ha").
      iIntros (l'). iApply IH.
  Qed.

  (* We need to take some extra care because the lifetime context may change during this operation. *)
  Fixpoint find_place_ctx π (E : elctx) (e : W.expr) : option (llctx → (llctx → list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    match e with
    | W.Loc l => Some (λ L T, T L [] l)
    | W.Deref o ot mc e =>
      T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [DerefPCtx o ot mc]) l))
    | W.GetMember e sls m => T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [GetMemberPCtx sls m]) l))
    | W.GetMemberUnion e uls m => T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [GetMemberUnionPCtx uls m]) l))
    | W.EnumDiscriminant els e => T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [EnumDiscriminantPCtx els]) l))
    | W.EnumData els variant e => T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [EnumDataPCtx els variant]) l))
    | W.AnnotExpr n x e => T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [AnnotExprPCtx n x]) l))
    | W.LocInfoE a e => find_place_ctx π E e

    (* Here we use the power of having a continuation available to add
    a typed_val_expr. It is important that this happens before we get
    to place_to_wp_mono since we will need to give up ownership of the
    root of the place expression once we hit it. This allows us to
    support e.g. a[a[0]]. *)
    | W.BinOp op ot PtrOp e1 e2 =>
      T' ← find_place_ctx π E e2;
      Some (λ L T, typed_val_expr π E L (W.to_expr e1) (λ L' v rt ty r, T' L' (λ L'' K l, T L'' (K ++ [BinOpPCtx op ot v rt ty r]) l)))
    | W.UnOp op PtrOp e => T' ← find_place_ctx π E e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [UnOpPCtx op]) l))
    (* TODO: Is the existential quantifier here a good idea or should this be a fullblown judgment? *)
    | W.UnOp op (IntOp it) e =>
      Some (λ L T, typed_val_expr π E L (UnOp op (IntOp it) (W.to_expr e)) (λ L' v rt ty r,
        v ◁ᵥ{π} r @ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T L' [] l)%I)
    | W.LValue e =>
      Some (λ L T, typed_val_expr π E L (W.to_expr e) (λ L' v rt ty r,
        v ◁ᵥ{π} r @ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T L' [] l)%I)
    | _ => None
    end.

  Class IntoPlaceCtx π E (e : expr) (T : llctx → (llctx → list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    into_place_ctx Φ Φ':
    (⊢ ∀ L, rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗ T L Φ' -∗
      (∀ L' K l, llctx_interp L' -∗ na_own π shrE -∗ Φ' L' K l -∗ place_to_wp π K (Φ ∘ val_of_loc) l) -∗
        WP e {{ Φ }}).

  Section find_place_ctx_correct.
  Arguments W.to_expr : simpl nomatch.
  Lemma find_place_ctx_correct E π e T:
    find_place_ctx π E e = Some T →
    IntoPlaceCtx π E (W.to_expr e) T.
  Proof.
    elim: e T => //= *.
    all: iIntros (Φ Φ' L) "#LFT #HE HL Hna HT HΦ'".
    all: iApply ewp_fupd.
    2,3: case_match.
    all: try match goal with
    |  H : ?x ≫= _ = Some _ |- _ => destruct x as [?|] eqn:Hsome
    end; simplify_eq/=.
    all: try match goal with
    |  H : context [IntoPlaceCtx _ _ _ _ ] |- _ => rename H into IH
    end.
    1: iApply @wp_value; by iApply ("HΦ'" with "HL Hna HT").
    1: {
      iApply ("HT" with "LFT HE HL Hna"). iIntros (L' rt ty v r) "HL Hna Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
        by iApply ("HΦ'" $! _ [] with "HL Hna HT").
    }
    4: {
      rewrite /LValue. iApply ("HT" with "LFT HE HL Hna"). iIntros (L' rt ty v r) "HL Hna Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
      by iApply ("HΦ'" $! _ [] with "HL Hna").
    }
    2: wp_bind. 1: rewrite -!/(W.to_expr _).
    2: iApply ("HT" with "LFT HE HL Hna"); iIntros (L' v rt ty r) "HL Hna Hv HT".
    2: iDestruct (IH with "LFT HE HL Hna HT") as "HT" => //.
    2: fold W.to_expr.
    1, 3-8: iDestruct (IH with "LFT HE HL Hna HT") as " HT" => //.
    all: wp_bind; iApply "HT".
    all: iIntros (L'' K l) "HL Hna HT" => /=.
    all: iDestruct ("HΦ'" with "HL Hna HT") as "HΦ"; rewrite place_to_wp_app /=.
    all: iApply (place_to_wp_mono with "HΦ"); iIntros (l') "HWP" => /=.
    8: iApply (@wp_wand with "[Hv HWP]"); first by iApply "HWP".
    1-7: iApply (@wp_wand with "HWP").
    all: iIntros (?); by iDestruct 1 as (? ->) "$".
  Qed.
  End find_place_ctx_correct.


  (** ** Condition on places: when is a client allowed to replace [lt] with [lt2]
    under a context where the intersected [bor_kind] is [b]?
    *)
  Section fix_inner.
    Context {rt rt2 : Type}
    .

    (** [b] is the intersection of all bor_kinds which are "above" the position affecting this place.
      This means: [b] expresses what we can do with the place.
      * [Shared] should not allow mutable borrowing/mutable accesses, refinement needs to stay the same (the refinement is fixed in the fractional borrow).
      * [Uniq] allows mutation and requires no condition on the refinement.
      * [Owned] states that there are no borrows above, only "plain" ownership.
          That means we can do arbitrary strong updates (even changing the refinement type if we need to).
    *)
    Import EqNotations.

    (** Condition on type changes from [lt] to [lt2] *)
    (* NOTE Now that ltype_eq involves the refinement, maybe we should merge this with the condition on the refinement?
        -> no. since the eq proof is used in the lifetime logic's inheritance vs in the Uniq case, we cannot fix to the current refinement, but rather need to have a proof for all refinements.
    *)
    Definition typed_place_cond_ty (b : bor_kind) (lt : ltype rt) (lt2 : ltype rt2) : iProp Σ :=
      match b with
      | Owned _ =>
          (* TODO weaken this? *)
          ⌜ltype_st lt = ltype_st lt2⌝
      | Uniq κ _ =>
          ∃ (Heq : rt = rt2),
          (* We could allow a disjunction here:
             - if we actually change the place type, then we change the contents of the borrow, and we must prove that we can actually unblock the new type [lt2] in time.
             - if we don't actually change the place type, we've proved this before, and it is fine.
              (this isn't completely true for products: we will need sideconditions for products to handle components that don't change, because we can't just extract this from the VS again when we change one component).
              TODO: pinned borrows actually allow to get the VS out now with the strong accessor, so there should be nothing stopping us from allowing this.
          *)
          (∀ b r, ltype_eq b r r (ltype_core lt) (ltype_core (rew <- [ltype] Heq in lt2))) ∗ imp_unblockable [κ] lt2

          (* ∨ ⌜lt = rew <- [lty] Heq in lt2⌝ *)
      | Shared κ =>
          (* TODO: Is this is too strict? It does not directly allow shared reborrows below shared references.
            Maybe change this to [ltype_incl lt2 lt]?
            OTOH, it's not really clear that that would be the right way to model shared reborrows...
          *)
          ⌜rt = rt2⌝ ∗ ⌜ltype_st lt = ltype_st lt2⌝
          (*∃ (Heq: rt = rt2),*)
            (*( ∀ b r, ltype_eq b r r lt (rew <- [ltype] Heq in lt2)) ∗ imp_unblockable [κ] lt2*)
      end%I.

    (** Condition on the refinement *)
    Definition typed_place_cond_rfn (b : bor_kind) (r : place_rfn rt) (r2 : place_rfn rt2) : iProp Σ :=
      match b with
      | Shared _ =>
          True
          (*∃ (Heq: rt = rt2), ⌜rew <- [place_rfn] Heq in r2 = r⌝*)
      | _ => True
      end%I.

    Global Instance  typed_place_cond_rfn_pers (r1 : place_rfn rt) (r2 : place_rfn rt2) k :
      Persistent (typed_place_cond_rfn k r1 r2 : iProp Σ).
    Proof. destruct k; apply _. Qed.

    (** Combined condition *)
    Definition typed_place_cond (b : bor_kind) (lt : ltype rt) (lt2 : ltype rt2) (r : place_rfn rt) (r2 : place_rfn rt2) : iProp Σ :=
      typed_place_cond_ty b lt lt2 ∗ typed_place_cond_rfn b r r2.

    Global Instance typed_place_cond_ty_pers b lt lt2 :
      Persistent (typed_place_cond_ty b lt lt2).
    Proof. destruct b; apply _. Qed.
    Global Instance typed_place_cond_pers b lt1 lt2 r1 r2 :
      Persistent (typed_place_cond b lt1 lt2 r1 r2).
    Proof. destruct b; apply _. Qed.

    Lemma typed_place_cond_ty_incl b1 b2 lt1 lt2 :
      b1 ⊑ₖ b2 -∗ typed_place_cond_ty b1 lt1 lt2 -∗ typed_place_cond_ty b2 lt1 lt2.
    Proof using Type*.
      iIntros "? Hcond//".
      destruct b1, b2; simpl; try done.
      - iDestruct "Hcond" as "(_ & $)".
      (*- iDestruct "Hcond" as (<-) "(Heq & Hub)"; cbn in *.*)
        (*iExists eq_refl. cbn. iFrame.*)
        (*iApply (imp_unblockable_shorten' with "[$] Hub").*)
      - iDestruct "Hcond" as (<-) "(Ha & _)".
        iDestruct ("Ha" $! inhabitant inhabitant) as "(( #Hly & _) & _)".
        rewrite !ltype_core_syn_type_eq. done.
      - iDestruct "Hcond" as (<-) "(Heq & _)"; cbn in *.
        iR.
        iDestruct ("Heq" $! inhabitant inhabitant) as "(( #Hly & _) & _)".
        rewrite !ltype_core_syn_type_eq//.
      - iDestruct "Hcond" as (<-) "(Heq & Hub)"; cbn in *.
        iExists eq_refl. cbn. iFrame.
        iApply (imp_unblockable_shorten' with "[$] Hub").
    Qed.
    Lemma typed_place_cond_rfn_incl b1 b2 r1 r2 :
     b1 ⊑ₖ b2 -∗ typed_place_cond_rfn b1 r1 r2 -∗ typed_place_cond_rfn b2 r1 r2.
    Proof using Type*.
      iIntros "? Hrfn//". destruct b1, b2; done.
    Qed.
    Lemma typed_place_cond_incl b1 b2 r1 r2 lt1 lt2 :
     b1 ⊑ₖ b2 -∗ typed_place_cond b1 lt1 lt2 r1 r2 -∗ typed_place_cond b2 lt1 lt2 r1 r2.
    Proof using Type*.
      iIntros "#Hincl [Hcond Hrfn]//". iSplit.
      - by iApply typed_place_cond_ty_incl.
      - by iApply typed_place_cond_rfn_incl.
    Qed.
  End fix_inner.

  Lemma typed_place_cond_rfn_trans {rt1 rt2 rt3} bmin (r1 : place_rfn rt1) (r2 : place_rfn rt2) (r3 : place_rfn rt3) :
    typed_place_cond_rfn bmin r1 r2 -∗ typed_place_cond_rfn bmin r2 r3 -∗ typed_place_cond_rfn bmin r1 r3 : iProp Σ.
  Proof.
    iIntros "H1 H2". destruct bmin; simpl; [done | | done].
    (*iDestruct "H1" as "(%Heq1 & %Ha)".*)
    (*iDestruct "H2" as "(%Heq2 & %Hb)".*)
    (*subst. iExists eq_refl. done.*)
    done.
  Qed.
  Lemma typed_place_cond_ty_trans {rt1 rt2 rt3} (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) b :
    typed_place_cond_ty b lt1 lt2 -∗
    typed_place_cond_ty b lt2 lt3 -∗
    typed_place_cond_ty b lt1 lt3 .
  Proof.
    destruct b; simpl.
    - iIntros "% % !%". congruence.
    - iIntros "(-> & ->) (-> & ->)".
      done.
    - iIntros "(%Heq & Heq & Hub) (%Heq' & Heq' & Hub')".
      subst.
      iExists eq_refl. iFrame. cbn.
      iIntros (b r). iApply (ltype_eq_trans with "Heq Heq'").
  Qed.
  Lemma typed_place_cond_trans {rt1 rt2 rt3} r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) b :
    typed_place_cond b lt1 lt2 r1 r2  -∗
    typed_place_cond b lt2 lt3 r2 r3 -∗
    typed_place_cond b lt1 lt3 r1 r3.
  Proof.
    iIntros "(Ht1 & Hr1) (Ht2 & Hr2)". iSplit.
    - iApply (typed_place_cond_ty_trans with "Ht1 Ht2").
    - iApply (typed_place_cond_rfn_trans with "Hr1 Hr2").
  Qed.

  Lemma imp_unblockable_incl_blocked_lfts {rt} κ (lt : ltype rt) :
    ([∗ list] κ' ∈ ltype_blocked_lfts lt, κ' ⊑ κ) -∗
    imp_unblockable [κ] lt.
  Proof.
    iIntros "#Houtl".
    iApply (imp_unblockable_shorten with "[Houtl]"); last iApply imp_unblockable_blocked_dead.
    iModIntro. iIntros "(#Hdead & _)".
    iApply big_sepL_fupd. iApply big_sepL_intro.
    iIntros "!>" (? κ' Hlook). iPoseProof (big_sepL_lookup with "Houtl") as "Hincl"; first done.
    iApply (lft_incl_dead with "Hincl Hdead"). done.
  Qed.

  (** Requires a sidecondition to make sure we can actually do the unblocking. *)
  (* NOTE: if we were to revise the use of unblocking and have a disjunct to just show ltype_eq instead of unblockable, we could get rid of the sidecondition *)
  Lemma typed_place_cond_ty_refl {rt} b (lt : ltype rt) :
    ([∗ list] κ' ∈ ltype_blocked_lfts lt, bor_kind_outlives b κ') -∗
    typed_place_cond_ty b lt lt.
  Proof.
    iIntros "#Houtl".
    destruct b => /=.
    - by iPureIntro.
    - done.
    - iExists eq_refl. cbn. iSplitR.
      { iIntros (??). iApply ltype_eq_refl. }
      by iApply imp_unblockable_incl_blocked_lfts.
  Qed.
  Lemma typed_place_cond_refl {rt} b r (lt : ltype rt) :
    ([∗ list] κ' ∈ ltype_blocked_lfts lt, bor_kind_outlives b κ') -∗
    typed_place_cond b lt lt r r.
  Proof.
    iIntros "Huniq". iSplit.
    + by iApply typed_place_cond_ty_refl.
    + destruct b => //.
      (*iExists eq_refl. done.*)
  Qed.

  Lemma typed_place_cond_ty_refl_ofty {rt} b (ty : type rt) :
    ⊢ typed_place_cond_ty b (◁ ty)%I (◁ ty)%I.
  Proof.
    iApply typed_place_cond_ty_refl. done.
  Qed.

  Lemma typed_place_cond_ty_syn_type_eq {rt1 rt2} b (lt1 : ltype rt1) (lt2 : ltype rt2) :
    typed_place_cond_ty b lt1 lt2 -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros "Hcond". destruct b; simpl.
    - done.
    - iDestruct "Hcond" as "(-> & $)".
    - iDestruct "Hcond" as "(%Heq & [Heq Hub])".
      iDestruct ("Heq" $! inhabitant inhabitant) as "((%Hly & _) & _)". subst; cbn in *.
      rewrite !ltype_core_syn_type_eq in Hly. iPureIntro. done.
  Qed.
  Lemma typed_place_cond_syn_type_eq {rt1 rt2} b (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 :
    typed_place_cond b lt1 lt2 r1 r2 -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros "(Ha & _)". by iApply typed_place_cond_ty_syn_type_eq.
  Qed.

  Lemma typed_place_cond_ty_uniq_core_eq {rt} (lt1 lt2 : ltype rt) κ γ :
    typed_place_cond_ty (Uniq κ γ) lt1 lt2 -∗ ∀ b r, ltype_eq b r r (ltype_core lt1) (ltype_core lt2).
  Proof.
    iIntros "(%Heq & Ha & _)". rewrite (UIP_refl _ _ Heq). done.
  Qed.
  Lemma typed_place_cond_ty_uniq_unblockable {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ γ :
    typed_place_cond_ty (Uniq κ γ) lt1 lt2 -∗ imp_unblockable [κ] lt2.
  Proof.
    iIntros "(%Heq & _ & Ha)". done.
  Qed.
  Lemma typed_place_cond_ty_shadowed_update_cur {rt_cur rt_full} (lt_cur lt_cur' : ltype rt_cur) r_cur r_cur' (lt_full : ltype rt_full) k :
    ([∗ list] κ0 ∈ ltype_blocked_lfts lt_full, bor_kind_outlives k κ0) -∗
    typed_place_cond_ty k (ShadowedLtype lt_cur r_cur lt_full) (ShadowedLtype lt_cur' r_cur' lt_full).
  Proof.
    iIntros "Hcond".
    destruct k; simpl; simp_ltypes.
    - done.
    - done.
    - iExists eq_refl. cbn. simp_ltypes.
      iSplitR. { iIntros (??). iApply ltype_eq_refl. }
      iApply shadowed_ltype_imp_unblockable.
      iApply imp_unblockable_incl_blocked_lfts.
      done.
  Qed.

  (* controls conditions on refinement type changes *)
  Definition place_access_rt_rel (bmin : bor_kind) (rt1 rt2 : Type) :=
    match bmin with
    | Owned _ => True
    | _ => rt1 = rt2
    end.
  Lemma place_access_rt_rel_refl bmin rt : place_access_rt_rel bmin rt rt.
  Proof. by destruct bmin. Qed.

  Lemma typed_place_cond_rfn_lift b {rt rto} (r1 : place_rfn rt) (r2 : place_rfn rt) (f : place_rfn rt → place_rfn rto):
    typed_place_cond_rfn b r1 r2 -∗
    typed_place_cond_rfn b (f r1) (f r2).
  Proof.
    destruct b; try by auto.
    (*iIntros "(%Hrefl & Ha)".*)
    (*rewrite (UIP_refl _ _ Hrefl). cbn.*)
    (*iDestruct "Ha" as "->". iExists eq_refl. done.*)
  Qed.
  Lemma typed_place_cond_rfn_refl b {rt} (r : place_rfn rt) :
    ⊢ typed_place_cond_rfn b r r.
  Proof.
    destruct b => //.
    (*iExists eq_refl. done.*)
  Qed.

  Lemma place_cond_ty_Uniq_rt_eq {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k κ γ :
    k ⊑ₖ Uniq κ γ -∗
    typed_place_cond_ty k lt1 lt2 -∗
    ⌜rt1 = rt2⌝.
  Proof.
    iIntros "Hincl Hcond".
    destruct k; simpl; first done.
    (* TODO why does the following not work? *)
    (*all: iDestruct "Hcond" as "(%Heq & _)". *)
    all: iDestruct "Hcond" as "(%Heq & Ha)"; iClear "Ha"; by done.
  Qed.
  Lemma place_cond_ty_Shared_rt_eq {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k κ :
    k ⊑ₖ Shared κ -∗
    typed_place_cond_ty k lt1 lt2 -∗
    ⌜rt1 = rt2⌝.
  Proof.
    iIntros "Hincl Hcond".
    destruct k; simpl; [done | | ].
    - iDestruct "Hcond" as "($ & _)".
    - iDestruct "Hcond" as "(%Heq & Ha)"; iClear "Ha"; by done.
  Qed.

  (* NOTE: if put the ltype_eq disjunct for the Uniq case into typed_place_cond,
      then we would get a direct subsumption lemma. *)
  Lemma ltype_eq_place_cond_ty_trans {rt rt2} (lt1 lt2 : ltype rt) (lt3 : ltype rt2) b :
    (∀ b' r, ltype_eq b' r r lt1 lt2) -∗
    typed_place_cond_ty b lt2 lt3 -∗
    typed_place_cond_ty b lt1 lt3.
  Proof.
    iIntros "Heq Hc".
    destruct b; simpl.
    - iDestruct "Hc" as "<-".
      iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
    - iDestruct "Hc" as "(-> & <-)".
      iR. iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
    - iDestruct "Hc" as "(%Heq & Heq' & $)". subst. iExists eq_refl.
      iIntros (??).
      iPoseProof (ltype_eq_core with "Heq") as "Heq".
      iApply (ltype_eq_trans with "Heq Heq'").
  Qed.
  Lemma place_cond_ty_ltype_eq_trans b {rt1 rt2} (lt1 : ltype rt1) (lt2 lt3 : ltype  rt2) :
    typed_place_cond_ty b lt1 lt2 -∗
    (∀ b' r, ltype_eq b' r r lt2 lt3) -∗
    typed_place_cond_ty b lt1 lt3.
  Proof.
    iIntros "Hcond #Heq".
    destruct b; simpl.
    - iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
    - iDestruct "Hcond" as "(-> & ->)".
      iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
    - iDestruct "Hcond" as "(%Heq & #Heq2 & Hub)". subst rt2.
      iExists eq_refl.
      iSplitR. { iIntros (??). iPoseProof (ltype_eq_core with "Heq") as "Heq'". iApply ltype_eq_trans; done. }
      iApply ltype_eq_imp_unblockable; done.
  Qed.
  Lemma ltype_eq_place_cond_trans {rt rt2} (lt1 lt2 : ltype rt) (lt3 : ltype rt2) b r r' :
    (∀ b' r, ltype_eq b' r r lt1 lt2) -∗
    typed_place_cond b lt2 lt3 r r' -∗
    typed_place_cond b lt1 lt3 r r'.
  Proof.
    iIntros "Heq (Hc & Hr)". iSplit; last done.
    iApply (ltype_eq_place_cond_ty_trans with "Heq Hc").
  Qed.

  Lemma typed_place_cond_ltype_eq_ofty {rt rt2} (lt1 : ltype rt) (lt2 : ltype rt2) (ty3 : type rt2) b r r' :
    typed_place_cond b lt1 lt2 r r' -∗
    (∀ b' r, ltype_eq b' r r lt2 (◁ ty3)%I) -∗
    typed_place_cond b lt1 (◁ ty3)%I r r'.
  Proof.
    iIntros "[Hc Hr] Heq". iSplit; last done.
    destruct b; simpl.
    - iDestruct "Hc" as "->".
      iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
    - iDestruct "Hc" as "(-> & ->)".
      iR. iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
    - iDestruct "Hc" as "(%Heq & Heq' & Hub)". destruct Heq. iExists eq_refl. cbn.
      iSplitL. {
        iIntros (??).
        iApply (ltype_eq_trans with "Heq'").
        iApply (ltype_eq_core _ _ _ _ (◁ _)%I). done.
      }
      iApply ofty_imp_unblockable.
  Qed.

  (** We can mutably borrow from the place, assuming that the ownership [b] of the place is at least Uniq κ. *)
  Lemma ofty_blocked_place_cond_ty b κ {rt} (ty : type rt) :
    (∀ γ, Uniq κ γ ⊑ₖ b) -∗
    typed_place_cond_ty b (◁ ty)%I (BlockedLtype ty κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Ha". simp_ltypes. done.
    - iIntros "Hincl". iDestruct ("Hincl" $! 1%positive) as "Hincl".
      iExists eq_refl. cbn. iSplitR.
      + simp_ltypes. iIntros (??). iApply ltype_eq_refl.
      + iApply (imp_unblockable_shorten' with "Hincl"). iApply blocked_imp_unblockable.
  Qed.

  (** TODO: this should only require [b] to be [Shared κ], in order to allow shared reborrows from shared references?
    Alternatively, maybe shared reborrows below shared references require special handling.
    They can also be justified by just copying the sharing predicate from the place?
  *)
  Lemma ofty_shr_blocked_place_cond_ty b κ {rt} (ty : type rt) :
    (∀ γ, Uniq κ γ ⊑ₖ b) -∗
    typed_place_cond_ty b (◁ ty)%I (ShrBlockedLtype ty κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Ha". simp_ltypes. done.
    - iIntros "Hincl". iDestruct ("Hincl" $! 1%positive) as "Hincl".
      iExists eq_refl. cbn. iSplitR.
      + simp_ltypes. iIntros (??). iApply ltype_eq_refl.
      + iApply (imp_unblockable_shorten' with "Hincl"). iApply shr_blocked_imp_unblockable.
  Qed.

  (* TODO later on generalize this to also capture condition on when we are allowed to do strong updates/
    change the refinement type  *)
  Definition bor_kind_writeable (b : bor_kind) :=
    match b with
    | Owned _ => True
    | Uniq _ _ => True
    | Shared _ => False
    end.
  Definition bor_kind_strongly_writeable (b : bor_kind) :=
    match b with
    | Owned _ => True
    | Uniq _ _ => False
    | Shared _ => False
    end.
  Definition bor_kind_mut_borrowable (b : bor_kind) :=
    match b with
    | Shared _ => False
    | _ => True
    end.

  Record weak_ctx (rto rti : Type) : Type := mk_weak {
    weak_lt : (ltype rti → place_rfn rti → ltype rto);
    weak_rfn : (place_rfn rti → place_rfn rto);
    weak_R : (ltype rti → place_rfn rti → iProp Σ)
  }.
  Global Arguments weak_lt {_ _}.
  Global Arguments weak_rfn {_ _}.
  Global Arguments weak_R {_ _}.
  Global Arguments mk_weak {_ _}.
  Add Printing Constructor weak_ctx.

  Record strong_ctx (rti : Type) : Type := mk_strong {
    strong_rt : Type → Type;
    strong_lt : (∀ rti2, ltype rti2 → place_rfn rti2 → ltype (strong_rt rti2));
    strong_rfn : (∀ rti2, place_rfn rti2 → place_rfn (strong_rt rti2));
    strong_R : (∀ rti2, ltype rti2 → place_rfn rti2 → iProp Σ)
  }.
  Global Arguments strong_rt {_}.
  Global Arguments strong_lt {_}.
  Global Arguments strong_rfn {_}.
  Global Arguments strong_R {_}.
  Global Arguments mk_strong {_}.
  Add Printing Constructor strong_ctx.

  (* TODO: change typed_place to use mstrong_ctx instead. Then we can also do OpenedLtype unfolding below arrays *)
  Record mstrong_ctx (rti rto : Type) : Type := mk_mstrong {
    (* rt-changing *)
    mstrong_strong : option (strong_ctx rti);
    (* non-rt-changing *)
    mstrong_weak : weak_ctx rti rto;
  }.
  (* Note: this gives us three distinct update modes, and we cannot subsume one into the other, because all of this is invariant. *)


  (* Problem with the current approach is just that I can't practically use the result of the boolean flag
      -- I can't state the tctx without without the equality proof.
      The alternative is that this should be directly embedded in the strong continuation.
   *)

  (*
    Parameters:
    - [π]: thread id
    - [E]: external lifetime context
    - [L]: local lifetime context
    - [l1]: location that we access
    - [ltyo]: ltype of [l1]
    - [r1]: refinement of [ltyo] at [l1]
    - [bmin0]: the intersection of all [bor_kind]s of places above this one on the way of the access
    - [b1]: the immediate [bor_kind] at which [ltyo] is owned
    - [P]: place ctx, the accesses that we go through
    - [T]: client continuation, with the following arguments:
      + [L' : llctx]: the new local lifetime context
      + [κs] : lifetimes for which we have obtained tokens to access the place
      + [l2 : loc] : inner location that is acessed by the place access (the "result")
      + [b2 : bor_kind] : inner [bor_kind] at which the accessed place is immediately owned
      + [bmin : bor_kind] : the intersection of all [bor_kind]s on the way to [l2]
      + [br] : true if the place requires the refinement type to be unchanged
      + [rti : Type] : refinement type of [l2]
      + [tyli : lty rti] : the ltype at [l2]
      + [rti : place_rfn rti] : the refinement of [tyli]
      + [strong : option (strong_ctx rti)] : describes how an update to the accessed place at [l2] is reflected in an update to [l1] in case we need to do a strong refinement update
      + [weak : option (weak_ctx rto rti)] : describes how an update to the accessed place at [l2] is reflected in an update to [l1] in case do a weak update.


      Note that the [strong] and [weak] options are incomparable. [weak] does not only give stronger assumptions, but also requires giving stronger guarantees, which not all place types can do.
      In particular, [OpenedLtype] can not guarantee that an update will uphold the contract of the place it is nested under, so it cannot support [weak] updates.
   *)
  Definition place_cont_t rto : Type := llctx → list lft → loc → bor_kind → bor_kind → ∀ rti, ltype rti → place_rfn rti → option (strong_ctx rti) → option (weak_ctx rto rti) → iProp Σ.
  Definition typed_place π (E : elctx) (L : llctx) (l1 : loc) {rto} (ltyo : ltype rto) (r1 : place_rfn rto) (bmin0 : bor_kind) (b1 : bor_kind) (P : list place_ectx_item) (T : place_cont_t rto) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      (* [bmin0] is the intersection of all bor_kinds to this place, including [b1] *)
      bmin0 ⊑ₖ b1 -∗
      (* assume ownership of l1 *)
      l1 ◁ₗ[π, b1] r1 @ ltyo -∗
      (* precondition provided by the client that we necessarily need to go through to get Φ *)
      (∀ (L' : llctx) (κs : list lft) (l2 : loc) (b2 bmin : bor_kind) (rti : Type) (ltyi : ltype rti) (ri : place_rfn rti)
        (strong : option (strong_ctx rti))
        (weak : option (weak_ctx rto rti)),
        (* sanity check *)
        (*bmin ⊑ₖ bmin0 -∗*)
        bmin ⊑ₖ b2 -∗
        (* l2 is the inner location we eventually access, provide that to the client *)
        l2 ◁ₗ[π, b2] ri @ ltyi -∗

        (* for any update to l2 by the client, we need to update our "outer" place accordingly: *)
        (* we have a conjunction: the client can choose to do a strong, refinement-type changing update, or a weak update *)
        (match strong with | Some strong =>
          ∀ (rti2 : Type) (ltyi2 : ltype rti2) (ri2 : place_rfn rti2),
          (* assume an update by the client *)
          l2 ◁ₗ[π, b2] ri2 @ ltyi2 -∗
          (* needs to have the same st *)
          ⌜ltype_st ltyi = ltype_st ltyi2⌝ ={F}=∗
          (* provide the updated ownership of l1 *)
          l1 ◁ₗ[π, b1] (strong.(strong_rfn) rti2 ri2) @ strong.(strong_lt) rti2 ltyi2 ri2 ∗
          (* and a proof that the "outer" update is legal *)
          ⌜ltype_st ltyo = ltype_st (strong.(strong_lt) rti2 ltyi2 ri2)⌝ ∗
          (* as well as a "remaining" ownership that we get out from the update *)
          strong.(strong_R) rti2 ltyi2 ri2
        | None => True
        end) ∧

        (* weak update *)
        (match weak with | Some weak =>
          ∀ (ltyi2 : ltype rti) (ri2 : place_rfn rti) (bmin' : bor_kind),
          (* the update made by the client is allowed by the intersected bmin *)
          bmin' ⊑ₖ bmin -∗
          (* assume an update by the client *)
          l2 ◁ₗ[π, b2] ri2 @ ltyi2 -∗
          (* we can assume that the update by the client obeys the intersected kind bmin along the current path *)
          typed_place_cond bmin' ltyi ltyi2 ri ri2 ={F}=∗
          (* provide the updated ownership of l1 *)
          l1 ◁ₗ[π, b1] (weak.(weak_rfn) ri2) @ weak.(weak_lt) ltyi2 ri2 ∗
          (* and a proof that the "outer" update is legal *)
          typed_place_cond bmin0 ltyo (weak.(weak_lt) ltyi2 ri2) r1 (weak.(weak_rfn) ri2) ∗
          (* the tokens for the lifetime *)
          llft_elt_toks κs ∗
          (* as well as a "remaining" ownership that we get out from the update *)
          weak.(weak_R) ltyi2 ri2
         | None => True
         end) -∗

        (* provide the continuation condition *)
        T L' κs l2 b2 bmin rti ltyi ri strong weak -∗
        (* and the context: we hand the client the new context [L'] *)
        llctx_interp L' -∗
        (* then we can assume the postcondition *)
        Φ l2) -∗
      place_to_wp π P Φ l1).

  (** Instances need to have priority >= 10, the ones below are reserved for ghost resolution, id, etc. *)
  Class TypedPlace E L π l1 {rto} (ltyo : ltype rto) (r1 : place_rfn rto) (bmin0 b1 : bor_kind) (P : list place_ectx_item) : Type :=
    typed_place_proof T : iProp_to_Prop (typed_place π E L l1 ltyo r1 bmin0 b1 P T).

  Import EqNotations.
  Lemma typed_place_id {rt} π E L (lt : ltype rt) bmin0 b r l (T : place_cont_t rt) :
    ⌜lctx_bor_kind_incl E L bmin0 b⌝ ∗ T L [] l b bmin0 rt lt r (Some $ mk_strong id (λ _ lti2 _, lti2) (λ _ , id) (λ _ _ _, True)) (Some $ mk_weak (λ lti2 _, lti2) id (λ _ _, True))
    ⊢ typed_place π E L l lt r bmin0 b [] T.
  Proof.
    iIntros "(%Hincl & Hs)" (Φ F ??). iIntros "#LFT #HE HL Hincl0 HP HΦ /=".
    iPoseProof (lctx_bor_kind_incl_use with "HE HL") as "#Hincl"; first apply Hincl.
    iSpecialize ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "[] HP").
    { iApply "Hincl". }
    iApply ("HΦ" with "[] Hs HL").
    iSplit.
    - iIntros (rti2 tyli2 ri2) "Hl Hcond" => /=. iFrame. done.
    - iIntros (tyli2 ri2 bmin') "Hincl' Hl Hcond" => /=. iFrame.
      iSplitL. { iApply (typed_place_cond_incl with "Hincl' Hcond"). }
      rewrite /llft_elt_toks.
      iSplitR; first iApply big_sepL_nil; done.
  Qed.
  Global Instance typed_place_id_inst {rt} π E L (lt : ltype rt) bmin0 b r l :
    TypedPlace E L π l lt r bmin0 b [] | 9 := λ T, i2p (typed_place_id π E L lt bmin0 b r l T).

  Lemma typed_place_eqltype {rto} π E L (lt1 lt2 : ltype rto) bmin0 b r l P T :
    full_eqltype E L lt1 lt2 →
    typed_place π E L l lt2 r bmin0 b P T -∗
    typed_place π E L l lt1 r bmin0 b P T.
  Proof.
    iIntros (Heq) "Hp". iIntros (????) "#CTX #HE HL Hincl0 Hl HΦ".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [apply Heq | ].
    iDestruct ("Heq" $! b r) as "[Hi1 _]".
    iApply fupd_place_to_wp.
    iMod (ltype_incl_use with "Hi1 Hl") as "Hl"; first done. iModIntro.
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".

    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 Hl").
    iIntros (L' κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _  with "Hincl1 Hl2 [Hs] HT HL").
    iSplit.
    - destruct strong as [ strong | ]; last done.
      iIntros (rti2 tyli2 ri2) "Hl2 %Hcond". iDestruct "Hs" as "[Hs _]".
      iMod ("Hs" with "Hl2 [//]") as "(Hl & %Hcond2 & HR)".
      iFrame. iModIntro.
      iDestruct ("Hi1") as "(-> & _)".
      iPureIntro. rewrite -Hcond2. done.
    - destruct weak as [ weak | ]; last done.
      iIntros (tyli2 ri2 bmin') "Hincl Hl2 Hcond". iDestruct "Hs" as "[_ Hs]".
      iMod ("Hs" with "Hincl Hl2 Hcond") as "(Hl & Hcond & Htoks & HR)".
      iFrame. iModIntro.
      iApply ltype_eq_place_cond_trans; last done.
      iApply "Heq".
  Qed.
  (* intentionally not an instance -- since [eqltype] is transitive, that would not be a good idea. *)

  (* generic instance constructors for descending below ofty *)
  Lemma typed_place_ofty_access_val_owned π E L {rt} l (ty : type rt) (r : rt) bmin0 wl P T :
    ty_has_op_type ty PtrOp MCCopy →
    (∀ F v, ⌜lftE ⊆ F⌝ -∗
      v ◁ᵥ{π} r @ ty ={F}=∗
      ∃ (l2 : loc) (rt2 : Type) (lt2 : ltype rt2) r2 b2, ⌜v = l2⌝ ∗
        v ◁ᵥ{π} r @ ty ∗ l2 ◁ₗ[π, b2] r2 @ lt2 ∗
        typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' [] li b3 bmin rti ltyi ri
            (match strong with
             | Some strong => Some $ mk_strong (λ _, _) (λ _ _ _, ◁ ty) (λ _ _, #r) (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
             | None => None
             end)
            (match weak with
             | Some weak => Some $ mk_weak (λ _ _, ◁ ty) (λ _, #r) (λ ltyi2 ri2, llft_elt_toks κs ∗ l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)
             | None =>
                 match strong with
                  | Some strong => Some $ mk_weak (λ _ _, ◁ ty) (λ _, #r) (λ ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)
                  | None => None
                  end
              end)
        ))
    ⊢ typed_place π E L l (◁ ty) (PlaceIn r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros (Hot) "HT".
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont". iApply fupd_place_to_wp.
    iPoseProof (ofty_ltype_acc_owned ⊤ with "Hl") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    simpl. iModIntro.
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout PtrOp) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    iApply (wp_deref with "Hl"); [by right | | done | done | ].
    { by rewrite val_to_of_loc. }
    iNext. iIntros (st) "Hl Hcred Ha".
    iMod ("HT" with "[] Hv") as "(%l2 & %rt2 & %lt2 & %r2 & %b2 & -> & Hv & Hl2 & HT)"; first done.
    iMod ("Ha" with "Hl [//] Hsc Hv") as "Hl".
    iModIntro.
    iExists l2. rewrite mem_cast_id_loc. iSplitR; first done.
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hl2").
    { iApply bor_kind_incl_refl. }
    iIntros (L2 κs l3 b3 bmin rti ltyi ri strong weak) "#Hincl1 Hl3 Hcl HT HL".
    iApply ("Hcont" with "[//] Hl3 [Hcl Hl] HT HL").
    iSplit.
    -  (* strong *) iDestruct "Hcl" as "[Hcl _]". simpl.
      destruct strong as [ strong | ]; simpl; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 %Hst".
      iMod ("Hcl" with "Hl2 [//]") as "(Hl' & % & Hstrong)".
      iModIntro. iFrame. done.
    - (* weak *)
      destruct weak as [weak | ]; simpl.
      + iDestruct "Hcl" as "[_ Hcl]". simpl.
        iIntros (ltyi2 ri2 ?) "#Hincl3 Hl2 Hcond".
        iMod ("Hcl" with "Hincl3 Hl2 Hcond") as "(Hl' & Hcond & Htoks & Hweak)".
        iModIntro. iFrame. iSplitL.
        { iApply typed_place_cond_refl. done. }
        rewrite /llft_elt_toks. done.
      + destruct strong as [ strong | ]; simpl; last done.
        iDestruct "Hcl" as "[Hcl _]".
        iIntros (ltyi2 ri2 ?) "#Hincl3 Hl2 Hcond".
        iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hst".
        iMod ("Hcl" with "Hl2 [//]") as "(Hl' & %Hst' & Hweak)".
        iFrame. iModIntro.
        iSplitL. { iApply typed_place_cond_refl. done. }
        rewrite /llft_elt_toks. done.
  Qed.

  (* TODO generalize this similarly as the one above? *)
  Lemma typed_place_ofty_access_val_uniq π E L {rt} l (ty : type rt) (r : rt) bmin0 κ γ P T :
    ty_has_op_type ty PtrOp MCCopy →
    ⌜lctx_lft_alive E L κ⌝ ∗
    (∀ F v, ⌜lftE ⊆ F⌝ -∗
      v ◁ᵥ{π} r @ ty ={F}=∗
      ∃ (l2 : loc) (rt2 : Type) (lt2 : ltype rt2) r2 b2, ⌜v = l2⌝ ∗
        v ◁ᵥ{π} r @ ty ∗ l2 ◁ₗ[π, b2] r2 @ lt2 ∗
        typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' κs li b3 bmin rti ltyi ri
          (option_map (λ strong, mk_strong (λ _, _) (λ _ _ _, ◁ ty) (λ _ _, PlaceIn r)
            (* give back ownership through R *)
            (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
          (option_map (λ weak, mk_weak (λ _ _, ◁ ty) (λ _, PlaceIn r)
            (λ ltyi2 ri2, l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
        ))
    ⊢ typed_place π E L l (◁ ty) (PlaceIn r) bmin0 (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros (Hot) "(%Hal & HT)".
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont". iApply fupd_place_to_wp.
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod (Hal with "HE HL") as "(%q' & Htok & HL_cl2)"; first done.
    iPoseProof (ofty_ltype_acc_uniq lftE with "CTX Htok HL_cl2 Hl") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iMod "HF_cl" as "_".
    simpl. iModIntro.
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout PtrOp) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    iApply (wp_deref with "Hl"); [by right | | done | done | ].
    { by rewrite val_to_of_loc. }
    iNext. iIntros (st) "Hl Hcred [Ha _]".
    iMod ("HT" with "[] Hv") as "(%l2 & %rt2 & %lt2 & %r2 & %b2 & -> & Hv & Hl2 & HT)"; first done.
    iMod (fupd_mask_mono with "(Ha Hl Hv)") as "(Hl & HL)"; first done.
    iPoseProof ("HL_cl" with "HL") as "HL".
    iModIntro.
    iExists l2. rewrite mem_cast_id_loc. iSplitR; first done.
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hl2").
    { iApply bor_kind_incl_refl. }
    iIntros (L2 κs l3 b3 bmin rti ltyi ri strong weak) "#Hincl1 Hl3 Hcl HT HL".
    iApply ("Hcont" with "[//] Hl3 [Hcl Hl] HT HL").
    iSplit.
    -  (* strong *) iDestruct "Hcl" as "[Hcl _]". simpl.
      destruct strong as [ strong | ]; simpl; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 %Hst".
      iMod ("Hcl" with "Hl2 [//]") as "(Hl' & % & Hstrong)".
      iModIntro. iFrame. done.
    - (* weak *) iDestruct "Hcl" as "[_ Hcl]". simpl.
      destruct weak as [weak | ]; simpl; last done.
      iIntros (ltyi2 ri2 ?) "#Hincl3 Hl2 Hcond".
      iMod ("Hcl" with "Hincl3 Hl2 Hcond") as "(Hl' & Hcond & Htoks & Hweak)".
      iModIntro. iFrame.
      iApply typed_place_cond_refl. done.
  Qed.

  (* NOTE: we need to require it to be a simple type to get this generic lemma *)
  Lemma typed_place_ofty_access_val_shared π E L {rt} l (ty : simple_type rt) (r : rt) bmin0 κ P T :
    ty_has_op_type ty PtrOp MCCopy →
    ⌜lctx_lft_alive E L κ⌝ ∗
    (∀ F v, ⌜lftE ⊆ F⌝ -∗
      v ◁ᵥ{π} r @ ty ={F}=∗
      ∃ (l2 : loc) (rt2 : Type) (lt2 : ltype rt2) r2 b2, ⌜v = l2⌝ ∗
        v ◁ᵥ{π} r @ ty ∗ l2 ◁ₗ[π, b2] r2 @ lt2 ∗
        typed_place π E L l2 lt2 r2 b2 b2 P (λ L' κs li b3 bmin rti ltyi ri strong weak,
          T L' κs li b3 bmin rti ltyi ri
          (option_map (λ strong, mk_strong (λ _, _) (λ _ _ _, ◁ ty) (λ _ _, PlaceIn r)
            (* give back ownership through R *)
            (λ rti2 ltyi2 ri2, l2 ◁ₗ[π, b2] strong.(strong_rfn) _ ri2 @ strong.(strong_lt) _ ltyi2 ri2 ∗ strong.(strong_R) _ ltyi2 ri2)) strong)
          (option_map (λ weak, mk_weak (λ _ _, ◁ ty) (λ _, PlaceIn r)
            (λ ltyi2 ri2, l2 ◁ₗ[π, b2] weak.(weak_rfn) ri2 @ weak.(weak_lt) ltyi2 ri2 ∗ weak.(weak_R) ltyi2 ri2)) weak)
        ))
    ⊢ typed_place π E L l (◁ ty) (PlaceIn r) bmin0 (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros (Hot) "(%Hal & HT)".
    iIntros (????) "#CTX #HE HL #Hincl #Hl Hcont". iApply fupd_place_to_wp.
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (Hal with "HE HL") as "(%q' & Htok & HL_cl2)"; first done.
    iPoseProof (ofty_ltype_acc_shared ⊤ with "Hl") as "(%ly & %Halg & %Hly & Hlb & >Hb)"; first done.
    rewrite simple_type_shr_equiv. iDestruct "Hb" as "(%v & %ly' & % & %Hly' & Hloc & Hv)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.

    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iMod (frac_bor_acc with "LFT Hloc Htok") as "(%q0 & >Hloc & Hl_cl)"; first done.
    simpl. iModIntro.
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout PtrOp) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (ty_own_val_has_layout with "Hv") as "#>%Hlyv"; first done.
    iApply wp_fupd.
    iApply (wp_deref with "Hloc"); [by right | | done | done | ].
    { by rewrite val_to_of_loc. }
    iNext. iIntros (st) "Hloc Hcred".
    iMod ("HT" with "[] Hv") as "(%l2 & %rt2 & %lt2 & %r2 & %b2 & -> & Hv & Hl2 & HT)"; first done.
    iMod ("Hl_cl" with "Hloc") as "Htok".
    iMod ("HL_cl2" with "Htok") as "HL". iPoseProof ("HL_cl" with "HL") as "HL".
    iModIntro.
    iExists l2. rewrite mem_cast_id_loc. iSplitR; first done.
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hl2").
    { iApply bor_kind_incl_refl. }
    iIntros (L2 κs l3 b3 bmin rti ltyi ri strong weak) "#Hincl1 Hl3 Hcl HT HL".
    iApply ("Hcont" with "[//] Hl3 [Hcl Hv] HT HL").
    iSplit.
    -  (* strong *) iDestruct "Hcl" as "[Hcl _]". simpl.
      destruct strong as [ strong | ]; simpl; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 %Hst".
      iMod ("Hcl" with "Hl2 [//]") as "(Hl' & % & Hstrong)".
      iModIntro. iFrame. iSplitR; done.
    - (* weak *) iDestruct "Hcl" as "[_ Hcl]". simpl.
      destruct weak as [weak | ]; simpl; last done.
      iIntros (ltyi2 ri2 ?) "#Hincl3 Hl2 Hcond".
      iMod ("Hcl" with "Hincl3 Hl2 Hcond") as "(Hl' & Hcond & Htoks & Hweak)".
      iModIntro. iFrame. iSplitR; first done.
      iApply typed_place_cond_refl. done.
  Qed.



  (** Fold an [lty] to a [type].
    This is usually used after accessing a place, to push the ◁ to the outside again.
  *)
  (* TODO: consider replacing this with a tactic hint *)
  Definition cast_ltype_to_type E L {rt} (lt : ltype rt) (T : type rt → iProp Σ) : iProp Σ :=
    ∃ ty, ⌜full_eqltype E L lt (◁ ty)⌝ ∗ T ty.
  Class CastLtypeToType {rt} (E : elctx) (L : llctx) (lt : ltype rt) : Type :=
    cast_ltype_to_type_proof T : iProp_to_Prop (cast_ltype_to_type E L lt T).


  (** Update the refinement of an [ltype]. If [lb = true], this can take a logical step and thus descend below other types.
      On the other hand, if [lb = false], this should only do an update at the top-level.
      User-defined ADTs should provide an instance of this if they provide means of borrowing below their abstraction-level.

      [R] is additional ownership that will be available after the (optional) logical step. We usually use this to return lifetime tokens that we first take, e.g. when resolving below a borrow.
      (We need this because we need to return the lifetime context immediately (not below the logical step) in order to support parallel operation when stratifying products.) *)
  (** [ResolveAll] will fail if we cannot resolve some variable. [ResolveTry] will just leave a [PlaceGhost] if we cannot resolve it. *)
  Inductive ResolutionMode := ResolveAll | ResolveTry.
  Definition resolve_ghost {rt} π E L (rm : ResolutionMode) (lb : bool) l (lt : ltype rt) b (r : place_rfn rt) (T : llctx → place_rfn rt → iProp Σ → bool → iProp Σ) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      l ◁ₗ[π, b] r @ lt ={F}=∗
      ∃ L' r' R progress,
      maybe_logical_step lb F (l ◁ₗ[π, b] r' @ lt ∗ R) ∗
      llctx_interp L' ∗ T L' r' R progress.
  Class ResolveGhost {rt} π E L rm lb l (lt : ltype rt) b γ : Type :=
    resolve_ghost_proof T : iProp_to_Prop (resolve_ghost π E L rm lb l lt b γ T).

  Inductive FindObsMode : Set :=
    | FindObsModeDirect
    | FindObsModeRel.
  Definition find_observation_cont_t (rt : Type) : Type := option rt → iProp Σ.
  Definition find_observation (rt : Type) (γ : gname) (m : FindObsMode) (T : find_observation_cont_t rt) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ |={F}=> (∃ r : rt, gvar_pobs γ r ∗ T (Some r)) ∨ T None.
  Class FindObservation (rt : Type) (γ : gname) (m : FindObsMode) : Type :=
    find_observation_proof T : iProp_to_Prop (find_observation rt γ m T).


  (** *** Stratification: unfold, unblock, and fold an ltype. *)
  (** Determines whether we descend below references.
    [StratMutStrong] will only descend below places with strong ownership mode (no references).
    [StratMutWeak] will also descend below mutable references.
    [StratMutNone] will in addition descend below shared references. *)
  Inductive StratifyMutabilityMode :=
    | StratMutStrong
    | StratMutWeak
    | StratMutNone
  .
  Global Instance StratifyMutabilityMode_eqdec : EqDecision StratifyMutabilityMode.
  Proof. solve_decision. Defined.

  (** Unfold ltypes upon descending or treat ◁ as a leaf? *)
  Inductive StratifyDescendUnfoldMode :=
    | StratDoUnfold
    | StratNoUnfold
  .
  Global Instance StratifyDescendUnfoldMode_eqdec : EqDecision StratifyDescendUnfoldMode.
  Proof. solve_decision. Defined.

  (** Fold ltypes when ascending? *)
  Inductive StratifyAscendMode :=
    | StratRefoldFull     (* failure if it cannot be folded to a [◁ ty] *)
    | StratRefoldOpened   (* need to fold at least all [OpenedLtype]s, but keeping blocked places is okay. *)
    | StratNoRefold       (* don't even try to fold *)
  .
  Global Instance StratifyAscendMode_eqdec : EqDecision StratifyAscendMode.
  Proof. solve_decision. Defined.

  (** Stratification is parameterized by four flags (that don't have any semantic meaning, but guide the automation):
    - [mu] determines whether it should descend below references.
    - [mdu] determines whether it should unfold ltypes upon descending or treat ◁ as a leaf.
    - [ma] determines whether ltypes are folded on ascending.
    - [ml] determines the operation at leaf nodes. This is generic, as it is determined by the concrete operation we take.

     Note that stratification is not parameterized by a [bmin] giving the allowed updates at the current place.
     This is motivated by the fact that our operations should anyways not be influenced by how the place is owned - we have one canonical shape the type should get into.
     Instead, we prove the corresponding [typed_place_cond] condition after the fact, where needed.
   *)
  Definition stratify_ltype_cont_t := llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ.
  Definition stratify_ltype {rt} (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (mdu : StratifyDescendUnfoldMode)
      (ma : StratifyAscendMode) {M} (ml : M) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind)
      (T : stratify_ltype_cont_t) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      l ◁ₗ[π, b] r @ lt ={F}=∗
      ∃ L' R (rt' : Type) (lt' : ltype rt') (r' : place_rfn rt'),
      llctx_interp L' ∗
      ⌜ltype_st lt = ltype_st lt'⌝ ∗
      logical_step F (l ◁ₗ[π, b] r' @ lt' ∗ R) ∗
      T L' R rt' lt' r'.

  Class StratifyLtype {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b : Type :=
    stratify_ltype_proof T : iProp_to_Prop (stratify_ltype π E L mu mdu ma ml l lt r b T).

  (** Post-hook that is run after stratification visits a node.
     This is intended to be overridden by different stratification clients, depending on [ml]. *)
  Definition stratify_ltype_post_hook_cont_t := llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ.
  Definition stratify_ltype_post_hook {rt} (π : thread_id) (E : elctx) (L : llctx) {M} (ml : M) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : stratify_ltype_post_hook_cont_t) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      l ◁ₗ[π, b] r @ lt ={F}=∗
      ∃ L' R (rt' : Type) (lt' : ltype rt') (r' : place_rfn rt'),
      llctx_interp L' ∗
      ⌜ltype_st lt = ltype_st lt'⌝ ∗
      l ◁ₗ[π, b] r' @ lt' ∗ R ∗
      T L' R rt' lt' r'.
  Class StratifyLtypePostHook {rt} π E L {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b : Type :=
    stratify_ltype_post_hook_proof T : iProp_to_Prop (stratify_ltype_post_hook π E L ml l lt r b T).

  (** Low-priority instance in case no overrides are provided for this [ml]. *)
  Lemma stratify_ltype_post_hook_id {rt} (π : thread_id) (E : elctx) (L : llctx) {M} (ml : M) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : stratify_ltype_post_hook_cont_t) :
    T L True%I _ lt r ⊢ stratify_ltype_post_hook π E L ml l lt r b T.
  Proof.
    iIntros "HT" (?? ?) "CTX HE HL Hb".
    iExists _, _, _, _, _. iFrame. done.
  Qed.
  Global Instance stratify_ltype_post_hook_id_inst {rt} π E L {M} (ml : M) l (lt : ltype rt) r b :
    StratifyLtypePostHook π E L ml l lt r b | 1000 := λ T, i2p (stratify_ltype_post_hook_id π E L ml l lt r b T).

  Lemma stratify_ltype_id {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b T :
    stratify_ltype_post_hook π E L ml l lt r b T
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "HT" (?? ?) "CTX HE HL Hb".
    iMod ("HT" with "[//] [//] CTX HE HL Hb") as "(%L2 & %R2 & %rt2 & %lt2 & %r2 & HL & Hst & Hb & HR & HT)".
    iExists _, _, _, _, _. iFrame. iApply logical_step_intro. by iFrame.
  Qed.
  (* TODO: remove this instance *)
  Global Instance stratify_ltype_id_inst {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b :
    StratifyLtype π E L mu mdu ma ml l lt r b | 1000 := λ T, i2p (stratify_ltype_id π E L mu mdu ma ml l lt r b T).

  Lemma stratify_ltype_eqltype {rt} π E L mu mdu ma {M} (ml : M) l (lt1 lt2 : ltype rt) (r1 r2 : place_rfn rt) b T :
    ⌜eqltype E L b r1 r2 lt1 lt2⌝ ∗ stratify_ltype π E L mu mdu ma ml l lt2 r2 b T -∗
    stratify_ltype π E L mu mdu ma ml l lt1 r1 b T.
  Proof.
    iIntros "(%Heq & Hs)".
    iIntros (???) "#CTX #HE HL Hb".
    iPoseProof (eqltype_use F with "CTX HE HL") as "(Hvs & HL)"; [done.. | ].
    iMod ("Hvs" with "Hb") as "Hb".
    iPoseProof (eqltype_acc with "CTX HE HL") as "#Heq"; first done.
    iPoseProof (ltype_eq_syn_type with "Heq") as "->".
    iPoseProof ("Hs" with "[//] [//] CTX HE HL Hb") as ">Hb". iModIntro.
    iDestruct "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & Hstep & HT)".
    iExists L', R, rt', lt', r'. iFrame.
  Qed.

  (** Operation for unblocking (remove Blocked and ShrBlocked at leaves). *)
  Inductive StratifyUnblock :=
    | StratifyUnblockOp.
  (* We specialize all flags except for the ascend mode, as that needs to be different for different operations. *)
  Definition stratify_ltype_unblock {rt} (π : thread_id) (E : elctx) (L : llctx) (ma : StratifyAscendMode) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :=
    stratify_ltype π E L StratMutNone StratNoUnfold ma StratifyUnblockOp l lt r b T.

  (** Operation for extracting observations from dead references. *)
  Inductive StratifyExtract :=
    | StratifyExtractOp (κ : lft).
  Definition stratify_ltype_extract {rt} (π : thread_id) (E : elctx) (L : llctx) (ma : StratifyAscendMode) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (κ : lft) (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :=
    stratify_ltype π E L StratMutStrong StratDoUnfold ma (StratifyExtractOp κ) l lt r b T.



  (* TODO: even shared borrows and reads should not always refold, in order to handle ShrBlocked.
      We might want to have an operation on ltypes that captures this in some way, e.g. by "slicing" out a part that can be copied or so.
      But probably this will have to be pretty specific to those. The best I can do is to unblock beforehand, at least.

     TODO: The unblocking should, in the case of shared-borrowing from shr_blocked, not apply to all shr_blocked that we can find, but only those that are dead.
  *)


  (** ** Subtyping judgment with access to lifetime contexts. *)
  (*
    Conceptually, what is subtyping in our type system? Does subtyping in our type system  allow refinement updates?
    For now: seems to be mostly relevant for uninit. But uninit is somewhat special, maybe, at least if you consider safe Rust.
    But later for unsafe code, uninit should conceivably take a stronger role.
    Also for loops now, we should have reasonable subsumption for uninit.
      e.g. what if the loop leaves one component of a struct uninitialized in the invariant, but always initializes at the start of an iteration?

   I would like to say that (i32, i32) is a subtype of (i32, uninit i32), because I can always deinitialize something. (Note: does not work for types with non-trivial drop)
    - with non-trivial drop, an explicit destructor call beforehand would deinitialize it.
    - in general, I could alternatively say that a "storagedead" should explicitly deinitialize primitive types like i32.
  Currently, we have this weird subsume instance that only works at top-level.

  TODO: think on whether the current solution is the right way.
  *)

  (** These are the core judgments used for subtyping by the type system.
     The main entry point is from [subsume_full].
     These judgments enforce stronger requirements than, e.g., [subsume_full]:
     - they require compatibility of [ty_sidecond] and [ty_syn_type]
     - they require subtyping to be persistent
     This allows to get compatibility lemmas, including for shared references.
     However, they are not compatible with mutable references, which have stronger requirements still. *)

  (** This is called "weak" because it just requires the subtyping to hold for a particular combination of refinements. *)
  Definition weak_subtype E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) (T : iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={F}=∗
    type_incl r1 r2 ty1 ty2 ∗ llctx_interp L ∗ T.
  Class Subtype (E : elctx) (L : llctx) {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) : Type :=
    subtype_proof T : iProp_to_Prop (weak_subtype E L r1 r2 ty1 ty2 T).

  Definition weak_subltype E L {rt1 rt2} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) (T : iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={F}=∗
    ltype_incl b r1 r2 lt1 lt2 ∗ llctx_interp L ∗ T.
  Class SubLtype (E : elctx) (L : llctx) {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Type :=
    subltype_proof T : iProp_to_Prop (weak_subltype E L b r1 r2 lt1 lt2 T).

  (** Owned value subtyping (is NOT compatible with shared references). *)
  Definition owned_type_incl π {rt1 rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : iProp Σ :=
    ⌜syn_type_size_eq (ty_syn_type ty1) (ty_syn_type ty2)⌝ ∗
    (ty_sidecond ty1 -∗ ty_sidecond ty2) ∗
    (∀ (v : val), v ◁ᵥ{ π} r1 @ ty1 -∗ v ◁ᵥ{ π} r2 @ ty2).

  Lemma type_incl_owned_type_incl π {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    type_incl r1 r2 ty1 ty2 -∗ owned_type_incl π r1 r2 ty1 ty2.
  Proof.
    iIntros "(%Hst & #$ & #Hv & _)".
    iDestruct ("Hv" $! π) as "$".
    iPureIntro. rewrite Hst.
    intros ly1 ly2 Hst1 Hst2. f_equiv. by eapply syn_type_has_layout_inj.
  Qed.

  Definition owned_subtype π E L (pers : bool) {rt1 rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F,
    ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗ |={F}=> ∃ L',
    (□?pers owned_type_incl π r1 r2 ty1 ty2) ∗ llctx_interp L' ∗ T L'.
  Class OwnedSubtype (π : thread_id) (E : elctx) (L : llctx) (pers : bool) {rt1 rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : Type :=
    owned_subtype_proof T : iProp_to_Prop (owned_subtype π E L pers r1 r2 ty1 ty2 T).

  Lemma owned_subtype_weak_subtype π E L pers {rt1 rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) T :
    weak_subtype E L r1 r2 ty1 ty2 (T L)
    ⊢ owned_subtype π E L pers r1 r2 ty1 ty2 T.
  Proof.
    iIntros "HT" (???) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & ? & ?)".
    iExists L. iFrame.
    iModIntro. iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    by iApply type_incl_owned_type_incl.
  Qed.
  Global Instance owned_subtype_weak_subtype_inst π E L pers {rt1 rt2} (r1 : rt1) (r2 : rt2) ty1 ty2 :
    OwnedSubtype π E L pers r1 r2 ty1 ty2 | 1000 := λ T, i2p (owned_subtype_weak_subtype π E L pers r1 r2 ty1 ty2 T).

  Lemma owned_type_incl_refl π {rt} (ty : type rt) (r : rt) :
    ⊢ owned_type_incl π r r ty ty.
  Proof.
    iSplitR. { iPureIntro. by eapply syn_type_size_eq_refl. }
    iSplitR. { eauto. }
    iIntros (v). eauto.
  Qed.
  Lemma owned_subtype_id π E L step {rt} (r1 r2 : rt) (ty : type rt) T :
    ⌜r1 = r2⌝ ∗ T L ⊢ owned_subtype π E L step r1 r2 ty ty T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (???) "#CTX #HE HL". iExists L. iFrame.
    iModIntro. destruct step; simpl; try iModIntro. all: iApply owned_type_incl_refl.
  Qed.
  Global Instance owned_subtype_id_inst π E L step {rt} (r1 r2 : rt) (ty : type rt) :
    OwnedSubtype π E L step r1 r2 ty ty | 5 := λ T, i2p (owned_subtype_id π E L step r1 r2 ty T).

  (** Owned location subtyping with a logical step (used for extracting ghost observations) *)
  Definition owned_subltype_step (π : thread_id) E L (l : loc) {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) (lt1 : ltype rt1) (lt2 : ltype rt2) (T : llctx → iProp Σ → iProp Σ) : iProp Σ :=
    ∀ F,
    ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    l ◁ₗ[π, Owned false] r1 @ lt1 -∗ |={F}=>
    ∃ L' R,
    (logical_step F (l ◁ₗ[π, Owned false] r2 @ lt2 ∗ R)) ∗
    (⌜syn_type_size_eq (ltype_st lt1) (ltype_st lt2)⌝) ∗
    llctx_interp L' ∗ T L' R.
  Class OwnedSubltypeStep (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) (lt1 : ltype rt1) (lt2 : ltype rt2) : Type :=
    owned_subltype_step_proof T : iProp_to_Prop (owned_subltype_step π E L l r1 r2 lt1 lt2 T).

  Lemma owned_subltype_step_weak_subltype π E L l {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) lt1 lt2 T :
    weak_subltype E L (Owned false) r1 r2 lt1 lt2 (T L True)
    ⊢ owned_subltype_step π E L l r1 r2 lt1 lt2 T.
  Proof.
    iIntros "HT" (??) "CTX HE HL Hl".
    iExists L, True%I. iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iModIntro. iDestruct "Hincl" as "(%Hst & #Hincl & _)".
    iSplitL; first last.
    { iPureIntro. rewrite Hst. eapply syn_type_size_eq_refl. }
    iApply fupd_logical_step. iMod (fupd_mask_mono with "(Hincl Hl)"); first done.
    iApply logical_step_intro. eauto.
  Qed.
  Global Instance owned_subltype_step_weak_subltype_inst π E L l {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) lt1 lt2 :
    OwnedSubltypeStep π E L l r1 r2 lt1 lt2 | 1000 := λ T, i2p (owned_subltype_step_weak_subltype π E L l r1 r2 lt1 lt2 T).

  (** Subtyping for compatibility with mutable references. Importantly, this is independent of the refinement. *)
  Definition mut_subtype E L {rt} (ty1 ty2 : type rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_subtype E L ty1 ty2⌝ ∗ T.
  Class MutSubtype (E : elctx) (L : llctx) {rt} (ty1 ty2 : type rt) : Type :=
    mut_subtype_proof T : iProp_to_Prop (mut_subtype E L ty1 ty2 T).

  Definition mut_subltype E L {rt} (lt1 lt2 : ltype rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_subltype E L lt1 lt2⌝ ∗ T.
  Class MutSubLtype (E : elctx) (L : llctx) {rt} (lt1 lt2 : ltype rt) : Type :=
    mut_subltype_proof T : iProp_to_Prop (mut_subltype E L lt1 lt2 T).

  Definition mut_eqtype E L {rt} (ty1 ty2 : type rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_eqtype E L ty1 ty2⌝ ∗ T.
  Class MutEqtype (E : elctx) (L : llctx) {rt} (ty1 ty2 : type rt) : Type :=
    mut_eqtype_proof T : iProp_to_Prop (mut_eqtype E L ty1 ty2 T).

  Definition mut_eqltype E L {rt} (lt1 lt2 : ltype rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_eqltype E L lt1 lt2⌝ ∗ T.
  Class MutEqLtype (E : elctx) (L : llctx) {rt} (lt1 lt2 : ltype rt) : Type :=
    mut_eqltype_proof T : iProp_to_Prop (mut_eqltype E L lt1 lt2 T).

  (** ** Prove a proposition using subtyping *)
  Inductive ProofMode :=
  | ProveDirect
  | ProveWithStratify.
  Global Instance ProofMode_eqdecision : EqDecision ProofMode.
  Proof. solve_decision. Defined.
  (* ideally, would like to both stratify and then subsume.
     But the problem is that both will take steps in the return case.
     So for return, I could either have two steps, or keep the context fold. *)
  Definition prove_with_subtype (E : elctx) (L : llctx) (step : bool) (pm : ProofMode) (P : iProp Σ) (T : llctx → list lft → iProp Σ → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ |={F}=>
      ∃ L' κs R, maybe_logical_step step F ((if pm is ProveWithStratify then (lft_dead_list κs ={lftE}=∗ P) else P) ∗ R) ∗ llctx_interp L' ∗ T L' κs R.
  Class ProveWithSubtype (E : elctx) (L : llctx) (step : bool) (pm : ProofMode) (P : iProp Σ) : Type :=
    prove_with_subtype_proof T : iProp_to_Prop (prove_with_subtype E L step pm P T).


  Lemma prove_with_subtype_sep E L step pm P1 P2 T :
    prove_with_subtype E L step pm P1 (λ L' κs R1, prove_with_subtype E L' step pm P2 (λ L'' κs2 R2, T L'' (κs ++ κs2) (R1 ∗ R2)))
    ⊢ prove_with_subtype E L step pm (P1 ∗ P2) T.
  Proof.
    iIntros "Hs" (F ??) "#CTX #HE HL".
    iMod ("Hs" with "[//] [//] CTX HE HL") as "(%L' & %κs1 & %R1 & Ha & HL & Hs)".
    iMod ("Hs" with "[//] [//] CTX HE HL") as "(%L'' & %κs2 & %R2 & Hb & ? & ?)".
    iExists L'', (κs1 ++ κs2), (R1 ∗ R2)%I. iFrame.
    iApply (maybe_logical_step_compose with "Ha").
    iApply (maybe_logical_step_compose with "Hb").
    iApply maybe_logical_step_intro.
    iIntros "!> (Ha2 & $) (Ha1 & $)".
    destruct pm; first by iFrame.
    rewrite lft_dead_list_app. iIntros "(Ht1 & Ht2)".
    iMod ("Ha1" with "Ht1") as "$". iMod ("Ha2" with "Ht2") as "$". done.
  Qed.
  Global Instance prove_with_subtype_sep_inst E L step pm P1 P2 : ProveWithSubtype E L step pm (P1 ∗ P2) :=
    λ T, i2p (prove_with_subtype_sep E L step pm P1 P2 T).

  Lemma prove_with_subtype_exists {X} E L step pm (Φ : X → iProp Σ) T :
    (∃ x, prove_with_subtype E L step pm (Φ x) T)
    ⊢ prove_with_subtype E L step pm (∃ x, Φ x) T.
  Proof.
    iIntros "(%x & Hs)" (F ??) "#CTX #HE HL".
    iMod ("Hs" with "[//] [//] CTX HE HL") as "(%L' & %κs & %R & Hs & ? & ?)".
    iExists L', κs, R. iFrame.
    iApply (maybe_logical_step_wand with "[] Hs").
    destruct pm. { iIntros "(? & ?)". eauto with iFrame. }
    iIntros "(Ha & $) Htok". iMod ("Ha" with "Htok") as "?". eauto with iFrame.
  Qed.
  Global Instance prove_with_subtype_exists_inst {X} E L step pm (Φ : X → iProp Σ) : ProveWithSubtype E L step pm (∃ x, Φ x) :=
    λ T, i2p (prove_with_subtype_exists E L step pm Φ T).

  (** For ofty location ownership, we have special handling to stratify first, if possible.
      This only happens in the [ProveWithStratify] proof mode though, because we sometimes directly want to get into [Subsume]. *)
  Lemma prove_with_subtype_ofty_step π E L (l : loc) bk {rt} (ty : type rt) (r : place_rfn rt) T :
    find_in_context (FindLoc l π) (λ '(existT rt' (lt', r', bk')),
      stratify_ltype π E L StratMutNone StratNoUnfold StratRefoldFull StratifyUnblockOp l lt' r' bk' (λ L2 R2 rt2 lt2 r2,
        (* can't take a step, because we already took one. *)
        (*owned_subltype_step E L false (l ◁ₗ[π, bk'] r' @ lt') (l ◁ₗ[π, bk] r @ ◁ ty) T*)
        match ltype_blocked_lfts lt2 with
        | [] =>
            (* we could unblock everything, directly subsume *)
            ⌜bk = bk'⌝ ∗ weak_subltype E L2 bk r2 r lt2 (◁ ty) (T L2 [] R2)
        | κs =>
            ⌜bk = bk'⌝ ∗ weak_subltype E L2 bk r2 r (ltype_core lt2) (◁ ty) (T L2 κs R2)
        end))
    ⊢ prove_with_subtype E L true ProveWithStratify (l ◁ₗ[π, bk] r @ (◁ ty))%I T.
  Proof.
    rewrite /FindLoc.
    iIntros "Ha". iDestruct "Ha" as ([rt' [[lt' r'] bk']]) "(Hl & Ha)". simpl.
    iIntros (???) "#CTX #HE HL". iMod ("Ha" with "[//] [//] CTX HE HL Hl") as "(%L2 & %R2 & %rt2 & %lt2 & %r2 & HL & %Hsteq & Hstep & HT)".
    destruct (decide (ltype_blocked_lfts lt2 = [])) as [-> | Hneq].
    - iDestruct "HT" as "(<- & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iExists _, [], _. iFrame.
      simpl. iModIntro. iApply logical_step_fupd. iApply (logical_step_wand with "Hstep").
      iIntros "(Hl & $)".
      iDestruct "Hincl" as "(_ & Hincl & _)".
      iMod (ltype_incl'_use with "Hincl Hl"); first done.
      iModIntro. by iIntros "_ !>".
    - iAssert (⌜bk = bk'⌝ ∗ weak_subltype E L2 bk r2 r (ltype_core lt2) (◁ ty) (T L2 (ltype_blocked_lfts lt2) R2))%I with "[HT]" as "(<- & HT)".
      { destruct (ltype_blocked_lfts lt2); done. }
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iModIntro. iExists _, _, _. iFrame.
      iApply (logical_step_wand with "Hstep").
      iIntros "(Hl & $)".
      iIntros "Hdead".
      iPoseProof (imp_unblockable_blocked_dead lt2) as "Hunblock".
      iDestruct "Hincl" as "(_ & Hincl & _)".
      iMod (imp_unblockable_use with "Hunblock Hdead Hl") as "Hl"; first done.
      by iMod (ltype_incl'_use with "Hincl Hl") as "$".
  Qed.
  Global Instance prove_with_subtype_ofty_step_inst π E L (l : loc) bk {rt} (ty : type rt) (r : place_rfn rt) : ProveWithSubtype E L true ProveWithStratify (l ◁ₗ[π, bk] r @ ◁ ty)%I | 500 :=
    λ T, i2p (prove_with_subtype_ofty_step π E L l bk ty r T).

  (* TODO: this is a hack because we can't eliminate (stratify_ltype ... (subsume_full ...)) into prove_with_subtype, so we can't call into subsume to do the Owned false -> Owned true adjustment... *)
  Lemma prove_with_subtype_ofty_step_owned_true π E L (l : loc) {rt} (ty : type rt) (r : place_rfn rt) T :
    find_in_context (FindLoc l π) (λ '(existT rt' (lt', r', bk')),
      stratify_ltype π E L StratMutNone StratNoUnfold StratRefoldFull StratifyUnblockOp l lt' r' bk' (λ L2 R2 rt2 lt2 r2,
        (* can't take a step, because we already took one. *)
        (*owned_subltype_step E L false (l ◁ₗ[π, bk'] r' @ lt') (l ◁ₗ[π, bk] r @ ◁ ty) T*)
        match bk' with
        | Owned wl =>
          prove_with_subtype E L2 false ProveDirect (maybe_creds (negb wl) ∗ ⌜if negb wl then match ltype_lty rt2 lt2 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end else True⌝) (λ L3 κs2 R3,
            match ltype_blocked_lfts lt2 with
            | [] =>
                (* we could unblock everything, directly subsume *)
                weak_subltype E L3 (Owned true) r2 r lt2 (◁ ty) (T L3 κs2 (R2 ∗ R3))
            | κs =>
                weak_subltype E L3 (Owned true) r2 r (ltype_core lt2) (◁ ty) (T L3 (κs ++ κs2) (R2 ∗ R3))
            end)
        | _ => False
        end))
    ⊢ prove_with_subtype E L true ProveWithStratify (l ◁ₗ[π, Owned true] r @ (◁ ty))%I T.
  Proof.
    rewrite /FindLoc.
    iIntros "Ha". iDestruct "Ha" as ([rt' [[lt' r'] bk']]) "(Hl & Ha)". simpl.
    iIntros (???) "#CTX #HE HL". iMod ("Ha" with "[//] [//] CTX HE HL Hl") as "(%L2 & %R2 & %rt2 & %lt2 & %r2 & HL & %Hsteq & Hstep & HT)".
    destruct bk' as [ wl | | ]; [ | done..].
    iMod ("HT" with "[] [] CTX HE HL") as "(%L3 & %κs2 & %R3 & Hs & HL & HT)"; [done.. | ].
    simpl. iMod ("Hs") as "((Hcreds & %) & HR3)".
    iAssert (logical_step F (l ◁ₗ[ π, Owned true] r2 @ lt2 ∗ R2)) with "[Hcreds Hstep]" as "Hstep".
    { iApply logical_step_fupd. iApply (logical_step_wand with "Hstep").
      iIntros "(Ha & $)". destruct wl; first done.
      iPoseProof (ltype_own_Owned_false_true with "Ha Hcreds") as "$"; done. }
    destruct (decide (ltype_blocked_lfts lt2 = [])) as [-> | Hneq].
    - iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iExists _, κs2, _. iFrame.
      simpl. iModIntro. iApply logical_step_fupd. iApply (logical_step_wand with "Hstep").
      iIntros "(Hl & $)".
      iDestruct "Hincl" as "(_ & Hincl & _)".
      iMod (ltype_incl'_use with "Hincl Hl"); first done.
      iModIntro. iFrame. by iIntros "_ !>".
    - iAssert (weak_subltype E L3 (Owned true) r2 r (ltype_core lt2) (◁ ty) (T L3 (ltype_blocked_lfts lt2 ++ κs2) (R2 ∗ R3)))%I with "[HT]" as "HT".
      { destruct (ltype_blocked_lfts lt2); simpl; first done. done. }
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iModIntro. iExists _, _, _. iFrame.
      iApply (logical_step_wand with "Hstep").
      iIntros "(Hl & $)".
      iFrame. iIntros "Hdead".
      iPoseProof (imp_unblockable_blocked_dead lt2) as "Hunblock".
      iDestruct "Hincl" as "(_ & Hincl & _)".
      rewrite lft_dead_list_app. iDestruct "Hdead" as "(Hdead & _)".
      iMod (imp_unblockable_use with "Hunblock Hdead Hl") as "Hl"; first done.
      by iMod (ltype_incl'_use with "Hincl Hl") as "$".
  Qed.
  Global Instance prove_with_subtype_ofty_step_owned_true_inst π E L (l : loc) {rt} (ty : type rt) (r : place_rfn rt) : ProveWithSubtype E L true ProveWithStratify (l ◁ₗ[π, Owned true] r @ ◁ ty)%I | 499 :=
    λ T, i2p (prove_with_subtype_ofty_step_owned_true π E L l ty r T).

  Lemma prove_with_subtype_pure E L step pm (P : Prop) T :
    ⌜P⌝ ∗ T L [] True ⊢ prove_with_subtype E L step pm (⌜P⌝) T.
  Proof.
    iIntros "(% & HT)". iIntros (???) "#CTX #HE HL".
    iExists L, [], True%I. iFrame.
    destruct pm.
    - by iApply maybe_logical_step_intro.
    - iIntros "!>". iApply maybe_logical_step_intro. iSplitL; last done.
      iIntros "_ !>". done.
  Qed.
  Global Instance prove_with_subtype_pure_inst E L step pm (P : Prop) : ProveWithSubtype E L step pm (⌜P⌝) | 50:=
    λ T, i2p (prove_with_subtype_pure E L step pm P T).

  Lemma prove_with_subtype_simplify_goal E L step pm P T (n : N) {SG : SimplifyGoal P (Some n)} :
    prove_with_subtype E L step pm (SG True).(i2p_P) T
    ⊢ prove_with_subtype E L step pm P T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL".
    iMod ("Ha" with "[//] [//] CTX HE HL") as "(%L' & %κs & %R & Ha & HL & HT)".
    unfold SimplifyGoal in SG.
    destruct SG as [P' Ha].
    iExists L', κs, R. iFrame.
    iApply (maybe_logical_step_wand with "[] Ha").
    iIntros "(Ha & $)".
    destruct pm.
    - iPoseProof (Ha with "Ha") as "Ha".
      rewrite /simplify_goal. iDestruct "Ha" as "($ & _)".
    - iIntros "Hdead". iMod ("Ha" with "Hdead") as "Ha".
      iPoseProof (Ha with "Ha") as "Ha".
      rewrite /simplify_goal. iDestruct "Ha" as "($ & _)".
      done.
  Qed.
  Global Instance prove_with_subtype_simplify_goal_inst E L step pm P {SG : SimplifyGoal P (Some 0%N)} :
    ProveWithSubtype E L step pm P := λ T, i2p (prove_with_subtype_simplify_goal E L step pm P T 0).

  (** Note: run fully-fledged simplification only after context search *)
  Global Instance prove_with_subtype_simplify_goal_full_inst E L step pm P n {SG : SimplifyGoal P (Some n)} :
    ProveWithSubtype E L step pm P | 1001 := λ T, i2p (prove_with_subtype_simplify_goal E L step pm P T n).

  (* Make low priority to enable overrides before we initiate context search. *)
  Lemma prove_with_subtype_find_direct E L step pm P T `{!CheckOwnInContext P} :
    P ∗ T L [] True%I
    ⊢ prove_with_subtype E L step pm P T.
  Proof.
    iIntros "(HP & HT)". iIntros (???) "#CTX #HE HL".
    iExists L, [], True%I. iFrame.
    iApply maybe_logical_step_intro. iSplitL; last done.
    destruct pm; first done. iIntros "!> _ !>". done.
  Qed.
  Global Instance prove_with_subtype_find_direct_inst E L step pm P `{!CheckOwnInContext P} :
    ProveWithSubtype E L step pm P | 1000 := λ T, i2p (prove_with_subtype_find_direct E L step pm P T).

  Lemma prove_with_subtype_primitive E L step pm P `{Hrel : !RelatedTo P} T :
    find_in_context Hrel.(rt_fic) (λ a,
      subsume_full E L step (fic_Prop Hrel.(rt_fic) a) P (λ L, T L []))
    ⊢ prove_with_subtype E L step pm P T.
  Proof.
    iIntros "(%a & Ha & Hsub)" (???) "#CTX #HE HL".
    iMod ("Hsub" with "[//] [//] CTX HE HL Ha") as "(%L2 & %R & Ha & ? & ?)".
    iModIntro. iExists _, _, _. iFrame.
    iApply (maybe_logical_step_wand with "[] Ha").
    iIntros "(? & $)".
    destruct pm; first done. iIntros "_ !>". done.
  Qed.
  (* only after running full simplification *)
  Global Instance prove_with_subtype_primitive_inst E L step pm P `{Hrel : !RelatedTo P} : ProveWithSubtype E L step pm P | 1002 :=
    λ T, i2p (prove_with_subtype_primitive E L step pm P T).

  Lemma prove_with_subtype_case_destruct E L step pm {A} (b : A) P T :
    case_destruct b (λ b r, (prove_with_subtype E L step pm (P b r) T))
    ⊢ prove_with_subtype E L step pm (case_destruct b P) T.
  Proof.
    rewrite /case_destruct. apply prove_with_subtype_exists.
  Qed.
  Global Instance prove_with_subtype_case_destruct_inst E L step pm {A} (b : A) P :
    ProveWithSubtype E L step pm (case_destruct b P) :=
    λ T, i2p (prove_with_subtype_case_destruct E L step pm b P T).


  Lemma prove_with_subtype_if_decide_true E L step pm P `{!Decision P} `{!CanSolve P} P1 P2 T :
    prove_with_subtype E L step pm P1 T ⊢
    prove_with_subtype E L step pm (if (decide P) then P1 else P2) T.
  Proof. rewrite decide_True; done. Qed.
  Global Instance prove_with_subtype_decide_true_inst E L step pm P `{!Decision P} `{!CanSolve P} P1 P2 :
    ProveWithSubtype E L step pm (if (decide P) then P1 else P2) :=
      λ T, i2p (prove_with_subtype_if_decide_true E L step pm P P1 P2 T).
  Lemma prove_with_subtype_if_decide_false E L step pm P `{!Decision P} `{!CanSolve (¬ P)} P1 P2 T :
    prove_with_subtype E L step pm P2 T ⊢
    prove_with_subtype E L step pm (if (decide P) then P1 else P2) T.
  Proof. rewrite decide_False; done. Qed.
  Global Instance prove_with_subtype_decide_false_inst E L step pm P `{!Decision P} `{!CanSolve (¬ P)} P1 P2 :
    ProveWithSubtype E L step pm (if (decide P) then P1 else P2) :=
      λ T, i2p (prove_with_subtype_if_decide_false E L step pm P P1 P2 T).

  Lemma prove_with_subtype_li_trace E L step pm {M} (m : M) P T :
    li_trace m (prove_with_subtype E L step pm P T)
    ⊢ prove_with_subtype E L step pm (li_trace m P) T.
  Proof.
    rewrite /li_trace. done.
  Qed.
  Global Instance prove_with_subtype_li_trace_inst E L step pm {M} (m : M) P :
    ProveWithSubtype E L step pm (li_trace m P) :=
    λ T, i2p (prove_with_subtype_li_trace E L step pm m P T).

  Lemma prove_with_subtype_scrounge_credits E L step pm (n : nat) T :
    find_in_context (FindCreditStore) (λ '(c, a),
      ⌜n ≤ c⌝ ∗ (credit_store (c - n)%nat a -∗ T L [] True%I))
    ⊢ prove_with_subtype E L step pm (£ n) T.
  Proof.
    iIntros "Ha". rewrite /FindCreditStore.
    iDestruct "Ha" as ([c a]) "(Hstore  & %Hn & HT)". simpl.
    iPoseProof (credit_store_scrounge _ _ n with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "HT".
    iIntros (???) "CTX HE HL". iModIntro. iExists _, _, _. iFrame.
    iApply maybe_logical_step_intro.
    iSplitL; last done.
    destruct pm; first done. iIntros "_ !>". done.
  Qed.
  Global Instance prove_with_subtype_scrounge_credits_inst E L step pm (n : nat) :
    ProveWithSubtype E L step pm (£ n) | 10 := λ T, i2p (prove_with_subtype_scrounge_credits E L step pm n T).

  Lemma prove_with_subtype_scrounge_atime E L step pm (n : nat) T :
    find_in_context (FindCreditStore) (λ '(c, a),
      ⌜n ≤ a⌝ ∗ (credit_store c (a - n)%nat -∗ T L [] True%I))
    ⊢ prove_with_subtype E L step pm (atime n) T.
  Proof.
    iIntros "Ha". rewrite /FindCreditStore.
    iDestruct "Ha" as ([c a]) "(Hstore  & %Hn & HT)". simpl.
    iPoseProof (credit_store_acc with "Hstore") as "(Hcred & Hat & Hcl)".
    replace (S a) with (S (a - n) + n)%nat by lia.
    iDestruct "Hat" as "(Hat & Hat')".
    iPoseProof ("Hcl" with "Hcred Hat") as "Hstore".
    iPoseProof ("HT" with "Hstore") as "HT".
    iIntros (???) "CTX HE HL". iModIntro. iExists _, _, _. iFrame.
    iApply maybe_logical_step_intro.
    iSplitL; last done.
    destruct pm; first done. iIntros "_ !>". done.
  Qed.
  Global Instance prove_with_subtype_scrounge_atime_inst E L step pm (n : nat) :
    ProveWithSubtype E L step pm (atime n) | 10 := λ T, i2p (prove_with_subtype_scrounge_atime E L step pm n T).


  (* TODO figure out how to nicely key the Rel2. Is there always a canonical order in which we want to have that?
     doesn't seem like it. *)
  Lemma prove_with_subtype_inherit_manual E L step pm {K} (k : K) κ κ' P Q T :
    lctx_lft_incl E L κ' κ →
    Inherit κ' k Q -∗
    (Q -∗ P) -∗
    T L [] True%I -∗
    prove_with_subtype E L step pm (Inherit κ k P) T.
  Proof.
    iIntros (Hi1) "Hinh HQP HT".
    iIntros (???) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1"; first apply Hi1.
    (*iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hi2. *)
    iPoseProof (Inherit_mono with "Hincl1 Hinh") as "Hinh".
    iPoseProof (Inherit_update with "[HQP] Hinh") as "Hinh".
    { iIntros (?) "HQ". iApply ("HQP" with "HQ"). }
    iExists _, _, _. iFrame. iApply maybe_logical_step_intro.
    iModIntro. iL. destruct pm; iFrame. eauto.
  Qed.

  (* We could make this an instance, but do not want to: it would sometimes make goals unprovable where stepping in manually would help *)
  Lemma prove_with_subtype_default E L step pm P T :
    P ∗ T L [] True ⊢
    prove_with_subtype E L step pm P T.
  Proof.
    iIntros "(? & ?)".
    iIntros (???) "???". iModIntro.
    iExists _, _, _. iFrame.
    iApply maybe_logical_step_intro. iL.
    destruct pm; eauto with iFrame.
  Qed.

  (** ** Prove a typed_place_cond (used together with [stratify_ltype]) *)

  (* Lattice with AllowWeak < AllowStrong. *)
  Inductive access_allowed : Type :=
  | AllowStrong
  | AllowWeak.
  (* Lattice with ResultStrong < ResultWeak *)
  Inductive access_result (rti rti2 : Type) : Type :=
  | ResultWeak (Heq : rti = rti2)
  | ResultStrong.
  Global Arguments ResultStrong {_ _}.
  Global Arguments ResultWeak {_ _}.

  Definition access_result_meet {rti1 rti2 rti3 : Type} (r1 : access_result rti1 rti2) (r2 : access_result rti2 rti3) : access_result rti1 rti3 :=
    match r1, r2 with
    | ResultWeak Heq1, ResultWeak Heq2 => ResultWeak $ eq_trans Heq1 Heq2
    | _, _ => ResultStrong
    end.
  Lemma access_result_meet_strong_r {rt1 rt2 rt3} (o : access_result rt1 rt2) :
    @access_result_meet rt1 rt2 rt3 o ResultStrong = ResultStrong.
  Proof. destruct o; done. Qed.
  Lemma access_result_meet_strong_l {rt1 rt2 rt3} (o : access_result rt2 rt3) :
    @access_result_meet rt1 rt2 rt3 ResultStrong o = ResultStrong.
  Proof. done. Qed.

  Lemma access_result_lift (f : Type → Type) {rt1 rt2} :
    access_result rt1 rt2 → access_result (f rt1) (f rt2).
  Proof.
    refine (λ Ha,
      match Ha with
      | ResultWeak Heq => ResultWeak _
      | ResultStrong => ResultStrong
      end).
    exact (rew [λ rt, f rt1 = f rt] Heq in @eq_refl _ (f rt1)).
  Defined.

  Definition access_result_refl {rt} : access_result rt rt := ResultWeak (eq_refl).



  Definition prove_place_cond (E : elctx) (L : llctx) {rt1 rt2} (bmin : bor_kind) (lt1 : ltype rt1) (lt2 : ltype rt2) (T : access_result rt1 rt2 → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      llctx_interp L ∗ ∃ upd,
        (match upd with ResultWeak _ => typed_place_cond_ty bmin lt1 lt2 | ResultStrong => ⌜ltype_st lt1 = ltype_st lt2⌝ end) ∗
        T upd.
  Class ProvePlaceCond (E : elctx) (L : llctx) {rt1 rt2} (bmin : bor_kind) (lt1 : ltype rt1) (lt2 : ltype rt2) : Type :=
    prove_place_cond_proof T : iProp_to_Prop (prove_place_cond E L bmin lt1 lt2 T).

  Lemma prove_place_cond_eqltype_l E L bmin {rt1 rt2} (lt1 lt1' : ltype rt1) (lt2 : ltype rt2) T :
    full_eqltype E L lt1 lt1' →
    prove_place_cond E L bmin lt1' lt2 T -∗
    prove_place_cond E L bmin lt1 lt2 T.
  Proof.
    iIntros (Heq) "Hcond". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [done.. | ].
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hcond)".
    iDestruct "Hcond" as "(%upd & Hcond & HT)".
    iExists upd. iFrame.
    destruct upd.
    - iApply ltype_eq_place_cond_ty_trans; done.
    - iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
  Qed.
  Lemma prove_place_cond_eqltype_r E L bmin {rt1 rt2} (lt1 : ltype rt1) (lt2 lt2' : ltype rt2) T :
    full_eqltype E L lt2 lt2' →
    prove_place_cond E L bmin lt1 lt2' T -∗
    prove_place_cond E L bmin lt1 lt2 T.
  Proof.
    iIntros (Heq) "Hcond". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [done.. | ].
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hcond)".
    iDestruct "Hcond" as "(%upd & Hcond & HT)".
    iExists upd. iFrame.
    destruct upd.
    - iApply (place_cond_ty_ltype_eq_trans with "Hcond").
      iModIntro. iIntros (??). iApply ltype_eq_sym. done.
    - iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". done.
  Qed.


  Definition prove_place_rfn_cond {rt1 rt2} (b : bool) (bmin : bor_kind) (r1 : place_rfn rt1) (r2 : place_rfn rt2) (T : iProp Σ) : iProp Σ :=
    (if b then typed_place_cond_rfn bmin r1 r2 else True%I) ∗ T.
  Class ProvePlaceRfnCond {rt1 rt2} b bmin (r1 : place_rfn rt1) (r2 : place_rfn rt2) :=
    prove_place_rfn_cond_proof T : iProp_to_Prop (prove_place_rfn_cond b bmin r1 r2 T).

  Lemma prove_place_rfn_cond_shared {rt} κ (r1 r2 : place_rfn rt) T :
    ⌜r1 = r2⌝ ∗ T ⊢ prove_place_rfn_cond true (Shared κ) r1 r2 T.
  Proof.
    iIntros "(-> & HT)". iSplitR; last done.
    done.
    (*iExists eq_refl. done.*)
  Qed.
  Global Instance prove_place_rfn_cond_shared_inst {rt} κ (r1 r2 : place_rfn rt) :
    ProvePlaceRfnCond true (Shared κ) r1 r2 := λ T, i2p (prove_place_rfn_cond_shared κ r1 r2 T).

  Lemma prove_place_rfn_cond_shared' {rt} κ (r1 r2 : place_rfn rt) T :
    T ⊢ prove_place_rfn_cond false (Shared κ) r1 r2 T.
  Proof.
    iIntros "HT". iSplitR; last done. done.
  Qed.
  Global Instance prove_place_rfn_cond_shared'_inst {rt} κ (r1 r2 : place_rfn rt) :
    ProvePlaceRfnCond false (Shared κ) r1 r2 := λ T, i2p (prove_place_rfn_cond_shared' κ r1 r2 T).

  Lemma prove_place_rfn_cond_uniq {rt1 rt2} b κ γ (r1 : place_rfn rt1) (r2 : place_rfn rt2) T :
    T ⊢ prove_place_rfn_cond b (Uniq κ γ) r1 r2 T.
  Proof.
    iIntros "HT". iSplitR; last done. destruct b; done.
  Qed.
  Global Instance prove_place_rfn_cond_uniq_inst {rt} b κ γ (r1 r2 : place_rfn rt) :
    ProvePlaceRfnCond b (Uniq κ γ) r1 r2 := λ T, i2p (prove_place_rfn_cond_uniq b κ γ r1 r2 T).

  Lemma prove_place_rfn_cond_owned {rt1 rt2} b wl (r1 : place_rfn rt1) (r2 : place_rfn rt2) T :
    T ⊢ prove_place_rfn_cond b (Owned wl) r1 r2 T.
  Proof.
    iIntros "HT". iSplitR; last done. destruct b; done.
  Qed.
  Global Instance prove_place_rfn_cond_owned_inst {rt} b wl (r1 r2 : place_rfn rt) :
    ProvePlaceRfnCond b (Owned wl) r1 r2 := λ T, i2p (prove_place_rfn_cond_owned b wl r1 r2 T).

  (** ** Solving [lctx_lft_alive_count] *)
  (** the continuation gets the list of opened lifetimes + the new local lifetime context *)
  Definition lctx_lft_alive_count_goal (E : elctx) (L : llctx) (κ : lft)
      (T : (list lft) * llctx → iProp Σ) : iProp Σ :=
    ∃ κs L', ⌜lctx_lft_alive_count E L κ κs L'⌝ ∗ T (κs, L').
  Program Definition lctx_lft_alive_count_hint E L κ (κs : list lft) (L' : llctx) :
    lctx_lft_alive_count E L κ κs L' →
    LiTactic (lctx_lft_alive_count_goal E L κ) := λ a, {|
      li_tactic_P T := T (κs, L');
    |}.
  Next Obligation.
    simpl. iIntros (E L κ κs L' ? T) "HT".
    iExists κs, L'. iFrame. done.
  Qed.

  (** ** Releasing lifetime tokens *)
  Definition llctx_release_toks_goal (L : llctx) (κs : list lft) (T : llctx → iProp Σ) : iProp Σ :=
    ∃ L', ⌜llctx_release_toks L κs L'⌝ ∗ T L'.
  Program Definition llctx_release_toks_hint L κs (L' : llctx) :
    llctx_release_toks L κs L' →
    LiTactic (llctx_release_toks_goal L κs) := λ a, {|
      li_tactic_P T := T L';
    |}.
  Next Obligation.
    iIntros (L κs L' ? T) "HT". iExists L'. iFrame. done.
  Qed.

  Lemma introduce_with_hooks_lft_toks E L κs T :
    li_tactic (llctx_release_toks_goal L κs) T ⊢
    introduce_with_hooks E L (llft_elt_toks κs) T.
  Proof.
    rewrite /li_tactic /llctx_release_toks_goal.
    iIntros "(%L' & %HL & HT)".
    iIntros (F ?) "#HE HL Htoks".
    iMod (llctx_return_elt_toks _ _ L' with "HL Htoks") as "HL"; first done.
    eauto with iFrame.
  Qed.
  Global Instance introduce_with_hooks_lft_toks_inst E L κs : IntroduceWithHooks E L (llft_elt_toks κs) | 10 :=
    λ T, i2p (introduce_with_hooks_lft_toks E L κs T).



  (** ** Some utilities for finishing a place access by either using the strong or the weak VS *)


  (* When finishing a place access:
      - done a weak update without rt change
      - done a strong update without rt change
      - done a strong update with rt change

     In which cases do I do a strong update? Currently, this is an input to typed_read_end etc.
        typed_read_end etc. should know which access is allowed: is it allowed to do an rt change or not? is it allowed to do a strong update or not?
        for most practical purposes, however, we don't need to distinguish strong updates and rt changes.
      So let's just keep the strong update flag for now.
  *)


  Definition typed_place_finish π (E : elctx) (L : llctx) {rto rti rti2} (strong : option (strong_ctx rti)) (weak : option (weak_ctx rto rti))
    (upd : access_result rti rti2) (R : iProp Σ) (R_weak : iProp Σ) l b (lt2 : ltype rti2) (r2 : place_rfn rti2) (T : llctx → iProp Σ) : iProp Σ :=
    (* use a weak update if possible, otherwise a strong update *)
    match upd with
    | ResultWeak Heq =>
        match weak with
        | Some weak =>
            l ◁ₗ[π, b] (weak.(weak_rfn) (rew <- Heq in r2)) @ (weak.(weak_lt) (rew <- Heq in lt2) (rew <- Heq in r2)) -∗
            weak.(weak_R) (rew <- Heq in lt2) (rew <- Heq in r2) -∗
            introduce_with_hooks E L (R_weak ∗ R) T
        | None =>
          match strong with
          | Some strong =>
              l ◁ₗ[π, b] (strong.(strong_rfn) rti2 r2) @ (strong.(strong_lt) rti2 lt2 r2) -∗
              strong.(strong_R) rti2 lt2 r2 -∗
              introduce_with_hooks E L R T
          | None => False
          end
        end
    | ResultStrong =>
        match strong with
        | Some strong =>
          l ◁ₗ[π, b] (strong.(strong_rfn) rti2 r2) @ (strong.(strong_lt) rti2 lt2 r2) -∗
          strong.(strong_R) rti2 lt2 r2 -∗
          introduce_with_hooks E L R T
        | _ => False
        end
    end.

  Lemma typed_place_finish_elim π (E : elctx) (L : llctx) {rto rti rti2} (strong : option (strong_ctx rti)) (weak : option (weak_ctx rto rti))
    (upd : access_result rti rti2) (R : iProp Σ) (R_weak : iProp Σ) l b (lt2 : ltype rti2) (r2 : place_rfn rti2) (T : llctx → iProp Σ) :
    typed_place_finish π E L strong weak upd R R_weak l b lt2 r2 T -∗
    (∃ weak' Heq, ⌜weak = Some weak'⌝ ∗ ⌜upd = ResultWeak Heq⌝ ∗
      (l ◁ₗ[π, b] (weak'.(weak_rfn) (rew <- Heq in r2)) @ (weak'.(weak_lt) (rew <- Heq in lt2) (rew <- Heq in r2)) -∗
      weak'.(weak_R) (rew <- Heq in lt2) (rew <- Heq in r2) -∗
      introduce_with_hooks E L (R_weak ∗ R) T)) ∨
    (∃ strong', ⌜strong = Some strong'⌝ ∗ (⌜weak = None⌝ ∨ ⌜upd = ResultStrong⌝) ∗
      (l ◁ₗ[π, b] (strong'.(strong_rfn) rti2 r2) @ (strong'.(strong_lt) rti2 lt2 r2) -∗
      strong'.(strong_R) rti2 lt2 r2 -∗
      introduce_with_hooks E L R T)).
  Proof.
    iIntros "Ha". destruct upd as [ Heq | ]; first destruct weak as [ weak | ].
    - iLeft. iExists _, _. iR. iR. done.
    - destruct strong as [ strong | ]; last done. iRight. iExists _. iR.
      iSplitR; last done. by iLeft.
    - destruct strong as [ strong | ]; last done. iRight. iExists _. iR.
      iSplitR; last done. by iRight.
  Qed.

  (** ** Read judgments *)
  (* In a given lifetime context, we can read from [e], in the process determining that [e] reads from a location [l] and getting a value typed at a type [ty] with a layout compatible with [ot], and afterwards, the remaining [T L' v ty' r'] needs to be proved, where [ty'] is the new type of the read value and [v] is the read value.

    The prover will prove a [typed_read] in a number of steps:
     - first, the place that is read is checked with [typed_place].
     - then, the actual type-checking of the read is performed with [typed_read_end]
   *)
  (* Parameters:
      - [π] : the thread id
      - [E] : external lifetime context
      - [L] : local lifetime context
      - [e] : read expression
      - [ot] : [op_type] to use for the read
      - [T] : continuation for the client, receiving the following arguments:
          + [L' : llctx] : the updated lifetime context, as the read may have side-effects
          + [v : val] : the read value
          + [rt' : Type] : the refinement type of the read value
          + [ty' : type rt] : the type of the read value
          + [r' : rt] : the refinement of the read value
  *)
  Definition typed_read (π : thread_id) (E : elctx) (L : llctx) (e : expr) (ot : op_type) (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      (∀ (l : loc),
        (* the client gets ownership of the read value and fractional ownership of the location *)
        (* this is below a logical step in order to execute stratification here.
          TODO we may want to move this into a separate thing, together with moving the skip in Use to a separate annotation *)
        logical_step F (∃ v q rt (ty : type rt) r,
          ⌜l `has_layout_loc` ot_layout ot⌝ ∗ ⌜v `has_layout_val` ot_layout ot⌝ ∗ l ↦{q} v ∗ ▷ v ◁ᵥ{π} r @ ty ∗
          (* additionally, the client can assume that it can transform this to the ownership required by the continuation T *)
          logical_step F (∀ st,
              l ↦{q} v -∗
              v ◁ᵥ{π} r @ ty ={F}=∗
              ∃ L' rt' (ty' : type rt') r',
                llctx_interp L' ∗ na_own π shrE ∗
                mem_cast v ot st ◁ᵥ{π} r' @ ty' ∗
                T L' (mem_cast v ot st) rt' ty' r')) -∗
        (* under this knowledge, the client has to prove the postcondition *)
        Φ (val_of_loc l)) -∗
      (* TODO: maybe different mask F *)
      WP e {{ Φ }})%I.


  (* The core of reading from a location [l] with [ot] that is typed at [lt] and immediately owned at [b2] below a path with intersected [bor_kind] [bmin].

    This is called [typed_read_end] because it ends the chain of typing rules applied to do the read, after typing all the places that are accessed to get to [l].

    The continuation [T] has access to the new place type and refinement of [l] after reading ([lt']),
    and the type ([ty3]) and refinement that is "moved out" of [l] for the client to keep (i.e., the ownership of the read value)
  *)
  Definition typed_read_end_cont_t (rt : Type) : Type :=
    llctx → val → ∀ rt3, type rt3 → rt3 → ∀ rt', ltype rt' → place_rfn rt' → access_result rt rt' → iProp Σ.
  Definition typed_read_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 bmin : bor_kind) (ac : access_allowed) (ot : op_type) (T : typed_read_end_cont_t rt) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      bmin ⊑ₖ b2 -∗
      (* given ownership of the read location *)
      l ◁ₗ[π, b2] r @ lt ={F}=∗
      ∃ q v
        (* the type of the object we read *)
        (* TODO: why do we quantify over rt2? can we also make this rt? *)
        rt2 (ty2 : type rt2) r2,
        (* we can provide fractional permission ownership of the stored value [v] to the client,
          typed at an actual type [ty2] (that we can extract from [lt]) *)
        ⌜l `has_layout_loc` ot_layout ot⌝ ∗ ⌜v `has_layout_val` ot_layout ot⌝ ∗ l ↦{q} v ∗ ▷ v ◁ᵥ{π} r2 @ ty2 ∗
        (* prove the continuation after the client is done *)
        logical_step F (∀ st,
          (* assuming that the client provides the ownership back... *)
          l ↦{q} v -∗
          v ◁ᵥ{π} r2 @ ty2 ={F}=∗
          (* ... we transform to some new ownership [ty3] that the client "can keep" (imagine we move out of [l]) *)
          ∃ (L' : llctx) (rt3 : Type) (ty3 : type rt3) r3,
            (mem_cast v ot st) ◁ᵥ{π} r3 @ ty3 ∗
            (* and the lifetime context *)
            llctx_interp L' ∗ na_own π shrE ∗
            (∃ rt' (lt' : ltype rt') (r' : place_rfn rt') res,
              (* and the remaining ownership for the location *)
              l ◁ₗ[π, b2] r' @ lt' ∗
              ⌜ltype_st lt' = ltype_st lt⌝ ∗
              match res with
              | ResultStrong => ⌜ac = AllowStrong⌝
              | ResultWeak _ => typed_place_cond bmin lt lt' r r'
              end ∗
              T L' (mem_cast v ot st) rt3 ty3 r3 rt' lt' r' res))).
  Class TypedReadEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 bmin : bor_kind) (br : access_allowed) (ot : op_type) : Type :=
    typed_read_end_proof T : iProp_to_Prop (typed_read_end π E L l lt r b2 bmin br ot T).

  (** ** Write judgments *)
  (* In a given lifetime context, we can write [v] to [e], compatible with [ot], where the written value has type [ty] at refinement [r], and afterwards, the remaining [T] needs to be proved.

    The prover will prove a [typed_write] in a number of steps:
     - first, the place that is read is checked with [typed_place].
     - then, the actual type-checking of the read is performed with [typed_read_end]
   *)
  Definition typed_write (π : thread_id) (E : elctx) (L : llctx) (e : expr) (ot : op_type) (v : val) {rt} (ty : type rt) (r : rt) (T : llctx → iProp Σ) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      (* provided by the client: for any location l... *)
      (∀ (l : loc),
        (* we can hand out ownership to [l], and when the client has written [v] to it,
          the postcondition holds. *)
        (* if the client provides ownership of v... *)
        (v ◁ᵥ{π} r @ ty -∗ logical_step F (
          (* This is something the client learns (in order to prove its wp), rather than something that is provided.
            That the type is compatible with the ot is something that actually needs to be proven as part of [typed_write_end],
            and so we provide it here to the client. *)
          ⌜v `has_layout_val` ot_layout ot⌝ ∗
          (* then it gets access to l *)
          l ↦|ot_layout ot| ∗
          (* and after having written v to it, it gets access to T *)
          logical_step F (l ↦ v ={F}=∗ ∃ L', llctx_interp L' ∗ na_own π shrE ∗ T L'))) -∗
        Φ (val_of_loc l)) -∗
      (* TODO: maybe different mask F *)
      WP e {{ Φ }})%I.


  (* The core of writing a value [v1] typed at [ty1] to a location [l2] typed at [lt2] with [ot], where [l2] immediately owned at [b2] below a path with intersected [bor_kind] [bmin].

    After the write, [l2] has a new type [ty3] that is passed on to the continuation.
  *)
  Definition typed_write_end_cont_t rt2 := llctx → ∀ rt3 : Type, type rt3 → rt3 → access_result rt2 rt3 → iProp Σ.
  Definition typed_write_end (π : thread_id) (E : elctx) (L : llctx) (ot : op_type) (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1) (b2 bmin : bor_kind) (ac : access_allowed) (l2 : loc) {rt2} (lt2 : ltype rt2) (r2 : place_rfn rt2) (T : typed_write_end_cont_t rt2) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      bmin ⊑ₖ b2 -∗
      (* given ownership of the written-to location *)
      l2 ◁ₗ[π, b2] r2 @ lt2 -∗
      (* assuming that the client provides ownership of [v1] *)
      v1 ◁ᵥ{π} r1 @ ty1 ={F}=∗
      (* we need to prove that [v1]'s layout is compatible with [ot], and provide it to the client *)
      ⌜v1 `has_layout_val` ot_layout ot⌝ ∗
      (* we provide [l2] *)
      l2 ↦|ot_layout ot| ∗

      (* and after the client has written to [l2] ... *)
      logical_step F (l2 ↦ v1 ={F}=∗
        ((∃ L' (rt3 : Type) (ty3 : type rt3) (r3 : rt3) res,
        llctx_interp L' ∗
        na_own π shrE ∗
        (* [l2] is typed at a new type [ty3] satisfying the postcondition *)
        l2 ◁ₗ[π, b2] PlaceIn r3 @ (◁ ty3) ∗
        ⌜ltype_st lt2 = ty_syn_type ty3⌝ ∗
        (* rt-changing, require br = false *)
        match res with
        | ResultStrong => ⌜ac = AllowStrong⌝
        | ResultWeak _ => typed_place_cond bmin lt2 (◁ ty3) r2 (PlaceIn r3)
        end ∗
        T L' rt3 ty3 r3 res)))).
  Class TypedWriteEnd (π : thread_id) (E : elctx) (L : llctx) (ot : op_type) (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1) (b2 bmin : bor_kind) (br : access_allowed) (l2 : loc) {rt2} (lt2 : ltype rt2) (r2 : place_rfn rt2) : Type :=
    typed_write_end_proof T : iProp_to_Prop (typed_write_end π E L ot v1 ty1 r1 b2 bmin br l2 lt2 r2 T).

  (** ** Borrow judgments *)
  (** [typed_borrow_mut] gets triggered when we borrow mutably at lifetime [κ] from a place [e].

    Usually, this will be proved in multiple steps:
    * we decompose [e] to a place context and a location
    * we find a typing for the location in the context
    * we type the place context with [typed_place]
    * we use [typed_borrow_mut_end] to do the final checking
  *)
  Definition typed_borrow_mut_cont_t := llctx → val → gname → ∀ (rt : Type), type rt → rt → iProp Σ.
  Definition typed_borrow_mut (π : thread_id) (E : elctx) (L : llctx) (e : expr) (κ : lft) (ty_annot : option rust_type) (T : typed_borrow_mut_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      (* for any location provided to the client *)
      (∀ (l : loc),
        (* and a time receipt we provide for generating our credits *)
        atime 1 -∗
        (* the client can assume after an update... *)
        logical_step F (
          (* credits to prepay the borrow *)
          £ num_cred -∗
          (* and the returned receipt *)
          atime 1 ={F}=∗
          ∃ L' (rt : Type) (ty : type rt) (r : rt) (γ : gname) (ly : layout),
          (* a new observation *)
          gvar_obs γ r ∗
          (* and a borrow *)
          &{κ}(∃ (r': rt), gvar_auth γ r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r') ∗
          (* + some well-formedness *)
          ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
          ⌜l `has_layout_loc` ly⌝ ∗
          loc_in_bounds l 0 (ly.(ly_size)) ∗ ty_sidecond ty ∗
          (* + the condition T *)
          llctx_interp L' ∗
          na_own π shrE ∗
          T L' (val_of_loc l) γ rt ty r) -∗
          Φ (val_of_loc l)) -∗
      WP e {{ Φ }})%I.

  Definition typed_borrow_mut_end_cont_t rt := gname → ltype rt → place_rfn rt → iProp Σ.
  Definition typed_borrow_mut_end (π : thread_id) (E : elctx) (L : llctx) (κ : lft) (l : loc) {rt} (ty : type rt) (r : place_rfn rt) (b2 bmin : bor_kind) (T : typed_borrow_mut_end_cont_t rt) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
    bmin ⊑ₖ b2 -∗
    (* given ownership of the location we borrow from *)
    (* TODO should we require a PlaceIn refinement here? *)
    l ◁ₗ[π, b2] r @ (◁ ty) -∗ £(num_cred) ={F}=∗
    (* we provide a borrow of ty *)
    ∃ (γ : gname) (ly : layout), place_rfn_interp_mut r γ ∗
    &{κ}(∃ (r': rt), gvar_auth γ r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r')  ∗
    ty_sidecond ty ∗
    ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗ loc_in_bounds l 0 (ly.(ly_size)) ∗
    (* and a blocked ownership of the borrowed location *)
    l ◁ₗ[π, b2] (PlaceGhost γ: place_rfn rt) @ (BlockedLtype ty κ) ∗
    (* and a proof that we can unblock again *)
    typed_place_cond bmin (◁ ty) (BlockedLtype ty κ) r (PlaceGhost γ) ∗
    (* and the context and postco *)
    llctx_interp L ∗ na_own π shrE ∗
    T γ (BlockedLtype ty κ) (PlaceGhost γ)).
  Class TypedBorrowMutEnd π (E : elctx) (L : llctx) (κ : lft) (l : loc) {rt} (ty : type rt) (r : place_rfn rt) (b2 bmin : bor_kind) : Type :=
    typed_borrow_mut_end_proof T : iProp_to_Prop (typed_borrow_mut_end π E L κ l ty r b2 bmin T).

  (** [typed_borrow_shr] gets triggered when we do a shared borrow at lifetime [κ] from a place [e].

    Usually, this will be proved in multiple steps:
    * we decompose [e] to a place context and a location
    * we find a typing for the location in the context
    * we type the place context with [typed_place]
    * we use [typed_borrow_shr_end] to do the final checking
  *)
  Definition typed_borrow_shr_cont_t := llctx → val → ∀ (rt : Type), type rt → place_rfn rt → iProp Σ.
  Definition typed_borrow_shr π (E : elctx) (L : llctx) (e : expr) (κ : lft) (ty_annot : option rust_type) (T : typed_borrow_shr_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
      (* for any location provided to the client... *)
      (∀ (l : loc),
      (* the client needs to prove the postcondition, assuming shared ownership after an update *)
      (* this requires two logical steps: one for stratifying, and one for initiating sharing *)
      logical_step F (logical_step F (
        (* one credit for the inheritance VS *)
        £1 ={F}=∗
        ∃ (L' : llctx) (rt : Type) (ty : type rt) (r : place_rfn rt) (r' : rt) (ly : layout),
          place_rfn_interp_shared r r' ∗ ty.(ty_shr) κ π r' l ∗
          ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
          ⌜l `has_layout_loc` ly⌝ ∗
          loc_in_bounds l 0 (ly.(ly_size)) ∗ ty.(ty_sidecond) ∗
          (* as well as the condition T *)
          llctx_interp L' ∗ na_own π shrE ∗
          T L' (val_of_loc l) rt ty r)) -∗
        Φ (val_of_loc l)) -∗
      WP e {{ Φ }})%I.

  Definition typed_borrow_shr_end_cont_t rt := ltype rt → place_rfn rt → iProp Σ.
  Definition typed_borrow_shr_end π (E : elctx) (L : llctx) (κ : lft) (l : loc) {rt} (ty : type rt) (r : place_rfn rt) (b2 bmin : bor_kind) (T : typed_borrow_shr_end_cont_t rt) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
    bmin ⊑ₖ b2 -∗
    (* given ownership of the location we borrow from

       TODO (this might well be an lty and not simply ◁ ty, to handle the case that a subplace was already shared-borrowed)
        but how to formulate this properly?
        Really, I want to say that [lt]'s core should be equivalent to ◁ty for some ty?
    *)
    l ◁ₗ[π, b2] r @ (◁ ty) ={F}=∗
    (* we provide a borrow of ty *)
    logical_step F (
    (* one credit for the inheritance VS *)
    £1 ={F}=∗
    ∃ ly (lt : ltype rt) r',
    place_rfn_interp_shared r r' ∗ ty.(ty_shr) κ π r' l ∗
    ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
    loc_in_bounds l 0 (ly.(ly_size)) ∗ ty.(ty_sidecond) ∗
    (* and a blocked ownership of the borrowed location *)
    l ◁ₗ[π, b2] r @ lt  ∗
    (* and a proof that we can unblock again *)
    typed_place_cond bmin (◁ ty) lt (r) (r)  ∗
    (* and the context and postco *)
    llctx_interp L ∗
    na_own π shrE ∗
    T lt (r))).
  Class TypedBorrowShrEnd π (E : elctx) (L : llctx) (κ : lft) (l : loc) {rt} (ty : type rt) (r : place_rfn rt) (b2 bmin : bor_kind) : Type :=
    typed_borrow_shr_end_proof T : iProp_to_Prop (typed_borrow_shr_end π E L κ l ty r b2 bmin T).

  (** ** Address-of judgments *)
  (** [*mut] address of *)
  Definition typed_addr_of_mut_cont_t := llctx → val → ∀ (rt : Type), type rt → rt → iProp Σ.
  Definition typed_addr_of_mut π (E : elctx) (L : llctx) (e : expr) (T : typed_addr_of_mut_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
    (* for any location provided to the client *)
    (∀ (l : loc),
      logical_step F (
        ∃ L' (rt : Type) (ty : type rt) (r : rt),
        l ◁ᵥ{π} r @ ty ∗
        llctx_interp L' ∗
        na_own π shrE ∗
        T L' (val_of_loc l) rt ty r) -∗
        Φ (val_of_loc l)) -∗
    WP e {{ Φ }})%I.

  (** This does not work below shared references, as we cannot get a full fraction out of the sharing predicate.
     This does not seem that terrible, because we should not take *mut references from shared borrows anyways.
     (Note: we are really using here that the difference between *mut and *const have the role of providing some intent by the programmer.) *)
  Definition typed_addr_of_mut_end_cont_t := llctx → ∀ rt0, type rt0 → rt0 → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ.
  Definition typed_addr_of_mut_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 bmin : bor_kind) (T : typed_addr_of_mut_end_cont_t) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ na_own π shrE -∗
    bmin ⊑ₖ b2 -∗
    (* given ownership of the location we borrow from *)
    l ◁ₗ[π, b2] r @ lt -∗
    (* do a logical step in order to be able to create [OpenedLtype] *)
    logical_step F (
    ∃ (L' : llctx)
      (rt0 : Type) (ty0 : type rt0) (r0 : rt0)
      (rt' : Type) (lt' : ltype rt') (r' : place_rfn rt'),
    (* provide ownership of some ty0, the result of the operation -- usually will be alias_ptr_t *)
    l ◁ᵥ{π} r0 @ ty0 ∗
    (* and blocked ownership of the borrowed location (where the notion of blocking is not fixed, and determined by the existentially-quantified lt');
       usually it will be AliasLtype l or OpenedLtype (AliasLtype l) .. *)
    l ◁ₗ[π, b2] r' @ lt' ∗
    (* and the ownership to move out *)
    l ◁ₗ[π, Owned false] r @ lt ∗
    ⌜ltype_st lt' = ltype_st lt⌝ ∗
    (* and the context and postco *)
    llctx_interp L' ∗
    na_own π shrE ∗
    T L' rt0 ty0 r0 rt' lt' r')).
  Class TypedAddrOfMutEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 bmin : bor_kind) : Type :=
    typed_addr_of_mut_end_proof T : iProp_to_Prop (typed_addr_of_mut_end π E L l lt r b2 bmin T).

  (*
     expected flow:
     - we do a typed_place
     - now we need to reshape the resulting ltype to an Owned ofty
       in order to be able to take that ownership out.
     - one possibility to do this: just have different _end instances for Owned, Uniq and Shared.
       Owned is straight; for Uniq and Shared we do a strong update.
       Shared is more challenging though: we can only get one fraction out.
       Also, we can't write here.
       There we again face the problem of specifying shared pointers in a reasonable way.
      For now: just don't support it for shared pointers.
   *)

  (* TODO addr_of_const
      This should give us some kind of shared ownership.
  *)

End judgments.

(* TODO: can we just make this a li_tactic? *)
Ltac solve_into_place_ctx :=
  match goal with
  | |- IntoPlaceCtx ?π ?E ?e ?T =>
      let e' := W.of_expr e in
      change_no_check (IntoPlaceCtx π E (W.to_expr e') T);
      refine (find_place_ctx_correct E π _ _ _); rewrite/=/W.to_expr/=; done
  end.
Global Hint Extern 0 (IntoPlaceCtx _ _ _ _) => solve_into_place_ctx : typeclass_instances.

(* we want this to be transparent because it's just a cosmetic wrapper around [stratify_ltype], but the same typeclasses should fire *)
Global Typeclasses Transparent stratify_ltype_unblock.

(** Tactic hint to compute a map lookup, either as [None] or [Some v]. *)
Definition compute_map_lookup_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (k : K) (T : option V → iProp Σ) : iProp Σ :=
  ∃ res, ⌜M !! k = res⌝ ∗ T res.
#[global] Typeclasses Opaque compute_map_lookup_goal.
Program Definition compute_map_lookup_hint `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) k res :
  M !! k = res →
  LiTactic (compute_map_lookup_goal M k) := λ a, {|
    li_tactic_P T := T res;
  |}.
Next Obligation.
  iIntros (?? K ?? V M k res Hlook T) "HT". iExists res. iFrame. done.
Qed.

(** Variant of [compute_map_lookup_goal] that expects a [Some v]. *)
Definition compute_map_lookup_nofail_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (k : K) (T : V → iProp Σ) : iProp Σ :=
  ∃ res, ⌜M !! k = Some res⌝ ∗ T res.
#[global] Typeclasses Opaque compute_map_lookup_nofail_goal.
Program Definition compute_map_lookup_nofail_hint `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) k res :
  M !! k = Some res →
  LiTactic (compute_map_lookup_nofail_goal M k) := λ a, {|
    li_tactic_P T := T res;
  |}.
Next Obligation.
  iIntros (?? K ?? V M k res Hlook T) "HT". iExists res. iFrame. done.
Qed.

(** Tactic hint to compute an iterated map lookup *)
Definition compute_map_lookups_nofail_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (ks : list K) (T : (list V) → iProp Σ) : iProp Σ :=
  ∃ res, ⌜Forall2 (λ k v, M !! k = Some v) ks res⌝ ∗ T (res).
#[global] Typeclasses Opaque compute_map_lookups_nofail_goal.
Program Definition compute_map_lookups_nofail_hint `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) ks res :
  Forall2 (λ k v, M !! k = Some v) ks res →
  LiTactic (compute_map_lookups_nofail_goal M ks) := λ a, {|
    li_tactic_P T := T res;
  |}.
Next Obligation.
  iIntros (?? K ?? V M ks res Hlook T) "HT". iExists res. iFrame. done.
Qed.

(** Tactic hint to simplify a map, e.g. compute deletes *)
Definition simplify_gmap_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (T : gmap K V → iProp Σ) : iProp Σ :=
  ∃ M', ⌜M = M'⌝ ∗ T M'.
#[global] Typeclasses Opaque simplify_gmap_goal.
Program Definition simplify_gmap_hint `{!typeGS Σ} `{Countable K} {V} (M M' : gmap K V) :
  M = M' →
  LiTactic (simplify_gmap_goal M) := λ a, {|
    li_tactic_P T := T M';
  |}.
Next Obligation.
  iIntros (?? K ?? V M M' -> T) "HT". iExists M'. iFrame. done.
Qed.

(** Tactic hint to simplify a lft map, e.g. compute deletes *)
(* We don't actually require an equality here, since the map doesn't have any semantic meaning *)
Definition opaque_eq {A} (a b : A) := True.
Global Opaque opaque_eq.
Definition simplify_lft_map_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (T : gmap K V → iProp Σ) : iProp Σ :=
  ∃ M', ⌜opaque_eq M M'⌝ ∗ T M'.
#[global] Typeclasses Opaque simplify_lft_map_goal.
Program Definition simplify_lft_map_hint `{!typeGS Σ} `{Countable K} {V} (M M' : gmap K V) :
  opaque_eq M M' →
  LiTactic (simplify_lft_map_goal M) := λ a, {|
    li_tactic_P T := T M';
  |}.
Next Obligation.
  iIntros (?? K ?? V M M' ? T) "HT". iExists M'. iFrame. done.
Qed.

(** Tactic hint to find a local lifetime and split it off from the context *)
Definition llctx_find_llft_goal `{!typeGS Σ} (L : llctx) (κ : lft) (key : llctx_find_llft_key) (T : (list lft * llctx) → iProp Σ) : iProp Σ :=
    ∃ L' κs, ⌜llctx_find_llft L κ key κs L'⌝ ∗ T (κs, L').
#[global] Typeclasses Opaque llctx_find_llft_goal.
Program Definition llctx_find_llft_hint `{!typeGS Σ} (L : llctx) (κ : lft) (key : llctx_find_llft_key) (κs : list lft) (L' : llctx) :
  llctx_find_llft L κ key κs L' →
  LiTactic (llctx_find_llft_goal L κ key) := λ H, {|
    li_tactic_P T := T (κs, L');
|}.
Next Obligation.
  iIntros (?? L κ key κs L' Hsplit T) "HL'". iExists L', κs. eauto.
Qed.

(** Tactic hint to compute a layout for a syn_type *)
Definition compute_layout_goal `{!typeGS Σ} (st : syn_type) (T : layout → iProp Σ) : iProp Σ :=
  ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ T ly.
#[global] Typeclasses Opaque compute_layout_goal.
Program Definition compute_layout_hint `{!typeGS Σ} (st : syn_type) (ly : layout) :
  syn_type_has_layout st ly →
  LiTactic (compute_layout_goal st) := λ a, {|
    li_tactic_P T := T ly;
  |}.
Next Obligation.
  iIntros (?? st ly Hly T) "HT". iExists ly. iFrame. done.
Qed.

(** Tactic hint to compute a struct_layout for a struct_layout_spec *)
Definition compute_struct_layout_goal `{!typeGS Σ} (sls : struct_layout_spec) (T : struct_layout → iProp Σ) : iProp Σ :=
  ∃ sl, ⌜struct_layout_spec_has_layout sls sl⌝ ∗ T sl.
#[global] Typeclasses Opaque compute_struct_layout_goal.
Program Definition compute_struct_layout_hint `{!typeGS Σ} (sls : struct_layout_spec) (sl : struct_layout) :
  struct_layout_spec_has_layout sls sl →
  LiTactic (compute_struct_layout_goal sls) := λ a, {|
    li_tactic_P T := T sl;
  |}.
Next Obligation.
  iIntros (?? sls sl Hly T) "HT". iExists sl. iFrame. done.
Qed.

(** Tactic hint to compute a semantic Rust type for a given syntactic [rust_type] *)
Definition interpret_rust_type_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) (T : sigT type → iProp Σ) : iProp Σ :=
  ∃ (rt : Type) (ty : type rt), T (existT _ ty).
#[global] Typeclasses Opaque interpret_rust_type_goal.
Definition interpret_rust_type_pure_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) {rt} (ty : type rt) := True.
Global Typeclasses Opaque interpret_rust_type_pure_goal.
Arguments interpret_rust_type_pure_goal : simpl never.
Program Definition interpret_rust_type_hint `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) {rt} (ty : type rt) :
  interpret_rust_type_pure_goal lfts sty ty →
  LiTactic (interpret_rust_type_goal lfts sty) := λ a, {|
    li_tactic_P T := T (existT _ ty);
  |}.
Next Obligation.
  iIntros (??? sty rt ty _ T) "Ha". simpl.
  iExists _, _. done.
Qed.

Global Typeclasses Opaque llctx_find_llft_goal.
Ltac solve_llctx_find_llft := fail "implement llctx_find_llft_solve".
Global Hint Extern 10 (LiTactic (llctx_find_llft_goal _ _ _)) =>
    eapply llctx_find_llft_hint; solve_llctx_find_llft : typeclass_instances.

Global Typeclasses Opaque lctx_lft_alive_count_goal.
Ltac solve_lft_alive_count := fail "implement solve_lft_alive_count".
#[global] Hint Extern 10 (LiTactic (lctx_lft_alive_count_goal _ _ _)) =>
    refine (lctx_lft_alive_count_hint _ _ _ _ _ _); solve_lft_alive_count : typeclass_instances.

Global Typeclasses Opaque llctx_release_toks_goal.
Ltac solve_llctx_release_toks := fail "implement solve_llctx_release_toks".
#[global] Hint Extern 10 (LiTactic (llctx_release_toks_goal _ _)) =>
    refine (llctx_release_toks_hint _ _ _ _); solve_llctx_release_toks : typeclass_instances.

Global Typeclasses Opaque simplify_gmap_goal.
Ltac solve_simplify_gmap := fail "implement solve_simplify_gmap".
#[global] Hint Extern 10 (LiTactic (simplify_gmap_goal _)) =>
    refine (simplify_gmap_hint _ _ _); solve_simplify_gmap : typeclass_instances.

Global Typeclasses Opaque simplify_lft_map_goal.
Ltac solve_simplify_lft_map := fail "implement solve_simplify_lft_map".
#[global] Hint Extern 10 (LiTactic (simplify_lft_map_goal _)) =>
    refine (simplify_lft_map_hint _ _ _); solve_simplify_lft_map : typeclass_instances.

Global Typeclasses Opaque compute_map_lookup_goal.
Ltac solve_compute_map_lookup := fail "implement solve_compute_map_lookup".
#[global] Hint Extern 10 (LiTactic (compute_map_lookup_goal _ _)) =>
    refine (compute_map_lookup_hint _ _ _ _); solve_compute_map_lookup : typeclass_instances.

Global Typeclasses Opaque compute_map_lookup_nofail_goal.
Ltac solve_compute_map_lookup_nofail := fail "implement solve_compute_map_lookup_nofail".
#[global] Hint Extern 10 (LiTactic (compute_map_lookup_nofail_goal _ _)) =>
    refine (compute_map_lookup_nofail_hint _ _ _ _); solve_compute_map_lookup_nofail : typeclass_instances.

Global Typeclasses Opaque compute_map_lookups_nofail_goal.
Ltac solve_compute_map_lookups_nofail := fail "implement solve_compute_map_lookups_nofail".
#[global] Hint Extern 10 (LiTactic (compute_map_lookups_nofail_goal _ _)) =>
    refine (compute_map_lookups_nofail_hint _ _ _ _); solve_compute_map_lookups_nofail : typeclass_instances.

Global Typeclasses Opaque compute_layout_goal.
Ltac solve_compute_layout := fail "implement solve_compute_layout".
#[global] Hint Extern 1 (LiTactic (compute_layout_goal _)) =>
    refine (compute_layout_hint _ _ _); solve_compute_layout : typeclass_instances.

Global Typeclasses Opaque compute_struct_layout_goal.
Ltac solve_compute_struct_layout := fail "implement solve_compute_struct_layout".
#[global] Hint Extern 1 (LiTactic (compute_struct_layout_goal _)) =>
    refine (compute_struct_layout_hint _ _ _); solve_compute_struct_layout : typeclass_instances.

Global Typeclasses Opaque interpret_rust_type_goal.
Ltac solve_interpret_rust_type := fail "implement solve_interpret_rust_type".
#[global] Hint Extern 1 (LiTactic (interpret_rust_type_goal _ _)) =>
    refine (interpret_rust_type_hint _ _ _ _); solve_interpret_rust_type : typeclass_instances.


(** ** Generic context folding mechanism *)
Section folding.
  Context `{!typeGS Σ}.
  (** We (formerly) use this primarily for unblocking the typing context when ending a lifetime *)

  (* bundled ltypes *)
  Record bltype := mk_bltype {
    bltype_rt : Type;
    bltype_rfn : place_rfn bltype_rt;
    bltype_ltype : ltype bltype_rt;
  }.
  Definition type_ctx := list (loc * bltype).
  Implicit Types (tctx : type_ctx).

  Definition type_ctx_interp π tctx : iProp Σ :=
    [∗ list] i ∈ tctx, let '(l, bt) := i in l ◁ₗ[π, Owned false] bt.(bltype_rfn) @ bt.(bltype_ltype).
  Lemma type_ctx_interp_cons π l t tctx :
    type_ctx_interp π ((l, t) :: tctx) ⊣⊢ (l ◁ₗ[π, Owned false] t.(bltype_rfn) @ t.(bltype_ltype)) ∗ type_ctx_interp π tctx.
  Proof. iApply big_sepL_cons. Qed.

  (* TODO maybe we should just put the locations in the tctx queue, instead of the whole type assignment? We're going to look for them in the context anyways. *)
  Section folder.
  Arguments delayed_prop : simpl never.
  Context {Acc : Type} (Acc_interp : Acc → iProp Σ).
  (** Initializer for doing a context fold with action [m].
      The automation will use this typing judgment as a hint to gather up the context and
        start folding over the context.

      Clients that want to initiate context folding should generate a goal with this judgment,
        with a [m] that identifies the folding action.
   *)
  Definition typed_pre_context_fold (π : thread_id) (E : elctx) (L : llctx) {M} (m : M) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    logical_step F (∃ L', llctx_interp L' ∗ T L').
  (* no TC for this -- typing rules for this will be directly applied by Ltac automation *)

  (** The main context folding judgment. [tctx] is the list of types to fold. *)
  Definition typed_context_fold {M} (π : thread_id) (E : elctx) (L : llctx) (m : M) (tctx : list loc) (acc : Acc) (T : llctx → M → Acc → iProp Σ) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      logical_step F (Acc_interp acc) ={F}=∗
      ∃ L' acc' m', llctx_interp L' ∗ logical_step F (Acc_interp acc') ∗ T L' m' acc').
  Class TypedContextFold (π : thread_id) (E : elctx) (L : llctx) {M} (m : M) (tctx : list loc) (acc : Acc) :=
    typed_context_fold_proof T : iProp_to_Prop (typed_context_fold π E L m tctx acc T).

  (**
    This does a context fold step, by transforming [tctx] and [acc].
    Clients of context folding should register instances of this (for the right [m]) in
      order to register the folding action.
    Every such rule should make progress, so that the whole thing is terminating.
   *)
  Definition typed_context_fold_step {M} (π : thread_id) (E : elctx) (L : llctx) (m : M) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) (acc : Acc) (T : llctx → M → Acc → iProp Σ) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      logical_step F (Acc_interp acc) -∗
      l ◁ₗ[ π, Owned false] r @ lt -∗ |={F}=>
      (∃ L' acc' m', llctx_interp L' ∗ logical_step F (Acc_interp acc') ∗ T L' m' acc')).
  Class TypedContextFoldStep {M} (π : thread_id) (E : elctx) (L : llctx) (m : M) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) (acc : Acc) :=
    typed_context_fold_step_proof T : iProp_to_Prop (typed_context_fold_step π E L m l lt r tctx acc T).

  (** Terminator for the context folding typing process.
    It gathers up the folding result and takes a program step to strip the accumulated laters.
  *)
  Definition typed_context_fold_end (π : thread_id) (E : elctx) (L : llctx) (acc : Acc) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      logical_step F (Acc_interp acc) -∗
      logical_step F (∃ L2, llctx_interp L2 ∗ T L2).
  (* no type class -- we should directly apply the typing rule for this. *)

  (** Finish context folding when the whole list has been processed. *)
  Lemma typed_context_fold_nil {M} E L π (m : M) acc T  :
    T L m acc
    ⊢ typed_context_fold π E L m [] acc T.
  Proof.
    iIntros "HT".
    iIntros (? ??) "#CTX #HE HL Hdel".
    iExists L, acc, m. by iFrame.
  Qed.
  Global Instance typed_context_fold_nil_inst {M} E L π (m : M) acc :
    TypedContextFold π E L m [] acc :=
      λ T, i2p (typed_context_fold_nil E L π m acc T).

  (** Take a context folding step. *)
  (* We make this optional, because some of the items may already have been used for stratifying other types (e.g. for invariant folding) *)
  Lemma typed_context_fold_cons {M} π E L (m : M) l (tctx : list loc) acc T :
    find_in_context (FindOptLoc l π) (λ res,
      match res with
      | None => typed_context_fold π E L m tctx acc T
      | Some (existT rt' (lt', r', bk')) =>
          ⌜bk' = Owned false⌝ ∗ (typed_context_fold_step π E L m l lt' r' tctx acc T)
      end)
    ⊢ typed_context_fold π E L m (l :: tctx) acc T.
  Proof.
    rewrite /FindOptLoc. iIntros "(%res & HT)".
    destruct res as [ [rt' [[lt' r'] bk']] | ]; simpl.
    - iDestruct "HT" as "(Hl & HT)". iPoseProof ("HT") as "(-> & HT)".
      iIntros (? ??) "#CTX #HE HL Hdel".
      iDestruct ("HT" with "[//] [//] CTX HE HL Hdel Hl") as ">Hs".
      done.
    - iDestruct "HT" as "(_ & HT)". iApply "HT".
  Qed.
  Global Instance typed_context_fold_cons_inst {M} E L π (m : M) l (tctx : list loc) acc :
    TypedContextFold π E L m (l :: tctx) acc :=
      λ T, i2p (typed_context_fold_cons π E L m l tctx acc T).

  (** Typing rule for ending context folding.
    Yields the accumulated result and continues with the next statement.
  *)
  Lemma type_context_fold_end E L π acc T :
    (introduce_with_hooks E L (Acc_interp acc) T)
    ⊢ typed_context_fold_end π E L acc T.
  Proof.
    iIntros "Hs". iIntros (? ??) "#(LFT & TIME & LLCTX) #HE HL Hstep".
    iApply logical_step_fupd.
    iApply (logical_step_wand with "Hstep").
    iIntros "Hacc". iMod ("Hs" with "[//] HE HL Hacc") as "(%L3 & HL & HT)".
    eauto with iFrame.
  Qed.

  (** Initialize context folding.
    This rule should be directly applied by Ltac automation, after it has gathere Inherit κ1 InheritDynIncl (llft_elt_toks κs)d up the [tctx]
      from the Iris context.
  *)
  Lemma typed_context_fold_init {M} (init_acc : Acc) E L π (m : M) (tctx : list loc) Φ T :
    Acc_interp init_acc ∗
    typed_context_fold π E L m tctx init_acc (λ L' m' acc, Φ m' acc ∗ typed_context_fold_end π E L' acc T) -∗
    typed_pre_context_fold π E L m T.
  Proof.
    iIntros "(Hinit & Hfold)".
    iIntros (???) "#CTX #HE HL".
    iApply fupd_logical_step.
    iDestruct ("Hfold" $! F with "[//] [//] CTX HE HL [Hinit]") as ">Hs".
    { iApply logical_step_intro. iFrame. }
    iDestruct "Hs" as (L' acc' m') "(HL & Hdel & ? & Hs)".
    rewrite /typed_context_fold_end.
    iApply ("Hs" with "[//] [//] CTX HE HL Hdel").
  Qed.
  End folder.

  (* Unfold the type context so Lithium separates the big_sep *)
  Lemma simplify_type_context π tctx T :
    (([∗ list] i ∈ tctx, let '(l, bt) := i in l ◁ₗ[ π, Owned false] bltype_rfn bt @ bltype_ltype bt) -∗ T) ⊢
    simplify_hyp (type_ctx_interp π tctx) T.
  Proof. done. Qed.
  Global Instance simplify_type_context_inst π tctx :
    SimplifyHyp (type_ctx_interp π tctx) (Some 0%N) :=
    λ T, i2p (simplify_type_context π tctx T).
End folding.

Section relate_list.
  Context `{!typeGS Σ}.
  (** A generalization of subsume_list. *)
  Record FoldableRelation {A B} : Type := FR {
    fr_rel : elctx → llctx → nat → A → B → iProp Σ → iProp Σ;
    fr_cap : nat;
    fr_inv : Prop;
    fr_core_rel : elctx → llctx → nat → A → B → iProp Σ;
    fr_elim_mode : bool;
    fr_elim E L i a b :
      ⊢ if fr_elim_mode then
        ∀ T F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ fr_rel E L i a b T ={F}=∗ fr_core_rel E L i a b ∗ llctx_interp L ∗ T
      else ∀ T, fr_rel E L i a b T -∗ fr_core_rel E L i a b ∗ T;
  }.
  Arguments fr_rel {_ _}.
  Arguments fr_core_rel {_ _}.
  Arguments fr_elim_mode {_ _}.

  Definition relate_list {A B} (E : elctx) (L : llctx) (ig : list nat) (l1 : list A) (l2 : list B) (i0 : nat) (R : FoldableRelation) (T : iProp Σ) : iProp Σ :=
    if R.(fr_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      (⌜i0 + length l1 ≤ R.(fr_cap)⌝ -∗ ⌜R.(fr_inv)⌝ -∗
      [∗ list] i ↦ a; b ∈ l1; l2, if decide ((i + i0)%nat ∈ ig) then True else R.(fr_core_rel) E L (i + i0)%nat a b) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length l1 ≤ R.(fr_cap)⌝ -∗ ⌜R.(fr_inv)⌝ -∗
      [∗ list] i ↦ a; b ∈ l1; l2, if decide ((i + i0)%nat ∈ ig) then True else R.(fr_core_rel) E L (i + i0)%nat a b) ∗ T)%I
  .
  Class RelateList {A B} (E : elctx) (L : llctx) (ig : list nat) (l1 : list A) (l2 : list B) (i0 : nat) (R : FoldableRelation) : Type :=
    relate_list_proof T : iProp_to_Prop (relate_list E L ig l1 l2 i0 R T).

  Lemma relate_list_ig_cons_le {A B} E L ig (j i0 : nat) (l1 : list A) (l2 : list B) (R : FoldableRelation) :
    (j < i0)%nat →
    ([∗ list] i ↦ a; b ∈ l1; l2, if decide (i + i0 ∈ (j :: ig))%nat then True else fr_core_rel R E L (i + i0)%nat a b) -∗
    ([∗ list] i ↦ a; b ∈ l1; l2, if decide (i + i0 ∈ (ig))%nat then True else fr_core_rel R E L (i + i0)%nat a b).
  Proof.
    intros Hlt.
    iInduction l1 as [ | a l1] "IH" forall (j i0 l2 Hlt); simpl; first by eauto.
    destruct l2 as [ | b l2]; simpl; first by eauto.
    case_decide as Hel.
    - apply elem_of_cons in Hel as [ ? | ?]; first lia.
      rewrite decide_True; last done. rewrite !left_id.
      iIntros "Ha". iApply (big_sepL2_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL2_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
    - apply not_elem_of_cons in Hel as [_ Hel].
      rewrite decide_False; last done.
      iIntros "($ & Ha)". iApply (big_sepL2_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL2_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
  Qed.

  Lemma relate_list_replicate_elim_full {A B} E L ig n (a : A) (b : B) i0 (R : FoldableRelation) T :
    R.(fr_elim_mode) = true →
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ ⌜R.(fr_inv)⌝ -∗
      □ ∀ i, ⌜(i0 ≤ i < R.(fr_cap))%nat⌝ -∗ ⌜i ∉ ig⌝ -∗ R.(fr_core_rel) E L i a b) -∗
    T -∗ relate_list E L ig (replicate n a) (replicate n b) i0 R T.
  Proof.
    intros Ha. rewrite /relate_list Ha.
    iIntros "HR HT" (F ?) "#CTX #HE HL".
    iPoseProof ("HR" with "CTX HE HL") as "#HR".
    iFrame "HT HL".
    iInduction n as [ | n] "IH" forall (i0) "HR"; simpl.
    { by iFrame. }
    iMod ("IH" $! (S i0) with "[]") as "Ha".
    { iModIntro. iIntros (Hinv i Hi Hnel). iModIntro. iApply "HR"; iPureIntro; first [done | lia]. }
    iModIntro. iIntros "%Hinv %Hi".
    case_decide.
    - iR.
      iApply (big_sepL2_wand with "(Ha [] [//])").
      { iPureIntro. lia. }
      iApply big_sepL2_intro; first (by rewrite !replicate_length).
      iModIntro. iIntros (?????). rewrite Nat.add_succ_r. eauto.
    - iSplitR. { iApply "HR"; simpl in Hinv; iPureIntro; first [lia | done]. }
      iApply (big_sepL2_mono with "(Ha [] [//])"); last by (iPureIntro; lia).
      iIntros (?????). rewrite Nat.add_succ_r. done.
  Qed.
  Lemma relate_list_replicate_elim_weak {A B} E L ig n (a : A) (b : B) i0 (R : FoldableRelation) T :
    R.(fr_elim_mode) = false →
    (⌜R.(fr_inv)⌝ -∗ □ ∀ i, ⌜(i0 ≤ i < R.(fr_cap))%nat⌝ -∗ ⌜i ∉ ig⌝ -∗ R.(fr_core_rel) E L i a b) -∗
    T -∗ relate_list E L ig (replicate n a) (replicate n b) i0 R T.
  Proof.
    intros Ha. rewrite /relate_list Ha.
    iIntros "HR $". iIntros "%Hinv %Hi". iPoseProof ("HR" with "[//]") as "#HR".
    iInduction n as [ | n] "IH" forall (i0 Hinv Hi) "HR"; simpl.
    { by iFrame. }
    iPoseProof ("IH" $! (S i0) with "[] [//] []") as "Ha".
    { iPureIntro. simpl in Hinv. lia. }
    { iModIntro. iIntros (i ? Hnel). iApply "HR"; iPureIntro; first [done | lia]. }
    case_decide.
    - iR.
      iApply (big_sepL2_wand with "Ha").
      iApply big_sepL2_intro; first (by rewrite !replicate_length).
      iModIntro. iIntros (?????). rewrite Nat.add_succ_r. eauto.
    - iSplitR. { iApply "HR"; simpl in Hinv; iPureIntro; first [lia | done]. }
      iApply (big_sepL2_mono with "Ha"). iIntros (?????). rewrite Nat.add_succ_r. done.
  Qed.

  Local Lemma relate_list_insert_in_ig' {A B} E L (ig : list nat) (l1 : list A) (l2 : list B) (i0 : nat) i x R :
    (i0 + i ∈ ig)%nat →
    (⌜i0 + length l1 ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i↦a;b ∈ l1;l2, if decide ((i + i0)%nat ∈ ig) then True else fr_core_rel R E L (i + i0) a b) -∗
    (⌜i0 + length (<[ i:= x]> l1) ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i↦a;b ∈ <[i:=x]>l1;l2, if decide ((i + i0)%nat ∈ ig) then True else fr_core_rel R E L (i + i0) a b).
  Proof.
    iIntros (Hel) "Ha %Hinv %".
    iSpecialize ("Ha" with "[] [//]").
    { rewrite insert_length in Hinv. done. }
    iInduction l1 as [ | a l1] "IH" forall (l2 i i0 Hel Hinv); simpl; first done.
    destruct l2 as [ | b l2]. { destruct i; done. }
    destruct i as [ | i].
    - simpl.
      case_decide; first done.
      rewrite Nat.add_0_r in Hel. done.
    - simpl.
      case_decide.
      + iDestruct "Ha" as "(_ & Ha)". iR.
        iPoseProof ("IH" $! _ _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL2_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL2_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
      + iDestruct "Ha" as "($ & Ha)".
        iPoseProof ("IH" $! _ _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL2_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL2_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
  Qed.
  Lemma relate_list_insert_in_ig {A B} E L ig (l1 : list A) (l2 : list B) (i0 : nat) i x R T `{CanSolve (i0 + i ∈ ig)%nat} :
    relate_list E L ig l1 l2 i0 R T
    ⊢ relate_list E L ig (<[i := x]> l1) l2 i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => unfold CanSolve in H; rename H into Hel end.
    iIntros "Ha".
    rewrite /relate_list; destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Ha" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. by iApply relate_list_insert_in_ig'.
    - iDestruct "Ha" as "(Ha & $)". by iApply relate_list_insert_in_ig'.
  Qed.
  Global Instance relate_list_insert_in_ig_inst {A B} E L ig (l1 : list A) (l2 : list B) (i0 : nat) i x R `{!CanSolve (i0 + i ∈ ig)%nat} :
    RelateList E L ig (<[i := x]> l1) l2 i0 R :=
    λ T, i2p (relate_list_insert_in_ig E L ig l1 l2 i0 i x R T).

  Lemma relate_list_cons_l {A B} E L ig (l1 : list A) (l2 : list B) i0 R a T :
    ⌜i0 ∉ ig⌝ ∗ (∃ b l2', ⌜l2 = b :: l2'⌝ ∗
      R.(fr_rel) E L i0 a b (relate_list E L ig l1 l2' (S i0) R T))
    ⊢ relate_list E L ig (a :: l1) l2 i0 R T.
  Proof.
    iIntros "(%Hnel & %b & %l2' & -> & HR)".
    rewrite /relate_list. iPoseProof (fr_elim R) as "Hx". destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL2_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL2_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(Ha & Hb & $)".
      iIntros "%Hinv %". iSpecialize ("Hb" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL2_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL2_mono with "Hb").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance relate_list_cons_l_inst {A B} E L ig (l1 : list A) (l2 : list B) i0 a R :
    RelateList E L ig (a :: l1) l2 i0 R :=
    λ T, i2p (relate_list_cons_l E L ig l1 l2 i0 R a T).

  Local Lemma relate_list_insert_not_in_ig' {A B} E L ig (l1 : list A) (l2 : list B) (R : FoldableRelation) i0 i a b :
    (i0 + i ∉ ig)%nat →
    i < length l1 →
    l2 !! i = Some b →
    fr_core_rel R E L (i0 + i) a b -∗
    (⌜i0 + length l1 ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i1↦a0;b0 ∈ l1;l2, if decide ((i1 + i0)%nat ∈ (i0 + i)%nat :: ig) then True else fr_core_rel R E L (i1 + i0) a0 b0) -∗
    (⌜i0 + length (<[i:=a]> l1) ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i1↦a0;b0 ∈ <[i:=a]> l1;l2, if decide ((i1 + i0)%nat ∈ ig) then True else fr_core_rel R E L (i1 + i0) a0 b0).
  Proof.
    iIntros (Hnel Hi Hlook) "HR Ha %Hinv %". iSpecialize ("Ha" with "[] [//]").
    { iPureIntro. rewrite insert_length in Hinv. lia. }
    iInduction l1 as [ | a' l1] "IH" forall (l2 i i0 Hnel Hi Hlook Hinv).
    { simpl in *. lia. }
    destruct i as [ | i]; simpl.
    - destruct l2 as [ | b' l2]; first done.
      injection Hlook as ->.
      rewrite !big_sepL2_cons.
      simpl. iDestruct "Ha" as "(_ & Ha)".
      rewrite decide_False; first last. { move: Hnel. rewrite Nat.add_0_r//. }
      rewrite Nat.add_0_r. iFrame.
      iApply big_sepL2_mono; first last.
      { iApply (relate_list_ig_cons_le); first last.
        { iApply big_sepL2_mono; last done. iIntros. rewrite -Nat.add_succ_r//. }
        lia.
      }
      iIntros. rewrite Nat.add_succ_r//.
    - destruct l2 as [ | b' l2]; first done.
      simpl in Hlook.
      rewrite !big_sepL2_cons/=.
      destruct (decide (i0 ∈ ig)).
      + iR. iDestruct "Ha" as "(_ & Ha)".
        iApply big_sepL2_mono; first last.
        { iApply ("IH" with "[] [] [] [] [HR]"); first last.
          - iApply big_sepL2_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - done.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
      + rewrite decide_False; first last. { apply not_elem_of_cons. split; last done. lia. }
        iDestruct "Ha" as "($ & Ha)".
        iApply big_sepL2_mono; first last.
        { iApply ("IH" with "[] [] [] [] [HR]"); first last.
          - iApply big_sepL2_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - done.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
  Qed.

  Lemma relate_list_insert_not_in_ig {A B} E L ig (l1 : list A) (l2 : list B) (R : FoldableRelation) i0 i a T `{CanSolve (i0 + i ∉ ig)%nat} :
    ⌜i < length l1⌝ ∗
    (∃ b, ⌜l2 !! i = Some b⌝ ∗ R.(fr_rel) E L (i0 + i) a b (relate_list E L ((i0 + i) :: ig)%nat l1 l2 i0 R T))
    ⊢ relate_list E L ig (<[i := a]> l1) l2 i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => rewrite /CanSolve in H; rename H into Hnel end.
    iIntros "(%Hi & %b & %Hlook & HR)".
    iPoseProof (fr_elim R) as "Hx".
    rewrite /relate_list. destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iApply (relate_list_insert_not_in_ig' with "HR Ha"); done.
    - iPoseProof ("Hx" with "HR") as "(HR & Ha & $)".
      iApply (relate_list_insert_not_in_ig' with "HR Ha"); done.
  Qed.
  Global Instance relate_list_insert_not_in_ig_inst {A B} E L ig (l1 : list A) (l2 : list B) R (i0 : nat) i a `{!CanSolve (i0 + i ∉ ig)%nat} :
    RelateList E L ig (<[i := a]> l1) l2 i0 R :=
    λ T, i2p (relate_list_insert_not_in_ig E L ig l1 l2 R i0 i a T).

  Lemma relate_list_app_l {A B} E L ig (l1 l1' : list A) (l2 : list B) (R : FoldableRelation) (i0 : nat) T :
    relate_list E L ig l1 (take (length l1) l2) i0 R (relate_list E L ig l1' (drop (length l1) l2) (length l1 + i0)%nat R T)
    ⊢ relate_list E L ig (l1 ++ l1') l2 i0 R T.
  Proof.
    iIntros "Ha".
    rewrite /relate_list; destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Ha" with "[//] CTX HE HL") as "(Ha & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hb & $ & $)".
      iModIntro. iIntros "%Hinv %".
      rewrite app_length in Hinv.
      iSpecialize ("Ha" with "[] [//]").
      { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]").
      { iPureIntro. lia. }
      rewrite -{3}(take_drop (length l1) l2).
      iApply (big_sepL2_app with "Ha").
      iApply (big_sepL2_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
    - iDestruct "Ha" as "(Ha & Hb & $)". iIntros "%Hinv %".
      rewrite app_length in Hinv.
      iSpecialize ("Ha" with "[] [//]").
      { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]").
      { iPureIntro. lia. }
      rewrite -{3}(take_drop (length l1) l2).
      iApply (big_sepL2_app with "Ha").
      iApply (big_sepL2_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
  Qed.
  Global Instance relate_list_app_l_inst {A B} E L ig (l1 l1' : list A) (l2 : list B) R i0 :
    RelateList E L ig (l1 ++ l1') l2 i0 R :=
    λ T, i2p (relate_list_app_l E L ig l1 l1' l2 R i0 T).
End relate_list.

Section relate_hlist.
  Context `{!typeGS Σ}.
  (** A generalization of subsume_list. *)
  Record HetFoldableRelation {A} {G : A → Type} {H : A → Type} : Type := HFR {
    hfr_rel : elctx → llctx → nat → ∀ {x : A}, G x → H x → iProp Σ → iProp Σ;
    hfr_cap : nat;
    hfr_inv : Prop;
    hfr_core_rel : elctx → llctx → nat → ∀ {x : A}, G x → H x → iProp Σ;
    hfr_elim_mode : bool;
    hfr_elim E L i (x : A) (a : G x) (b : H x) :
      ⊢ if hfr_elim_mode then
        ∀ T F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ hfr_rel E L i a b T ={F}=∗ hfr_core_rel E L i a b ∗ llctx_interp L ∗ T
      else ∀ T, hfr_rel E L i a b T -∗ hfr_core_rel E L i a b ∗ T;
  }.
  Arguments hfr_rel {_ _ _}.
  Arguments hfr_core_rel {_ _ _}.
  Arguments hfr_elim_mode {_ _ _}.

  Definition relate_hlist {A} {G H : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : hlist H Xs) (i0 : nat) (R : @HetFoldableRelation A G H) (T : iProp Σ) : iProp Σ :=
    if R.(hfr_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      (⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := (p : (sigT (λ x : A, G x * H x)%type))  in
        if decide ((i + i0)%nat ∈ ig) then True else
        R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := p in
        if decide ((i + i0)%nat ∈ ig) then True else R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ T)%I
  .
  Class RelateHList {A} {G H : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : hlist H Xs) (i0 : nat) (R : @HetFoldableRelation A G H) : Type :=
    relate_hlist_proof T : iProp_to_Prop (relate_hlist E L ig Xs l1 l2 i0 R T).

  Lemma relate_hlist_nil {A} {G H : A → Type} E L ig (l1 : hlist G []) (l2 : hlist H []) i0 R T :
    T ⊢ relate_hlist E L ig [] l1 l2 i0 R T.
  Proof.
    iIntros "HT". rewrite /relate_hlist. destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iFrame. iIntros "!> _ _". inv_hlist l1; inv_hlist l2. done.
    - iFrame. iIntros (??). inv_hlist l1; inv_hlist l2; done.
  Qed.
  Global Instance relate_hlist_nil_inst {A} {G H : A → Type} E L ig (l1 : hlist G []) (l2 : hlist H []) i0 R :
    RelateHList E L ig [] (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_nil E L ig l1 l2 i0 R T).

  Lemma relate_hlist_cons {A} {G H : A → Type} E L ig (X : A) (Xs : list A) (l1 : hlist G (X :: Xs)) (l2 : hlist H (X :: Xs)) i0 R T :
    ⌜i0 ∉ ig⌝ ∗ (∃ a l1' b l2', ⌜l1 = a +:: l1'⌝ ∗ ⌜l2 = b +:: l2'⌝ ∗
      R.(hfr_rel) E L i0 _ a b (relate_hlist E L ig Xs l1' l2' (S i0) R T))
    ⊢ relate_hlist E L ig (X :: Xs) l1 l2 i0 R T.
  Proof.
    iIntros "(%Hnel & %a & %l1' & %b & %l2' & -> & -> & HR)".
    rewrite /relate_hlist. iPoseProof (hfr_elim R) as "Hx". destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(Ha & Hb & $)".
      iIntros "%Hinv %". iSpecialize ("Hb" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance relate_hlist_cons_l_inst {A} {G H} E L ig (X : A) (Xs : list A) (l1 : hlist G (X::Xs)) (l2 : hlist H (X :: Xs)) i0 R :
    RelateHList E L ig (X :: Xs) (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_cons E L ig X Xs l1 l2 i0 R T).

  (* TODO more instances similar to the ones for relate_list *)
End relate_hlist.

(*
Section relate_hplist.
  Context `{!typeGS Σ}.

  Definition relate_hplist {A} {G : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : plist G Xs) (i0 : nat) (R : @HetFoldableRelation A G) (T : iProp Σ) : iProp Σ :=
    if R.(hfr_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      (⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := (p : (sigT (λ x : A, G x * G x)%type))  in
        if decide ((i + i0)%nat ∈ ig) then True else
        R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := p in
        if decide ((i + i0)%nat ∈ ig) then True else R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ T)%I
  .
  Class RelateHList {A} {G : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : hlist G Xs) (i0 : nat) (R : @HetFoldableRelation A G) : Type :=
    relate_hlist_proof T : iProp_to_Prop (relate_hlist E L ig Xs l1 l2 i0 R T).

  Lemma relate_hlist_nil {A} {G : A → Type} E L ig (l1 : hlist G []) (l2 : hlist G []) i0 R T :
    T -∗
    relate_hlist E L ig [] l1 l2 i0 R T.
  Proof.
    iIntros "HT". rewrite /relate_hlist. destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iFrame. iIntros "!> _ _". inv_hlist l1; inv_hlist l2. done.
    - iFrame. iIntros (??). inv_hlist l1; inv_hlist l2; done.
  Qed.
  Global Instance relate_hlist_nil_inst {A} {G : A → Type} E L ig (l1 : hlist G []) (l2 : hlist G []) i0 R :
    RelateHList E L ig [] (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_nil E L ig l1 l2 i0 R T).

  Lemma relate_hlist_cons {A} {G : A → Type} E L ig (X : A) (Xs : list A) (l1 : hlist G (X :: Xs)) (l2 : hlist G (X :: Xs)) i0 R T :
    ⌜i0 ∉ ig⌝ ∗ (∃ a l1' b l2', ⌜l1 = a +:: l1'⌝ ∗ ⌜l2 = b +:: l2'⌝ ∗
      R.(hfr_rel) E L i0 _ a b (relate_hlist E L ig Xs l1' l2' (S i0) R T)) -∗
    relate_hlist E L ig (X :: Xs) l1 l2 i0 R T.
  Proof.
    iIntros "(%Hnel & %a & %l1' & %b & %l2' & -> & -> & HR)".
    rewrite /relate_hlist. iPoseProof (hfr_elim R) as "Hx". destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(Ha & Hb & $)".
      iIntros "%Hinv %". iSpecialize ("Hb" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance relate_hlist_cons_l_inst {A} {G} E L ig (X : A) (Xs : list A) (l1 : hlist G (X::Xs)) (l2 : hlist G (X :: Xs)) i0 R :
    RelateHList E L ig (X :: Xs) (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_cons E L ig X Xs l1 l2 i0 R T).

  (* TODO more instances similar to the ones for relate_list *)
End relate_hlist.
*)

Section fold_list.
  Context `{!typeGS Σ}.
  (** A generalization of subsume_list. *)
  Record FoldablePredicate {A} : Type := FP {
    fp_pred : elctx → llctx → nat → A → iProp Σ → iProp Σ;
    fp_cap : nat;
    fp_inv : Prop;
    fp_elim_mode : bool;
    fp_core_pred : elctx → llctx → nat → A → iProp Σ;
    fp_elim E L i a :
      ⊢ if fp_elim_mode then (∀ T F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ fp_pred E L i a T ={F}=∗ fp_core_pred E L i a ∗ llctx_interp L ∗ T) else ∀ T, fp_pred E L i a T -∗ fp_core_pred E L i a ∗ T;
  }.
  Arguments fp_pred {_}.
  Arguments fp_core_pred {_}.
  Arguments fp_elim_mode {_}.

  Definition fold_list {A} (E : elctx) (L : llctx) (ig : list nat) (l : list A) (i0 : nat) (R : FoldablePredicate) (T : iProp Σ) : iProp Σ :=
    if R.(fp_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
        (⌜i0 + length l ≤ R.(fp_cap)⌝ -∗ ⌜R.(fp_inv)⌝ -∗ [∗ list] i ↦ a ∈ l, if decide ((i + i0)%nat ∈ ig) then True else R.(fp_core_pred) E L (i + i0)%nat a) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length l ≤ R.(fp_cap)⌝ -∗ ⌜R.(fp_inv)⌝ -∗ [∗ list] i ↦ a ∈ l, if decide ((i + i0)%nat ∈ ig) then True else R.(fp_core_pred) E L (i + i0)%nat a) ∗ T)%I.
  Class FoldList {A} (E : elctx) (L : llctx) (ig : list nat) (l : list A) (i0 : nat) (R : FoldablePredicate) : Type :=
    fold_list_proof T : iProp_to_Prop (fold_list E L ig l i0 R T).

  Lemma fold_list_ig_cons_le {A} E L ig (j i0 : nat) (l1 : list A) (R : FoldablePredicate) :
    (j < i0)%nat →
    ([∗ list] i ↦ a ∈ l1, if decide (i + i0 ∈ (j :: ig))%nat then True else fp_core_pred R E L (i + i0)%nat a) -∗
    ([∗ list] i ↦ a ∈ l1, if decide (i + i0 ∈ (ig))%nat then True else fp_core_pred R E L (i + i0)%nat a).
  Proof.
    intros Hlt.
    iInduction l1 as [ | a l1] "IH" forall (j i0 Hlt); simpl; first by eauto.
    case_decide as Hel.
    - apply elem_of_cons in Hel as [ ? | ?]; first lia.
      rewrite decide_True; last done. rewrite !left_id.
      iIntros "Ha". iApply (big_sepL_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
    - apply not_elem_of_cons in Hel as [_ Hel].
      rewrite decide_False; last done.
      iIntros "($ & Ha)". iApply (big_sepL_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
  Qed.

  Lemma fold_list_replicate_elim_full {A} E L ig n (a : A) i0 (R : FoldablePredicate) T :
    R.(fp_elim_mode) = true →
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ ⌜R.(fp_inv)⌝ -∗ □ ∀ i, ⌜(i < R.(fp_cap))%nat⌝ -∗ R.(fp_core_pred) E L i a) -∗
    T -∗ fold_list E L ig (replicate n a) i0 R T.
  Proof.
    rewrite /fold_list. iIntros (->) "HR HT". iIntros (F ?) "#CTX #HE HL".
    iPoseProof ("HR" with "CTX HE HL") as "#HR".
    iFrame "HT HL".
    iModIntro. iIntros "%Hinv %Hinv'". iSpecialize ("HR" with "[//]").
    iInduction n as [ | n] "IH" forall (i0 Hinv); simpl.
    { by iFrame. }
    iPoseProof ("IH" $! (S i0) with "[]") as "Ha".
    { simpl in Hinv. iPureIntro. lia. }
    case_decide.
    - iR.
      iApply (big_sepL_wand with "Ha").
      iApply big_sepL_intro.
      iModIntro. iIntros (???). rewrite Nat.add_succ_r. eauto.
    - iFrame. iSplitR. { iApply "HR". simpl in Hinv. iPureIntro. lia. }
      iApply (big_sepL_mono with "Ha").
      iIntros (???). rewrite Nat.add_succ_r. done.
  Qed.

  Lemma fold_list_replicate_elim_weak {A} E L ig n (a : A) i0 (R : FoldablePredicate) T :
    R.(fp_elim_mode) = false →
    (⌜R.(fp_inv)⌝ -∗ □ ∀ i, ⌜(i < R.(fp_cap))%nat⌝ -∗ R.(fp_core_pred) E L i a) -∗
    T -∗ fold_list E L ig (replicate n a) i0 R T.
  Proof.
    rewrite /fold_list. iIntros (->) "HR $".
    iIntros "%Hinv %Hinv'". iSpecialize ("HR" with "[//]").
    iDestruct "HR" as "#HR".
    iInduction n as [ | n] "IH" forall (i0 Hinv); simpl.
    { by iFrame. }
    iPoseProof ("IH" $! (S i0) with "[]") as "Ha".
    { simpl in Hinv. iPureIntro. lia. }
    case_decide.
    - iR.
      iApply (big_sepL_wand with "Ha").
      iApply big_sepL_intro.
      iModIntro. iIntros (???). rewrite Nat.add_succ_r. eauto.
    - iFrame. iSplitR. { iApply "HR". simpl in Hinv. iPureIntro. lia. }
      iApply (big_sepL_mono with "Ha").
      iIntros (???). rewrite Nat.add_succ_r. done.
  Qed.

  Local Lemma fold_list_insert_in_ig' {A} E L (ig : list nat) (l1 : list A) (i0 : nat) i x R :
    (i0 + i ∈ ig)%nat →
    (⌜i0 + length l1 ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a ∈ l1, if decide ((i1 + i0)%nat ∈ ig) then True else fp_core_pred R E L (i1 + i0) a) -∗
    (⌜i0 + length (<[i:=x]> l1) ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a ∈ <[i:=x]> l1, if decide ((i1 + i0)%nat ∈ ig) then True else fp_core_pred R E L (i1 + i0) a).
  Proof.
    iIntros (Hel) "Ha". iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
    { rewrite insert_length in Hinv. done. }
    iInduction l1 as [ | a l1] "IH" forall (i i0 Hel Hinv); simpl; first done.
    destruct i as [ | i].
    - simpl.
      case_decide; first done.
      rewrite Nat.add_0_r in Hel. done.
    - simpl.
      case_decide.
      + iDestruct "Ha" as "(_ & Ha)". iR.
        iPoseProof ("IH" $! _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
      + iDestruct "Ha" as "($ & Ha)".
        iPoseProof ("IH" $! _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
  Qed.

  Lemma fold_list_insert_in_ig {A} E L ig (l1 : list A) (i0 : nat) i x R T `{CanSolve (i0 + i ∈ ig)%nat} :
    fold_list E L ig l1 i0 R T
    ⊢ fold_list E L ig (<[i := x]> l1) i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => unfold CanSolve in H; rename H into Hel end.
    rewrite /fold_list. destruct fp_elim_mode.
    - iIntros "HP" (??) "#CTX #HE HL".
      iMod ("HP" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. by iApply fold_list_insert_in_ig'.
    - iIntros "(HP & $)". by iApply fold_list_insert_in_ig'.
  Qed.
  Global Instance fold_list_insert_in_ig_inst {A} E L ig (l1 : list A) (i0 : nat) i x R `{!CanSolve (i0 + i ∈ ig)%nat} :
    FoldList E L ig (<[i := x]> l1) i0 R :=
    λ T, i2p (fold_list_insert_in_ig E L ig l1 i0 i x R T).

  Lemma fold_list_cons {A} E L ig (l1 : list A) i0 R a T :
    ⌜i0 ∉ ig⌝ ∗ (R.(fp_pred) E L i0 a (fold_list E L ig l1 (S i0) R T))
    ⊢ fold_list E L ig (a :: l1) i0 R T.
  Proof.
    iIntros "(%Hnel & HR)". rewrite /fold_list.
    iPoseProof (fp_elim R) as "Hx". destruct fp_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(HR & HT)".
      iPoseProof ("HT") as "(Ha & $)".
      iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance fold_list_cons_inst {A} E L ig (l1 : list A) i0 a R :
    FoldList E L ig (a :: l1) i0 R := λ T, i2p (fold_list_cons E L ig l1 i0 R a T).

  Lemma fold_list_nil {A} E L ig i0 R T :
    T ⊢ fold_list E L ig ([] : list A) i0 R T.
  Proof.
    iIntros "HT". rewrite /fold_list.
    destruct fp_elim_mode.
    - iIntros (??) "#CTX #HE $". iModIntro. iFrame.
      iIntros "_ _". by iApply big_sepL_nil.
    - iFrame. iIntros "_ _". by iApply big_sepL_nil.
  Qed.
  Global Instance fold_list_nil_inst {A} E L ig i0 R :
    FoldList E L ig ([] : list A) i0 R := λ T, i2p (fold_list_nil E L ig i0 R T).

  Local Lemma fold_list_insert_not_in_ig' {A} E L ig (l1 : list A) (R : FoldablePredicate) i0 i a :
    (i0 + i ∉ ig)%nat →
    i < length l1 →
    fp_core_pred R E L (i0 + i) a -∗
    (⌜i0 + length l1 ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a0 ∈ l1, if decide ((i1 + i0)%nat ∈ (i0 + i)%nat :: ig) then True else fp_core_pred R E L (i1 + i0) a0) -∗
    (⌜i0 + length (<[i:=a]> l1) ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a0 ∈ <[i:=a]> l1, if decide ((i1 + i0)%nat ∈ ig) then True else fp_core_pred R E L (i1 + i0) a0).
  Proof.
    iIntros (Hnel Hi) "HR Ha".
    iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
    { iPureIntro. rewrite insert_length in Hinv. lia. }
    iInduction l1 as [ | a' l1] "IH" forall (i i0 Hnel Hi Hinv).
    { simpl in *. lia. }
    destruct i as [ | i]; simpl.
    - iDestruct "Ha" as "(_ & Ha)".
      rewrite decide_False; first last. { move: Hnel. rewrite Nat.add_0_r//. }
      rewrite Nat.add_0_r. iFrame.
      iApply big_sepL_mono; first last.
      { iApply (fold_list_ig_cons_le); first last.
        { iApply big_sepL_mono; last done. iIntros. rewrite -Nat.add_succ_r//. }
        lia.
      }
      iIntros. rewrite Nat.add_succ_r//.
    - destruct (decide (i0 ∈ ig)).
      + iR. iDestruct "Ha" as "(_ & Ha)".
        iApply big_sepL_mono; first last.
        { iApply ("IH" with "[] [] [] [HR] [Ha]"); first last.
          - iApply big_sepL_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
      + rewrite decide_False; first last. { apply not_elem_of_cons. split; last done. lia. }
        iDestruct "Ha" as "($ & Ha)".
        iApply big_sepL_mono; first last.
        { iApply ("IH" with "[] [] [] [HR]"); first last.
          - iApply big_sepL_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Lemma fold_list_insert_not_in_ig {A} E L ig (l1 : list A) (R : FoldablePredicate) i0 i a T `{CanSolve (i0 + i ∉ ig)%nat} :
    ⌜i < length l1⌝ ∗
    (R.(fp_pred) E L (i0 + i) a (fold_list E L ((i0 + i) :: ig)%nat l1 i0 R T))
    ⊢ fold_list E L ig (<[i := a]> l1) i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => rewrite /CanSolve in H; rename H into Hnel end.
    iIntros "(%Hi & HR)". rewrite /fold_list.
    iPoseProof (fp_elim R) as "Hx". destruct fp_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL ") as "(Ha & $ & $)".
      iModIntro. by iApply (fold_list_insert_not_in_ig' with "HR Ha").
    - iPoseProof ("Hx" with "HR") as "(HR & Ha & $)".
      by iApply (fold_list_insert_not_in_ig' with "HR Ha").
  Qed.
  Global Instance fold_list_insert_not_in_ig_inst {A} E L ig (l1 : list A) R (i0 : nat) i a `{!CanSolve (i0 + i ∉ ig)%nat} :
    FoldList E L ig (<[i := a]> l1) i0 R :=
    λ T, i2p (fold_list_insert_not_in_ig E L ig l1 R i0 i a T).

  Lemma fold_list_app {A} E L ig (l1 l1' : list A) (R : FoldablePredicate) (i0 : nat) T :
    fold_list E L ig l1 i0 R (fold_list E L ig l1' (length l1 + i0)%nat R T)
    ⊢ fold_list E L ig (l1 ++ l1') i0 R T.
  Proof.
    rewrite /fold_list. destruct fp_elim_mode.
    - iIntros "Ha" (??) "#CTX #HE HL".
      iMod ("Ha" with "[//] CTX HE HL") as "(Ha & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hb & $ & $)".
      iModIntro. iIntros "%Hinv %". rewrite app_length in Hinv.
      iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]"). { iPureIntro. lia. }
      rewrite big_sepL_app. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
    - iIntros "(Ha & Hb & $)".
      iIntros "%Hinv %". rewrite app_length in Hinv.
      iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]"). { iPureIntro. lia. }
      rewrite big_sepL_app. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
  Qed.
  Global Instance fold_list_app_inst {A} E L ig (l1 l1' : list A) R i0 :
    FoldList E L ig (l1 ++ l1') i0 R :=
    λ T, i2p (fold_list_app E L ig l1 l1' R i0 T).
End fold_list.

(** ** OnEndlft triggers *)
Section endlft_triggers.
  Context `{!typeGS Σ}.
  (* no typeclass for this one, as rules are directly applied by Ltac automation *)
  Definition typed_on_endlft_pre (π : thread_id) (E : elctx) (L : llctx) (κ : lft) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L -∗ [† κ] ={F}=∗ ∃ L', llctx_interp L' ∗ T L'.

  Definition typed_on_endlft (π : thread_id) (E : elctx) (L : llctx) (κ : lft) (worklist: list (sigT (@id Type) * iProp Σ)) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L -∗ [† κ] ={F}=∗ ∃ L', llctx_interp L' ∗ T L'.
  Class TypedOnEndlft (π : thread_id) (E : elctx) (L : llctx) (κ : lft) (worklist : list (sigT (@id Type) * iProp Σ)) :=
    typed_on_endlft_proof T : iProp_to_Prop (typed_on_endlft π E L κ worklist T).

  Definition typed_on_endlft_trigger {K} (E : elctx) (L : llctx) (key : K) (P : iProp Σ) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L -∗ P ={F}=∗ ∃ L', llctx_interp L' ∗ T L'.
  Class TypedOnEndlftTrigger {K} (E : elctx) (L : llctx) (key : K) (P : iProp Σ) :=
    typed_on_endlft_trigger_proof T : iProp_to_Prop (typed_on_endlft_trigger E L key P T).

  (* no instance, automation needs to manually instantiate the worklist *)
  Lemma typed_on_endlft_pre_init worklist π E L κ T :
    typed_on_endlft π E L κ worklist T
    ⊢ typed_on_endlft_pre π E L κ T.
  Proof. done. Qed.

  Lemma typed_on_endlft_nil π E L κ T :
    T L ⊢ typed_on_endlft π E L κ [] T.
  Proof.
    iIntros "Hs" (F ?) "HE HL ?". iModIntro. iExists L. iFrame.
  Qed.
  Global Instance typed_on_endlft_nil_inst π E L κ : TypedOnEndlft π E L κ [] :=
    λ T, i2p (typed_on_endlft_nil π E L κ T).

  Lemma typed_on_endlft_cons {K} π E L κ key P worklist T :
    find_in_context (FindInherit κ key P) (λ _,
      typed_on_endlft_trigger E L key P (λ L', typed_on_endlft π E L' κ worklist T))
    ⊢ typed_on_endlft π E L κ ((existT K key, P) :: worklist) T.
  Proof.
    iIntros "Hs" (F ?) "#HE HL #Hdead".
    iDestruct "Hs" as ([]) "(Hinh & Hc)". simpl.
    rewrite /Inherit.
    iMod ("Hinh" with "[//] Hdead") as "HP".
    iMod ("Hc" with "[//] HE HL HP") as "(%L' & HL & HT)".
    iApply ("HT" with "[//] HE HL Hdead").
  Qed.
  Global Instance typed_on_endlft_cons_inst {K} π E L κ (key : K) P worklist : TypedOnEndlft π E L κ ((existT K key, P) :: worklist) :=
    λ T, i2p (typed_on_endlft_cons π E L κ key P worklist T).
End endlft_triggers.

(** For implementation of [GetLftNamesAnnot].
   Get the symbolic lifetimes associated for a type [ty], according to the structure given by [tree],
    and map the names given in [tree] to the symbolic lifetimes in [ty].
   Outputs an updated map [lfts'] with those names. *)
Class GetLftNames `{!typeGS Σ} {rt} (ty : type rt) (lfts : gmap string lft) (tree : LftNameTree) (lfts' : gmap string lft) := GLN {}.
Global Hint Mode GetLftNames ! ! + + - + - : typeclass_instances.
Global Arguments GLN {_ _ _ _ _ _ _}.
Global Instance get_lft_names_leaf `{!typeGS Σ} {rt} (ty : type rt) lfts : GetLftNames ty lfts LftNameTreeLeaf lfts := GLN.



From lithium Require Import hooks.
Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | typed_value ?x ?π => constr:(TypedValue x π)
  | typed_bin_op ?π ?E ?L ?v1 ?P1 ?v2 ?P2 ?o ?ot1 ?ot2 => constr:(TypedBinOp π E L v1 P1 v2 P2 o ot1 ot2)
  | typed_un_op ?π ?E ?L ?v ?P ?o ?ot => constr:(TypedUnOp π E L v P o ot)
  | typed_call ?π ?E ?L ?κs ?v ?P ?vs ?tys => constr:(TypedCall π E L κs v P vs tys)
  | typed_place ?π ?E ?L ?l ?lto ?ro ?b1 ?b2 ?K => constr:(TypedPlace E L π l lto ro b1 b2 K)
  | typed_read_end ?π ?E ?L ?l ?lt ?r ?b1 ?b2 ?al ?ot => constr:(TypedReadEnd π E L l lt r b1 b2 al  ot)
  | typed_write_end ?π ?E ?L ?ot ?v ?ty1 ?r1 ?b1 ?b2 ?al ?l ?lt2 ?r2 => constr:(TypedWriteEnd π E L ot v ty1 r1 b1 b2 al l lt2 r2)
  | typed_addr_of_mut_end ?π ?E ?L ?l ?lt ?r ?b1 ?b2 => constr:(TypedAddrOfMutEnd π E L l lt r b1 b2)
  | typed_annot_expr ?π ?E ?L ?n ?a ?v ?P => constr:(TypedAnnotExpr π E L n a v P)
  | typed_if ?E ?L ?v ?P => constr:(TypedIf E L v P)
  | typed_assert ?π ?E ?L ?v ?ty ?r  => constr:(TypedAssert π E L v ty r)
  | typed_switch ?π ?E ?L ?v ?ty ?r ?it => constr:(TypedSwitch π E L v ty r it)
  | typed_annot_stmt ?a => constr:(TypedAnnotStmt a)
  | subsume_full ?E ?L ?wl ?P1 ?P2 => constr:(SubsumeFull E L wl P1 P2)
  | prove_with_subtype ?E ?L ?wl ?pm ?P => constr:(ProveWithSubtype E L wl pm P)
  | typed_on_endlft ?π ?E ?L ?κ ?worklist => constr:(TypedOnEndlft π E L κ worklist)
  | weak_subtype ?E ?L ?r1 ?r2 ?ty1 ?ty2 => constr:(Subtype E L r1 r2 ty1 ty2)
  | mut_subtype ?E ?L ?ty1 ?ty2 => constr:(MutSubtype E L ty1 ty2)
  | owned_subtype ?π ?E ?L ?wl ?r1 ?r2 ?ty1 ?ty2 => constr:(OwnedSubtype π E L wl r1 r2 ty1 ty2)
  | weak_subltype ?E ?L ?k ?r1 ?r2 ?lt1 ?lt2 => constr:(SubLtype E L k r1 r2 lt1 lt2)
  | mut_subltype ?E ?L ?lt1 ?lt2 => constr:(MutSubLtype E L lt1 lt2)
  | owned_subltype_step ?π ?E ?L ?l ?r1 ?r2 ?lt1 ?lt2 => constr:(OwnedSubltypeStep π E L l r1 r2 lt1 lt2)
  | _ => fail "unknown judgement" c
  end.
