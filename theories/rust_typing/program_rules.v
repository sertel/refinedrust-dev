From stdpp Require Import gmap.
From caesium Require Import lang proofmode derived lifting.
From refinedrust Require Export base type lft_contexts annotations ltypes programs.
From refinedrust Require Import ltype_rules.
Set Default Proof Using "Type".

(** * Core rules of the type system *)

Section typing.
  Context `{typeGS Σ}.
  (* NOTE: find_in_context instances should always have a sep conj in their premise, even if the LHS is just [True].
    This is needed by the liFindInContext/ liFindHypOrTrue automation!
  *)

  (** Instances so that Lithium knows what to search for when needing to provide something *)
  (** For locations and values, we use the ones that also find a refinement type, since it may be desirable to change it (consider e.g. changing to uninit) *)
  Global Instance related_to_loc l π b {rt} (lt : ltype rt) (r : place_rfn rt) : RelatedTo (l ◁ₗ[π, b] r @ lt)  | 100 :=
    {| rt_fic := FindLocP l π |}.
  Global Instance related_to_val v π {rt} (ty : type rt) (r : rt) : RelatedTo (v ◁ᵥ{π} r @ ty)  | 100 :=
    {| rt_fic := FindValP v π|}.
  (* TODO: need a relatedto for shared ownership? *)

  Global Instance related_to_named_lfts M : RelatedTo (named_lfts M) | 100 :=
    {| rt_fic := FindNamedLfts |}.
  Global Instance related_to_gvar_pobs {rt} γ (r : rt) : RelatedTo (gvar_pobs γ r) | 100 :=
    {| rt_fic := FindGvarPobsP γ |}.

  Global Instance related_to_credit_store n m : RelatedTo (credit_store n m) | 100 :=
    {| rt_fic := FindCreditStore |}.

  Global Instance related_to_freeable l n q k : RelatedTo (freeable_nz l n q k) | 100 :=
    {| rt_fic := FindFreeable l |}.

  Global Instance related_to_loc_in_bounds l pre suf : RelatedTo (loc_in_bounds l pre suf) | 100 :=
    {| rt_fic := FindLocInBounds l |}.

  (* TODO instances needed for the other things? *)

  (** Value ownership *)
  Lemma find_in_context_type_val_id v π T :
    (∃ rt (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T (existT rt (ty, r)))
    ⊢ find_in_context (FindVal v π) T.
  Proof. iDestruct 1 as (rt ty r) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_id_inst π v :
    FindInContext (FindVal v π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_val_id v π T).

  Lemma find_in_context_type_valp_id v π T :
    (∃ rt (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T (v ◁ᵥ{π} r @ ty))
    ⊢ find_in_context (FindValP v π) T.
  Proof. iDestruct 1 as (rt ty r) "(Hl & HT)". iExists (v ◁ᵥ{π} r @ ty)%I => /=. iFrame. Qed.
  Global Instance find_in_context_type_valp_id_inst π v :
    FindInContext (FindValP v π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_valp_id v π T).

  Lemma find_in_context_type_valp_loc l π T :
    (∃ rt (lt : ltype rt) r, l ◁ₗ[π, Owned false] r @ lt ∗ T (l ◁ₗ[π, Owned false] r @ lt))
    ⊢ find_in_context (FindValP (val_of_loc l) π) T.
  Proof. iDestruct 1 as (rt lt r) "(Hl & HT)". iExists (l ◁ₗ[π, Owned false] r @ lt)%I. iFrame. done. Qed.
  Global Instance find_in_context_type_valp_loc_inst π l :
    FindInContext (FindValP (val_of_loc l) π) FICSyntactic | 5 :=
    λ T, i2p (find_in_context_type_valp_loc l π T).

  Lemma find_in_context_type_val_with_rt_id {rt} v π T :
    (∃ (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T (ty, r))
    ⊢ find_in_context (FindValWithRt rt v π) T.
  Proof. iDestruct 1 as (ty r) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_with_rt_id_inst {rt} π v :
    FindInContext (FindValWithRt rt v π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_val_with_rt_id v π T).

  (* TODO: generalize to different rt to handle typaram instantiation?*)
  Lemma own_val_subsume_id v π {rt} (r1 r2 : rt) (ty1 ty2 : type rt) T :
    ⌜r1 = r2⌝ ∗ ⌜ty1 = ty2⌝ ∗ T
    ⊢ subsume (Σ := Σ) (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "(-> & -> & $)"; eauto.
  Qed.
  Definition own_val_subsume_id_inst v π {rt} (r1 r2 : rt) (ty1 ty2 : type rt) :
    Subsume (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) :=
    λ T, i2p (own_val_subsume_id v π r1 r2 ty1 ty2 T).

  (** Location ownership *)
  Lemma find_in_context_type_loc_id l π T:
    (∃ rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (existT rt (lt, r, b)))
    ⊢ find_in_context (FindLoc l π) T.
  Proof. iDestruct 1 as (rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_id_inst π l :
    FindInContext (FindLoc l π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_loc_id l π T).

  Lemma find_in_context_type_opt_loc_id l π T:
    (∃ rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (Some (existT rt (lt, r, b))))
    ⊢ find_in_context (FindOptLoc l π) T.
  Proof. iDestruct 1 as (rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_opt_loc_id_inst π l :
    FindInContext (FindOptLoc l π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_opt_loc_id l π T).
  Lemma find_in_context_type_opt_loc_none l π T:
    (True ∗ T None)
    ⊢ find_in_context (FindOptLoc l π) T.
  Proof. iDestruct 1 as "[_ HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_opt_loc_none_inst π l :
    FindInContext (FindOptLoc l π) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_type_opt_loc_none l π T).

  Lemma find_in_context_type_locp_loc l π T :
    (∃ rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (l ◁ₗ[π, b] r @ lt))
    ⊢ find_in_context (FindLocP l π) T.
  Proof. iDestruct 1 as (rt lt r b) "[Hl HT]". iExists (l ◁ₗ[π, b] r @ lt)%I => /=. iFrame. Qed.
  Global Instance find_in_context_type_locp_loc_inst π l :
    FindInContext (FindLocP l π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_locp_loc l π T).
  Lemma find_in_context_type_locp_val (l : loc) π T :
    (∃ rt (ty : type rt) r , l ◁ᵥ{π} r @ ty ∗ T (l ◁ᵥ{π} r @ ty))
    ⊢ find_in_context (FindLocP l π) T.
  Proof. iDestruct 1 as (rt ty r) "[Hl HT]". iExists (l ◁ᵥ{π} r @ ty)%I => /=. iFrame. Qed.
  (* NOTE: important: has lower priority! If there's a location assignment available, should just use that. *)
  Global Instance find_in_context_type_locp_val_inst π l :
    FindInContext (FindLocP l π) FICSyntactic | 2 :=
    λ T, i2p (find_in_context_type_locp_val l π T).

  Lemma find_in_context_type_loc_with_rt_id {rt} l π T:
    (∃ (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (lt, r, b))
    ⊢ find_in_context (FindLocWithRt rt l π) T.
  Proof. iDestruct 1 as (lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_with_rt_id_inst {rt} π l :
    FindInContext (FindLocWithRt rt l π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_loc_with_rt_id l π T).

  (* used for unifying evars *)
  Lemma own_shr_subsume_id v π {rt} (r1 r2 : rt) (κ1 κ2 : lft) (ty : type rt) T :
    ⌜r1 = r2⌝ ∗ ⌜κ1 = κ2⌝ ∗ T
    ⊢ subsume (Σ := Σ) (v ◁ₗ{π, κ1} r1 @ ty) (v ◁ₗ{π, κ2} r2 @ ty) T.
  Proof.
    iIntros "(-> & -> & $)"; eauto.
  Qed.
  Definition own_shr_subsume_id_inst v π {rt} (r1 r2 : rt) (κ1 κ2 : lft) (ty : type rt) :
    Subsume (v ◁ₗ{π, κ1} r1 @ ty) (v ◁ₗ{π, κ2} r2 @ ty) :=
    λ T, i2p (own_shr_subsume_id v π r1 r2 κ1 κ2 ty T).

  (** NamedLfts *)
  Lemma subsume_named_lfts M M' T :
    ⌜M = M'⌝ ∗ T ⊢ subsume (Σ := Σ) (named_lfts M) (named_lfts M') T.
  Proof. iIntros "(-> & $) $". Qed.
  Global Instance subsume_named_lfts_inst M M' : Subsume (named_lfts M) (named_lfts M') :=
    λ T, i2p (subsume_named_lfts M M' T).

  Lemma find_in_context_named_lfts T:
    (∃ M, named_lfts M ∗ T M) ⊢
    find_in_context FindNamedLfts T.
  Proof. iDestruct 1 as (M) "[Hn HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_named_lfts_inst :
    FindInContext FindNamedLfts FICSyntactic | 1 :=
    λ T, i2p (find_in_context_named_lfts T).

  (** CreditStore *)
  Lemma subsume_credit_store n m n' m' T :
    ⌜n = n'⌝ ∗ ⌜m = m'⌝ ∗ T ⊢ subsume (Σ := Σ) (credit_store n m) (credit_store n' m') T.
  Proof.
    iIntros "(<- & <- & HT) $ //".
  Qed.
  Global Instance subsume_credit_store_inst n m n' m' : Subsume (credit_store n m) (credit_store n' m') :=
    λ T, i2p (subsume_credit_store n m n' m' T).

  Lemma find_in_context_credit_store T :
    (∃ n m, credit_store n m ∗ T (n, m)) ⊢
    find_in_context FindCreditStore T.
  Proof.
    iDestruct 1 as (n m) "[Hc HT]". iExists (n, m). by iFrame.
  Qed.
  Global Instance find_in_context_credit_store_inst :
    FindInContext FindCreditStore FICSyntactic | 1 :=
    λ T, i2p (find_in_context_credit_store T).

  (** FindOptLftDead *)
  Lemma subsume_lft_dead κ1 κ2 T :
    ⌜κ1 = κ2⌝ ∗ T ⊢ subsume (Σ := Σ) ([† κ1]) ([† κ2]) T.
  Proof. iIntros "(-> & $)". eauto. Qed.
  Global Instance subsume_lft_dead_inst κ1 κ2 :
    Subsume ([† κ1]) ([† κ2]) := λ T, i2p (subsume_lft_dead κ1 κ2 T).

  Lemma find_in_context_opt_lft_dead κ T :
    [† κ] ∗ T true
    ⊢ find_in_context (FindOptLftDead κ) T.
  Proof.
    iIntros "(Hdead & HT)". iExists true. iFrame. done.
  Qed.
  Global Instance find_in_context_opt_lft_dead_inst κ :
    FindInContext (FindOptLftDead κ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_lft_dead κ T).

  (* dummy instance in case we don't find it *)
  Lemma find_in_context_opt_lft_dead_none κ T :
    True ∗ T false
    ⊢ find_in_context (FindOptLftDead κ) T.
  Proof.
    iIntros "(_ & HT)". iExists false. iFrame. simpl. done.
  Qed.
  Global Instance find_in_context_opt_lft_dead_none_inst κ :
    FindInContext (FindOptLftDead κ) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_opt_lft_dead_none κ T).

  (** Freeable *)
  Lemma subsume_freeable l1 q1 n1 k1 l2 q2 n2 k2 T :
    ⌜l1 = l2⌝ ∗ ⌜n1 = n2⌝ ∗ ⌜q1 = q2⌝ ∗ ⌜k1 = k2⌝ ∗ T
    ⊢ subsume (freeable_nz l1 n1 q1 k1) (freeable_nz l2 n2 q2 k2) T.
  Proof.
    iIntros "(-> & -> & -> & -> & $)". eauto.
  Qed.
  Global Instance subsume_freeable_inst l1 q1 n1 k1 l2 q2 n2 k2 :
    Subsume (freeable_nz l1 n1 q1 k1) (freeable_nz l2 n2 q2 k2) :=
    λ T, i2p (subsume_freeable l1 q1 n1 k1 l2 q2 n2 k2 T).

  Lemma find_in_context_freeable l T :
    (∃ q n k, freeable_nz l n q k ∗ T (n, q, k))
    ⊢ find_in_context (FindFreeable l) T.
  Proof.
    iDestruct 1 as (q n k) "(Ha & HT)".
    iExists (n, q, k). by iFrame.
  Qed.
  Global Instance find_in_context_freeable_inst l :
    FindInContext (FindFreeable l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_freeable l T).

  Lemma simplify_hyp_freeable l n q k T :
    ((freeable_nz l n q k) -∗ T)
    ⊢ simplify_hyp (freeable l n q k) T.
  Proof.
    iIntros "Ha Hf". iApply "Ha".
    destruct n; done.
  Qed.
  Global Instance simplify_hyp_freeable_inst l n q k :
    SimplifyHyp (freeable l n q k) (Some 0%N) :=
    λ T, i2p (simplify_hyp_freeable l n q k T).


  (** FindOptGvarRel *)
  Lemma find_in_context_opt_gvar_rel γ T :
    (∃ rt (γ' : gname) (R : rt → rt → Prop), Rel2 γ' γ R ∗ T (inl (existT rt (γ', R))))
    ⊢ find_in_context (FindOptGvarRel γ) T.
  Proof.
    iIntros "(%rt & %γ' & %R & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_opt_gvar_rel_inst γ :
    FindInContext (FindOptGvarRel γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_gvar_rel γ T).

  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_gvar_rel_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptGvarRel γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_rel_dummy_inst γ :
    FindInContext (FindOptGvarRel γ) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_opt_gvar_rel_dummy γ T).

  Lemma subsume_gvar_rel {rt} γ1' γ1 γ2' γ2 (R1 R2 : rt → rt → Prop ) T :
    ⌜γ1' = γ2'⌝ ∗ ⌜γ1 = γ2⌝ ∗ ⌜∀ x1 x2, R1 x1 x2 ↔ R2 x1 x2⌝ ∗ T ⊢ subsume (Σ := Σ) (Rel2 γ1' γ1 R1) (Rel2 γ2' γ2 R2) T.
  Proof.
    iIntros "(-> & -> & %HR & $)".
    iIntros "Hrel". iDestruct "Hrel" as "(% & % & ? & ? & %HR')".
    iExists _, _. iFrame. iPureIntro. by apply HR.
  Qed.
  Global Instance subsume_gvar_rel_inst {rt} γ1' γ1 γ2' γ2 (R1 R2 : rt → rt → Prop) : Subsume (Rel2 γ1' γ1 R1) (Rel2 γ2' γ2 R2) :=
    λ T, i2p (subsume_gvar_rel γ1' γ1 γ2' γ2 R1 R2 T).

  (** FindOptGvarPobs *)
  Lemma find_in_context_opt_gvar_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T (inl (existT rt r)))
    ⊢ find_in_context (FindOptGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_opt_gvar_pobs_inst γ :
    FindInContext (FindOptGvarPobs γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_gvar_pobs γ T).

  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_gvar_pobs_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptGvarPobs γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_dummy_inst γ :
    FindInContext (FindOptGvarPobs γ) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_opt_gvar_pobs_dummy γ T).

  (** FindGvarPobs *)
  Lemma find_in_context_gvar_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T ((existT rt r)))
    ⊢ find_in_context (FindGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_inst γ :
    FindInContext (FindGvarPobs γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs γ T).

  Lemma find_in_context_gvar_pobs_p_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T (gvar_pobs γ r))
    ⊢ find_in_context (FindGvarPobsP γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists (gvar_pobs γ r) => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_p_pobs_inst γ :
    FindInContext (FindGvarPobsP γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs_p_pobs γ T).

  Lemma find_in_context_gvar_pobs_p_obs γ T :
    (∃ rt (r : rt), gvar_obs γ r ∗ T (gvar_obs γ r))
    ⊢ find_in_context (FindGvarPobsP γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists (gvar_obs γ r) => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_p_obs_inst γ :
    FindInContext (FindGvarPobsP γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs_p_obs γ T).

  Lemma subsume_gvar_pobs {rt} γ (r1 r2 : rt) T :
    ⌜r1 = r2⌝ ∗ T ⊢ subsume (Σ := Σ) (gvar_pobs γ r1) (gvar_pobs γ r2) T.
  Proof. iIntros "(-> & $) $". Qed.
  Global Instance subsume_gvar_pobs_inst {rt} γ (r1 r2 : rt) : Subsume (gvar_pobs γ r1) (gvar_pobs γ r2) :=
    λ T, i2p (subsume_gvar_pobs γ r1 r2 T).

  Lemma subsume_full_gvar_obs_pobs E L {rt} step γ (r1 r2 : rt) T :
    (⌜r1 = r2⌝ ∗ (gvar_pobs γ r2 -∗ T L (True)%I)) ⊢ subsume_full E L step (gvar_obs γ r1) (gvar_pobs γ r2) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (???) "#CTX #HE HL Hobs". iMod (gvar_obs_persist with "Hobs") as "#Hobs".
    iExists _, _. iPoseProof ("HT" with "Hobs") as "$". iFrame.
    iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance subsume_full_gvar_obs_pobs_inst E L {rt} step γ (r1 r2 : rt) : SubsumeFull E L step (gvar_obs γ r1) (gvar_pobs γ r2) :=
    λ T, i2p (subsume_full_gvar_obs_pobs E L step γ r1 r2 T).

  (** FindInherit *)
  Lemma find_in_context_inherit {K} κ (key : K) P T :
    Inherit κ key P ∗ T () ⊢
    find_in_context (FindInherit κ key P) T.
  Proof.
    iIntros "(Hinh & HT)". iExists (). by iFrame.
  Qed.
  Global Instance find_in_context_inherit_inst {K} κ (key : K) P :
    FindInContext (FindInherit κ key P) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_inherit κ key P T).

  (** FindLocInBounds *)
  Lemma find_in_context_loc_in_bounds l T :
    (∃ pre suf, loc_in_bounds l pre suf ∗ T (loc_in_bounds l pre suf))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (pre suf) "[??]". iExists (loc_in_bounds _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_inst l :
    FindInContext (FindLocInBounds l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_loc_in_bounds l T).

  Lemma find_in_context_loc_in_bounds_loc l T :
    (∃ π k rt (lt : ltype rt) r, l ◁ₗ[π, k] r @ lt ∗ T (l ◁ₗ[π, k] r @ lt))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (?????) "[??]". iExists (ltype_own _ _ _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_loc_inst l :
    FindInContext (FindLocInBounds l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_loc_in_bounds_loc l T).

  Lemma subsume_loc_in_bounds (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T :
    ⌜l1.1 = l2.1⌝ ∗ ⌜(l1.2 + pre2 ≤ l2.2 + pre1)%Z⌝ ∗ ⌜(l2.2 + suf2 ≤ l1.2 + suf1)%Z⌝ ∗ T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof.
    iIntros "(% & % & % & $)". by iApply loc_in_bounds_offset.
  Qed.
  Global Instance subsume_loc_in_bounds_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 100 :=
    λ T, i2p (subsume_loc_in_bounds l1 l2 pre1 suf1 pre2 suf2 T).

  Lemma subsume_loc_in_bounds_evar1 (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T `{!IsProtected pre2} :
    ⌜pre1 = pre2⌝ ∗ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre1 suf2) T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof. iIntros "(-> & $)". Qed.
  Global Instance subsume_loc_in_bounds_evar1_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) `{!IsProtected pre2} :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 20 :=
    λ T, i2p (subsume_loc_in_bounds_evar1 l1 l2 pre1 suf1 pre2 suf2 T).
  Lemma subsume_loc_in_bounds_evar2 (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T `{!IsProtected suf2} :
    ⌜suf1 = suf2⌝ ∗ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf1) T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof. iIntros "(-> & $)". Qed.
  Global Instance subsume_loc_in_bounds_evar2_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) `{!IsProtected suf2} :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 20 :=
    λ T, i2p (subsume_loc_in_bounds_evar2 l1 l2 pre1 suf1 pre2 suf2 T).

  (* TODO: maybe generalize this to have a TC or so so? *)
  Lemma subsume_place_loc_in_bounds π (l1 l2 : loc) {rt} (lt : ltype rt) k r (pre suf : nat) T :
    ⌜l1 = l2⌝ ∗ ⌜pre = 0%nat⌝ ∗ li_tactic (compute_layout_goal (ltype_st lt)) (λ ly,
      ⌜suf ≤ ly_size ly⌝ ∗ (l1 ◁ₗ[π, k] r @ lt -∗ T))
    ⊢ subsume (l1 ◁ₗ[π, k] r @ lt) (loc_in_bounds l2 pre suf) T.
  Proof.
    rewrite /compute_layout_goal. iIntros "(-> & -> & %ly & %Halg & %Ha & HT)".
    iIntros "Ha". iPoseProof (ltype_own_loc_in_bounds with "Ha") as "#Hb"; first done.
    iPoseProof ("HT" with "Ha") as "$".
    iApply (loc_in_bounds_shorten_suf with "Hb"). lia.
  Qed.
  Global Instance subsume_place_loc_in_bounds_inst π (l1 l2 : loc) {rt} (lt : ltype rt) k r (pre suf : nat) :
    Subsume (l1 ◁ₗ[π, k] r @ lt) (loc_in_bounds l2 pre suf) :=
    λ T, i2p (subsume_place_loc_in_bounds π l1 l2 lt  k r pre suf T).

  (** Simplify instances *)
  Lemma simplify_goal_lft_dead_list κs T :
    ([∗ list] κ ∈ κs, [† κ]) ∗ T ⊢ simplify_goal (lft_dead_list κs) T.
  Proof.
    rewrite /simplify_goal. iFrame. eauto.
  Qed.
  Global Instance simplify_goal_lft_dead_list_inst κs :
    SimplifyGoal (lft_dead_list κs) (Some 0%N) := λ T, i2p (simplify_goal_lft_dead_list κs T).

  (** ** SubsumeFull instances *)
  (** We have low-priority instances to escape into subtyping judgments *)
  (* TODO should make compatible with mem_casts? *)
  (*
  Lemma subsume_full_own_val {rt1 rt2} π E L step v (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    weak_subtype E L r1 r2 ty1 ty2 (T L True) -∗
    subsume_full E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "HT" (F ?) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & HT)".
    iDestruct "Hincl" as "(_ & _ & #Hincl & _)".
    iExists _, True%I. iFrame.
    iApply maybe_logical_step_intro. rewrite right_id.
    by iPoseProof ("Hincl" with "Hv") as "$".
  Qed.
  (* low priority, more specific instances should trigger first *)
  Global Instance subsume_full_own_val_inst {rt1 rt2} π E L step v (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) | 100 :=
    λ T, i2p (subsume_full_own_val π E L step v ty1 ty2 r1 r2 T).
  *)

  Lemma subsume_full_value_evar π E L step v {rt} (ty : type rt) (r1 r2 : rt) T :
    ⌜r1 = r2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (v ◁ᵥ{π} r1 @ ty) (v ◁ᵥ{π} r2 @ ty) T.
  Proof.
    iIntros "(-> & HT)". by iApply subsume_full_id.
  Qed.
  Global Instance subsume_full_value_evar_inst π E L step v {rt} (ty : type rt) (r1 r2 : rt) :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty) (v ◁ᵥ{π} r2 @ ty) | 5 :=
    λ T, i2p (subsume_full_value_evar π E L step v ty r1 r2 T).

  Lemma subsume_full_owned_subtype π E L step v {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    owned_subtype π E L false r1 r2 ty1 ty2 (λ L', T L' True%I)
    ⊢ subsume_full E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "HT" (???) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & Hincl & HL & HT)".
    iDestruct "Hincl" as "(_ & _ & Hincl)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    iExists _, _. iFrame. iApply maybe_logical_step_intro.
    by iFrame.
  Qed.
  Global Instance subsume_full_uninit_owned_subtype_inst π E L step v {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty1)%I (v ◁ᵥ{π} r2 @ ty2)%I | 100 :=
    λ T, i2p (subsume_full_owned_subtype π E L step v ty1 ty2 r1 r2 T).

  (* TODO: how does the evar thing work here? *)
  Lemma subsume_full_own_loc_bk_evar {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) b1 b2 r1 r2 T `{!ContainsProtected b2}:
    ⌜b1 = b2⌝ ∗ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T
    ⊢ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T.
  Proof. iIntros "(-> & HT)". done. Qed.
  Global Instance subsume_full_own_loc_bk_evar_inst {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 b1 b2 `{!ContainsProtected b2}:
    SubsumeFull E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) | 1000 :=
    λ T, i2p (subsume_full_own_loc_bk_evar π E L step l lt1 lt2 b1 b2 r1 r2 T).

  Lemma subsume_full_own_loc_owned_false {rt1 rt2} π E L l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T :
    owned_subltype_step π E L l r1 r2 lt1 lt2 T
    ⊢ subsume_full E L true (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) T.
  Proof.
    iIntros "HT" (???) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] CTX HE HL Hl") as "(%L' & %R & Hstep & %Hly & HL & HT)".
    iExists L', R. by iFrame.
  Qed.
  Global Instance subsume_full_own_loc_owned_false_inst {rt1 rt2} π E L l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 :
    SubsumeFull E L true (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) | 1001 :=
    λ T, i2p (subsume_full_own_loc_owned_false π E L l lt1 lt2 r1 r2 T).

  Lemma subsume_full_own_loc_owned_false_true {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T
    `{!TCDone (match ltype_lty _ lt2 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end)} :
    prove_with_subtype E L s ProveDirect (have_creds) (λ L2 κs R,
      subsume_full E L2 s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) (λ L3 R2, T L3 (R ∗ R2)))
    ⊢ subsume_full E L s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned true] r2 @ lt2) T.
  Proof.
    iIntros "HT" (???) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & %κs & %R & Hs & HL & HT)".
    iMod ("HT" with "[//] [//] CTX HE HL Hl") as "(%L3 & %R2 & Hstep2 & HL & HT)".
    iExists _, _. iFrame.
    iApply (maybe_logical_step_compose with "Hs").
    iApply (maybe_logical_step_compose with "Hstep2").
    iApply maybe_logical_step_intro. iModIntro.
    iIntros "(Hl & $) (Hcred & $)".
    iApply (ltype_own_Owned_false_true with "Hl Hcred"); done.
  Qed.
  Global Instance subsume_full_own_loc_owned_false_true_inst {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2
    `{!TCDone (match ltype_lty _ lt2 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end)} :
    SubsumeFull E L s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned true] r2 @ lt2) | 1001 :=
    λ T, i2p (subsume_full_own_loc_owned_false_true π E L s l lt1 lt2 r1 r2 T).

  Lemma subsume_full_own_loc_owned_true_false {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T
    `{!TCDone (match ltype_lty _ lt1 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end)} :
      introduce_with_hooks E L (£ (num_cred - 1) ∗ atime 1) (λ L2,
      subsume_full E L2 s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) T)
    ⊢ subsume_full E L s (l ◁ₗ[π, Owned true] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) T.
  Proof.
    iIntros "HT" (???) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_Owned_true_false with "Hl") as "(((Hcred1 & Hcred) & Hat) & Hl)"; first done.
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iMod ("HT" with "[//] HE HL [$Hcred $Hat]") as "(%L2 & HL & HT)".
    by iApply ("HT" with "[//] [//] CTX HE HL").
  Qed.
  Global Instance subsume_full_own_loc_owned_true_false_inst {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2
    `{!TCDone (match ltype_lty _ lt1 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end)} :
    SubsumeFull E L s (l ◁ₗ[π, Owned true] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) | 1001 :=
    λ T, i2p (subsume_full_own_loc_owned_true_false π E L s l lt1 lt2 r1 r2 T).

  (* TODO should make compatible with location simplification *)
  Lemma subsume_full_own_loc {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) b1 b2 r1 r2 T :
    ⌜lctx_bor_kind_direct_incl E L b2 b1⌝ ∗ weak_subltype E L b2 r1 r2 lt1 lt2 (T L True%I)
    ⊢ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T.
  Proof.
    iIntros "(%Hincl & HT)" (F ??) "#CTX #HE HL Hl".
    iPoseProof (lctx_bor_kind_direct_incl_use with "HE HL") as "#Hincl"; first done.
    iPoseProof (ltype_bor_kind_direct_incl with "Hincl Hl") as "Hl".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & HT)".
    iMod (ltype_incl_use with "Hincl' Hl") as "Hl"; first done.
    iExists _, True%I. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance subsume_full_own_loc_inst {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 b1 b2 :
    SubsumeFull E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) | 1002 :=
    λ T, i2p (subsume_full_own_loc π E L step l lt1 lt2 b1 b2 r1 r2 T).

  (** ** Subtyping instances: [weak_subtype] *)
  Lemma weak_subtype_id E L {rt} (ty : type rt) r T :
    T ⊢ weak_subtype E L r r ty ty T.
  Proof.
    iIntros "$" (??) "?? $". iApply type_incl_refl.
  Qed.
  Global Instance weak_subtype_refl_inst E L {rt} (ty : type rt) r :
    Subtype E L r r ty ty := λ T, i2p (weak_subtype_id E L ty r T).

  Lemma weak_subtype_evar1 E L {rt} (ty : type rt) r r2 T :
    ⌜r = r2⌝ ∗ T ⊢ weak_subtype E L r r2 ty ty T.
  Proof.
    iIntros "(<- & $)" (??) "?? $". iApply type_incl_refl.
  Qed.
  (* We want this to work even if [r2] has shape e.g. [Z.of_nat ?evar], so we do not actually require this to be an evar.
      Instead, we have a super low priority so that more specific instances will get picked first. *)
  Global Instance weak_subtype_evar1_inst E L {rt} (ty : type rt) r r2 :
    Subtype E L r r2 ty ty | 200 := λ T, i2p (weak_subtype_evar1 E L ty r r2 T).

  Lemma weak_subtype_evar2 E L {rt} (ty ty2 : type rt) r r2 T :
    ⌜ty = ty2⌝ ∗ weak_subtype E L r r2 ty ty T ⊢ weak_subtype E L r r2 ty ty2 T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subtype_evar2_inst E L {rt} (ty : type rt) r r2 `{!IsProtected ty2} :
    Subtype E L r r2 ty ty2 | 100 := λ T, i2p (weak_subtype_evar2 E L ty ty2 r r2 T).

  (** ** Subtyping instances: [mut_subtype] *)
  Lemma mut_subtype_id E L {rt} (ty : type rt) T :
    T ⊢ mut_subtype E L ty ty T.
  Proof.
    iIntros "$". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_subtype_refl_inst E L {rt} (ty : type rt) :
    MutSubtype E L ty ty := λ T, i2p (mut_subtype_id E L ty T).

  Lemma mut_subtype_evar E L {rt} (ty ty2 : type rt) T :
    ⌜ty = ty2⌝ ∗ T ⊢ mut_subtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Global Instance mut_subtype_evar_inst E L {rt} (ty : type rt) `{!IsProtected ty2} :
    MutSubtype E L ty ty2 | 100 := λ T, i2p (mut_subtype_evar E L ty ty2 T).

  (** ** Subtyping instances: [mut_eqtype] *)
  Lemma mut_eqtype_id E L {rt} (ty : type rt) T :
    T ⊢ mut_eqtype E L ty ty T.
  Proof.
    iIntros "$". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_eqtype_refl_inst E L {rt} (ty : type rt) :
    MutEqtype E L ty ty := λ T, i2p (mut_eqtype_id E L ty T).

  Lemma mut_eqtype_evar E L {rt} (ty ty2 : type rt) T :
    ⌜ty = ty2⌝ ∗ T ⊢ mut_eqtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Global Instance mut_eqtype_evar_inst E L {rt} (ty : type rt) `{!IsProtected ty2} :
    MutEqtype E L ty ty2 | 100 := λ T, i2p (mut_eqtype_evar E L ty ty2 T).


  (** ** Subtyping instances: [weak_subltype] *)
  (* Instances for [weak_subltype] include:
      - identity
      - folding/unfolding
      - structural lifting
      - lifetime subtyping; below Uniq, we can only replace by equivalences. Thus, we need to prove subtyping in both directions. We may want to have a dedicated judgment for that.
     We, however, cannot trigger [resolve_ghost], as it needs to open stuff up and thus needs steps.

     The instances, especially for folding/unfolding, should use the structure of the second lt (the target) as guidance for incrementally manipulating the first one.
     After making the heads match, structurally descend.
   *)

  Lemma weak_subltype_id E L {rt} (lt : ltype rt) k r T :
    T ⊢ weak_subltype E L k r r lt lt T.
  Proof. iIntros "$" (??) "_ _ $". iApply ltype_incl_refl. Qed.
  Global Instance weak_subltype_refl_inst E L {rt} (lt : ltype rt) k r : SubLtype E L k r r lt lt | 1 :=
    λ T, i2p (weak_subltype_id E L lt k r T).

  Lemma weak_subltype_evar1 E L {rt} (lt1 : ltype rt) k r1 r2 T :
    ⌜r1 = r2⌝ ∗ T ⊢ weak_subltype E L k r1 r2 lt1 lt1 T.
  Proof.
    iIntros "(<- & HT)" (??) "#CTX #HE HL". iFrame. iApply ltype_incl_refl.
  Qed.
  (*Global Instance weak_subltype_evar1_inst E L {rt} (lt1 : ltype rt) k r1 r2  :*)
    (*SubLtype E L k r1 r2 (lt1)%I (lt1)%I | 1 :=*)
    (*λ T, i2p (weak_subltype_evar1 E L lt1 k r1 r2 T).*)
  Global Instance weak_subltype_evar1_inst E L {rt} (lt1 : ltype rt) k r1 r2 :
    SubLtype E L k r1 r2 (lt1)%I (lt1)%I | 1000 :=
    λ T, i2p (weak_subltype_evar1 E L lt1 k r1 r2 T).

  Lemma weak_subltype_evar2 E L {rt} (lt1 lt2 : ltype rt) k r1 r2 T :
    ⌜lt1 = lt2⌝ ∗ weak_subltype E L k r1 r2 lt1 lt1 T ⊢ weak_subltype E L k r1 r2 lt1 lt2 T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_evar2_inst E L {rt} (lt1 lt2 : ltype rt) k r1 r2 `{!IsProtected lt2} :
    SubLtype E L k r1 r2 (lt1)%I (lt2)%I | 100 :=
    λ T, i2p (weak_subltype_evar2 E L lt1 lt2 k r1 r2 T).

  (* Escape into the stronger subtyping judgment. Note: should not be used when lt2 is an evar. *)
  Lemma weak_subltype_base E L {rt} (lt1 lt2 : ltype rt) k r1 r2 T :
    ⌜r1 = r2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 lt1 lt2 T.
  Proof.
    iIntros "(<- & %Hsub & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hsub"; first done.
    iFrame. iPoseProof ("Hsub" $! _ _) as "(Ha1 & _)". done.
  Qed.
  Global Instance weak_subltype_base_inst E L {rt} (lt1 lt2 : ltype rt) k r1 r2 :
    SubLtype E L k r1 r2 (lt1)%I (lt2)%I | 200 :=
    λ T, i2p (weak_subltype_base E L lt1 lt2 k r1 r2 T).

  Lemma weak_subltype_ofty_ofty_owned_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) wl r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subtype E L r1 r2' ty1 ty2 T)
    ⊢ weak_subltype E L (Owned wl) (#r1) r2 (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply type_ltype_incl_owned_in.
  Qed.
  Global Instance weak_subltype_ofty_ofty_owned_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) wl r1 r2 : SubLtype E L (Owned wl) #r1 r2 (◁ ty1)%I (◁ ty2)%I | 10 :=
    λ T, i2p (weak_subltype_ofty_ofty_owned_in E L ty1 ty2 wl r1 r2 T).

  Lemma weak_subltype_ofty_ofty_shared_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subtype E L r1 r2' ty1 ty2 T)
    ⊢ weak_subltype E L (Shared κ) (#r1) (r2) (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply type_ltype_incl_shared_in.
  Qed.
  Global Instance weak_subltype_ofty_ofty_shared_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ r1 r2 : SubLtype E L (Shared κ) #r1 r2 (◁ ty1)%I (◁ ty2)%I | 10 :=
    λ T, i2p (weak_subltype_ofty_ofty_shared_in E L ty1 ty2 κ r1 r2 T).

  (* Note: no similar rule for Uniq -- we can just get strong subtyping through the base lemmas *)

  (** ** Subtyping instances: [mut_eqltype] *)
  Lemma mut_eqltype_id E L {rt} (lt : ltype rt) T :
    T ⊢ mut_eqltype E L lt lt T.
  Proof. iIntros "$". iPureIntro. reflexivity. Qed.
  Global Instance mut_eqltype_refl_inst E L {rt} (lt : ltype rt) : MutEqLtype E L lt lt | 1 :=
    λ T, i2p (mut_eqltype_id E L lt T).

  Lemma mut_eqltype_base_evar E L {rt} (lt1 lt2 : ltype rt) T :
    ⌜lt1 = lt2⌝ ∗ T
    ⊢ mut_eqltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_eqltype_base_evar_inst E L {rt} (lt1 lt2 : ltype rt) `{!IsProtected lt2} :
    MutEqLtype E L (lt1)%I (lt2)%I | 100 := λ T, i2p (mut_eqltype_base_evar E L lt1 lt2 T).

  Lemma mut_eqltype_ofty E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) T :
    mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqltype E L (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%Heqt & $)".
    iPureIntro. eapply full_eqtype_eqltype; done.
  Qed.
  Global Instance mut_eqltype_ofty_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) :
    MutEqLtype E L (◁ ty1)%I (◁ ty2)%I | 5 := λ T, i2p (mut_eqltype_ofty E L ty1 ty2 T).

  (** ** Subtyping instances: [mut_subltype] *)
  Lemma mut_subltype_id E L {rt} (lt : ltype rt) T :
    T ⊢ mut_subltype E L lt lt T.
  Proof. iIntros "$". iPureIntro. reflexivity. Qed.
  Global Instance mut_subltype_refl_inst E L {rt} (lt : ltype rt) : MutSubLtype E L lt lt | 1 :=
    λ T, i2p (mut_subltype_id E L lt T).

  Lemma mut_subltype_base_evar E L {rt} (lt1 lt2 : ltype rt) T :
    ⌜lt1 = lt2⌝ ∗ T
    ⊢ mut_subltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_subltype_base_evar_inst E L {rt} (lt1 lt2 : ltype rt) `{!IsProtected lt2} :
    MutSubLtype E L (lt1)%I (lt2)%I | 100 := λ T, i2p (mut_subltype_base_evar E L lt1 lt2 T).

  (** ** Subtyping instances: [owned_subltype_step] *)

  (** ** casts *)
  Lemma cast_ltype_to_type_id E L {rt} (ty : type rt) T :
    T ty ⊢ cast_ltype_to_type E L (◁ ty) T.
  Proof.
    iIntros "HT". iExists ty. iFrame "HT". done.
  Qed.
  Global Instance cast_ltype_to_type_id_inst E L {rt} (ty : type rt) :
    CastLtypeToType E L (◁ ty)%I :=
    λ T, i2p (cast_ltype_to_type_id E L ty T).


  (** ** prove_place_cond *)
  Lemma prove_place_cond_ofty_refl E L bmin {rt} (ty : type rt) T :
    T (ResultWeak eq_refl) ⊢ prove_place_cond E L bmin (◁ ty) (◁ ty) T.
  Proof.
    iIntros "HT" (F ?) "#CTX HE $". iExists (ResultWeak eq_refl). iFrame.
    iApply typed_place_cond_ty_refl_ofty.
  Qed.
  (* high-priority instance for reflexivity *)
  Global Instance prove_place_cond_ofty_refl_inst E L bmin {rt} (ty : type rt) :
    ProvePlaceCond E L bmin (◁ ty)%I (◁ ty)%I | 2 := λ T, i2p (prove_place_cond_ofty_refl E L bmin ty T).

  Lemma prove_place_cond_trivial E L bmin {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) T :
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ T ResultStrong ⊢ prove_place_cond E L bmin lt1 lt2 T.
  Proof.
    iIntros "(Hst & HT)" (F ?) "#CTX HE $".
    iExists ResultStrong. by iFrame.
  Qed.
  (* very low-priority instance *)
  Global Instance prove_place_cond_trivial_inst E L bmin {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ProvePlaceCond E L bmin lt1 lt2 | 200 := λ T, i2p (prove_place_cond_trivial E L bmin lt1 lt2 T).

  (** Lemmas to eliminate BlockedLtype on either side *)
  Lemma prove_place_cond_blocked_r_Uniq E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ κ' γ  T :
    ⌜lctx_lft_incl E L κ' κ⌝ ∗ prove_place_cond E L (Uniq κ γ) lt (◁ ty) T ⊢
    prove_place_cond E L (Uniq κ γ) lt (BlockedLtype ty κ') T.
  Proof.
    iIntros "(%Hincl & HT)".
    iIntros (F ?) "#CTX HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl"; first done.
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & Hcond & HT)".
    iExists upd. iFrame.
    destruct upd.
    - subst rt2. simpl. iDestruct "Hcond" as "(%Heq & Heq & Hub)".
      rewrite (UIP_refl _ _ Heq).
      iExists eq_refl. cbn. simp_ltypes.
      iSplitL "Heq"; first done.
      iApply imp_unblockable_shorten'; first done.
      iApply blocked_imp_unblockable.
    - simp_ltypes. done.
  Qed.
  Global Instance prove_place_cond_blocked_r_Uniq_inst E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ κ' γ :
    ProvePlaceCond E L (Uniq κ γ) lt (BlockedLtype ty κ') | 5 := λ T, i2p (prove_place_cond_blocked_r_Uniq E L ty lt κ κ' γ T).

  Lemma prove_place_cond_blocked_r_Owned E L {rt rt2} (lt : ltype rt2) (ty : type rt) κ' wl T :
    prove_place_cond E L (Owned wl) lt (BlockedLtype ty κ') T ⊢
    prove_place_cond E L (Owned wl) lt (BlockedLtype ty κ') T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & Hcond & HT)".
    iExists upd. by iFrame.
  Qed.
  Global Instance prove_place_cond_blocked_r_Owned_inst E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ' wl :
    ProvePlaceCond E L (Owned wl) lt (BlockedLtype ty κ') | 5 := λ T, i2p (prove_place_cond_blocked_r_Owned E L lt ty κ' wl T).
  (* no shared lemma *)

  Lemma prove_place_cond_blocked_l_Uniq E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ κ' γ  T :
    prove_place_cond E L (Uniq κ γ) (◁ ty)%I lt T ⊢
    prove_place_cond E L (Uniq κ γ) (BlockedLtype ty κ') lt T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & Hcond & T))".
    iExists _. iModIntro. iFrame.
    simpl. destruct upd as [ Heq0 | ].
    - iDestruct "Hcond" as "(%Heq & #Heq & #Hub)"; subst rt2.
      rewrite (UIP_refl _ _ Heq).
      iExists eq_refl. cbn. simp_ltypes.
      iSplitL; done.
    - by iFrame.
  Qed.
  Global Instance prove_place_cond_blocked_l_Uniq_inst E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ κ' γ :
    ProvePlaceCond E L (Uniq κ γ) (BlockedLtype ty κ') lt | 5 := λ T, i2p (prove_place_cond_blocked_l_Uniq E L ty lt κ κ' γ T).

  Lemma prove_place_cond_blocked_l_Owned E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ' wl T :
    prove_place_cond E L (Owned wl) (◁ ty)%I lt T ⊢
    prove_place_cond E L (Owned wl) (BlockedLtype ty κ') lt T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & Hcond & T))".
    iExists upd. iFrame. done.
  Qed.
  Global Instance prove_place_cond_blocked_l_Owned_inst E L {rt rt2} (ty : type rt) (lt : ltype rt2) κ' wl :
    ProvePlaceCond E L (Owned wl) (BlockedLtype ty κ') lt | 5 := λ T, i2p (prove_place_cond_blocked_l_Owned E L ty lt κ' wl T).

  Lemma prove_place_cond_coreable_r_Owned E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs wl T :
    prove_place_cond E L (Owned wl) lt1 lt2 T ⊢
    prove_place_cond E L (Owned wl) lt1 (CoreableLtype κs lt2) T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & Hcond & HT)".
    iExists upd. by iFrame.
  Qed.
  Global Instance prove_place_cond_coreable_r_Owned_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs wl :
    ProvePlaceCond E L (Owned wl) lt1 (CoreableLtype κs lt2) | 5 := λ T, i2p (prove_place_cond_coreable_r_Owned E L lt1 lt2 κs wl T).
  (* κ needs to outlive all the κ' ∈ κs *)
  Lemma prove_place_cond_coreable_r_Uniq E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs κ γ T :
    ([∗ list] κ' ∈ κs, ⌜lctx_lft_incl E L κ' κ⌝) ∗ prove_place_cond E L (Uniq κ γ) lt1 lt2 T
    ⊢ prove_place_cond E L (Uniq κ γ) lt1 (CoreableLtype κs lt2) T.
  Proof.
    iIntros "(#Hal & HT)". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hcond & HT)".
    iPoseProof (big_sepL_lft_incl_incl with "HE HL Hal") as "#Hincl".
    iFrame "HL". iExists upd. iFrame.
    destruct upd.
    - simpl; subst rt2. iDestruct "Hcond" as "(%Heq & Heq & Hub)".
      rewrite (UIP_refl _ _ Heq). iExists eq_refl. cbn.
      simp_ltypes. iSplitL "Heq"; first done.
      iApply imp_unblockable_shorten; last iApply coreable_ltype_imp_unblockable.
      iModIntro. iIntros "(#Hdead & _)". iApply big_sepL_fupd.
      iApply big_sepL_intro. iIntros "!>" (? κ' Hlook).
      iPoseProof (big_sepL_lookup with "Hincl") as "#Hincl0"; first done.
      by iApply (lft_incl_dead with "Hincl0 Hdead").
    - simp_ltypes. done.
  Qed.
  Global Instance prove_place_cond_coreable_r_Uniq_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs κ γ :
    ProvePlaceCond E L (Uniq κ γ) lt1 (CoreableLtype κs lt2) | 5 := λ T, i2p (prove_place_cond_coreable_r_Uniq E L lt1 lt2 κs κ γ T).

  Lemma prove_place_cond_coreable_l_Owned E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs wl T :
    prove_place_cond E L (Owned wl) lt1 lt2 T
    ⊢ prove_place_cond E L (Owned wl) (CoreableLtype κs lt1) lt2 T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & Hcond & HT)".
    iExists upd. by iFrame.
  Qed.
  Global Instance prove_place_cond_coreable_l_Owned_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs wl :
    ProvePlaceCond E L (Owned wl) (CoreableLtype κs lt1) lt2 | 5 := λ T, i2p (prove_place_cond_coreable_l_Owned E L lt1 lt2 κs wl T).

  Lemma prove_place_cond_coreable_l_Uniq E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs κ γ T :
    prove_place_cond E L (Uniq κ γ) lt1 lt2 T
    ⊢ prove_place_cond E L (Uniq κ γ) (CoreableLtype κs lt1) lt2 T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hcond & HT)".
    iFrame. iExists upd. iFrame.
    destruct upd.
    - subst rt2. iDestruct "Hcond" as "(%Heq & Heq & Hub)".
      rewrite (UIP_refl _ _ Heq).
      iExists eq_refl. cbn. simp_ltypes. by iFrame.
    - simp_ltypes. done.
  Qed.
  Global Instance prove_place_cond_coreable_l_Uniq_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs κ γ :
    ProvePlaceCond E L (Uniq κ γ) (CoreableLtype κs lt1) lt2 | 5 := λ T, i2p (prove_place_cond_coreable_l_Uniq E L lt1 lt2 κs κ γ T).

  (* NOTE: unfolding lemmas should have lower priority than the primitive ones. *)

  (** find obs *)
  Import EqNotations.
  Lemma find_observation_direct (rt : Type) γ (T : find_observation_cont_t rt) :
    find_in_context (FindOptGvarPobs γ) (λ res,
      match res with
      | inr _ => find_observation rt γ FindObsModeRel T
      | inl (existT rt' r) => ∃ (Heq : rt' = rt), T (Some (rew Heq in r))
      end)%I
    ⊢ find_observation rt γ FindObsModeDirect T.
  Proof.
    iDestruct 1 as ([[rt' r] | ]) "(Hobs & HT)"; simpl.
    - iDestruct "HT" as (->) "HT". iIntros (??). iModIntro.
      iLeft. eauto with iFrame.
    - iIntros (??). by iApply "HT".
  Qed.
  Global Instance find_observation_direct_inst (rt : Type) γ :
    FindObservation rt γ FindObsModeDirect := λ T, i2p (find_observation_direct rt γ T).

  Lemma find_observation_rel (rt : Type) γ (T : find_observation_cont_t rt) :
    find_in_context (FindOptGvarRel γ) (λ res,
      match res with
      | inr _ => T None
      | inl (existT rt' (γ', R)) => ∃ (Heq : rt' = rt),
          find_observation rt' γ' FindObsModeDirect (λ or,
            match or with
            | None => False
            | Some r => ∀ r', ⌜R r r'⌝ -∗ T (Some $ rew Heq in r')
            end)
      end)%I
    ⊢ find_observation rt γ FindObsModeRel T.
  Proof.
    iDestruct 1 as ([[rt' [γ' R]] | ]) "(Hobs & HT)"; simpl.
    - iDestruct "HT" as (->) "HT".
      iIntros (??). iMod ("HT" with "[//]") as "HT".
      iDestruct "HT" as "[(%r & Hobs' & HT) | []]".
      iPoseProof (Rel2_use_pobs with "Hobs' Hobs") as "(%r2 & Hobs & %HR)".
      iSpecialize ("HT" with "[//]").
      iMod (gvar_obs_persist with "Hobs") as "Hobs".
      iModIntro. iLeft. eauto with iFrame.
    - iIntros (??). iRight. done.
  Qed.
  Global Instance find_observation_rel_inst (rt : Type) γ :
    FindObservation rt γ FindObsModeRel := λ T, i2p (find_observation_rel rt γ T).

  (** ** resolve_ghost *)
  (* One note: these instances do not descend recursively -- that is the task of the stratify_ltype call that is triggering the resolution. resolve_ghost instances should always resolve at top-level, or at the level of atoms of stratify_ltype's traversal (in case of user-defined types) *)
  Import EqNotations.

  (* a trivial low-priority instance, in case no other instance triggers.
    In particular, we should also make sure that custom instances for user-defined types get priority. *)
  Lemma resolve_ghost_id {rt} π E L l (lt : ltype rt) rm lb k r (T : llctx → place_rfn rt → iProp Σ → bool → iProp Σ) :
    match rm, r with
    | ResolveTry, PlaceIn _ => T L r True true
    | ResolveTry, PlaceGhost _ => T L r True false
    | ResolveAll, PlaceIn _ => T L r True true
    | ResolveAll, PlaceGhost _ => False
    end
    ⊢ resolve_ghost π E L rm lb l lt k r T.
  Proof.
    iIntros "HT" (F ??) "#CTX #HE HL Hl".
    destruct rm.
    - destruct r; last done.
      iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. by iFrame.
    - destruct r.
      + iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
      + iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_id_inst {rt} π E L l (lt : ltype rt) rm lb k r :
    ResolveGhost π E L rm lb l lt k r | 200 := λ T, i2p (resolve_ghost_id π E L l lt rm lb k r T).

  Lemma resolve_ghost_ofty_Owned {rt} π E L l (ty : type rt) γ rm lb wl T :
    find_observation rt γ FindObsModeDirect (λ or,
      match or with
      | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
      | Some r => T L (PlaceIn $ r) True true
      end)
    ⊢ resolve_ghost π E L rm lb l (◁ ty)%I (Owned wl) (PlaceGhost γ) T.
  Proof.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hl".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & ? & %r' & Hrfn & Hb)".
      iPoseProof (gvar_pobs_agree_2 with "Hrfn Hobs") as "->".
      iModIntro. iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. simpl. iSplitL; last done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own. eauto with iFrame.
    - iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance resolve_ghost_ofty_owned_inst {rt} π E L l (ty : type rt) γ wl rm lb :
    ResolveGhost π E L rm lb l (◁ ty)%I (Owned wl) (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_ofty_Owned π E L l ty γ rm lb wl T).

  Lemma resolve_ghost_ofty_Uniq {rt} π E L l (ty : type rt) γ rm lb κ γ' T :
    find_observation rt γ FindObsModeDirect (λ or,
      match or with
      | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
      | Some r => T L (PlaceIn $ r) True true
      end)
    ⊢ resolve_ghost π E L rm lb l (◁ ty)%I (Uniq κ γ') (PlaceGhost γ) T.
  Proof.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hl".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & ? & Hrfn & Hb)".
      iDestruct "Hrfn" as "(%v1 & %v2 & Hauth & Hobs' & %HR)".
      iPoseProof (gvar_pobs_agree_2 with "Hauth Hobs") as "->".
      simpl. subst.
      iModIntro. iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. iSplitL; last done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own. eauto with iFrame.
    - iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance resolve_ghost_ofty_uniq_inst {rt} π E L l (ty : type rt) γ κ γ' rm lb :
    ResolveGhost π E L rm lb l (◁ ty)%I (Uniq κ γ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_ofty_Uniq π E L l ty γ rm lb κ γ' T).


  (** ** Extraction *)
  (* We register a few post-hooks for actually extracting stuff. *)
  Lemma stratify_ltype_extract_mutltype π E L {rt} (lt : ltype rt) r κ γ l (wl : bool) (T : stratify_ltype_post_hook_cont_t) :
    match ltype_uniq_extractable lt with
    | None =>
        T L True%I _ (MutLtype lt κ) (#(r, γ))
    | Some κm =>
        prove_with_subtype E L false ProveDirect (£ (Nat.b2n wl)) (λ L' κs R,
          (R -∗ T L' (MaybeInherit κm InheritGhost (place_rfn_interp_mut_extracted r γ)) _ (◁ uninit PtrSynType)%I (#())))
    end
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (MutLtype lt κ) (#(r, γ)) (Owned wl) T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL Hl".
    destruct (ltype_uniq_extractable lt) as [ κm | ] eqn:Hextract; first last.
    { iExists L, True%I, _, _, _. iFrame. done. }
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & %κs & %R & >(Hcred & HR)& HL & HT)".
    iMod (ltype_uniq_extractable_deinit_mut' with "Hcred Hl") as "(Hl & Hrfn)"; [done.. | | ].
    { left. done. }
    iSpecialize ("HT" with "HR").
    iPoseProof (MaybeInherit_update (place_rfn_interp_mut_extracted r γ) with "[] Hrfn") as "Ha".
    { iIntros (?) "Ha". iMod (place_rfn_interp_mut_extract with "Ha") as "?". done. }
    iExists _, _, _, _, _. iFrame.
    iFrame. simp_ltypes. done.
  Qed.
  Global Instance stratify_ltype_extract_mutltype_inst π E L {rt} (lt : ltype rt) r κ γ l (wl : bool) :
    StratifyLtypePostHook π E L (StratifyExtractOp κ) l (MutLtype lt κ) (#(r, γ)) (Owned wl) :=
    λ T, i2p (stratify_ltype_extract_mutltype π E L lt r κ γ l wl T).

  Lemma stratify_ltype_extract_shrltype π E L {rt} (lt : ltype rt) r κ l (wl : bool) (T : stratify_ltype_post_hook_cont_t) :
    prove_with_subtype E L false ProveDirect (£ (Nat.b2n wl)) (λ L' κs R, (R -∗ T L' (True) _ (◁ uninit PtrSynType)%I (#())))
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (ShrLtype lt κ) r (Owned wl) T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L' & %κs & %R & >(Hcred & HR)& HL & HT)".
    iMod (ltype_deinit_shr' with "Hcred Hl") as "Hl"; [done.. | | ].
    { left. done. }
    iSpecialize ("HT" with "HR").
    iExists _, _, _, _, _. iFrame.
    iFrame. simp_ltypes. done.
  Qed.
  Global Instance stratify_ltype_extract_shrltype_inst π E L {rt} (lt : ltype rt) r κ l (wl : bool) :
    StratifyLtypePostHook π E L (StratifyExtractOp κ) l (ShrLtype lt κ) r (Owned wl) :=
    λ T, i2p (stratify_ltype_extract_shrltype π E L lt r κ l wl T).


  (** ** ltype stratification *)
  (* TODO change the ResolveTry and also make it a parameter of stratify *)

  (* when we recursively want to descend, we cannot let the resolution use the logical step *)
  Lemma stratify_ltype_resolve_ghost_rec {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) b r T :
    resolve_ghost π E L ResolveTry false l lt b r (λ L1 r R progress,
      if progress then
      stratify_ltype π E L1 mu mdu ma ml l lt r b
        (λ L2 R' rt' lt' r', T L2 (R ∗ R') rt' lt' r')
      else
        (* otherwise treat this as a leaf *)
        R -∗ stratify_ltype_post_hook π E L1 ml l lt r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "Hres". iIntros (???) "#CTX #HE HL Hl".
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & >(Hl & HR) & HL & HP)"; [done.. | ].
    destruct prog.
    - iPoseProof ("HP" with "[//] [//] CTX HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & Hcond & Hb & HT)".
      iModIntro. iExists L2, _, rt', lt', r'. iFrame "Hcond HT HL".
      iApply (logical_step_wand with "Hb"). iIntros "($ & $)". done.
    - by iApply (stratify_ltype_id _ _ _ mu mdu ma with "(HP HR) [//] [//] CTX HE HL").
  Qed.
  (* at a leaf, we can use the logical step to do the resolution -- this allows to descend deeper into the type, which is useful for custom user-defined types *)
  Lemma stratify_ltype_resolve_ghost_leaf {rt} π E L mu mdu ma {M} (ml : M) rm l (lt : ltype rt) b r T :
    resolve_ghost π E L rm true l lt b r (λ L1 r R progress, T L1 R _ lt r)
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "Hres". iIntros (???) "#CTX #HE HL Hl".
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & Hl & HL & HR)"; [done.. | ].
    simpl. iModIntro. iExists L1, _, _, lt, r1.
    iFrame. done.
  Qed.

  (* This should have a lower priority than the leaf instances we call for individual [ml] -- those should instead use [stratify_ltype_resolve_ghost_leaf]. *)
  Global Instance stratify_ltype_resolve_ghost_inst {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) b γ :
    StratifyLtype π E L mu mdu ma ml l lt (PlaceGhost γ) b | 100 := λ T, i2p (stratify_ltype_resolve_ghost_rec π E L mu mdu ma ml l lt b (PlaceGhost γ) T).

  Lemma stratify_ltype_blocked {rt} π E L mu mdu ma {M} (ml : M) l (ty : type rt) κ r b T :
    find_in_context (FindOptLftDead κ) (λ found,
      if found then stratify_ltype π E L mu mdu ma ml l (◁ ty)%I r b T
      else stratify_ltype_post_hook π E L ml l (BlockedLtype ty κ) r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l (BlockedLtype ty κ) r b T.
  Proof.
    rewrite /FindOptLftDead.
    iIntros "(%found & Hdead & Hp)". destruct found.
    - iIntros (???) "#(LFT & TIME & LLCTX) #HE HL Hl".
      iMod (unblock_blocked with "Hdead Hl") as "Hl"; first done.
      iPoseProof ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L' & %R & %rt' & %lt' & %r' & Hl & Hstep & HT)".
      iModIntro. iExists L', R, rt', lt', r'. by iFrame.
    - by iApply stratify_ltype_id.
  Qed.
  (* No instance here, as we may not always want to do that. *)

  (* TODO: also make this one optional *)
  Lemma stratify_ltype_coreable {rt} π E L mu mdu ma {M} (ml : M) l (lt_full : ltype rt) κs r b T :
    lft_dead_list κs ∗ stratify_ltype π E L mu mdu ma ml l (ltype_core lt_full) r b T
    ⊢ stratify_ltype π E L mu mdu ma ml l (CoreableLtype κs lt_full) r b T.
  Proof.
    iIntros "(#Hdead & Hstrat)".
    iIntros (F ??) "#CTX #HE HL Hl".
    iMod (unblock_coreable with "Hdead Hl") as "Hl"; first done.
    iMod ("Hstrat" with "[//] [//] CTX HE HL Hl") as "Ha".
    iDestruct "Ha" as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _. iFrame.
    iPureIntro. rewrite -Hst ltype_core_syn_type_eq. by simp_ltypes.
  Qed.
  (* No instance here, as we may not always want to do that. *)

  Lemma stratify_ltype_shrblocked {rt} π E L mu mdu ma {M} (ml : M) l (ty : type rt) κ r b T :
    find_in_context (FindOptLftDead κ) (λ found,
      if found then stratify_ltype π E L mu mdu ma ml l (◁ ty)%I r b T
      else stratify_ltype_post_hook π E L ml l (ShrBlockedLtype ty κ) r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShrBlockedLtype ty κ) r b T.
  Proof.
    rewrite /FindOptLftDead.
    iIntros "(%found & Hdead & Hstrat)". destruct found.
    - iIntros (F ??) "#CTX #HE HL Hl".
      iMod (unblock_shrblocked with "Hdead Hl") as "Hl"; first done.
      iMod ("Hstrat" with "[//] [//] CTX HE HL Hl") as "Ha".
      iDestruct "Ha" as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
      iModIntro. iExists _, _, _, _, _. iFrame.
      iPureIntro. done.
    - by iApply stratify_ltype_id.
  Qed.
  (* No instance here, as we may not always want to do that. *)

  (* NOTE: we make the assumption that, even for fully-owned places, we want to keep the invariant structure, and not just unfold it completely and forget about the invariants. This is why we keep it open when the refinement type is different, even though we could in principle also close it to any lt_cur'.

    Is there a better criterion for this than the refinement type?
    - currently, prove_place_cond requires the refinement type to be the same, even for Owned.
    - for some of the subtyping we may want to allow the subtyping to actually be heterogeneous.

    Points in the design space:
    - [aggressive] just fold every time we can, by always proving a subtyping.
    - [aggressive unless Owned] fold every time as long as the place cond is provable.
        + in particular: fold if we can get back a lifetime token.
    - [relaxed]
    -

    Some thoughts on stuff that would be good:
    - make stratification more syntax-guided, i.e. have a "goal" ltype?
      + this would make the behavior when we moved stuff out beforehand much more predictable, eg. for value_t: don't just have a general rule for stratifying value every time, but only when we actually want to have something there.


  *)
  Lemma stratify_ltype_opened_Owned {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r wl (T : stratify_ltype_cont_t) :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned false) (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost) r'
        else
          (* fold the invariant *)
          ∃ ri,
            (* show that the core of lt_cur' is a subtype of lt_inner and then fold to lt_full *)
            weak_subltype E L' (Owned false) (r') (#ri) (ltype_core lt_cur') lt_inner (
              (* re-establish the invariant *)
              ∃ rf, prove_with_subtype E L' true ProveWithStratify (Cpre ri rf) (λ L'' κs R2,
              (* either fold to coreable, or to the core of lt_full *)
              match ltype_blocked_lfts lt_cur', κs with
              | [], [] =>
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (ltype_core lt_full) (#rf))
              | κs', _ =>
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs' ++ κs) lt_full) (#rf))
              end)))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Owned wl) T.
  Proof.
    iIntros "Hstrat". iIntros (F ??) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst1 & %Hst2 & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst & Hstep & HT)".
    destruct (decide (ma = StratNoRefold)) as [-> | ].
    - (* don't fold *)
      iModIntro.
      iExists _, _, _, _, _. iFrame.
      iSplitR. { iPureIntro. simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. iFrame.
      rewrite -Hst.
      iSplitR. { done. }
      iSplitR; first done. iSplitR; first done.
      iSplitR; first done. done.
    - (* fold it again *)
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & %rf & HT)".
      iMod ("HT" with "[//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".
      iPoseProof (imp_unblockable_blocked_dead lt_cur') as "(_ & #Hb)".
      set (κs' := ltype_blocked_lfts lt_cur').
      destruct (decide (κs = [] ∧ κs' = [])) as [[-> ->] | ].
      + iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. rewrite ltype_core_syn_type_eq. rewrite -Hst2 -Hst1 //. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        iPoseProof ("Hb" with "[] Hl") as "Hl". { by iApply big_sepL_nil. }
        iMod (fupd_mask_mono with "Hl") as "Hl"; first done.
        rewrite ltype_own_core_equiv.
        iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
        simpl.
        iPoseProof ("Hcl" with "Hpre") as "(Hpost & Hvs')".
        iMod (fupd_mask_mono with "(Hvs' [] Hl)") as "Ha"; first done.
        { by iApply lft_dead_list_nil. }
        rewrite ltype_own_core_equiv. by iFrame.
      + iAssert (T L3 (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs' ++ κs) lt_full) #rf)%I with "[HT]" as "HT".
        { destruct κs, κs'; naive_solver. }
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro.
          simp_ltypes. rewrite -Hst2 -Hst1. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iPoseProof ("Hcl" with "Hpre") as "($ & Hvs')".
        iModIntro.
        iExists ly.
        iSplitR. { rewrite -Hst2 -Hst1. done. }
        iSplitR; first done. iSplitR; first done.
        iIntros "Hdead".
        rewrite lft_dead_list_app. iDestruct "Hdead" as "(Hdead' & Hdead)".
        (* unblock lt_cur' *)
        iPoseProof (imp_unblockable_blocked_dead lt_cur') as "(_ & #Hub)".
        iMod ("Hub" with "Hdead' Hl") as "Hl".
        (* shift to lt_inner *)
        rewrite !ltype_own_core_equiv.
        iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
        (* shift to the core of lt_full *)
        iMod ("Hvs'" with "Hdead Hl") as "Hl".
        eauto.
  Qed.
  Global Instance stratify_ltype_opened_owned_inst {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r wl:
    StratifyLtype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Owned wl) := λ T, i2p (stratify_ltype_opened_Owned π E L mu mdu ma ml l lt_cur lt_inner lt_full Cpre Cpost r wl T).

  (* NOTE what happens with the inclusion sidecondition for the κs when we shorten the outer reference?
     - we should not shorten after unfolding (that also likely doesn't work with OpenedLtype -- we cannot arbitrarily modify the lt_inner/lt_full)
     - if we are borrowing at a lifetime which doesn't satisfy this at the borrow time, that is a bug, as we are violating the contract of the outer reference.
     So: this sidecondition does not restrict us in any way. *)
  Lemma stratify_ltype_opened_Uniq {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r κ γ T :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned false) (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost) r'
        else
          (* fold the invariant *)
          ∃ ri,
            (* show that lt_cur' is a subtype of lt_inner and then fold to lt_full *)
            weak_subltype E L' (Owned false) (r') (#ri) (lt_cur') lt_inner (
              (* re-establish the invariant *)
              ∃ rf,
              prove_with_subtype E L' true ProveWithStratify (Cpre ri rf) (λ L'' κs R2,
              (* either fold to coreable, or to the core of lt_full *)
              match κs, ltype_blocked_lfts lt_cur' with
              | [], [] =>
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (ltype_core lt_full) (#rf))
              | _, κs' =>
                    (* inclusion sidecondition: require that all the blocked stuff ends before κ *)
                    ([∗ list] κ' ∈ κs ++ κs', ⌜lctx_lft_incl E L'' κ' κ⌝) ∗
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs ++ κs') lt_full) (#rf))
              end)))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Uniq κ γ) T.
  Proof.
    iIntros "Hstrat". iIntros (F ??) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst1 & %Hst2 & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst & Hstep & HT)".
    destruct (decide (ma = StratNoRefold)).
    - (* don't fold *)
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR. { iPureIntro. simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. iFrame.
      rewrite -Hst.
      iSplitR. { done. }
      iSplitR; first done. iSplitR; first done.
      iSplitR; first done. done.
    - (* fold it again *)
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & %rf & HT)".
      iMod ("HT" with "[//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".
      iPoseProof (imp_unblockable_blocked_dead lt_cur') as "#(_ & Hub)".
      set (κs' := ltype_blocked_lfts lt_cur').
      destruct (decide (κs = [] ∧ κs' = [])) as [[-> ->] | ].
      + iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. rewrite ltype_core_syn_type_eq. rewrite -Hst2 -Hst1 //. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        (* instantiate own_lt_cur' with ownership of lt_cur' *)
        iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
        iMod ("Hcl" $! (λ π _ l, l ◁ₗ[π, Owned false] r' @ lt_cur')%I [] with "Hpre [] Hl []") as "Ha".
        { by iApply big_sepL_nil. }
        { iModIntro. iIntros "_ Hb".
          iMod ("Hub" with "[] Hb") as "Hb". { iApply big_sepL_nil. done. }
          rewrite !ltype_own_core_equiv.
          iApply (ltype_incl_use_core with "Hincl Hb"); first done. }
        iDestruct "Ha" as "($ & Hobs & Hcl)".
        iMod ("Hcl" with "[] Hobs") as "Hl".
        { iApply big_sepL_nil. done. }
        iMod "Hcl_F" as "_". rewrite ltype_own_core_equiv. done.
      + iAssert (([∗ list] κ' ∈ κs ++ κs', ⌜lctx_lft_incl E L3 κ' κ⌝) ∗ T L3 (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs ++ κs') lt_full) (PlaceIn rf))%I with "[HT]" as "HT".
        { destruct κs, κs'; naive_solver. }
        iDestruct "HT" as "(#Hincl1 & HT)".
        iPoseProof (big_sepL_lft_incl_incl with "HE HL Hincl1") as "#Hincl2".
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. simp_ltypes. rewrite -Hst2 -Hst1. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
        iMod ("Hcl" $! (λ π _ l, l ◁ₗ[π, Owned false] r' @ lt_cur')%I (κs ++ κs') with "[Hpre] [] Hl []") as "Ha".
        { rewrite lft_dead_list_app. iIntros "(Hdead & _)". by iApply "Hpre". }
        { done. }
        { iModIntro. iIntros "#Hdead Hb".
          rewrite lft_dead_list_app. iDestruct "Hdead" as "(_ & Hdead)".
          iMod ("Hub" with "Hdead Hb") as "Hb".
          rewrite !ltype_own_core_equiv.
          iApply (ltype_incl_use_core with "Hincl Hb"); first done. }
        iDestruct "Ha" as "($ & Hobs & Hcl)".
        iMod "Hcl_F" as "_".
        iModIntro. rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iExists ly. rewrite -Hst2 -Hst1. iSplitR; first done.
        iSplitR; first done. iSplitR; first done. iFrame.
  Qed.
  Global Instance stratify_ltype_opened_uniq_inst {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r κ γ :
    StratifyLtype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Uniq κ γ) := λ T, i2p (stratify_ltype_opened_Uniq π E L mu mdu ma ml l lt_cur lt_inner lt_full Cpre Cpost r κ γ T).

  Lemma stratify_ltype_shadowed_shared {rt_cur rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (r_cur : place_rfn rt_cur) r_full κ T :
    stratify_ltype π E L mu mdu ma ml l lt_cur r_cur (Shared κ) (λ L' R rt_cur' lt_cur' (r_cur' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R rt_full (ShadowedLtype lt_cur' r_cur' lt_full) r_full
        else
          (T L' R rt_full (lt_full) (r_full))
      )
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShadowedLtype lt_cur r_cur lt_full) r_full (Shared κ) T.
  Proof.
    iIntros "Hstrat".
    iIntros (???) "#CTX #HE HL Hl".
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own. iDestruct "Hl" as "(%Hst & Hcur & Hfull)".
    iMod ("Hstrat" with "[//] [//] CTX HE HL Hcur") as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hst' & Ha & HT)".
    iModIntro. case_decide.
    - iExists _, _, _, _, _. iFrame. simp_ltypes.
      iR. iApply (logical_step_wand with "Ha").
      iIntros "(Ha & $)". rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
      iSplitR. { rewrite -Hst'//. }
      iFrame.
    - iExists _, _, _, _, _. iFrame. simp_ltypes.
      iR. iApply (logical_step_wand with "Ha").
      iIntros "(Ha & $)". iFrame.
  Qed.
  Global Instance stratify_ltype_shadowed_shared_inst {rt_cur rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (r_cur : place_rfn rt_cur) (r_full : place_rfn rt_full) κ :
    StratifyLtype π E L mu mdu ma ml l (ShadowedLtype lt_cur r_cur lt_full) r_full (Shared κ) := λ T, i2p (stratify_ltype_shadowed_shared π E L mu mdu ma ml l lt_cur lt_full r_cur r_full κ T).


  (* NOTE: instances for descending below MutLty, etc., are in the respective type's files. *)

  (** Unblock stratification: We define instances for the leaves of the unblocking stratifier *)
  (* On an ofty leaf, do a ghost resolution.
    This will also trigger resolve_ghost instances for custom-user defined types.
    This needs to have a lower priority than custom user-defined instances (e.g. for [◁ value_t]), so we give it a high cost. *)
  Global Instance stratify_ltype_unblock_ofty_in_inst {rt} π E L mu mdu ma l (ty : type rt) (r : place_rfn rt) b :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (◁ ty)%I r b | 100 :=
    λ T, i2p (stratify_ltype_resolve_ghost_leaf π E L mu mdu ma StratifyUnblockOp ResolveAll l (◁ ty)%I b r T).

  (* Note: instance needs to have a higher priority than the resolve_ghost instance -- we should first unblock *)
  Global Instance stratify_ltype_unblock_blocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (BlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_blocked π E L mu mdu ma StratifyUnblockOp l ty κ r b T).
  Global Instance stratify_ltype_unblock_shrblocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (ShrBlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_shrblocked π E L mu mdu ma StratifyUnblockOp l ty κ r b T).
  Global Instance stratify_ltype_unblock_coreable_inst {rt} π E L mu mdu ma l (lt : ltype rt) b r κs :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (CoreableLtype κs lt) r b | 5 := λ T, i2p (stratify_ltype_coreable π E L mu mdu ma StratifyUnblockOp l lt κs r b T).

  (** Extract stratification: we also want to Unblock here *)
  Global Instance stratify_ltype_extract_blocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ κ' :
    StratifyLtype π E L mu mdu ma (StratifyExtractOp κ') l (BlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_blocked π E L mu mdu ma (StratifyExtractOp κ') l ty κ r b T).
  Global Instance stratify_ltype_extract_shrblocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ κ' :
    StratifyLtype π E L mu mdu ma (StratifyExtractOp κ') l (ShrBlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_shrblocked π E L mu mdu ma (StratifyExtractOp κ') l ty κ r b T).
  Global Instance stratify_ltype_extract_coreable_inst {rt} π E L mu mdu ma l (lt : ltype rt) b r κs κ' :
    StratifyLtype π E L mu mdu ma (StratifyExtractOp κ') l (CoreableLtype κs lt) r b | 5 := λ T, i2p (stratify_ltype_coreable π E L mu mdu ma (StratifyExtractOp κ') l lt κs r b T).

  (** ** place typing *)

  (** *** Instances for unblocking & updating refinements *)
  (** Note: all of these instances should have higher priority than the id instances,
        so that the client of [typed_place] does not have to do this.
      TODO: can we find an elegant way to do this for nested things (eliminate a stratify_ltype)?
        e.g. when something below is blocked and we need to unblock it, or we need to update the refinement.
        currently, the client has to do this...
        Problem why we can't directly do it: we need at least one step of computation to do it, and typed_place does not always take a step.
    *)

  (* TODO: some of this is really duplicated with stratify, in particular the unblocking and the ltype unfolding. Could we have an instance that just escapes into a shallow version of stratify that requires no logstep in order avoid duplication? *)

  (* TODO: we probably want to generalize this to not immediately require a dead token for κ,
    but rather have a "dead" context and spawn a sidecondition for inclusion in one of the dead lifetimes? *)
  Lemma typed_place_blocked_unblock {rt} π E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P T :
    ⌜bor_kind_writeable bmin0⌝ ∗ [† κ] ∗ typed_place π E L l (◁ ty) r bmin0 b P T
    ⊢ typed_place π E L l (BlockedLtype ty κ) r bmin0 b P T.
  Proof.
    iIntros "(%Hw & Hdead & Hp)". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hincl0 Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_blocked with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 Hl").
    iIntros (L' κs l2 b2 bmin rti tyli ri strong weak) "Hincl1 Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hl2 [Hs] HT HL").
    iSplit.
    - destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hl & Hcond & HR)".
      iFrame. done.
    - destruct weak as [ weak | ]; last done.
      iIntros (ltyi2 ri2 bmin') "Hincl Hl2 Hcond".
      iMod ("Hs" with "Hincl Hl2 Hcond") as "(Hl & Hcond & Htoks & HR)".
      iFrame. iModIntro.
      iDestruct "Hcond" as "(Ht & Hr)". iSplit.
      + destruct bmin0; [done.. | ].
        unfold typed_place_cond_ty. simp_ltypes. done.
      + done.
  Qed.
  Global Instance typed_place_blocked_unblock_inst {rt} π E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P:
    TypedPlace E L π l (BlockedLtype ty κ) r bmin0 b P | 5 := λ T, i2p (typed_place_blocked_unblock π E L l ty κ r bmin0 b P T).

  Lemma typed_place_shrblocked_unblock {rt} π E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P T :
    ⌜bor_kind_writeable bmin0⌝ ∗ [† κ] ∗ typed_place π E L l (◁ ty) r bmin0 b P T
    ⊢ typed_place π E L l (ShrBlockedLtype ty κ) r bmin0 b P T.
  Proof.
    iIntros "(%Hw & Hdead & Hp)". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hincl0 Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_shrblocked with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 Hl").
    iIntros (L' κs l2 b2 bmin rti tyli ri strong weak) "Hincl1 Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hl2 [Hs] HT HL").
    iSplit.
    - destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hl & Hcond & HR)".
      iFrame. done.
    - destruct weak as [ weak | ]; last done.
      iIntros (ltyi2 ri2 bmin') "Hincl Hl2 Hcond".
      iMod ("Hs" with "Hincl Hl2 Hcond") as "(Hl & Hcond & Htoks & HR)".
      iFrame. iModIntro.
      iDestruct "Hcond" as "(Ht & Hr)". iSplit.
      + destruct bmin0; [done.. | ].
        unfold typed_place_cond_ty. simp_ltypes. done.
      + done.
  Qed.
  Global Instance typed_place_shrblocked_unblock_inst {rt} π E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P:
    TypedPlace E L π l (ShrBlockedLtype ty κ) r bmin0 b P | 5 := λ T, i2p (typed_place_shrblocked_unblock π E L l ty κ r bmin0 b P T).

  Lemma typed_place_coreable_unblock {rt} π E L l (lt : ltype rt) κs (r : place_rfn rt) bmin0 b P T :
    ⌜bor_kind_writeable bmin0⌝ ∗ lft_dead_list κs ∗ typed_place π E L l (ltype_core lt) r bmin0 b P T
    ⊢ typed_place π E L l (CoreableLtype κs lt) r bmin0 b P T.
  Proof.
    iIntros "(%Hw & Hdead & Hp)". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hincl0 Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_coreable with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 Hl").
    iIntros (L' κs' l2 b2 bmin rti tyli ri strong weak) "Hincl1 Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hl2 [Hs] HT HL").
    iSplit.
    - destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hl & Hcond & HR)".
      iFrame. rewrite ltype_st_coreable. rewrite ltype_core_syn_type_eq. done.
    - destruct weak as [ weak | ]; last done.
      iIntros (ltyi2 ri2 bmin') "Hincl Hl2 Hcond".
      iMod ("Hs" with "Hincl Hl2 Hcond") as "(Hl & Hcond & Htoks & HR)".
      iFrame. iModIntro.
      iDestruct "Hcond" as "(Ht & Hr)". iSplit.
      + destruct bmin0; simpl; [simp_ltypes; done | done | ].
        unfold typed_place_cond_ty. simp_ltypes. done.
      + done.
  Qed.
  Global Instance typed_place_coreable_unblock_inst {rt} π E L l (lt : ltype rt) κs r bmin0 b P :
    TypedPlace E L π l (CoreableLtype κs lt) r bmin0 b P | 5 :=
      λ T, i2p (typed_place_coreable_unblock π E L l lt κs r bmin0 b P T).

  Lemma typed_place_resolve_ghost {rt} π E L l (lt : ltype rt) bmin0 b γ P T :
    ⌜lctx_bor_kind_alive E L b⌝ ∗ ⌜bor_kind_writeable bmin0⌝ ∗
    resolve_ghost π E L ResolveAll false l lt b (PlaceGhost γ) (λ L' r R progress,
      introduce_with_hooks E L' R (λ L'', typed_place π E L'' l lt r bmin0 b P T))
    ⊢ typed_place π E L l lt (PlaceGhost γ) bmin0 b P T.
  Proof.
    iIntros "(% & %Hw & Hres)". iIntros (????) "#CTX #HE HL Hincl0 Hl HΦ".
    iApply fupd_place_to_wp.
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L' & %r & %R & %prog & Hstep & HL & HP)"; [done.. | ].
    iMod "Hstep" as "(Hl & HR)".
    iMod ("HP" with "[] HE HL HR") as "(%L'' & HL & HP)"; first done.
    iModIntro. iApply ("HP" with "[//] [//] CTX HE HL Hincl0 Hl").
    iIntros (L1 κs l2 b2 bmin rti tyli ri strong weak) "Hincl1 Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hl2 [Hs] HT HL").
    iSplit.
    - destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hl & Hcond & HR)".
      iFrame. done.
    - destruct weak as [ weak | ]; last done.
      iIntros (ltyi2 ri2 bmin') "Hincl Hl2 Hcond".
      iMod ("Hs" with "Hincl Hl2 Hcond") as "(Hl & Hcond & Htoks & HR)".
      iFrame. iModIntro.
      done.
      (*iDestruct "Hcond" as "(Ht & Hr)". iSplit; first done.*)
      (*destruct bmin0; done.*)
  Qed.
  (* this needs to have a lower priority than place_blocked_unblock *)
  Global Instance typed_place_resolve_ghost_inst {rt} π E L l (lt : ltype rt) bmin0 b γ P :
    TypedPlace E L π l lt (PlaceGhost γ) bmin0 b P | 8 := λ T, i2p (typed_place_resolve_ghost π E L l lt bmin0 b γ P T).

  (** *** Place access instances *)

  Import EqNotations.

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
      ⊢
    typed_place π E L l (◁ ty) (PlaceIn r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
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

  (* instances for Opened *)
  (* NOTE: these should have a higher priority than place id, because we always want to descend below Opened when accessing a place, in order to get the actual current type *)
  Lemma typed_place_opened_owned π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r bmin0 l wl P T :
    typed_place π E L l lt_cur r bmin0 (Owned false) P (λ L' κs l2 b2 bmin rti ltyi ri strong weak,
      T L' κs l2 b2 bmin rti ltyi ri
        (option_map (λ strong, mk_strong strong.(strong_rt)
          (λ rti2 ltyi2 ri2, OpenedLtype (strong.(strong_lt) _ ltyi2 ri2) lt_inner lt_full Cpre Cpost)
          (λ rti2 ri2, strong.(strong_rfn) _ ri2)
          strong.(strong_R)) strong)
        (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
        None)
    ⊢ typed_place π E L l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r bmin0 (Owned wl) P T.
  Proof.
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL #Hincl0 Hl HR".
    iPoseProof (opened_ltype_acc_owned with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL [] Hl").
    { destruct bmin0; done. }
    iIntros (L' ??????? strong weak) "? Hl Hv".
    iApply ("HR" with "[$] Hl").
    iSplit; last done.
    destruct strong as [ strong | ]; last done.
    iIntros (???) "Hl Hst".
    iDestruct "Hv" as "[Hv _]".
    iMod ("Hv" with "Hl Hst") as "(Hl & %Hst & $)".
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    cbn. eauto with iFrame.
  Qed.
  Global Instance typed_place_opened_owned_inst π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r bmin0 l wl P :
    TypedPlace E L π l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r bmin0 (Owned wl) P | 5 :=
        λ T, i2p (typed_place_opened_owned π E L lt_cur lt_inner lt_full Cpre Cpost r bmin0 l wl P T).

  Lemma typed_place_opened_uniq π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r bmin0 l κ γ P T :
    typed_place π E L l lt_cur r bmin0 (Owned false) P (λ L' κs l2 b2 bmin rti ltyi ri strong weak,
      T L' κs l2 b2 bmin rti ltyi ri
        (option_map (λ strong, mk_strong strong.(strong_rt)
          (λ rti2 ltyi2 ri2, OpenedLtype (strong.(strong_lt) _ ltyi2 ri2) lt_inner lt_full Cpre Cpost)
          (λ rti2 ri2, strong.(strong_rfn) _ ri2)
          strong.(strong_R)) strong)
        (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
        None)
    ⊢ typed_place π E L l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r bmin0 (Uniq κ γ) P T.
  Proof.
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL #Hincl0 Hl HR".
    iPoseProof (opened_ltype_acc_uniq with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL [] Hl").
    { destruct bmin0; done. }
    iIntros (L' ??????? strong weak) "? Hl Hv".
    iApply ("HR" with "[$] Hl").
    iSplit; last done.
    destruct strong as [ strong | ]; last done.
    iIntros (???) "Hl Hst".
    iDestruct "Hv" as "[Hv _]".
    iMod ("Hv" with "Hl Hst") as "(Hl & %Hst & $)".
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    cbn. eauto with iFrame.
  Qed.
  Global Instance typed_place_opened_uniq_inst π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r bmin0 l κ γ P :
    TypedPlace E L π l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r bmin0 (Uniq κ γ) P | 5 :=
        λ T, i2p (typed_place_opened_uniq π E L lt_cur lt_inner lt_full Cpre Cpost r bmin0 l κ γ P T).

  Lemma typed_place_shadowed_shared π E L {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) r_cur (r_full : place_rfn rt_full) bmin0 l κ P (T : place_cont_t rt_full) :
    (* sidecondition needed for the weak update *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (ltype_blocked_lfts lt_full)⌝ ∗
    typed_place π E L l lt_cur (#r_cur) bmin0 (Shared κ) P (λ L' κs l2 b2 bmin rti ltyi ri strong weak,
      T L' κs l2 b2 bmin rti ltyi ri
          (option_map (λ strong, mk_strong (λ _, rt_full) (λ rti ltyi ri, ShadowedLtype (strong.(strong_lt) _ ltyi ri) (strong.(strong_rfn) _ ri) lt_full) (λ _ _, r_full) strong.(strong_R)) strong)
          (option_map (λ weak, mk_weak (λ ltyi ri, ShadowedLtype (weak.(weak_lt) ltyi ri) (weak.(weak_rfn) ri) lt_full) (λ _, r_full) weak.(weak_R)) weak)
    )
    ⊢ typed_place π E L l (ShadowedLtype lt_cur (#r_cur) lt_full) r_full bmin0 (Shared κ) P T.
  Proof.
    iIntros "(Houtl & HT)".
    iIntros (????) "#CTX #HE HL Hincl Hl Hc".
    iPoseProof (lctx_bor_kind_outlives_all_use with "Houtl HE HL") as "#Houtl'".
    iPoseProof (shadowed_ltype_acc_cur with "Hl") as "(Hcur & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hincl Hcur").
    iIntros (L' κs l2 b2 bmin rti ltyi ri strong weak) "Hincl' Hl Hcc".
    iApply ("Hc" with "Hincl' Hl").
    iSplit; simpl.
    - destruct strong as [ strong | ]; simpl; last done.
      iIntros (rti2 ltyi2 ri2) "Hl %Hst".
      iDestruct "Hcc" as "[ Hcc _]".
      iMod ("Hcc" with "Hl [//]") as "(Hl & %Hst' & $)".
      iPoseProof ("Hcl" with "[] Hl") as "Hl".
      { done. }
      iFrame.
      simp_ltypes. done.
    - destruct weak as [ weak | ]; simpl; last done.
      iDestruct "Hcc" as "[_ Hcc]".
      iIntros (lti2 ri2 bmin') "Hincl Hl Hcond".
      iMod ("Hcc" with "Hincl Hl Hcond") as "(Hl & Hcond & Htoks & Hr)".
      iFrame.
      iDestruct "Hcond" as "(Hcond & _)".
      iPoseProof (typed_place_cond_ty_syn_type_eq with "Hcond") as "%Hsteq".
      iPoseProof ("Hcl" with "[//] Hl") as "Hl".
      iFrame. iSplitL; first last. { destruct bmin0; done. }
      iApply typed_place_cond_ty_shadowed_update_cur. done.
  Qed.
  Global Instance typed_place_shadowed_shr_inst π E L {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) r_cur r_full bmin0 l κ P :
    TypedPlace E L π l (ShadowedLtype lt_cur #r_cur lt_full) r_full bmin0 (Shared κ) P | 5 :=
        λ T, i2p (typed_place_shadowed_shared π E L lt_cur lt_full r_cur r_full bmin0 l κ P T).

  (** typing of expressions *)
  Lemma typed_val_expr_wand E L e π T1 T2 :
    typed_val_expr π E L e T1 -∗
    (∀ L' v rt ty r, T1 L' v rt ty r -∗ T2 L' v rt ty r) -∗
    typed_val_expr π E L e T2.
  Proof.
    iIntros "He HT" (Φ) "#LFT #HE HL Hna HΦ".
    iApply ("He" with "LFT HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv Hty".
    iApply ("HΦ" with "HL Hna Hv"). by iApply "HT".
  Qed.

  Lemma typed_if_wand E L v (P T1 T2 T1' T2' : iProp Σ):
    typed_if E L v P T1 T2 -∗
    ((T1 -∗ T1') ∧ (T2 -∗ T2')) -∗
    typed_if E L v P T1' T2'.
  Proof.
    iIntros "Hif HT Hv". iDestruct ("Hif" with "Hv") as (b ?) "HC".
    iExists _. iSplit; first done. destruct b.
    - iDestruct "HT" as "[HT _]". by iApply "HT".
    - iDestruct "HT" as "[_ HT]". by iApply "HT".
  Qed.

  Lemma typed_bin_op_wand E L π v1 P1 Q1 v2 P2 Q2 op ot1 ot2 T:
    typed_bin_op π E L v1 Q1 v2 Q2 op ot1 ot2 T -∗
    (P1 -∗ Q1) -∗
    (P2 -∗ Q2) -∗
    typed_bin_op π E L v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "H Hw1 Hw2 H1 H2".
    iApply ("H" with "[Hw1 H1]"); [by iApply "Hw1"|by iApply "Hw2"].
  Qed.

  Lemma typed_un_op_wand E L π v P Q op ot T:
    typed_un_op π E L v Q op ot T -∗
    (P -∗ Q) -∗
    typed_un_op π E L v P op ot T.
  Proof.
    iIntros "H Hw HP". iApply "H". by iApply "Hw".
  Qed.

  Definition uncurry_rty {T} (f : ∀ rt, type rt → rt → T) : sigT (λ rt, type rt * rt)%type → T :=
    λ '(existT rt (ty, r)), f rt ty r.

  Lemma type_val_context v π T :
    (find_in_context (FindVal v π) (uncurry_rty T)) ⊢ typed_value v π T.
  Proof.
    iDestruct 1 as ([rt [ty r]]) "[Hv HT]". simpl in *.
    iIntros "LFT". iExists _, _, _. iFrame.
  Qed.
  Global Instance type_val_context_inst v π :
    TypedValue v π | 100 := λ T, i2p (type_val_context v π T).

  Lemma type_val E L v π T :
    typed_value v π (T L v) ⊢ typed_val_expr π E L (Val v) T.
  Proof.
    iIntros "Hv" (Φ) "#LFT #HE HL Hna HΦ".
    iDestruct ("Hv" with "LFT") as "(%rt & %ty & %r & Hty & HT)".
    iApply wp_value. iApply ("HΦ" with "HL Hna Hty HT").
  Qed.

  Lemma type_call E L π T ef eκs es:
    (∃ M, named_lfts M ∗
    li_tactic (compute_map_lookups_nofail_goal M eκs) (λ eκs',
    named_lfts M -∗
    typed_val_expr π E L ef (λ L' vf rtf tyf rf,
        foldr (λ e T L'' vl tys, typed_val_expr π E L'' e (λ L''' v rt ty r, T L''' (vl ++ [v]) (tys ++ [existT rt (ty, r)])))
              (λ L'' vl tys, typed_call π E L'' eκs' vf (vf ◁ᵥ{π} rf @ tyf) vl tys T)
              es L' [] [])))
    ⊢ typed_val_expr π E L (CallE ef eκs es) T.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %eκs' & _ & He)". iIntros (Φ) "#CTX #HE HL Hna HΦ".
    rewrite /CallE.
    iApply wp_call_bind. iApply ("He" with "Hnamed CTX HE HL Hna"). iIntros (L' vf rtf tyf rf) "HL Hna Hvf HT".
    iAssert ([∗ list] v;rty∈[];([] : list $ @sigT Type (λ rt, (type rt * rt)%type)), let '(existT rt (ty, r)) := rty in v ◁ᵥ{π} r @ ty)%I as "-#Htys". { done. }
    move: {2 3 5} ([] : list val) => vl.
    generalize (@nil (@sigT Type (fun rt : Type => prod (@type Σ H rt) rt))) at 2 3 as tys; intros tys.
    iInduction es as [|e es] "IH" forall (L' vl tys) => /=. 2: {
      iApply ("HT" with "CTX HE HL Hna"). iIntros (L'' v rt ty r) "HL Hna Hv Hnext". iApply ("IH" with "HΦ HL Hna Hvf Hnext").
      iFrame. by iApply big_sepL2_nil.
    }
    by iApply ("HT" with "Hvf Htys CTX HE HL Hna").
  Qed.

  Lemma type_bin_op E L o e1 e2 ot1 ot2 π T :
    typed_val_expr π E L e1 (λ L1 v1 rt1 ty1 r1, typed_val_expr π E L1 e2 (λ L2 v2 rt2 ty2 r2,
      typed_bin_op π E L2 v1 (v1 ◁ᵥ{π} r1 @ ty1) v2 (v2 ◁ᵥ{π} r2 @ ty2) o ot1 ot2 T))
    ⊢ typed_val_expr π E L (BinOp o ot1 ot2 e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL Hna HΦ".
    wp_bind. iApply ("He1" with "LFT HE HL Hna"). iIntros (L1 v1 rt1 ty1 r1) "HL Hna Hv1 He2".
    wp_bind. iApply ("He2" with "LFT HE HL Hna"). iIntros (L2 v2 rt2 ty2 r2) "HL Hna Hv2 Hop".
    iApply ("Hop" with "Hv1 Hv2 LFT HE HL Hna HΦ").
  Qed.

  Lemma type_un_op E L o e ot π T :
    typed_val_expr π E L e (λ L' v rt ty r, typed_un_op π E L' v (v ◁ᵥ{π} r @ ty) o ot T)
    ⊢ typed_val_expr π E L (UnOp o ot e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL Hna HΦ".
    wp_bind. iApply ("He" with "LFT HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv Hop".
    by iApply ("Hop" with "Hv LFT HE HL Hna").
  Qed.

  Lemma type_ife E L e1 e2 e3 π T:
    typed_val_expr π E L e1 (λ L' v rt ty r, typed_if E L' v (v ◁ᵥ{π} r @ ty) (typed_val_expr π E L' e2 T) (typed_val_expr π E L' e3 T))
    ⊢ typed_val_expr π E L (IfE BoolOp e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL Hna HΦ".
    wp_bind. iApply ("He1" with "LFT HE HL Hna"). iIntros (L1 v1 rt1 ty1 r1) "HL Hna Hv1 Hif".
    iDestruct ("Hif" with "Hv1") as "HT".
    iDestruct "HT" as (b) "(% & HT)".
    iApply wp_if_bool; [done|..]. iIntros "!> Hcred".
    destruct b; by iApply ("HT" with "LFT HE HL Hna").
  Qed.

  Lemma type_annot_expr E L n {A} (a : A) e π T:
    typed_val_expr π E L e (λ L' v rt ty r, typed_annot_expr π E L' n a v (v ◁ᵥ{π} r @ ty) T)
    ⊢ typed_val_expr π E L (AnnotExpr n a e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL Hna HΦ".
    wp_bind. iApply ("He" with "LFT HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv HT".
    iDestruct ("HT" with "LFT HE HL Hv") as "HT".
    iInduction n as [|n] "IH" forall (Φ). {
      rewrite /AnnotExpr/=.
      iApply fupd_wp.
      iMod "HT" as "(%L2 & % & % & % & HL & Hv & Hf)".
      iApply wp_value.
      iApply ("HΦ" with "[$] Hna [$] [$]").
    }
    rewrite annot_expr_S_r. wp_bind.
    iApply wp_skip. iIntros "!> Hcred".
    iApply fupd_wp. iMod "HT".
    iMod (lc_fupd_elim_later with "Hcred HT") as ">HT". iModIntro.
    iApply ("IH" with "HΦ Hna HT").
  Qed.

  Lemma type_logical_and E L e1 e2 π T:
    typed_val_expr π E L e1 (λ L1 v1 rt1 ty1 r1, typed_if E L1 v1 (v1 ◁ᵥ{π} r1 @ ty1)
       (typed_val_expr π E L1 e2 (λ L2 v2 rt2 ty2 r2, typed_if E L2 v2 (v2 ◁ᵥ{π} r2 @ ty2)
           (typed_value (val_of_bool true) π (T L2 (val_of_bool true))) (typed_value (val_of_bool false) π (T L2 (val_of_bool false)))))
       (typed_value (val_of_bool false) π (T L1 (val_of_bool false))))
    ⊢ typed_val_expr π E L (e1 &&{BoolOp, BoolOp, u8} e2)%E T.
  Proof.
    iIntros "HT". rewrite /LogicalAnd. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L1 v rt ty r) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    2: { iApply type_val. by rewrite !val_of_bool_i2v. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L2 v2 rt2 ty2 r2) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT"; iApply type_val; by rewrite !val_of_bool_i2v.
  Qed.

  Lemma type_logical_or E L e1 e2 π T:
    typed_val_expr π E L e1 (λ L1 v1 rt1 ty1 r1, typed_if E L1 v1 (v1 ◁ᵥ{π} r1 @ ty1)
      (typed_value (val_of_bool true) π (T L1 (val_of_bool true)))
      (typed_val_expr π E L1 e2 (λ L2 v2 rt2 ty2 r2, typed_if E L2 v2 (v2 ◁ᵥ{π} r2 @ ty2)
        (typed_value (val_of_bool true) π (T L2 (val_of_bool true))) (typed_value (val_of_bool false) π (T L2 (val_of_bool false))))))
    ⊢ typed_val_expr π E L (e1 ||{BoolOp, BoolOp, u8} e2)%E T.
  Proof.
    iIntros "HT". rewrite /LogicalOr. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L1 v rt ty r) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    1: { iApply type_val. by rewrite !val_of_bool_i2v. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L2 v2 rt2 ty2 r2) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT"; iApply type_val; by rewrite !val_of_bool_i2v.
  Qed.

  (** Similar to type_assign, use is formulated with a skip over the expression, in order to allow
    on-demand unblocking. We can't just use any of the potential place access steps, because there might not be any (if it's just a location). So we can't easily use any of the other steps around.
   *)
  Lemma type_use E L ot T e o π :
    ⌜if o is Na2Ord then False else True⌝ ∗ typed_read π E L e ot T
    ⊢ typed_val_expr π E L (use{ot, o} e)%E T.
  Proof.
    iIntros "[% Hread]" (Φ) "#(LFT & TIME & LLCTX) #HE HL Hna HΦ".
    wp_bind.
    iApply ("Hread" $! _ ⊤ with "[//] [//] [//] [$TIME $LFT $LLCTX] HE HL Hna").
    iIntros (l) "Hl".
    iApply ewp_fupd.
    rewrite /Use. wp_bind.
    iApply (wp_logical_step with "TIME Hl"); [solve_ndisj.. | ].
    iApply wp_skip. iNext. iIntros "_".
    iIntros "(%v & %q & %rt & %ty & %r & %Hlyv & %Hv & Hl & Hv & Hcl)".
    iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; try by eauto using val_to_of_loc.
    { destruct o; naive_solver. }
    iIntros "!> %st Hl Hcred Hcl".
    iMod ("Hcl" with "Hl Hv") as "(%L' & %rt' & %ty' & %r' & HL & Hna & Hv & HT)"; iModIntro.
    by iApply ("HΦ" with "HL Hna Hv HT").
  Qed.

  (* This lemma is about AssignSE, which adds a skip around the LHS expression.
     The reason is that we might need to unblock e1 first and only after that get access to the location we need for justifying the actual write
      - so we can't just use the actual write step,
      - and we also cannot use the place access on the LHS itself, because that might not even take a step (if it's just a location).
     *)
  Lemma type_assign E L π ot e1 e2 s fn R o ϝ :
    typed_val_expr π E L e2 (λ L' v rt ty r, ⌜if o is Na2Ord then False else True⌝ ∗
      typed_write π E L' e1 ot v ty r (λ L'', typed_stmt π E L'' s fn R ϝ))
    ⊢ typed_stmt π E L (e1 <-{ot, o} e2; s) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#(LFT & TIME & LLCTX) #HE HL Hna Hcont".
    wps_bind. iApply ("He" with "[$TIME $LFT $LLCTX] HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv [% He1]".
    wps_bind. iApply ("He1" $! _ ⊤ with "[//] [//] [//] [$TIME $LFT $LLCTX] HE HL Hna"). iIntros (l) "HT".
    unfold AssignSE. wps_bind.
    iSpecialize ("HT" with "Hv").
    iApply (wp_logical_step with "TIME HT"); [solve_ndisj.. | ].
    iApply (wp_skip).
    iNext. iIntros "Hcred (Hly & Hl & Hcl)".
    iModIntro.
    (* TODO find a way to do this without destructing the logstep *)
    rewrite /logical_step.
    iMod "Hcl" as "(%n & Hat & Hcl)".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wps_assign_credits with "TIME Hp Hat"); rewrite ?val_to_of_loc //. { destruct o; naive_solver. }
    iMod (fupd_mask_subseteq) as "Hcl_m"; last iApply fupd_intro.
    { destruct o; solve_ndisj. }
    iFrame. iNext. iIntros "Hl Hat Hcred'". iMod "Hcl_m" as "_".
    rewrite Nat.add_0_r. iDestruct "Hcred'" as "(Hcred1 & Hcred')".
    rewrite (additive_time_receipt_sep 1). iDestruct "Hat" as "(Hat1 & Hat)".
    iMod ("Hcl" with "Hcred' Hat Hl") as ">(%L'' & HL & Hna & Hs)".
    (* TODO maybe provide excess credits + receipt *)
    by iApply ("Hs" with "[$TIME $LFT $LLCTX] HE HL Hna").
  Qed.

  Lemma type_mut_addr_of π E L e T :
    typed_addr_of_mut π E L e T
    ⊢ typed_val_expr π E L (&raw{Mut} e)%E T.
  Proof.
    iIntros "HT" (?) "#CTX #HE HL Hna Hcont".
    rewrite /Raw. wp_bind.
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] CTX HE HL Hna").
    iIntros (l) "HT".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME HT"); [done.. | ].
    iApply wp_skip. iNext. iIntros "Hcred".
    iDestruct 1 as (L' rt ty r) "(Hl & HL & Hna & HT)".
    iApply ("Hcont" with "HL Hna Hl HT").
  Qed.
  (* Corresponding lemmas for borrows are in references.v *)


  Import EqNotations.
  (** Entry point for checking reads *)
  Lemma type_read π E L T T' e ot :
    (** Decompose the expression *)
    IntoPlaceCtx π E e T' →
    T' L (λ L' K l,
      (** Find the type assignment *)
      find_in_context (FindLoc l π) (λ '(existT rto (lt1, r1, b)),
      (** Check the place access *)
      typed_place π E L' l lt1 r1 b b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 bmin : bor_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) (strong : option $ strong_ctx rti) (weak : option $ weak_ctx rto rti),
        (** Stratify *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (** Omitted from the paper: Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        prove_place_rfn_cond (if upd is ResultWeak _ then true else false) bmin ri2 ri3 (
        (** Require the stratified place to be a value type *)
        (* TODO remove this and instead have a [ltype_read_as] TC or so. Currently this will prevent us from reading from ShrBlocked*)
        cast_ltype_to_type E L2 lt3 (λ ty3,
        (** Finish reading *)
        typed_read_end π E L2 l2 (◁ ty3) ri3 b2 bmin (if strong is Some _ then AllowStrong else AllowWeak) ot (λ L3 v rt3 ty3 r3 rt2' lt2' ri2' upd2,
        typed_place_finish π E L3 strong weak (access_result_meet upd upd2) R (llft_elt_toks κs) l b lt2' ri2' (λ L4, T L4 v _ ty3 r3))
      )))))))%I
    ⊢ typed_read π E L e ot T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL Hna HΦ".
    iApply (HT' with "CTX HE HL Hna HT'").
    iIntros (L' K l) "HL Hna". iDestruct 1 as ([rt ([ty r] & ?)]) "[Hl HP]".
    iApply ("HP" with "[//] [//] CTX HE HL [] Hl").
    { iApply bor_kind_incl_refl. }
    iIntros (L'' κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hl2 Hs HT HL".
    iApply "HΦ".
    iPoseProof ("HT" with "[//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L2 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hcond & Hrcond & HT)".
    iApply (logical_step_wand with "Hl2").
    iIntros "!> (Hl2 & HR)".
    iDestruct "HT" as "(%ty3 & %Heqt & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heqt.
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "(Hincl & HL)"; first done; first apply Heqt.
    iMod  ("Hincl" with "Hl2") as "Hl2".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hna [//] Hl2") as "Hread".
    iDestruct "Hread" as (q v rt2 ty2' r2) "(% & % & Hl2 & Hv & Hcl)".
    iModIntro. iExists v, q, _, _, _. iSplitR; first done. iSplitR; first done.
    iFrame "Hl2 Hv".
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl" (st) "Hl2 Hv".
    iMod ("Hcl" $! st with "Hl2 Hv") as (L3 rt4 ty4 r4) "(Hmv & HL & Hna & Hcl)".
    iDestruct "Hcl" as "(%rt' & %lt' & %r' & %res & Hl2 & %Hsteq & Hx & Hfin)" => /=.
    iPoseProof (typed_place_finish_elim with "Hfin") as "[Hweak | Hstrong]".
    + (* do a weak update *)
      iDestruct "Hweak" as "(%weak' & %Heq & -> & %Hw & Hfin)". subst rt'.
      destruct upd as [ upd | ]; last done.
      simpl in Hw. iDestruct "Hs" as "[_ Hs]". subst rt2'.
      destruct res; last done.
      (*rewrite (UIP_refl _ _ Heq).*)
      iMod ("Hs" with "[] Hl2 [Hcond Hx Hrcond]") as "(Hl & Hcond'' & Htoks & HR')".
      { iApply bor_kind_incl_refl. }
      { iApply (typed_place_cond_trans with "[-Hx] Hx").
        iApply (typed_place_cond_ltype_eq_ofty with "[-]"); last done.
        iFrame.
      }
      cbn. iDestruct ("Hfin" with "Hl HR'") as "Hfin".
      iMod ("Hfin" with "[] HE HL [$HR $Htoks]") as "(%L4 & HL & HT)"; first done.
      iModIntro. iExists _, _, _, _. iFrame.
    + (* also need to do a strong update due to the stratification *)
      iDestruct "Hstrong" as "(%strong' & -> & %Hw & Hfin)".
      iDestruct "Hs" as "[Hs _]".
      iMod ("Hs" with "Hl2 [Hcond]") as "(Hl & Hcond'' & HR')".
      { unshelve iSpecialize ("Heq" $! (Owned false) inhabitant); first apply _.
        iPoseProof (ltype_eq_syn_type with "Heq") as "%Hst2".
        destruct upd.
        - iPoseProof (typed_place_cond_ty_syn_type_eq with "Hcond") as "%Hcond2".
          rewrite Hsteq Hcond2 //.
        - rewrite Hsteq -Hst2. done.
      }
      cbn. iDestruct ("Hfin" with "Hl HR'") as "Hfin".
      iMod ("Hfin" with "[] HE HL HR") as "(%L4 & HL & HT)"; first done.
      iModIntro. iExists _, _, _, _. iFrame.
  Qed.

  (** [type_read_end] instance that does a copy *)
  Lemma type_read_ofty_copy E L {rt} π (T : typed_read_end_cont_t rt) b2 bmin br l (ty : type rt) r ot `{!Copyable ty}:
    (** We have to show that the type allows reads *)
    (⌜ty_has_op_type ty ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗
      (** The place is left as-is *)
      ∀ v, T L v rt ty r rt (◁ ty) (#r) (ResultWeak eq_refl))
    ⊢ typed_read_end π E L l (◁ ty) (#r) b2 bmin br ot T.
  Proof.
    iIntros "(%Hot & %Hal & Hs)" (F ???) "#CTX #HE HL Hna".
    destruct b2 as [ wl | | ]; simpl.
    - iIntros "_ Hb".
      iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & #Hv & Hcl))"; first done.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      specialize (ty_op_type_stable Hot) as Halg''.
      assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
      iModIntro. iExists _, _, rt, _, _.
      iFrame "Hl Hv".
      iSplitR; first done. iSplitR; first done.
      iApply (logical_step_wand with "Hcl").
      iIntros "Hcl %st Hl _". iMod ("Hcl" with "Hl [//] Hsc Hv") as "Hl".
      iModIntro. iExists L, rt, ty, r.
      iPoseProof (ty_memcast_compat with "Hv") as "Ha"; first done. iFrame "Ha HL Hna".
      (* weak update *)
      iExists _, _, _, (ResultWeak eq_refl). iFrame.
      iR. iSplitR. { iApply typed_place_cond_refl. done. }
      iApply "Hs".
    - iIntros "Hincl0 #Hl".
      simpl in Hal.
      iPoseProof (ofty_ltype_acc_shared with "Hl") as "(%ly & %Halg & %Hly & Hlb & >Hl')"; first done.

      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Htok & HL & Hclose)"; [solve_ndisj | done | ].
      iMod (copy_shr_acc _ _ _ shrE with "CTX Hl' Hna Htok") as "(>%Hly' & (%q'' & %v & Hna & (>Hll & #Hv) & Hclose_l))";
        [solve_ndisj | solve_ndisj | | ].
      { apply shr_locsE_incl. }
      iDestruct (ty_own_val_has_layout with "Hv") as "#>%Hlyv"; first done.
      iModIntro. iExists _, _, rt, _, _. iFrame "Hll Hv".
      assert (ly = ot_layout ot) as ->.
      { specialize (ty_op_type_stable Hot) as ?. eapply syn_type_has_layout_inj; done. }
      iSplitR; first done. iSplitR; first done.
      iApply logical_step_intro. iIntros (st) "Hll Hv'".
      iMod ("Hclose_l" with "Hna [Hv Hll]") as "[Hna Htok]".
      { eauto with iFrame. }
      iMod ("Hclose" with "Htok HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro. iExists L, rt, ty, r.
      iPoseProof (ty_memcast_compat with "Hv'") as "Hid"; first done. simpl. iFrame.
      iExists _, _, _, (ResultWeak eq_refl).  iFrame "Hl".
      iR. iSplitR; last done. iSplitR; last iApply typed_place_cond_rfn_refl.
      iApply typed_place_cond_ty_refl_ofty.
    - iIntros "Hincl0 Hl".
      simpl in Hal.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as (q') "(Htok & HL_cl2)"; [solve_ndisj | ].
      iPoseProof (ofty_ltype_acc_uniq with "CTX Htok HL_cl2 Hl") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
      iMod "HF_cl" as "_".
      assert (ly = ot_layout ot) as ->.
      { specialize (ty_op_type_stable Hot) as ?. eapply syn_type_has_layout_inj; done. }
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iSplitR; first done.
      iApply logical_step_mask_mono; last iApply (logical_step_wand with "Hcl"); first done.
      iIntros "[Hcl _]".
      iIntros (st) "Hl #Hv".
      iMod (fupd_mask_mono with "(Hcl Hl Hv)") as "(Hl & HL)"; first done.
      iPoseProof ("HL_cl" with "HL") as "HL".
      iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.
      iModIntro. iExists L, rt, ty, r. iFrame "Hid HL Hna".
      iExists _, _, _, (ResultWeak eq_refl). iFrame.
      iR. iSplitR; last done. iSplitR; last iApply typed_place_cond_rfn_refl.
      iApply typed_place_cond_ty_refl_ofty.
  Qed.
  Global Instance type_read_ofty_copy_inst E L {rt} π b2 bmin br l (ty : type rt) r ot `{!Copyable ty} :
    TypedReadEnd π E L l (◁ ty)%I (PlaceIn r) b2 bmin br ot | 10 :=
    λ T, i2p (type_read_ofty_copy E L π T b2 bmin br l ty r ot).

  (*
  For more generality, maybe have LtypeReadAs lty (λ ty r, ...)
    that gives us an accessor as a type?
    => this should work fine.
     - T ty .. (Shared κ) -∗ LtypeReadAs (ShrBlocked ty) T
     - T ty .. k -∗ LtypeReadAs (◁ ty) T
     -
  How does that work for moves? Well, we cannot move if it isn't an OfTy.
     so there we should really cast first.
  Note here: we should only trigger the copy instance if we can LtypeReadAs as something that is copy.
     So we should really make that a TC and make it a precondition, similar to SimplifyHyp etc.

  And similar for LtypeWriteAs lty (λ ty r, ...)?
    well, there it is more difficult, because it even needs to hold if there are Blocked things below.
    I don't think we can nicely solve that part.
   *)

  (** NOTE instance for moving is defined in value.v *)

  (* TODO: potentially lemmas for reading from mut-ref and box ltypes.
      (this would be required for full generality, because shr_blocked can be below them)
   *)

  Lemma type_write E L T T' e ot v rt (ty : type rt) r π :
    IntoPlaceCtx π E e T' →
    T' L (λ L' K l, find_in_context (FindLoc l π) (λ '(existT rto (lt1, r1, b)),
      typed_place π E L' l lt1 r1 b b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 bmin : bor_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) (strong : option $ strong_ctx rti) (weak : option $ weak_ctx rto rti),
        (* unblock etc. TODO: this requirement is too strong. *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (* certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        prove_place_rfn_cond (if upd is ResultWeak _ then true else false) bmin ri2 ri3 (
        (* end writing *)
        typed_write_end π E L2 ot v ty r b2 bmin (if strong is Some _ then AllowStrong else AllowWeak) l2 lt3 ri3 (λ L3 (rt3' : Type) (ty3 : type rt3') (r3 : rt3') upd2,
        typed_place_finish π E L3 strong weak (access_result_meet upd upd2) R (llft_elt_toks κs) l b (◁ ty3)%I (PlaceIn r3) T)))))))
    ⊢ typed_write π E L e ot v ty r T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL Hna HΦ".
    iApply (HT' with "CTX HE HL Hna HT'").
    iIntros (L' K l) "HL Hna". iDestruct 1 as ([rt1 ([ty1 r1] & ?)]) "[Hl HP]".
    iApply ("HP" with "[//] [//] CTX HE HL [] Hl").
    { iApply bor_kind_incl_refl. }
    iIntros (L'' κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hl2 Hs HT HL".
    iApply ("HΦ"). iIntros "Hv".
    iPoseProof ("HT" with "[//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L2 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iModIntro. iApply (logical_step_wand with "Hl2").
    iIntros "(Hl2 & HR)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hcond & Hrcond & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hna [//] Hl2 Hv") as "Hwrite".
    iDestruct "Hwrite" as "(% & Hl2 & Hcl)".
    iModIntro. iFrame "Hl2". iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl Hl2".
    iMod ("Hcl" with "Hl2") as "Hcl".
    iDestruct "Hcl" as "(%L3 & %rt3 & %ty3 & %r3 & %res & HL & Hna & Hl2 & %Hsteq & Hx & Hfin)".
    iPoseProof (typed_place_finish_elim with "Hfin") as "[Hweak | Hstrong]".
    - (* weak *)
      iDestruct "Hweak" as "(%weak' & %Heq & -> & %Hres & Hfin)".
      iDestruct "Hs" as "[_ Hs]". subst rt3.
      destruct upd as [ upd | ]; last done. subst rt2'.
      iMod ("Hs" with "[] Hl2 [Hcond Hx Hrcond]") as "(Hl & Hcond'' & Htoks & HR')".
      { iApply bor_kind_incl_refl. }
      { destruct res; last done.
        iApply (typed_place_cond_trans with "[$Hcond $Hrcond] Hx"). }
      cbn. iPoseProof ("Hfin" with "Hl HR'") as "Hfin".
      iMod ("Hfin" with "[//] HE HL [$HR $Htoks]") as "(%L4 & HL & HT)".
      iModIntro. iExists L4. iFrame.
    - (* strong *)
      iDestruct "Hstrong" as "(%strong' & -> & %Hres & Hfin)".
      iDestruct "Hs" as "[Hs _]".
      iMod ("Hs" with "Hl2 [Hcond Hrcond]") as "(Hl & Hcond'' & HR')".
      { destruct upd.
        - iPoseProof (typed_place_cond_ty_syn_type_eq with "Hcond") as "%Hcond2".
          simp_ltypes. rewrite Hcond2 //.
        - simp_ltypes. rewrite Hsteq //. }
        iPoseProof ("Hfin" with "Hl HR'") as "Hfin".
        iMod ("Hfin" with "[//] HE HL HR") as "(%L4 & HL & HT)".
        iModIntro. iExists _. iFrame.
  Qed.

  (* TODO: generalize to other places where we can overwrite, but which can't be folded to an ofty *)

  (** Currently have [ty2], want to write [ty]. This allows updates of the refinement type (from rt to rt2).
     This only works if the path is fully owned ([bmin = Owned _]).
     We could in principle allow this also for Uniq paths by suspending the mutable reference's contract with [OpenedLtype], but currently we have decided against that. *)
  (* TODO the syntype equality requirement currently is too strong: it does not allow us to go from UntypedSynType to "proper sy types".
    more broadly, this is a symptom of our language not understanding about syntypes.
  *)
  Lemma type_write_ofty_strong E L {rt rt2} π (T : typed_write_end_cont_t rt2) l (ty : type rt) (ty2 : type rt2) r1 (r2 : rt2) v ot wl wl' :
    (⌜ty_has_op_type ty ot MCNone⌝ ∗ ⌜ty_syn_type ty = ty_syn_type ty2⌝ ∗
        (ty2.(ty_ghost_drop) π r2 -∗ T L rt ty r1 ResultStrong))
    ⊢ typed_write_end π E L ot v ty r1 (Owned wl) (Owned wl') AllowStrong l (◁ ty2) (#r2) T.
  Proof.
    iIntros "(%Hot & %Hst_eq & HT)".
    iIntros (F qL ??) "#CTX #HE HL Hna _ Hl Hv".
    iPoseProof (ofty_ltype_acc_owned with "Hl") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v0 & Hl0 & Hv0 & Hcl))"; first done.

    iDestruct (ty_own_val_has_layout with "Hv0") as "%Hlyv0"; first done.
    iDestruct (ty_has_layout with "Hv") as "#(%ly' & % & %Hlyv)".
    assert (ly' = ly) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite Hst_eq. }
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iSplitR; first done.
    iSplitL "Hl0".
    { iExists v0. iFrame. iSplitR; first done. done. }
    iPoseProof (ty_own_ghost_drop _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
    iApply (logical_step_compose with "Hcl").
    iApply (logical_step_compose with "Hgdrop").
    iApply logical_step_intro.
    iIntros "Hgdrop Hcl Hl".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc'".
    iMod ("Hcl" with "Hl [//] Hsc' Hv") as "Hl".
    iExists _, rt, ty, r1, ResultStrong. iFrame.
    iSplitR. { done. }
    iR.
    iApply ("HT" with "Hgdrop").
  Qed.
  Global Instance type_write_ofty_strong_inst E L {rt rt2} π l (ty : type rt) (ty2 : type rt2) (r1 : rt) (r2 : rt2) v ot wl wl' :
    TypedWriteEnd π E L ot v ty r1 (Owned wl) (Owned wl') AllowStrong l (◁ ty2)%I (PlaceIn r2) | 10 :=
    λ T, i2p (type_write_ofty_strong E L π T l ty ty2 r1 r2 v ot wl wl').

  (** This does not allow updates to the refinement type, rt stays the same. *)
  (* TODO: also allow writes here if the place is not an ofty *)
  (* Write v : r1 @ ty to l : #r2 @ ◁ ty2. We first need to show that ty is a subtype of ty2.
     Afterwards, we obtain l : #r3 @ ◁ ty2 for some r3, as well as the result of ghost-dropping r2 @ ty2. *)
  Lemma type_write_ofty_weak E L {rt} π (T : typed_write_end_cont_t rt) b2 bmin ac l (ty ty2 : type rt) r1 r2 v ot :
    (∃ r3, owned_subtype π E L false r1 r3 ty ty2 (λ L2,
      ⌜ty_syn_type ty = ty_syn_type ty2⌝ ∗ (* TODO: would be nice to remove this requirement *)
      ⌜ty_has_op_type ty ot MCNone⌝ ∗ ⌜lctx_bor_kind_alive E L2 b2⌝ ∗ ⌜bor_kind_writeable b2⌝ ∗ (ty2.(ty_ghost_drop) π r2 -∗ T L2 rt ty2 r3 (ResultWeak eq_refl))))
    ⊢ typed_write_end π E L ot v ty r1 b2 bmin ac l (◁ ty2) (#r2) T.
  Proof.
    iIntros "(%r3 & HT)".
    iIntros (F qL ??) "#CTX #HE HL Hna #Hincl Hl Hv".
    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & Hsub & HL & %Hst_eq & %Hot & %Hal & %Hwriteable & HT)".
    iDestruct ("Hsub") as "(#%Hly_eq & _ & Hsub)".
    iPoseProof ("Hsub" with "Hv") as "Hv".
    destruct b2 as [ wl | | ]; simpl.
    - iPoseProof (ofty_ltype_acc_owned with "Hl") as "(%ly & %Halg & %Hly & #Hsc & _ & >(%v0 & Hl & Hv0 & Hcl))"; first done.
      iDestruct (ty_own_val_has_layout with "Hv0") as "%"; first done.
      iDestruct (ty_has_layout with "Hv") as "(%ly'' & % & %)".
      assert (ly'' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      specialize (ty_op_type_stable Hot) as ?.
      assert (ly = ot_layout ot) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite -Hst_eq. }
      iModIntro. iSplitR; first done. iSplitL "Hl".
      { iExists v0. iFrame. done. }
      iPoseProof (ty_own_ghost_drop _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hgdrop").
      iApply logical_step_intro. iIntros "Hgdrop Hcl Hl".
      (*iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc'".*)
      iMod ("Hcl" with "Hl [] [] Hv") as "Hl"; [done.. | ].
      iModIntro.
      iExists _, _, ty2, r3, (ResultWeak eq_refl).
      iFrame.
      iR.
      iSplitR.
      { iSplit; first iApply typed_place_cond_ty_refl_ofty.
        destruct bmin; simpl; done. }
      iApply ("HT" with "Hgdrop").
    - (* we know that bmin is also Shared, so it can't be writeable *)
      (*destruct bmin; done.*)
      done.
    - (* we know that bmin is also Uniq, since it can't be shared *)
      destruct bmin as [ | | κ' ?]; [done.. | ]. rewrite {1}/bor_kind_incl.
      simpl in Hal.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as "(%q & Htok & Htok_cl)"; first done.
      iPoseProof (ofty_ltype_acc_uniq lftE with "CTX Htok Htok_cl Hl") as "(%ly & %Halg & %Hly & Hlb & >Hb)"; first done.
      iMod "HF_cl" as "_".
      iDestruct "Hb" as "(%v0 & Hl & Hv0 & Hcl)".
      iDestruct (ty_own_val_has_layout with "Hv0") as "%"; first done.
      iDestruct (ty_has_layout with "Hv") as "(%ly'' & % & %)".
      assert (ly'' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      specialize (ty_op_type_stable  Hot) as ?.
      assert (ly = ot_layout ot) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite -Hst_eq. }
      iModIntro. iSplitR; first done. iSplitL "Hl".
      { iExists v0. iFrame. done. }
      iPoseProof (ty_own_ghost_drop _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
      iApply (logical_step_compose with "Hgdrop").
      iApply (logical_step_mask_mono lftE); first done.
      iApply (logical_step_compose with "Hcl").
      iApply logical_step_intro. iIntros "[Hcl _] Hgdrop Hl".
      iMod (fupd_mask_mono with "(Hcl Hl Hv)") as "(Hl & HL)"; [done.. | ].
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro.
      iExists _, _, ty2, r3, (ResultWeak eq_refl). iFrame.
      iR.
      iSplitR.
      { iSplit; first iApply typed_place_cond_ty_refl_ofty. done. }
      iApply ("HT" with "Hgdrop").
  Qed.
  Global Instance type_write_ofty_weak_inst E L {rt} π b2 bmin br l ty ty2 (r1 r2 : rt) v ot :
    TypedWriteEnd π E L ot v ty r1 b2 bmin br l (◁ ty2)%I (PlaceIn r2) | 20 :=
    λ T, i2p (type_write_ofty_weak E L π T b2 bmin br l ty ty2 r1 r2 v ot).

  (* TODO move *)
  (*
  Fixpoint try_fold_lty {rt} (lt : lty rt) : option (type rt) :=
    match lt with
    | BlockedLty _ _ => None
    | ShrBlockedLty _ _ => None
    | OfTy ty => Some ty
    | MutLty lt κ =>
        ty ← try_fold_lty lt;
        Some (mut_ref ty κ)
    | ShrLty lt κ =>
        (* TODO *)
        (*ty ← try_fold_lty lt;*)
        (*Some (shr_ref ty κ)*)
        None
    | BoxLty lt =>
        (* TODO *)
        (*ty ← try_fold_lty lt;*)
        (*Some (box ty)*)
        None
    | ProdLty lt1 lt2 sl =>
        ty1 ← try_fold_lty lt1;
        ty2 ← try_fold_lty lt2;
        if decide (sl = pair_layout_spec ty1 ty2) then Some (pair_t ty1 ty2) else None
    end.
  Lemma try_fold_lty_correct {rt} (lt : lty rt) (ty : type rt) :
    try_fold_lty lt = Some ty →
    ⊢ ltype_eq lt (◁ ty)%I.
  Proof.
  Abort.

  (* The following lemmas are really somewhat awkward, because of the whole "pushing down" thing: we are really overwriting the MutLty(etc.) here, not its contents. But still, we need to replicate these lemmas that are really similar, because we can't phrase the ownership generically. *)

  (* Basically for Uniq ownership. We need to take care that we are not disrupting the contract of the mutable reference that may be above it (in the b2=Uniq case). *)
  Lemma type_write_mutlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt * gname)) (lt2 : lty rt) r1 r2 v κ ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (MutLty lt2 κ)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (MutLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_mutlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v κ wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (MutLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.

  (* Same lemmas for box *)
  Lemma type_write_boxlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt)) (lt2 : lty rt) r1 r2 v ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (BoxLty lt2)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (BoxLty lt2) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_boxlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (BoxLty lt2) (PlaceIn r2) T.
  Proof.
  Abort.

  (* Same for sharing. This works, again, because we are writing to the place the shared reference is stored in, not below the shared reference. *)
  Lemma type_write_shrlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt)) (lt2 : lty rt) r1 r2 v κ ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (ShrLty lt2 κ)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (ShrLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_shrlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v κ wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (ShrLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
   *)

  (* TODO: product typing rule.
    This will be a bit more complicated, as we essentially need to require that directly below the product, nothing is blocked.
    Of course, with nested products, this gets more complicated...
   *)

  Lemma type_addr_of_mut π E L (e : expr) (T : typed_addr_of_mut_cont_t) T' :
    IntoPlaceCtx π E e T' →
    T' L (λ L1 K l, find_in_context (FindLoc l π) (λ '(existT rto (lt1, r1, b)),
      (* place *)
      typed_place π E L1 l lt1 r1 b b K (λ L2 κs (l2 : loc) (b2 bmin : bor_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) strong weak,
        typed_addr_of_mut_end π E L2 l2 lt2 ri2 b2 bmin (λ L3 rtb tyb rb rt' lt' r',
          typed_place_finish π E L3 strong weak ResultStrong True (llft_elt_toks κs) l b lt' r' (λ L4,
            (* in case lt2 is already an AliasLtype, the simplify_hyp instance for it will make sure that we don't actually introduce that assignment into the context *)
            l2 ◁ₗ[π, Owned false] ri2 @ lt2 -∗
            T L4 l2 rtb tyb rb)))))
    ⊢ typed_addr_of_mut π E L e T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL Hna HΦ".
    iApply (HT' with "CTX HE HL Hna HT'").
    iIntros (L1 K l) "HL Hna". iDestruct 1 as ([rto [[lt1 r1] b]]) "(Hl & Hplace)" => /=.
    iApply ("Hplace" with "[//] [//] CTX HE HL [] Hl").
    { iApply bor_kind_incl_refl. }
    iIntros (L2 κs l2 b2 bmin rti ltyi ri strong weak) "#Hincl Hl2 Hs Hcont HL".
    iApply "HΦ".
    iApply logical_step_fupd.
    iSpecialize ("Hcont" with "[//] [//] [//] CTX HE HL Hna [//] Hl2").
    iApply (logical_step_wand with "Hcont").
    iDestruct 1 as (L3 rtb tyb rb rt' lt' r') "(Htyb & Hl2 & Hl2' & %Hst & HL & Hna & HT)".

    rewrite /typed_place_finish. simpl.
    (* strong update *) iDestruct "Hs" as "[Hs _]".
    destruct strong as [ strong' | ]; last done.
    iMod ("Hs" with "Hl2 []") as "(Hl & Hcond & HR')".
    { done. }
    simpl.
    iDestruct ("HT" with "Hl HR'") as "HT".
    iMod ("HT" with "[//] HE HL [//]") as "(%L4 & HL & HT)".
    iModIntro.

    iExists L4, _, tyb, rb. iFrame.
    by iApply "HT".
  Qed.
  (* NOTE: instances for [typed_addr_of_mut_end] are in alias_ptr.v *)

  (** Top-level rule for creating a mutable borrow *)
  Lemma type_borrow_mut E L T T' e κ π (orty : option rust_type) :
    (** Decompose the expression *)
    IntoPlaceCtx π E e T' →
    T' L (λ L1 K l,
      (** Find the type assignment in the context *)
      find_in_context (FindLoc l π) (λ '(existT rto (lt1, r1, b)),
      (** Check the place access *)
      typed_place π E L1 l lt1 r1 b b K (λ L2 κs (l2 : loc) (b2 bmin : bor_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) strong weak,
        (** Omitted from paper: find the credit context to give the borrow-step a time receipt *)
        find_in_context (FindCreditStore) (λ '(n, m),
        (** Stratify *)
        stratify_ltype_unblock π E L2 StratRefoldFull l2 lt2 ri2 b2 (λ L3 R rt2' lt2' ri2',
        (** Omitted from paper: Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L3 bmin lt2 lt2' (λ upd,
        prove_place_rfn_cond (if upd is ResultWeak _ then true else false) bmin ri2 ri2' (
        (** The result of the stratification needs to be a value type *)
        ∃ ty2 ri2'',
        ⌜ri2' = #ri2''⌝ ∗
        mut_eqltype E L3 lt2' (◁ ty2) (
        (** Omitted from the paper: There is optionally a type annotation for the content of the borrow which is generated by the frontend.
           We use this type annotation, but only if we are at an Owned place -- below mutable references (e.g. when reborrowing) our options for subtyping are much more limited. *)
        typed_option_map (option_combine orty (match bmin with Owned _ => Some () | _ => None end))
          (λ '(rty, _) (T : sigT (λ rt, type rt * rt * access_result rt2' rt)%type → _),
          (** Find the lifetime name mapping *)
          find_in_context (FindNamedLfts) (λ M, named_lfts M -∗
          (** Interpret the type annotation *)
          li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt3 ty3),
          (* TODO it would be really nice to have a stronger form of subtyping here that also supports unfolding/folding of invariants *)
            ∃ ri3, weak_subtype E L3 ri2'' ri3 ty2 ty3 (T (existT rt3 (ty3, ri3, ResultStrong)))
          )))
          (existT rt2' (ty2, ri2'', access_result_refl)) (λ '(existT rt4 (ty4, ri4, upd')),
          (** finish borrow *)
          typed_borrow_mut_end π E L3 κ l2 ty4 (#ri4) b2 bmin (λ (γ : gname) (lt5 : ltype rt4) (r5 : place_rfn rt4),
          (** return the credit store *)
          credit_store n m -∗
          typed_place_finish π E L3 strong weak (access_result_meet upd upd') R (llft_elt_toks κs) l b
          lt5 r5 (λ L4, T L4 (val_of_loc l2) γ rt4 ty4 ri4)))))))))))
    ⊢ typed_borrow_mut π E L e κ orty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL Hna HΦ".
    iApply (HT' with "CTX HE HL Hna HT'").
    iIntros (L1 K l) "HL Hna". iDestruct 1 as ([rt1 ([ty1 r1] & ?)]) "[Hl HP]".
    iApply ("HP" $! _ F with "[//] [//] CTX HE HL [] Hl").
    { iApply bor_kind_incl_refl. }
    iIntros (L2 κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hl2 Hs HT HL2".
    iDestruct "HT" as ([n m]) "(Hstore & HT)".
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hstore)".
    (* bring the place type in the right shape *)
    iApply ("HΦ" with "Hat").
    iPoseProof ("HT" with "[//] [//] CTX HE HL2 Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L3 & %R & %rt' & %lt' & %r' & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hcond & Hrcond & HT)".
    iDestruct "HT" as "(%ty2 & %ri2' & -> & HT)".
    iDestruct "HT" as "(%Heq & HT)".
    (*iMod ("HT" with "[//] CTX HE HL") as "(#Hincl_ty2 & HL & HT)".*)

    iApply (logical_step_wand with "Hl2").
    iIntros "!> (Hl2 & HR) !> Hcred Hat".
    iPoseProof ("Hstore" with "Hat") as "Hstore".

    (*iMod (ltype_incl_use with "Hincl_ty2 Hl2") as "Hl2"; first done.*)
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "[Hvs HL]"; [solve_ndisj | apply Heq | ].
    iMod ("Hvs" with "Hl2") as "Hl2".
    iPoseProof (ltype_own_has_layout with "Hl2") as "(%ly & %Halg & %Hly)".

    (* eliminate the optional subtyping *)
    iPoseProof (typed_option_map_elim_fupd _ _ _ (λ '(existT rt4 (ty4, r4, upd')),
      ltype_incl b2 (#ri2') (#r4) (◁ ty2) (◁ ty4) ∗ typed_place_cond bmin (◁ ty2) (◁ ty4) (#ri2') (#r4) )%I with "HT [] [] HL") as ">(%ra & HL & Hincl & Hbor)"; first done.
    { iIntros ([rst ?]) "%Heqo HL Ha".
      rewrite /FindNamedLfts.
      iDestruct "Ha" as "(%M & HM & HT)". iPoseProof ("HT" with "HM") as "Ha".
      rewrite /interpret_rust_type_goal. iDestruct "Ha" as "(%rt3 & %ty3 & %r3 & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iModIntro. iPoseProof "Hincl" as "(%Hsteq & _)".
      iExists (existT _ (ty3, r3, ResultStrong)). iFrame "HL HT".
      destruct bmin; [ | destruct orty; done.. ].
      iSplitR; last done.
      destruct b2; [ | done..]. iApply (type_ltype_incl_owned_in with "Hincl"). }
    { iSplitR; first iApply ltype_incl_refl. iSplitL; first iApply typed_place_cond_ty_refl_ofty.
      iApply typed_place_cond_rfn_refl. }
    destruct ra as [rt4 [[ty4 r4] upd']].
    iDestruct "Hincl" as "(#Hincl & #Hcond2)".

    iMod (ltype_incl_use with "Hincl Hl2") as "Hl2"; first done.
    iPoseProof (ltype_incl_syn_type with "Hincl") as "%Hst_eq".
    iMod ("Hbor" $! F with "[//] [//] [//] CTX HE HL Hna [//] Hl2 Hcred") as "Hbor".
    iDestruct "Hbor" as (γ ly') "(Hobs & Hbor & Hsc & %Halg' & Hlb & Hblock & Hcond' & HL & Hna & HT)".
    iSpecialize ("HT" with "Hstore").
    assert (ly' = ly) as ->. { move: Hst_eq Halg' Halg. simp_ltypes => -> ??. by eapply syn_type_has_layout_inj. }
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heq.

    iPoseProof (typed_place_finish_elim with "HT") as "[Hweak | Hstrong]".
    - (* weak update *)
      iDestruct "Hweak" as "(%weak' & %Heq' & -> & %Hmeet & HT)".
      iDestruct "Hs" as "[_ Hs]". subst rt4.
      destruct upd; last done. destruct upd'; last done. simpl in Hmeet.
      subst rt'.
      (*rewrite (UIP_refl _ _ Heq1) in Hmeet. simpl in Hmeet. *)
      iMod ("Hs" with "[] Hblock [Hcond Hcond' Hrcond]") as "(Hl & Hcond & Htoks & HR')".
      { iApply bor_kind_incl_refl. }
      { iApply (typed_place_cond_trans with "[$Hcond]"); first iApply typed_place_cond_rfn_refl.
        iApply ltype_eq_place_cond_trans; first done.
        (*iApply ltype_eq_place_cond_trans. *)
        (* want: the place cond holds trivially, because we are Owned if they are different *)
        iApply (typed_place_cond_trans with "[Hcond2 Hrcond] Hcond'").
        iDestruct "Hcond2" as "(Hcond2 & Hcond2')".
        iFrame "Hcond2". iApply (typed_place_cond_rfn_trans with "Hrcond Hcond2'"). }
      cbn.
      iDestruct ("HT" with "Hl HR'") as "HT".
      iMod ("HT" with "[//] HE HL [$HR $Htoks]") as "(%L4 & HL & HT)".
      iModIntro. iExists L4, _, _, _, γ, ly. iFrame.
      iSplitR; done.
    - (* strong update *) iDestruct "Hs" as "[Hs _]".
      iDestruct "Hstrong" as "(%strong' & -> & %Hw & HT)".
      iMod ("Hs" with "Hblock [Hcond Hcond']") as "(Hl & Hcond & HR')".
      { iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "%Heq2".
        move: Hst_eq. simp_ltypes => Hst_eq.
        simp_ltypes. iPureIntro. congruence. }
      simpl.
      iDestruct ("HT" with "Hl HR'") as "HT".
      iMod ("HT" with "[//] HE HL HR") as "(%L4 & HL & HT)".
      iModIntro. iExists L4, _, _, _, γ, ly. iFrame.
      iSplitR; done.
  Qed.

  (** Finish a mutable borrow *)
  Lemma type_borrow_mut_end E L π κ l (rt : Type) (ty : type rt) (r : place_rfn rt) b2 bmin T:
    (** Check that the place is owned in a way which allows borrows *)
    ⌜bor_kind_mut_borrowable b2⌝ ∗
    ⌜lctx_bor_kind_incl E L (Uniq κ inhabitant) bmin⌝ ∗
    (** The lifetime at which we borrow still needs to be alive *)
    ⌜lctx_lft_alive E L κ⌝ ∗
    (** Then, the place becomes blocked *)
    (∀ γ, T γ (BlockedLtype ty κ) (PlaceGhost γ))
    ⊢ typed_borrow_mut_end π E L κ l ty (r) b2 bmin T.
  Proof.
    simpl. iIntros "(%Hbor & %Hincl & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hna #Hincl0 Hl Hcred".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iPoseProof ("Hcl_L" with "HL") as "HL".
    destruct b2 eqn:Hmin.
    - (* owned *)
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcreda & (%r' & Hrfn & Hb))".
      iDestruct "CTX" as "(LFT & TIME & LLFT)".
      iMod (fupd_mask_subseteq lftE) as "Hcl_m"; first done.
      iMod (gvar_alloc r') as (γ) "[Hauth Hobs]".
      iMod (bor_create lftE κ (∃ r', gvar_auth γ r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r') with "LFT [Hauth Hb]") as "[Hb Hinh]"; first solve_ndisj.
      { iPoseProof (maybe_later_mono with "Hb") as "Hb". iNext. eauto with iFrame. }
      iMod "Hcl_m" as "_".
      iModIntro. iExists γ, ly. iFrame "Hb HL Hna Hlb Hsc".
      iSplitL "Hobs Hrfn".
      { destruct r.
        - iDestruct "Hrfn" as "->". done.
        - simpl. iExists _, _. iFrame. done. }
      iSplitR; first done.
      iSplitL "Hinh Hcred Hcreda".
      { rewrite ltype_own_blocked_unfold /blocked_lty_own.
        iExists ly. iSplitR; first done. iSplitR; first done. iSplitR; first done.
        iFrame "Hlb Hcreda". iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
        iIntros "Hdead". iMod ("Hinh" with "Hdead") as "Hinh".
        iApply (lc_fupd_add_later with "Hcred1").
        iNext. done. }
      iSplitR.
      { iSplit.
        + iApply ofty_blocked_place_cond_ty. iIntros (?). destruct bmin; simpl; done.
        + destruct bmin; simpl; done.
      }
      iApply "HT".
    - (* shared bor is contradictory *)
      destruct bmin; done.
    - (* mutable bor: reborrow *)
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcreda & Hrfn & Hb)".

      iDestruct "CTX" as "(LFT & TIME & LLFT)".
      iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iMod "Hb".
      iMod (pinned_bor_rebor_full _ _ κ with "LFT [] [Hcred1 Hcred2] Hb") as "(Hb & Hcl_b)"; [done | | | ].
      { iPoseProof (bor_kind_incl_trans with "Hincl Hincl0") as "?"; done. }
      { iEval (rewrite lc_succ). iFrame. }

      simpl.
      iPoseProof (place_rfn_interp_mut_iff with "Hrfn") as "(%r' & Hrfn & Hrfn')".
      iMod (gvar_alloc r') as (γ') "[Hauth' Hobs']".

      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (Hal with "HE HL") as "(%q' & Htok & Htok_cl)"; first done.

      (* put in the refinement *)
      iMod (bor_create lftE κ (∃ r', gvar_obs γ r' ∗ gvar_auth γ' r') with "LFT [Hrfn Hauth']") as "(Hrfn & Hcl_rfn)"; first done.
      { iNext. iExists _. iFrame. }
      iMod (bor_combine with "LFT Hb Hrfn") as "Hb"; first done.

      iMod (bor_acc_cons with "LFT Hb Htok") as "(Hb & Hcl_b')"; first done.
      iDestruct "Hb" as "((%r1 & >Hauth1 & Hb1) & (%r2 & >Hobs1 & >Hauth2))".
      iPoseProof (gvar_agree with "Hauth2 Hobs'") as "->".
      iPoseProof (gvar_agree with "Hauth1 Hobs1") as "->".
      set (bor' := ((∃ r' : rt, gvar_auth γ' r' ∗ (|={lftE}=> l ↦: ty_own_val ty π r')))%I).
      iMod ("Hcl_b'" $! bor' with "[Hobs1 Hauth1] [Hauth2 Hb1]") as "(Ha & Htok)".
      { iNext. iIntros "Ha".
        iDestruct "Ha" as "(%r'' & Hauth & Ha)".
        iMod (gvar_update r'' with "Hauth1 Hobs1") as "(Hauth1 & Hobs1)".
        iModIntro. iNext. iSplitL "Ha Hauth1"; eauto with iFrame. }
      { iNext. iExists _. iFrame. }
      iMod ("Htok_cl" with "Htok") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iMod "Hcl_F" as "_".
      iModIntro. iExists γ', _. iSpecialize ("HT" $! γ').
      iFrame. iSplitL "Hobs' Hrfn'".
      { destruct r; simpl.
        - iDestruct "Hrfn'" as "->". iFrame.
        - iExists _, _. iFrame. done. }
      iR. iR. iR.
      (* we've got some leftover credits here *)
      iSplitL "Hcl_b Hcl_rfn Hcreda".
      { rewrite ltype_own_blocked_unfold /blocked_lty_own.
        iExists _. iR. iR. iR. iR.
        iDestruct "Hcreda" as "($ & $)".
        iIntros "#Hdead". iMod ("Hcl_b" with "Hdead") as "$".
        iMod ("Hcl_rfn" with "Hdead") as "Hrfn".
        iDestruct "Hrfn" as "(%r'' & >Hobs & >Hauth)".
        iMod (gvar_obs_persist with "Hauth") as "Hauth".
        iModIntro. iExists _, _. iFrame. done. }
      iSplitL; first last. { destruct bmin; done. }
      iApply ofty_blocked_place_cond_ty.
      iIntros (?). done.
  Qed.
  Global Instance type_borrow_mut_inst E L π κ l rt (ty : type rt) r b2 bmin :
    TypedBorrowMutEnd π E L κ l ty (r) b2 bmin | 20 :=
    λ T, i2p (type_borrow_mut_end E L π κ l rt ty r b2 bmin T).

  Lemma type_borrow_shr E L T T' e κ orty π :
    IntoPlaceCtx π E e T' →
    T' L (λ L1 K l, find_in_context (FindLoc l π) (λ '(existT rto (lt1, r1, b)),
      (* place *)
      typed_place π E L1 l lt1 r1 b b K (λ L2 κs (l2 : loc) (b2 bmin : bor_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) strong weak,
      (* stratify *)
      stratify_ltype_unblock π E L2 StratRefoldOpened l2 lt2 ri2 b2 (λ L3 R rt2' lt2' ri2',
      (* certify that this stratification is allowed, or otherwise commit to a strong update *)
      prove_place_cond E L3 bmin lt2 lt2' (λ upd,
      prove_place_rfn_cond (if upd is ResultWeak _ then true else false) bmin ri2 ri2' (
      (* needs to be a type *)
      (* we require unblocking to have happened before. TODO: maybe also in a nested way? *)
      ∃ ty2 ri2'', ⌜ri2' = #ri2''⌝ ∗
      (* TODO: drop this assumption to support borrowing of partially shr-blocked places / find some other formulation *)
      mut_eqltype E L3 lt2' (◁ ty2) (
        typed_option_map (option_combine orty (match bmin with Owned _ => Some () | _ => None end))
          (λ '(rty, _) (T : sigT (λ rt, type rt * rt * access_result rt2' rt)%type → _),
          find_in_context (FindNamedLfts) (λ M, named_lfts M -∗
          li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt3 ty3),
            ∃ ri3, weak_subtype E L3 ri2'' ri3 ty2 ty3 (T (existT rt3 (ty3, ri3, ResultStrong)))
          )))
          (existT rt2' (ty2, ri2'', access_result_refl)) (λ '(existT rt4 (ty4, ri4, upd')),
          (* finish borrow *)
          typed_borrow_shr_end π E L3 κ l2 ty4 (#ri4) b2 bmin (λ (lt5 : ltype rt4) (r5 : place_rfn rt4),
          (* return toks *)
          typed_place_finish π E L3 strong weak (access_result_meet upd upd') R (llft_elt_toks κs) l b lt5 r5
            (λ L4, T L4 (val_of_loc l2) rt4 ty4 (#ri4)))))))))))
    ⊢ typed_borrow_shr π E L e κ orty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL Hna HΦ".
    iApply (HT' with "CTX HE HL Hna HT'").
    iIntros (L1 K l) "HL Hna". iDestruct 1 as ([rt1 ([ty1 r1] & ?)]) "[Hl HP]".
    iApply ("HP" $! _ F with "[//] [//] CTX HE HL [] Hl").
    { iApply bor_kind_incl_refl. }
    iIntros (L2 κs l2 b2 bmin rti tyli ri strong weak) "#Hincl1 Hl2 Hs HT HL".
    (* bring the place type in the right shape *)
    iApply ("HΦ").
    iPoseProof ("HT" with "[//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step.
    iMod "Hb" as "(%L3 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hcond & Hrcond & HT)".
    iDestruct "HT" as (ty2 ri2') "(-> & %Heq & HT)".
    (* needs two logical steps: one for stratification and one for initiating sharing.
       - that means: creating a reference will now be two skips.
       - this shouldn't be very problematic. *)
    iApply (logical_step_wand with "Hl2").
    iIntros "!>(Hl2 & HR)".
    iApply fupd_logical_step.
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "[Hvs HL]"; [solve_ndisj | apply Heq | ].
    iMod ("Hvs" with "Hl2") as "Hl2".
    iPoseProof (ltype_own_has_layout with "Hl2") as "(%ly & %Halg & %Hly)".


    (* eliminate the optional subtyping *)
    iPoseProof (typed_option_map_elim_fupd _ _ _ (λ '(existT rt4 (ty4, r4, upd')),
      ltype_incl b2 (#ri2') (#r4) (◁ ty2) (◁ ty4) ∗ typed_place_cond bmin (◁ ty2) (◁ ty4) (#ri2') (#r4) )%I with "HT [] [] HL") as ">(%ra & HL & Hincl & Hbor)"; first done.
    { iIntros ([rst ?]) "%Heqo HL Ha".
      rewrite /FindNamedLfts.
      iDestruct "Ha" as "(%M & HM & HT)". iPoseProof ("HT" with "HM") as "Ha".
      rewrite /interpret_rust_type_goal. iDestruct "Ha" as "(%rt3 & %ty3 & %r3 & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iModIntro. iPoseProof "Hincl" as "(%Hsteq & _)".
      iExists (existT _ (ty3, r3, ResultStrong)). iFrame "HL HT".
      destruct bmin; [ | destruct orty; done.. ].
      iSplitR; last done.
      destruct b2; [ | done..]. iApply (type_ltype_incl_owned_in with "Hincl"). }
    { iSplitR; first iApply ltype_incl_refl. iSplitL; first iApply typed_place_cond_ty_refl_ofty.
      iApply typed_place_cond_rfn_refl. }
    destruct ra as [rt4 [[ty4 r4] upd']].
    iDestruct "Hincl" as "(#Hincl & #Hcond2)".

    iMod (ltype_incl_use with "Hincl Hl2") as "Hl2"; first done.
    iPoseProof (ltype_incl_syn_type with "Hincl") as "%Hst_eq".
    iPoseProof ("Hbor" $! F with "[//] [//] [//] CTX HE HL Hna [//] Hl2") as ">Hb".
    iModIntro. iApply logical_step_fupd. iApply (logical_step_wand with "Hb").
    iIntros "Ha !> Hcred".
    iDestruct ("Ha" with "Hcred") as ">(%ly' & %lt' & %r' & Hrfn & Hshr & %Halg' & Hlb & Hsc & Hblocked & Hcond' & HL & Hna & HT)".
    assert (ly' = ly) as ->. { move: Hst_eq Halg' Halg. simp_ltypes => -> ??. by eapply syn_type_has_layout_inj. }
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heq.

    iPoseProof (typed_place_finish_elim with "HT") as "[Hweak | Hstrong]".
    - (* weak update *)
      iDestruct "Hweak" as "(%weak' & %Heq' & -> & %Hmeet & HT)".
      iDestruct "Hs" as "[_ Hs]". subst rt4.
      destruct upd; last done. destruct upd'; last done. simpl in Hmeet.
      (*rewrite (UIP_refl _ _ Heq1) in Hmeet. simpl in Hmeet. *)
      iMod ("Hs" with "[] Hblocked [Hcond Hcond' Hrcond]") as "(Hl & Hcond & Htoks & HR')".
      { iApply bor_kind_incl_refl. }
      { iApply (typed_place_cond_trans with "[$Hcond $Hrcond]").
        iApply ltype_eq_place_cond_trans; first done.
        (*iApply ltype_eq_place_cond_trans. *)
        (* want: the place cond holds trivially, because we are Owned if they are different *)
        iApply (typed_place_cond_trans with "[Hcond2] Hcond'").
        done. }
      cbn.
      iDestruct ("HT" with "Hl HR'") as "HT".
      iMod ("HT" with "[//] HE HL [$HR $Htoks]") as "(%L4 & HL & HT)".
      iModIntro. iExists L4, _, _, _, _, ly. iFrame.
      iSplitR; done.
    - (* strong update *) iDestruct "Hs" as "[Hs _]".
      iPoseProof (typed_place_cond_syn_type_eq with "Hcond'") as "%Heq'".
      iDestruct "Hstrong" as "(%strong' & -> & %Hw & HT)".
      iMod ("Hs" with "Hblocked [Hcond Hcond']") as "(Hl & Hcond & HR')".
      { iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "%Heq2".
        move: Hst_eq. simp_ltypes => Hst_eq.
        simp_ltypes. iPureIntro. simp_ltypes. congruence. }
      simpl.
      iDestruct ("HT" with "Hl HR'") as "HT".
      iMod ("HT" with "[//] HE HL HR") as "(%L4 & HL & HT)".
      iModIntro. iExists L4, _, _, _, _, ly. iFrame.
      iSplitR; done.
  Qed.

  Lemma type_borrow_shr_end_owned E L π κ l {rt : Type} (ty : type rt) (r : place_rfn rt) bmin wl T:
    ⌜lctx_bor_kind_incl E L (Uniq κ inhabitant) bmin⌝ ∗
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜Forall (lctx_lft_alive E L) ty.(ty_lfts)⌝ ∗
    (T (ShrBlockedLtype ty κ) r)
    ⊢ typed_borrow_shr_end π E L κ l ty r (Owned wl) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hal & %Hal' & HT)".
    iIntros (F ???) "#[LFT TIME] #HE HL Hna #Hincl0 Hl".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iMod (lctx_lft_alive_tok_noend (κ ⊓ (lft_intersect_list ty.(ty_lfts))) with "HE HL") as "Ha"; first done.
    { eapply lctx_lft_alive_intersect; first done. by eapply lctx_lft_alive_intersect_list. }
    iDestruct "Ha" as "(%q' & Htok & HL & Hcl_L')".
    (* owned *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & %r' & Hrfn & Hl)".
    iMod (maybe_use_credit with "Hcred Hl") as "(Hcred & Hat & (%v & Hl & Hv))"; first done.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (bor_create lftE κ (∃ v, l ↦ v ∗ v ◁ᵥ{π} r' @ ty)%I with "LFT [Hv Hl]") as "(Hb & Hinh)"; first done.
    { eauto with iFrame. }
    iMod "Hcl_F" as "_".
    iPoseProof (place_rfn_interp_owned_share' with "Hrfn") as "#Hrfn'".
    iPoseProof (ty_share _ F with "[$LFT $TIME] Htok [//] [//] Hlb Hb") as "Hshr"; first done.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hshr").
    iApply (logical_step_intro_maybe with "Hat").
    iModIntro. iIntros "Hcred' !> (#Hshr & Htok) !> Hcred1".
    iMod ("Hcl_L'" with "Htok HL") as "HL".
    iPoseProof ("Hcl_L" with "HL") as "HL".
    iExists ly, (ShrBlockedLtype ty κ), _. iFrame "Hrfn' Hshr Hlb Hsc HL Hna". iSplitR; first done.
    iSplitL "Hcred' Hinh Hcred1".
    { iModIntro. rewrite ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iExists ly. iFrame "Hlb Hsc". iSplitR; first done. iSplitR; first done.
      iExists r'. iSplitR; first done. iFrame "Hshr Hcred'".
      iIntros "Hdead". iMod ("Hinh" with "Hdead"). iApply (lc_fupd_add_later with "Hcred1").
      iNext. eauto with iFrame. }
    iModIntro.
    iSplitR.
    { destruct bmin; simpl; [done | done | ].
      iSplit; last done.
      iExists eq_refl. cbn.
      simp_ltypes. iSplitR. { iIntros (??). iApply ltype_eq_refl. }
      iApply imp_unblockable_shorten'; first done.
      iApply shr_blocked_imp_unblockable.
    }
    iApply "HT".
  Qed.
  Global Instance type_borrow_shr_owned_inst E L π κ l rt (ty : type rt) r wl bmin :
    TypedBorrowShrEnd π E L κ l ty r (Owned wl) bmin | 20 :=
    λ T, i2p (type_borrow_shr_end_owned E L π κ l ty r bmin wl T).

  Lemma type_borrow_shr_end_uniq E L π κ l {rt : Type} (ty : type rt) (r : place_rfn rt) bmin κ' γ T:
    ⌜lctx_bor_kind_incl E L (Uniq κ inhabitant) bmin⌝ ∗
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜Forall (lctx_lft_alive E L) ty.(ty_lfts)⌝ ∗
    (T (ShrBlockedLtype ty κ) r)
    ⊢ typed_borrow_shr_end π E L κ l ty r (Uniq κ' γ) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hal & %Hal' & HT)".
    (* basically, we do the same as for creating a mutable reference, but then proceed to do sharing *)
    iIntros (F ???) "#(LFT & TIME & LLCTX) #HE HL Hna #Hincl0 Hl".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iMod (lctx_lft_alive_tok_noend (κ ⊓ (lft_intersect_list ty.(ty_lfts))) with "HE HL") as "Ha"; first done.
    { eapply lctx_lft_alive_intersect; first done. by eapply lctx_lft_alive_intersect_list. }
    iDestruct "Ha" as "(%q' & Htok & HL & Hcl_L')".
    (* owned *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & Hrfn & Hl)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hl".
    iDestruct "Hcred" as "((Hcred1 & Hcred2 & Hcred) & Hat)".
    iMod (pinned_bor_rebor_full _ _ κ with "LFT [] [Hcred1 Hcred2] Hl") as "(Hl & Hl_cl)"; first done.
    { iPoseProof (bor_kind_incl_trans with "Hincl Hincl0") as "Hincl2". done. }
    { iSplitL "Hcred1"; iFrame. }
    iMod "Hcl_F" as "_".

    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
    iMod (bor_exists_tok with "LFT Hl Htok1") as "(%r' & Hl & Htok1)"; first done.
    iMod (bor_sep with "LFT Hl") as "(Hauth & Hl)"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (bor_fupd_later with "LFT Hl Htok1") as "Ha"; [done.. | ].
    iApply (lc_fupd_add_later with "Hcred1").
    iNext. iMod ("Ha") as "(Hl & Htok1)".

    iMod (place_rfn_interp_mut_share' with "LFT Hrfn Hauth Htok1") as "(#Hrfn & Hmut & Hauth & Htok1)"; first done.
    iPoseProof (ty_share _ F with "[$LFT $TIME $LLCTX] [Htok1 Htok2] [] [] Hlb Hl") as "Hstep".
    { done. }
    { rewrite -lft_tok_sep. iFrame. }
    { done. }
    { done. }
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_atime with "Hat").
    iModIntro. iIntros "Hcred' Hat". iModIntro.
    iIntros "(#Hshr & Htok) Hcred1".
    iExists _, _, _. iFrame.
    iFrame. iR. iR. iR.
    rewrite lft_tok_sep.
    iMod ("Hcl_L'" with "Htok HL") as "HL".
    iPoseProof ("Hcl_L" with "HL") as "$".

    iDestruct "Hmut" as ">Hmut". iR. iR.
    iSplitL "Hauth Hmut Hat Hcred' Hl_cl".
    { rewrite ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iExists ly. iR. iR. iR. iR. iExists _. iR.
      iFrame. done. }
    iSplitL. { iApply ofty_shr_blocked_place_cond_ty. iModIntro. iIntros (?). done. }
    destruct bmin; done.
  Qed.
  Global Instance type_borrow_shr_uniq_inst E L π κ l rt (ty : type rt) r κ' γ bmin :
    TypedBorrowShrEnd π E L κ l ty r (Uniq κ' γ) bmin | 20 :=
    λ T, i2p (type_borrow_shr_end_uniq E L π κ l ty r bmin κ' γ T).

  Lemma type_borrow_shr_end_shared E L π κ l {rt : Type} (ty : type rt) (r : place_rfn rt) κ' bmin T:
    ⌜lctx_bor_kind_incl E L (Shared κ) bmin⌝ ∗
    (T (◁ ty) r)
    ⊢ typed_borrow_shr_end π E L κ l ty r (Shared κ') bmin T.
  Proof.
    simpl. iIntros "(%Hincl & HT)".
    iIntros (F ???) "#[LFT TIME] #HE HL Hna #Hincl0 #Hl".
    iPoseProof (lctx_bor_kind_incl_acc with "HE HL") as "#Hincl"; first apply Hincl.
    iModIntro. iApply logical_step_intro. iIntros "Hcred".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hsc & Hlb & %r' & Hrfn & #Hl)".
    iDestruct "Hl" as "-#Hl". iMod (fupd_mask_mono with "Hl") as "#Hl"; first done.
    iExists ly, (◁ ty)%I, _.
    iAssert (κ ⊑ κ')%I as "Hinclκ".
    { iApply (bor_kind_incl_trans with "Hincl Hincl0"). }
    iPoseProof (ty_shr_mono with "Hinclκ Hl") as "$".
    iR. iFrame "Hlb Hsc". iModIntro. iR.
    iSplitR. { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iR. iR. iFrame "∗ #". iExists _. iR. done. }
    iFrame. iSplitL; first iApply typed_place_cond_ty_refl_ofty.
    iApply typed_place_cond_rfn_refl.
  Qed.
  Global Instance type_borrow_shr_end_shared_inst E L π κ l rt (ty : type rt) r κ' bmin :
    TypedBorrowShrEnd π E L κ l ty r (Shared κ') bmin | 20 :=
    λ T, i2p (type_borrow_shr_end_shared E L π κ l ty r κ' bmin T).

  (** statements *)
  Lemma type_goto E L π b fn R s ϝ :
    fn.(rf_fn).(f_code) !! b = Some s →
    typed_stmt π E L s fn R ϝ
    ⊢ typed_stmt π E L (Goto b) fn R ϝ.
  Proof.
    iIntros (HQ) "Hs". iIntros (?) "#LFT #HE HL Hna Hcont". iApply wps_goto => //.
    iModIntro. iIntros "Hcred". by iApply ("Hs" with "LFT HE HL Hna").
  Qed.

  (** Goto a block if we have already proved it with a particular precondition [P]. *)
  (* This is not in Lithium goal shape, but that's fine since it is only manually applied by automation. *)
  Lemma type_goto_precond E L π P b fn R ϝ :
    (* TODO maybe we should also stratify? *)
    typed_block π P b fn R ϝ ∗ prove_with_subtype E L false ProveDirect (P E L) (λ L' _ R, R -∗⌜L = L'⌝ ∗ True (* TODO maybe relax *))
    ⊢ typed_stmt π E L (Goto b) fn R ϝ.
  Proof.
    iIntros "(Hblock & Hsubt)". iIntros (?) "#CTX #HE HL Hna Hcont".
    iMod ("Hsubt" with "[] [] CTX HE HL") as "(%L' & % & %R2 & >(HP & HR2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "HR2") as "(<- & _)".
    by iApply ("Hblock" with "CTX HE HL Hna HP").
  Qed.

  Lemma typed_block_rec π fn R P b ϝ s :
    fn.(rf_fn).(f_code) !! b = Some s →
    (□ (∀ E L, (□ typed_block π P b fn R ϝ) -∗ P E L -∗ typed_stmt π E L s fn R ϝ))
    ⊢ typed_block π P b fn R ϝ.
  Proof.
    iIntros (Hs) "#Hb". iLöb as "IH".
    iIntros (? E L) "#CTX #HE HL Hna HP Hcont".
    iApply wps_goto => //=. iNext. iIntros "Hcred".
    by iApply ("Hb" with "IH HP CTX HE HL Hna").
  Qed.

  (** current goal: Goto.
     Instead of just jumping there, we can setup an invariant [P] on ownership and the lifetime contexts.
     Then instead prove: wp of the block, but in the context we can persistently assume the WP of the goto with the same invariant already. *)
  (* Note: these need to be manually applied. *)
  Lemma typed_goto_acc E L π fn R P b ϝ s :
    fn.(rf_fn).(f_code) !! b = Some s →
    (* TODO maybe also stratify? *)
    prove_with_subtype E L false ProveDirect (P E L) (λ L' _ R2, R2 -∗
      ⌜L' = L⌝ ∗ (* TODO maybe relax if we have a separate condition on lifetime contexts *)
      □ (∀ E L, (□ typed_block π P b fn R ϝ) -∗ P E L -∗ typed_stmt π E L s fn R ϝ))
    ⊢ typed_stmt π E L (Goto b) fn R ϝ.
  Proof.
    iIntros (Hlook) "Hsubt". iIntros (?) "#CTX #HE HL Hna Hcont".
    iMod ("Hsubt" with "[] [] CTX HE HL") as "(%L' & % & %R2 & >(Hinv &HR2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "HR2") as "(-> & Hrec)".
    iApply (typed_block_rec with "Hrec CTX HE HL Hna Hinv"); done.
  Qed.

  Lemma type_assert E L e s fn π R ϝ :
    typed_val_expr π E L e (λ L' v rt ty r, typed_assert π E L' v ty r s fn R ϝ)
    ⊢ typed_stmt π E L (assert{BoolOp}: e; s) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hna Hcont". wps_bind.
    iApply ("He" with "CTX HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv Hs".
    iDestruct ("Hs" with "CTX HE HL Hna Hv") as (?) "(HL & Hna & Hs)".
    iApply wps_assert_bool; [done.. | ]. iIntros "!> Hcred". by iApply ("Hs" with "CTX HE HL Hna").
  Qed.

  Lemma type_if E L π e s1 s2 fn R join ϝ :
    typed_val_expr π E L e (λ L' v rt ty r, typed_if E L' v (v ◁ᵥ{π} r @ ty)
          (typed_stmt π E L' s1 fn R ϝ) (typed_stmt π E L' s2 fn R ϝ))
    ⊢ typed_stmt π E L (if{BoolOp, join}: e then s1 else s2) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hna Hcont". wps_bind.
    iApply ("He" with "CTX HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv Hs".
    iDestruct ("Hs" with "Hv") as "(%b & % & Hs)".
    iApply wps_if_bool; [done|..]. iIntros "!> Hcred". by destruct b; iApply ("Hs" with "CTX HE HL Hna").
  Qed.

  Lemma type_switch E L π it e m ss def fn R ϝ:
    typed_val_expr π E L e (λ L' v rt ty r, typed_switch π E L' v rt ty r it m ss def fn R ϝ)
    ⊢ typed_stmt π E L (Switch it e m ss def) fn R ϝ.
  Proof.
    iIntros "He" (?) "#CTX #HE HL Hna Hcont".
    have -> : (Switch it e m ss def) = (W.to_stmt (W.Switch it (W.Expr e) m (W.Stmt <$> ss) (W.Stmt def)))
      by rewrite /W.to_stmt/= -!list_fmap_compose list_fmap_id.
    iApply tac_wps_bind; first done.
    rewrite /W.to_expr /W.to_stmt /= -list_fmap_compose list_fmap_id.

    iApply ("He" with "CTX HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv Hs".
    iDestruct ("Hs" with "Hv") as (z Hn) "Hs".
    iAssert (⌜∀ i : nat, m !! z = Some i → is_Some (ss !! i)⌝%I) as %?. {
      iIntros (i ->). iDestruct "Hs" as (s ->) "_"; by eauto.
    }
    iApply wps_switch; [done|done|..]. iIntros "!> Hcred".
    destruct (m !! z) => /=.
    - iDestruct "Hs" as (s ->) "Hs". by iApply ("Hs" with "CTX HE HL Hna").
    - by iApply ("Hs" with "CTX HE HL Hna").
  Qed.

  Lemma type_exprs E L s e fn R π ϝ :
    (typed_val_expr π E L e (λ L' v rt ty r, v ◁ᵥ{π} r @ ty -∗ typed_stmt π E L' s fn R ϝ))
    ⊢ typed_stmt π E L (ExprS e s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hna Hcont". wps_bind.
    iApply ("Hs" with "CTX HE HL Hna"). iIntros (L' v rt ty r) "HL Hna Hv Hs".
    iApply wps_exprs. iApply step_fupd_intro => //. iIntros "!> Hcred".
    by iApply ("Hs" with "Hv CTX HE HL Hna").
  Qed.

  Lemma type_skips E L s fn R π ϝ :
    (|={⊤}[∅]▷=> (£1 -∗ typed_stmt π E L s fn R ϝ)) ⊢ typed_stmt π E L (SkipS s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hna Hcont".
    iApply wps_skip. iApply (step_fupd_wand with "Hs"). iIntros "Hs Hcred".
    by iApply ("Hs" with "Hcred CTX HE HL Hna").
  Qed.

  Lemma type_skips' E L s fn R π ϝ :
    typed_stmt π E L s fn R ϝ ⊢ typed_stmt π E L (SkipS s) fn R ϝ.
  Proof.
    iIntros "Hs". iApply type_skips. iApply step_fupd_intro; first done.
    iIntros "!> Hcred". done.
  Qed.

  Lemma typed_stmt_annot_skip {A} π E L (a : A) s fn R ϝ :
    typed_stmt π E L s fn R ϝ ⊢ typed_stmt π E L (annot: a; s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hna Hcont".
    iApply wps_annot. iApply step_fupd_intro; first done.
    iIntros "!> _". by iApply ("Hs" with "CTX HE HL Hna").
  Qed.
  Lemma typed_stmt_annot_credits `{!typeGS Σ} π E L {A} (a : A) s rf R ϝ n :
    atime n -∗
    (atime (S n) -∗ £ (S (num_laters_per_step n)) -∗ typed_stmt π E L s rf R ϝ) -∗
    typed_stmt π E L (annot: a; s) rf R ϝ.
  Proof.
    iIntros "Hat HT".
    iIntros (?) "#CTX #HE HL Hna Hcont".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (derived.wps_annot_credits with "[] Hat Hp").
    { iDestruct "CTX" as "(_ & $ & _)". }
    iNext. iIntros "Hcred Hat".
    rewrite Nat.add_0_r.
    by iApply ("HT" with "Hat Hcred CTX HE HL Hna").
  Qed.

  Lemma typed_expr_assert_type π E L n sty v {rt} (ty : type rt) r T :
    (∃ lfts, named_lfts lfts ∗
      (named_lfts lfts -∗ li_tactic (interpret_rust_type_goal lfts sty) (λ '(existT _ ty2),
        ∃ r2, subsume_full E L false (v ◁ᵥ{π} r @ ty) (v ◁ᵥ{π} r2 @ ty2) (λ L2 R2, R2 -∗ T L2 v _ ty2 r2))))%I
    ⊢ typed_annot_expr π E L n (AssertTypeAnnot sty) v (v ◁ᵥ{π} r @ ty) T.
  Proof.
    iIntros "(%lfts & Hnamed & HT)". iPoseProof ("HT" with "Hnamed") as "HT".
    rewrite /interpret_rust_type_goal. iDestruct "HT" as "(%rt2 & %ty2 & %r2 & HT)".
    iIntros "#CTX #HE HL Hv".
    iApply step_fupdN_intro; first done. iNext.
    iMod ("HT" with "[] [] CTX HE HL Hv") as "(%L2 & %R2 & >(Hv & HR2) & HL & HT)"; [done.. | ].
    iModIntro. iExists _, _, _, _. iFrame. by iApply ("HT" with "HR2").
  Qed.
  Global Instance typed_expr_assert_type_inst π E L n sty v {rt} (ty : type rt) r :
    TypedAnnotExpr π E L n (AssertTypeAnnot sty) v (v ◁ᵥ{π} r @ ty) :=
    λ T, i2p (typed_expr_assert_type π E L n sty v ty r T).

  Lemma typed_expr_get_lft_names π E L n tree v {rt} (ty : type rt) r T :
    (∃ lfts, named_lfts lfts ∗
      trigger_tc (GetLftNames ty lfts tree) (λ lfts',
        (* simplify the updated map *)
        li_tactic (simplify_lft_map_goal lfts') (λ lfts',
          named_lfts lfts' -∗ T L v _ ty r)))
    ⊢ typed_annot_expr π E L n (GetLftNamesAnnot tree) v (v ◁ᵥ{π} r @ ty) T.
  Proof.
    rewrite /simplify_lft_map_goal.
    iIntros "(%lfts & Hnamed & %lfts' & %_ & %lfts'' & _ & HT)".
    iPoseProof (named_lfts_update _ lfts'' with "Hnamed") as "Hnamed".
    iIntros "? ? HL Hv". iApply step_fupdN_intro; first done. iNext.
    iModIntro. iExists L, _, _, _. iFrame. by iApply "HT".
  Qed.
  Global Instance typed_expr_get_lft_names_inst π E L n tree v {rt} (ty : type rt) r :
    TypedAnnotExpr π E L n (GetLftNamesAnnot tree) v (v ◁ᵥ{π} r @ ty) :=
    λ T, i2p (typed_expr_get_lft_names π E L n tree v ty r T).

  (** ** Handling of lifetime-related annotations *)
  (** Endlft triggers *)
  (** Instance for returning lifetime tokens [Inherit κ1 InheritDynIncl (llft_elt_toks κs)] *)
  Lemma typed_on_endlft_trigger_dyn_incl E L κs T :
    li_tactic (llctx_release_toks_goal L κs) (λ L', T L')
    ⊢ typed_on_endlft_trigger E L InheritDynIncl (llft_elt_toks κs) T.
  Proof.
    rewrite /llctx_release_toks_goal.
    iIntros "(%L' & %Hrel & Hs)" (F ?) "#HE HL Htoks".
    iMod (llctx_return_elt_toks _ _ L' with "HL Htoks") as "HL"; first done.
    eauto with iFrame.
  Qed.
  Global Instance typed_on_endlft_trigger_dyn_incl_inst E L κs : TypedOnEndlftTrigger E L InheritDynIncl (llft_elt_toks κs) :=
    λ T, i2p (typed_on_endlft_trigger_dyn_incl E L κs T).

  (** Instance for obtaining observations [Inherit κ1 (InheritGhost) ..] *)
  Lemma typed_on_endlft_trigger_ghost E L (P : iProp Σ) T :
    (P -∗ T L)
    ⊢ typed_on_endlft_trigger E L InheritGhost P T.
  Proof.
    iIntros "HT" (F ?) "#HE HL HP".
    iPoseProof ("HT" with "HP") as "HT".
    eauto with iFrame.
  Qed.
  Global Instance typed_on_endlft_trigger_ghost_inst E L (P : iProp Σ) : TypedOnEndlftTrigger E L InheritGhost P :=
    λ T, i2p (typed_on_endlft_trigger_ghost E L P T).

  (** Instance for resolving Rel2 with another observation *)
  (* TODO *)

  (* Currently the thing with static is broken.
    Maybe I should have MaybeInherit that simplifies to the direct proposition if it doesn't have a lifetime. *)

  (* Point: I should still run the endlft hooks *)
  (* TODO *)
  Lemma introduce_with_hooks_maybe_inherit_none E L {K} (k : K) P T :
    introduce_with_hooks E L P T
    ⊢ introduce_with_hooks E L (MaybeInherit None k P) T.
  Proof.
    iIntros "HT" (??) "#HE HL Hinh".
    rewrite /MaybeInherit.
    iMod ("Hinh" with "[//]") as "HP".
    iApply ("HT" with "[//] HE HL HP").
  Qed.
  Global Instance introduce_with_hooks_maybe_inherit_none_inst E L {K} (k : K) P :
    IntroduceWithHooks E L (MaybeInherit None k P) := λ T, i2p (introduce_with_hooks_maybe_inherit_none E L k P T).

  Lemma introduce_with_hooks_maybe_inherit_some E L {K} (k : K) κ P T :
    introduce_with_hooks E L (Inherit κ k P) T
    ⊢ introduce_with_hooks E L (MaybeInherit (Some κ) k P) T.
  Proof.
    iIntros "HT" (??) "#HE HL Hinh".
    rewrite /MaybeInherit. iApply ("HT" with "[//] HE HL Hinh").
  Qed.
  Global Instance introduce_with_hooks_maybe_inherit_some_inst E L {K} (k : K) κ P :
    IntroduceWithHooks E L (MaybeInherit (Some κ) k P) := λ T, i2p (introduce_with_hooks_maybe_inherit_some E L k κ P T).

  Lemma introduce_with_hooks_inherit E L {K} (k : K) κ P T :
    find_in_context (FindOptLftDead κ) (λ dead,
      if dead
      then typed_on_endlft_trigger E L k P T
      else Inherit κ k P -∗ T L)
    ⊢ introduce_with_hooks E L (Inherit κ k P) T.
  Proof.
    rewrite /FindOptLftDead/=. iIntros "(%dead & Hdead & HT)".
    simpl in *. destruct dead.
    - iIntros (??) "#HE HL Hinh".
      rewrite /Inherit. iMod ("Hinh" with "[//] Hdead") as "HP".
      iApply ("HT" with "[//] HE HL HP").
    - iIntros (??) "#HE HL Hinh".
      iExists L. iFrame. by iApply ("HT" with "Hinh").
  Qed.
  Global Instance introduce_with_hooks_inherit_inst E L {K} (k : K) κ P :
    IntroduceWithHooks E L (Inherit κ k P) := λ T, i2p (introduce_with_hooks_inherit E L k κ P T).

  (** StartLft *)
  Lemma type_startlft E L (n : string) sup_lfts s fn R π ϝ :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookups_nofail_goal M sup_lfts) (λ κs,
      ∀ κ, named_lfts (named_lft_update n κ M) -∗
      (* add a credit -- will be used by endlft *)
      introduce_with_hooks E ((κ ⊑ₗ{0%nat} κs) :: L) (£ 1) (λ L2,
      typed_stmt π E L2 s fn R ϝ)))
    ⊢ typed_stmt π E L (annot: (StartLftAnnot n sup_lfts); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %κs & %Hlook & Hcont)".
    iIntros (?) "#(LFT & TIME & LLCTX) #HE HL Hna Hcont'".
    iApply wps_annot => /=.
    iMod (llctx_startlft _ _ κs with "LFT LLCTX HL") as (κ) "HL"; [solve_ndisj.. | ].
    iApply step_fupd_intro; first solve_ndisj. iNext. iIntros "Hcred".
    iApply fupd_wps.
    iMod ("Hcont" with "[Hnamed] [] HE HL Hcred") as "(%L2 & HL & HT)"; [ | done | ].
    { iApply named_lfts_update. done. }
    by iApply ("HT" with "[$LFT $TIME $LLCTX] HE HL Hna").
  Qed.

  (** Alias lifetimes: like startlft but without the atomic part *)
  Lemma type_alias_lft E L (n : string) sup_lfts s fn R π ϝ :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookups_nofail_goal M sup_lfts) (λ κs,
      ∀ κ, named_lfts (named_lft_update n κ M) -∗ typed_stmt π E ((κ ≡ₗ κs) :: L) s fn R ϝ))
    ⊢ typed_stmt π E L (annot: (AliasLftAnnot n sup_lfts); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %κs & %Hlook & Hcont)".
    iIntros (?) "#(LFT & TIME & LLCTX) #HE HL Hna Hcont'".
    iApply wps_annot => /=.
    set (κ := lft_intersect_list κs).
    iAssert (llctx_interp ((κ ≡ₗ κs) :: L))%I with "[HL]" as "HL".
    { iFrame "HL". iSplit; iApply lft_incl_refl. }
    iApply step_fupd_intro; first solve_ndisj. iNext. iIntros "Hcred".
    iApply ("Hcont" $! κ with "[Hnamed] [$LFT $TIME $LLCTX] HE HL Hna").
    { iApply named_lfts_update. done. }
    done.
  Qed.

  (** EndLft *)
  (* TODO: also make endlft apply to local aliases, endlft should just remove them, without triggering anything. *)
  Inductive CtxFoldExtract : Type :=
    | CtxFoldExtractAllInit (κ : lft)
    | CtxFoldExtractAll (κ : lft).
  Lemma type_endlft E L π (n : string) s fn R ϝ :
    (∃ M, named_lfts M ∗
      (* if this lifetime does not exist anymore, this is a nop *)
      li_tactic (compute_map_lookup_goal M n) (λ o,
      match o with
      | Some κ =>
        (* find some credits *)
        prove_with_subtype E L false ProveDirect (£1) (λ L1 _ R2,
        (* find the new llft context *)
        li_tactic (llctx_find_llft_goal L1 κ LlctxFindLftFull) (λ '(_, L2),
        (* simplify the name map *)
        li_tactic (simplify_lft_map_goal (named_lft_delete n M)) (λ M',
        (named_lfts M' -∗ (□ [† κ]) -∗
        (* extract observations from now-dead mutable references *)
        typed_pre_context_fold π E L2 (CtxFoldExtractAllInit κ) (λ L3,
        (* give back credits *)
        introduce_with_hooks E L3 (R2 ∗ £1 ∗ atime 1) (λ L4,
        (* run endlft triggers *)
        typed_on_endlft_pre π E L4 κ (λ L5,
        typed_stmt π E L5 s fn R ϝ)))))))
      | None => named_lfts M -∗ typed_stmt π E L s fn R ϝ
      end))
    ⊢ typed_stmt π E L (annot: (EndLftAnnot n); s) fn R ϝ.
  Proof.
    iIntros "(%M & Hnamed & Hlook)".
    unfold compute_map_lookup_goal.
    iDestruct "Hlook" as (o) "(<- & HT)".
    destruct (M !! n) as [κ | ]; first last.
    { iIntros (?) "#CTX #HE HL Hna Hcont". iApply wps_annot.
      iApply step_fupdN_intro; first done.
      iIntros "!> _". by iApply ("HT" with "Hnamed CTX HE HL Hna"). }
    unfold llctx_find_llft_goal, li_tactic.
    iIntros (?) "#CTX #HE HL Hna Hcont".
    iMod ("HT" with "[] [] CTX HE HL") as "(%L2 & % & %R2 & >(Hc & HR2) & HL & HT)"; [done.. | ].
    iDestruct "HT" as "(%L' & % & %Hkill & Hs)".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%M' & _ & Hs)".
    iPoseProof (llctx_end_llft ⊤ with "HL") as "Ha"; [done | done | apply Hkill | ].
    iApply fupd_wps.
    iMod ("Ha"). iApply (lc_fupd_add_later with "Hc"). iNext. iMod ("Ha") as "(#Hdead & HL)".

    iPoseProof ("Hs" with "[Hnamed] Hdead") as "HT".
    { by iApply named_lfts_update. }
    iPoseProof ("HT" $! ⊤ with "[] [] CTX HE HL") as "Hstep"; [done.. | ].
    rewrite /logical_step.
    iMod ("Hstep") as "(%k & Hat' & Hk)".
    iMod (persistent_time_receipt_0)as "Hp".
    iApply (wps_annot_credits with "[] Hat' Hp").
    { iDestruct "CTX" as "(_ & $ & _)". }
    iModIntro. iNext. iIntros "(Hc1 & Hc) Hat'". rewrite Nat.add_0_r.
    iEval (rewrite additive_time_receipt_succ) in "Hat'".
    iDestruct "Hat'" as "(Hat1 & Hat)".
    iMod ("Hk" with "Hc Hat") as "(%L5 & HL & HT)".

    iMod ("HT" with "[] HE HL [$HR2 $Hc1 $Hat1]") as "(%L6 & HL & HT)"; first done.
    iMod ("HT" with "[] HE HL Hdead") as "(%L7 & HL & HT)".
    { done. }
    by iApply ("HT" with "CTX HE HL Hna").
  Qed.

  (** Dynamic inclusion *)
  Lemma type_dyn_include_lft π E L n1 n2 s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n1) (λ κ1,
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (lctx_lft_alive_count_goal E L κ2) (λ '(κs, L'),
      Inherit κ1 InheritDynIncl (llft_elt_toks κs) -∗
      named_lfts M -∗
      typed_stmt π ((κ1 ⊑ₑ κ2) :: E) L' s fn R ϝ))))
    ⊢ typed_stmt π E L (annot: DynIncludeLftAnnot n1 n2; s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ1 & %Hlook1 & %κ2 & %Hlook2 & Hs)".
    unfold lctx_lft_alive_count_goal.
    iDestruct "Hs" as "(%κs & %L' & %Hal & Hs)".
    iIntros (?) "#(LFT & TIME & LCTX) #HE HL Hna Hcont".
    iMod (lctx_include_lft_sem with "LFT HE HL") as "(HL & #Hincl & Hinh)"; [done.. | ].
    iSpecialize ("Hs" with "Hinh").
    iApply wps_annot. iApply step_fupdN_intro; first done.
    iIntros "!> _".
    iApply ("Hs" with "Hnamed [$] [] HL Hna").
    { iFrame "HE Hincl". }
    done.
  Qed.

  (** ExtendLft *)
  Lemma type_extendlft E L π (n : string) s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n) (λ κ,
      li_tactic (llctx_find_llft_goal L κ LlctxFindLftOwned) (λ '(κs, L'),
      (named_lfts M -∗ typed_stmt π E ((κ ≡ₗ κs) :: L') s fn R ϝ))))
    ⊢ typed_stmt π E L (annot: (EndLftAnnot n); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal /llctx_find_llft_goal.
    iIntros "(%M & Hnamed & %κ & _ & %L' & %κs & %Hfind & Hs)".
    iIntros (?) "#(LFT & TIME & LCTX) #HE HL Hna Hcont".
    iMod (llctx_extendlft_local_owned with "LFT HL") as "HL"; [done.. | ].
    iApply wps_annot. iApply step_fupdN_intro; first done. iIntros "!> _".
    by iApply ("Hs" with "Hnamed [$] HE HL Hna").
  Qed.

  (** CopyLftNameAnnot *)
  Lemma type_copy_lft_name π E L n1 n2 s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (simplify_lft_map_goal (named_lft_update n1 κ2 (named_lft_delete n1 M))) (λ M',
        named_lfts M' -∗ typed_stmt π E L s fn R ϝ)))
    ⊢ typed_stmt π E L (annot: CopyLftNameAnnot n1 n2; s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ2 & _ & Hs)".
    iIntros (?) "#CTX #HE HL Hna Hcont".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%M' & _ & Hs)".
    iApply wps_annot. iApply step_fupdN_intro; first done.
    iIntros "!> _". by iApply ("Hs" with "Hnamed CTX HE HL Hna").
  Qed.

  (** We instantiate the context folding mechanism for unblocking. *)
  Inductive CtxFoldStratify : Type :=
    | CtxFoldStratifyAllInit
    | CtxFoldStratifyAll.

  (* Note: the following two lemmas introduce evars on application and are thus not suitable to be directly applied with Lithium.
    They either need an Ltac oracle, or (this is what we do) use some evar magic below.
  *)
  Definition typed_context_fold_stratify_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_stratify π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R T :
    (* TODO: this needs a different stratification strategy *)
    stratify_ltype_unblock π E L StratRefoldOpened l lt r (Owned false)
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_stratify_interp π) π E L' (CtxFoldStratifyAll) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_stratify_interp π) π E L (CtxFoldStratifyAll) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (? ??) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.

  Lemma typed_context_fold_stratify_init tctx π E L T :
    typed_context_fold (typed_context_fold_stratify_interp π) π E L (CtxFoldStratifyAll) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_stratify_interp π) π E L' acc T)
    ⊢ typed_pre_context_fold π E L CtxFoldStratifyAllInit T.
  Proof.
    iIntros "Hf". iApply (typed_context_fold_init (typed_context_fold_stratify_interp π) ([], True%I) _ _ _ (CtxFoldStratifyAll)). iFrame.
    rewrite /typed_context_fold_stratify_interp/type_ctx_interp; simpl; done.
  Qed.

  Lemma type_stratify_context_annot E L π s fn R ϝ :
    typed_pre_context_fold π E L CtxFoldStratifyAllInit (λ L', typed_stmt π E L' s fn R ϝ)
    ⊢ typed_stmt π E L (annot: (StratifyContextAnnot); s) fn R ϝ.
  Proof.
    iIntros "HT".
    iIntros (?) "#CTX #HE HL Hna Hcont".
    iApply fupd_wps.
    iPoseProof ("HT" $! ⊤ with "[//] [//] CTX HE HL") as "Hstep".
    (* TODO need to unfold logical_step because we cannot eliminate one over a statement wp *)
    rewrite /logical_step.
    iMod "Hstep" as "(%n & Hat & Hvs)".
    iMod (persistent_time_receipt_0) as "Hp".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wps_annot_credits with "TIME Hat Hp").
    iModIntro. iNext. rewrite Nat.add_0_r. rewrite (additive_time_receipt_sep 1).
    iIntros "[Hcred1 Hcred] [Hat1 Hat]".
    iApply fupd_wps.
    iMod ("Hvs" with "Hcred Hat") as "(%L' & HL & HT)".
    by iApply ("HT" with "[$LFT $TIME $LLCTX] HE HL Hna").
  Qed.

  (** We instantiate the context folding mechanism for extraction of observations. *)
    Definition typed_context_fold_extract_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_extract π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R κ T :
    stratify_ltype_extract π E L StratRefoldOpened l lt r (Owned false) κ
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_stratify_interp π) π E L' (CtxFoldExtractAll κ) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_stratify_interp π) π E L (CtxFoldExtractAll κ) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (? ??) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.

  Lemma typed_context_fold_extract_init tctx π E L κ T :
    typed_context_fold (typed_context_fold_stratify_interp π) π E L (CtxFoldExtractAll κ) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_stratify_interp π) π E L' acc T)
    ⊢ typed_pre_context_fold π E L (CtxFoldExtractAllInit κ) T.
  Proof.
    iIntros "Hf". iApply (typed_context_fold_init (typed_context_fold_stratify_interp π) ([], True%I) _ _ _ (CtxFoldExtractAll κ)). iFrame.
    rewrite /typed_context_fold_stratify_interp/type_ctx_interp; simpl; done.
  Qed.

  (* Typing rule for [Return] *)
  (*
    Problem: uninit takes a syn_type, but we only have a layout.
    Options;
     - add a "Untyped ly" syn_type that just literally takes a layout.
     - just track the semantic type in the runtime_function we annotate typed_stmt with;
        i.e. have a custom notion of runtime_function for the type system that bundles up a bit more info.

     The proper solution would be a tighter integration of the notion of syntactic types into the language, as I had originally planned?
      - or would it? Really, at runtime we would still have concrete layouts. But in principle, I could then also just store the syn_type, since at runtime a syn_type uniquely identifies its layout.

     What are semantic types? Are they runtime things or static things?
      - maybe Uninit takes a bit of a special role here. It really specifies a property on the concrete bytes, and that does not make that much sense statically. (it's a "runtime type")
        => maybe Uninit should be a place type instead?
          => No. having an uninit value makes sense, it's not inherently tied to a particular location.
         Still, it takes up a somewhat special role, against the backdrop of the other types that we have (it has no direct correspondence in Rust). Even then, it's also different from e.g. owned-ptr, or place-ptr, which also do not have direct correspondences in Rust.
      -

   *)

  Lemma type_return E L π e fn (R : typed_stmt_R_t) ϝ:
    typed_val_expr π E L e (λ L' v rt ty r,
      v ◁ᵥ{π} r @ ty -∗
      typed_context_fold (typed_context_fold_stratify_interp π) π E L' CtxFoldStratifyAll fn.(rf_locs).*1 ([], True%I) (λ L2 m' acc,
        introduce_with_hooks E L2 (type_ctx_interp π acc.1 ∗ acc.2) (λ L3,
          prove_with_subtype E L3 true ProveDirect (
            foldr (λ (e : (loc * layout)) T, e.1 ◁ₗ[π, Owned false] (#()) @ (◁ (uninit (UntypedSynType e.2))) ∗ T)
            True%I
            fn.(rf_locs)) (λ L3 _ R2, introduce_with_hooks E L3 R2 (λ L4,
            (* important: when proving the postcondition [R v], we already have the ownership obtained by deinitializing the local variables [R2] available.
              The remaining goal is fully encoded by [R v], so the continuation is empty.
            *)
            R v L4
            )))))
    ⊢ typed_stmt π E L (return e) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hna Hcont". wps_bind.
    wp_bind.
    iApply ("He" with "CTX HE HL Hna").
    iIntros (L' v rt ty r) "HL Hna Hv HR".
    iApply fupd_wp.
    iMod ("HR" with "Hv [] [] CTX HE HL []") as "(%L2 & %acc & %m' & HL & Hstep & HT)"; [done.. | | ].
    { simpl. iApply logical_step_intro. iSplitR; last done. rewrite /type_ctx_interp. done. }
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iModIntro. iApply to_expr_wp. wp_bind.
    iApply (wp_logical_step with "TIME Hstep"); [done.. | ].
    iApply wp_skip. iNext. iIntros "_ Hacc".
    rewrite /typed_context_fold_stratify_interp.
    destruct acc as (ctx & R2).
    iMod ("HT" with "[] HE HL Hacc") as "(%L3 & HL & HT)"; first done.
    iMod ("HT" with "[] [] [$] HE HL") as "(%L4 & % & %R3 & HP & HL & HT)"; [done.. | ].
    iApply (wp_maybe_logical_step with "TIME HP"); [done.. | ].
    iModIntro. iApply wp_skip. iNext. iIntros "_ (Ha & HR2)".
    iApply wps_return.
    unfold li_tactic, llctx_find_llft_goal.
    iMod ("HT" with "[] HE HL HR2") as "(%L5 & HL & HT)"; first done.


    generalize (rf_locs fn) as ls => ls.
    iAssert (|={⊤}=> ([∗ list] l ∈ ls, l.1 ↦|l.2|))%I with "[Ha]" as ">Ha".
    { iInduction ls as [|[l ly] ls] "IH"; csimpl in*; simplify_eq.
      { by iFrame. }
      iDestruct "Ha" as "[Hl HR]".
      iMod ("IH" with "HR") as "?".
      iFrame.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly' & %Halg & % & _ & _ & _ & % & <- & Hv)".
      simpl in Halg. apply syn_type_has_layout_untyped_inv in Halg as [-> _].
      iMod (fupd_mask_mono with "Hv") as "(%v0 & Hl & Hv)"; first done.
      iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Halg' & %)".
      simpl in Halg'. apply syn_type_has_layout_untyped_inv in Halg' as [-> _].
      iExists _. by iFrame. }
    by iApply ("Hcont" with "HL Hna Ha HT").
  Qed.
End typing.



(* This must be an hint extern because an instance would be a big slowdown . *)
Global Hint Extern 1 (Subsume (?v ◁ᵥ{_} ?r1 @ ?ty1) (?v ◁ᵥ{_} ?r2 @ ?ty2)) =>
  class_apply own_val_subsume_id_inst : typeclass_instances.
Global Hint Extern 1 (Subsume (?l ◁ₗ{_, _} ?r1 @ ?ty) (?l ◁ₗ{_, _} ?r2 @ ?ty)) =>
  class_apply own_shr_subsume_id_inst : typeclass_instances.


Global Typeclasses Opaque subsume_full.
Global Typeclasses Opaque credit_store.
Global Typeclasses Opaque typed_value.
Global Typeclasses Opaque typed_option_map.
Global Typeclasses Opaque typed_val_expr.

Global Typeclasses Opaque typed_bin_op.

Global Typeclasses Opaque typed_un_op.

Global Typeclasses Opaque typed_if.

Global Typeclasses Opaque typed_call.

Global Typeclasses Opaque typed_annot_expr.

Global Typeclasses Opaque introduce_with_hooks.
Global Typeclasses Opaque typed_stmt_post_cond.

Global Typeclasses Opaque typed_assert.

Global Typeclasses Opaque typed_annot_stmt.

Global Typeclasses Opaque typed_switch.

Global Typeclasses Opaque typed_place.

Global Typeclasses Opaque cast_ltype_to_type.

Global Typeclasses Opaque resolve_ghost.

Global Typeclasses Opaque find_observation.

Global Typeclasses Opaque stratify_ltype.
Global Typeclasses Opaque typed_stmt.

Global Typeclasses Opaque typed_block.


Global Typeclasses Opaque stratify_ltype_post_hook.

Global Typeclasses Opaque weak_subtype.

Global Typeclasses Opaque weak_subltype.

Global Typeclasses Opaque owned_subtype.

Global Typeclasses Opaque owned_subltype_step.

Global Typeclasses Opaque mut_subtype.

Global Typeclasses Opaque mut_subltype.

Global Typeclasses Opaque mut_eqtype.

Global Typeclasses Opaque mut_eqltype.

Global Typeclasses Opaque prove_with_subtype.

Global Typeclasses Opaque prove_place_cond.
Global Typeclasses Opaque prove_place_rfn_cond.
Global Typeclasses Opaque typed_read_end.

Global Typeclasses Opaque typed_write_end.

Global Typeclasses Opaque typed_borrow_mut.

Global Typeclasses Opaque typed_borrow_mut_end.

Global Typeclasses Opaque typed_borrow_shr.

Global Typeclasses Opaque typed_borrow_shr_end.

Global Typeclasses Opaque typed_addr_of_mut.

Global Typeclasses Opaque typed_addr_of_mut_end.

Global Typeclasses Opaque typed_context_fold.


Global Typeclasses Opaque typed_context_fold_end.

Global Typeclasses Opaque relate_list.

Global Typeclasses Opaque relate_hlist.

Global Typeclasses Opaque fold_list.

Global Typeclasses Opaque typed_on_endlft.

Global Typeclasses Opaque typed_on_endlft_trigger.
Global Typeclasses Opaque typed_pre_context_fold.

Global Typeclasses Opaque typed_context_fold_step.

Global Typeclasses Opaque typed_write.



Global Typeclasses Opaque llctx_release_toks_goal.

Global Typeclasses Opaque lctx_lft_alive_count_goal.

Global Typeclasses Opaque typed_place_finish.

Global Typeclasses Transparent typed_place_finish.

Global Typeclasses Opaque typed_read.
