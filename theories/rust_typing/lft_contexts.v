(** Based on a file from the RustBelt development.
  https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/8753a224e99ce646e27729aa078367d64788f447/theories/typing/lft_contexts.v
*)
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.base_logic Require Import ghost_map.
From lrust.lifetime Require Import frac_borrow.
From refinedrust Require Export base.
From refinedrust Require Import fraction_counting util.
From iris.prelude Require Import options.
Set Default Proof Using "Type".

(** * Lifetime contexts for keeping track of which lifetimes are alive *)

Class lctxGS Σ := LctxGS {
  (* maps local lifetime names to their corresponding ghost name *)
  lctx_name_inG :: ghost_mapG Σ lft gname;
  (* track the fractions for one lifetime *)
  lctx_inG :: fraction_mapG Σ;
  (* track the decomposition of one lifetime into an atomic lifetime and "extra" lifetimes at some fraction *)
  lctx_decomp_inG :: ghost_mapG Σ lft (positive * lft * frac);
  (* name for the map *)
  lctx_name : gname;
  (* name for the decomposition map *)
  lctx_decomp_name : gname;
}.
Global Hint Mode lctxGS - : typeclass_instances.
Class lctxGPreS Σ := LctxGPreS {
  lctx_pre_name_inG :: ghost_mapG Σ lft gname;
  lctx_pre_inG :: fraction_mapG Σ;
  lctx_pre_decomp_inG :: ghost_mapG Σ lft (positive * lft * frac);
}.
Global Hint Mode lctxGPreS - : typeclass_instances.
Definition lctxΣ : gFunctors :=
  #[ ghost_mapΣ (lft) gname; fraction_mapΣ; ghost_mapΣ lft (positive * lft * frac) ].
Global Instance subG_lctxΣ Σ : subG (lctxΣ) Σ → lctxGPreS Σ.
Proof. solve_inG. Qed.

Definition elctx_elt : Type := lft * lft.
Notation elctx := (list elctx_elt).

(* nicer version for the singleton case *)
Fixpoint lft_intersect_list' (κs : list lft) : lft :=
    match κs with
    | [] => static
    | [κ] => κ
    | κ :: κs => κ ⊓ lft_intersect_list' κs
    end.
Lemma lft_intersect_list'_iff κs :
  lft_intersect_list' κs = lft_intersect_list κs.
Proof.
  induction κs as [ | κ κs IH]; simpl; first done.
  destruct κs as [ | κ' κs]; simpl.
  { rewrite right_id //. }
  simpl in IH. rewrite IH //.
Qed.

Declare Scope rrust_elctx_scope.
Delimit Scope rrust_elctx_scope with EL.
(* We need to define [elctx] and [llctx] as notations to make eauto
   work. But then, Coq is not able to bind them to their
   notations, so we have to use [Arguments] everywhere. *)
Bind Scope rrust_elctx_scope with elctx_elt.

Notation "κ1 ⊑ₑ κ2" := (@pair lft lft κ1 κ2) (at level 70).

Definition llctx_elt : Type := (option nat * lft * list lft).
Notation llctx := (list llctx_elt).

(* locally-owned lifetimes with a "borrow count" *)
Notation "κ '⊑ₗ{' c '}' κl" := (@pair (@prod (option nat) lft) (list lft) (Some c%nat, κ) κl) (at level 70).
(* local aliases with no distinct ownership *)
Notation "κ '≡ₗ' κl" := (@pair (@prod (option nat) lft) (list lft) (None, κ) κl) (at level 70).

Section lft_contexts.
  Context `{!invGS Σ, !lftGS Σ lft_userE, !lctxGS Σ}.
  Implicit Type (κ : lft).

  (* External lifetime contexts. *)
  Definition elctx_elt_interp (x : elctx_elt) : iProp Σ :=
    (x.1 ⊑ x.2)%I.

  Definition elctx_interp (E : elctx) : iProp Σ :=
    ([∗ list] x ∈ E, elctx_elt_interp x)%I.
  Global Instance elctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) elctx_interp.
  Proof. intros ???. by apply big_opL_permutation. Qed.
  Global Instance elctx_interp_persistent E :
    Persistent (elctx_interp E).
  Proof. apply _. Qed.

  (* Local lifetime contexts. *)
  (** The fraction_map for [κ] is stored at [γ]. *)
  Definition lft_has_gname_def (κ : lft) (γ : gname) : iProp Σ :=
    ghost_map_elem lctx_name κ DfracDiscarded γ.
  Definition lft_has_gname_aux : seal (@lft_has_gname_def). Proof. by eexists. Qed.
  Definition lft_has_gname := lft_has_gname_aux.(unseal).
  Definition lft_has_gname_eq : @lft_has_gname = @lft_has_gname_def := lft_has_gname_aux.(seal_eq).

  Global Instance lft_has_gname_pers κ γ : Persistent (lft_has_gname κ γ).
  Proof. rewrite lft_has_gname_eq. apply _. Qed.
  Global Instance lft_has_gname_timeless κ γ : Timeless (lft_has_gname κ γ).
  Proof. rewrite lft_has_gname_eq. apply _. Qed.

  Lemma lft_has_gname_agree κ γ1 γ2 :
    lft_has_gname κ γ1 -∗ lft_has_gname κ γ2 -∗ ⌜γ1 = γ2⌝.
  Proof. rewrite lft_has_gname_eq. apply ghost_map_elem_agree. Qed.

  (** The local lifetime [κ] is κ = i ⊓ κextra ⊓ κs.
    This serves to link up the interpretation of the fraction_map with the fragments, without leaking these details.
   *)
  Definition lft_decomp_def (κ : lft) (i : positive) (κextra : lft) (qextra : frac) : iProp Σ :=
    ghost_map_elem lctx_decomp_name κ DfracDiscarded (i, κextra, qextra).
  Definition lft_decomp_aux : seal (@lft_decomp_def). Proof. by eexists. Qed.
  Definition lft_decomp := lft_decomp_aux.(unseal).
  Definition lft_decomp_eq : @lft_decomp = @lft_decomp_def := lft_decomp_aux.(seal_eq).

  Global Instance lft_decomp_pers κ i κextra qextra: Persistent (lft_decomp κ i κextra qextra).
  Proof. rewrite lft_decomp_eq. apply _. Qed.
  Global Instance lft_decomp_timeless κ i κextra qextra : Timeless (lft_decomp κ i κextra qextra).
  Proof. rewrite lft_decomp_eq. apply _. Qed.

  Lemma lft_decomp_agree κ i1 i2 κextra1 κextra2 qextra1 qextra2 :
    lft_decomp κ i1 κextra1 qextra1 -∗ lft_decomp κ i2 κextra2 qextra2 -∗ ⌜i1 = i2⌝ ∧ ⌜κextra1 = κextra2⌝ ∧ ⌜qextra1 = qextra2⌝.
  Proof.
    iIntros "H1 H2". rewrite lft_decomp_eq.
    iPoseProof (ghost_map_elem_agree with "H1 H2") as "%Heq".
    iPureIntro. by injection Heq.
  Qed.

  Definition llft_own_frac κ (qc : frac) : iProp Σ :=
    ∃ i κextra qextra, lft_decomp κ i κextra qextra ∗
    let qeff := Qp.min 1 qextra in
    qc.[positive_to_lft i] ∗ (qeff * qc).[κextra].

  Global Instance llft_own_frac_fractional κ : Fractional (llft_own_frac κ).
  Proof.
    iIntros (q1 q2). iSplit.
    - iIntros "(%i & %κextra & %qextra & #Hmeta & Hi & Hextra)".
      rewrite Qp.mul_add_distr_l. rewrite !lft_tok_fractional.
      iDestruct "Hi" as "(Hi1 & Hi2)". iDestruct "Hextra" as "(Hextra1 & Hextra2)".
      iSplitL "Hi1 Hextra1"; iExists _, _, _; iFrame "#"; iFrame.
    - iIntros "((%i & %κextra & %qextra & #Hmeta1 & Hi1 & Hextra1) & (% & % & % & #Hmeta2 & Hi2 & Hextra2))".
      iPoseProof (lft_decomp_agree with "Hmeta1 Hmeta2") as "(<- & <- & <-)".
      iExists _, _, _. iFrame "Hmeta1".
      rewrite Qp.mul_add_distr_l. rewrite !lft_tok_fractional. iFrame.
  Qed.

  (** Enforces the shape of a local lifetime. *)
  Definition llft_shape (κ : lft) (κs : list lft) : iProp Σ :=
    let κ' := lft_intersect_list κs in
    ∃ i κextra qextra, lft_decomp κ i κextra qextra ∗
    ⌜κ = κ' ⊓ positive_to_lft i ⊓ κextra⌝.
  Instance llft_shape_pers κ κs : Persistent (llft_shape κ κs).
  Proof. apply _. Qed.

  (* We can kill a local lifetime κ. *)
  Definition llft_killable (κ : lft) : iProp Σ :=
    ∃ i κextra qextra, lft_decomp κ i κextra qextra ∗
    (1.[positive_to_lft i] ={↑lftN ∪ lft_userE}[lft_userE]▷=∗ [†positive_to_lft i]).


  (** We currently have a fraction of the "core" of local lifetime [κ].
     This is handed out to clients as a certificate to decrease the lifetime again. *)
  Definition llft_elt_tok_def (κ : lft) : iProp Σ :=
    ∃ γ, lft_has_gname κ γ ∗ fraction_map_elem γ (llft_own_frac κ).
  Definition llft_elt_tok_aux : seal (@llft_elt_tok_def). Proof. by eexists. Qed.
  Definition llft_elt_tok := llft_elt_tok_aux.(unseal).
  Definition llft_elt_tok_eq : @llft_elt_tok = @llft_elt_tok_def := llft_elt_tok_aux.(seal_eq).


  (** Rough workflow:
      - we get llft_elt_tok in the right multiplicity for all lifetimes
      - from that, we inductively get a token of the full intersected thing by lower-bounding fractions, + a viewshift to get all the tokens back.
    *)
  Definition llft_elt_toks (κs : list lft) : iProp Σ :=
    [∗ list] κ ∈ κs, llft_elt_tok κ.
  Lemma llft_elt_toks_app κs1 κs2 :
    llft_elt_toks (κs1 ++ κs2) ⊣⊢ llft_elt_toks κs1 ∗ llft_elt_toks κs2.
  Proof. apply big_sepL_app. Qed.

  (* To support calling functions with lifetime parameters, the local lifetime [κ] may be an
  intersection of not just the atomic lifetime [id] but also of some extra
  lifetimes [κextra], of which a smaller fraction [qextra] is owned.

  For [ϝ], since [κs] is empty, the caller can just keep the persistent [lft_decomp] to know that it will get the full fraction back afterwards, which is sufficient to extract the lifetime tokens for [κextra] again. *)
  Definition llctx_owned_elt_interp (c : nat) (κ : lft) (κs : list lft) : iProp Σ :=
    ∃ γ, lft_has_gname κ γ ∗
    (* authorative management of the lifetime *)
    fraction_map_auth γ (llft_own_frac κ) 1 c ∗
    (* decomposition of the lifetime *)
    llft_shape κ κs ∗
    (* when we have the full thing, we can kill it *)
    llft_killable κ.

  (* Local lifetime contexts without the "ending a lifetime" viewshifts -- these are fractional. *)
  Definition llctx_owned_elt_interp_noend (c : nat) (κ : lft) (κs : list lft) (q : Qp) : iProp Σ :=
    ∃ γ, lft_has_gname κ γ ∗
    (* [qc] is the fraction still available here *)
    fraction_map_auth γ (llft_own_frac κ) q c ∗
    (* decomposition of the lifetime *)
    llft_shape κ κs.

  Global Instance llctx_owned_elt_interp_noend_fractional c κ κs :
    Fractional (llctx_owned_elt_interp_noend c κ κs).
  Proof.
    iIntros (q q'). iSplit; iIntros "H".
    - iDestruct "H" as (γ) "(#? & Hfrac & #Hshape)".
      rewrite fraction_map_auth_fractional. iDestruct "Hfrac" as "[Hfrac1 Hfrac2]".
      iSplitL "Hfrac1"; iExists _; by iFrame "∗%#".
    - iDestruct "H" as "[Hq Hq']".
      iDestruct "Hq" as (γ1) "(#Hm1 & Hfrac1 & Hshape1)".
      iDestruct "Hq'" as (γ2) "(#Hm2 & Hfrac2 & _)".
      iPoseProof (lft_has_gname_agree with "Hm1 Hm2") as "<-".
      iExists γ1. iFrame "Hm1 Hshape1". rewrite fraction_map_auth_fractional. iFrame.
  Qed.

  Lemma llctx_owned_elt_interp_acc_noend c κ κs :
    llctx_owned_elt_interp c κ κs ⊢
    llctx_owned_elt_interp_noend c κ κs 1 ∗ (llctx_owned_elt_interp_noend c κ κs 1 -∗ llctx_owned_elt_interp c κ κs).
  Proof.
    iIntros "H". iDestruct "H" as (γ) "(#Hm & Hauth & #Hshape & Hkill)".
    iSplitL "Hauth". { iExists γ. iFrame "#∗". }
    iIntros "(%γ' & Hm' & Hauth & _)".
    iPoseProof (lft_has_gname_agree with "Hm Hm'") as "<-".
    iExists γ. iFrame "#∗".
  Qed.

  (** κ is an alias for the intersection of κs, expressed through a mutual dynamic inclusion. *)
  Definition llctx_alias_elt_interp (κ : lft) (κs : list lft) : iProp Σ :=
    κ ⊑ lft_intersect_list κs ∗ lft_intersect_list κs ⊑ κ.
  Global Instance llctx_alias_elt_interp_pers κ κs : Persistent (llctx_alias_elt_interp κ κs).
  Proof. apply _. Qed.

  Definition llctx_elt_interp (x : llctx_elt) : iProp Σ :=
    match x with
    | (Some c, κ, κs) => llctx_owned_elt_interp c κ κs
    | (None, κ, κs) => llctx_alias_elt_interp κ κs
    end.
  Definition llctx_elt_interp_noend (x : llctx_elt) (q : Qp) : iProp Σ :=
    match x with
    | (Some c, κ, κs) => llctx_owned_elt_interp_noend c κ κs q
    | (None, κ, κs) => llctx_alias_elt_interp κ κs
    end.

  Global Instance llctx_elt_interp_noend_fractional x :
    Fractional (llctx_elt_interp_noend x).
  Proof.
    destruct x as [[[c | ] κ] κs]; apply _.
  Qed.

  Lemma llctx_elt_interp_acc_noend x :
    llctx_elt_interp x ⊢
    llctx_elt_interp_noend x 1 ∗ (llctx_elt_interp_noend x 1 -∗ llctx_elt_interp x).
  Proof.
    iIntros "H". destruct x as [[[c | ] κ] κs].
    - by iApply llctx_owned_elt_interp_acc_noend.
    - iFrame. iIntros "$".
  Qed.

  (** noend contexts *)
  Definition llctx_interp_noend (L : llctx) (q : Qp) : iProp Σ :=
    [∗ list] x ∈ L, llctx_elt_interp_noend x q.
  Global Instance llctx_interp_fractional L :
    Fractional (llctx_interp_noend L).
  Proof.
    intros ??. rewrite -big_sepL_sep. by setoid_rewrite <-fractional.
  Qed.
  Global Instance llctx_interp_as_fractional L q :
    AsFractional (llctx_interp_noend L q) (llctx_interp_noend L) q.
  Proof. split; first done. apply _. Qed.

  Global Instance llctx_interp_combine_sep L q1 q2 : CombineSepAs (llctx_interp_noend L q1) (llctx_interp_noend L q2) (llctx_interp_noend L (q1 + q2)).
  Proof.
    rewrite /CombineSepAs. iIntros "Ha".
    iPoseProof (fractional_split with "Ha") as "Ha"; last by iApply "Ha".
    apply _.
  Qed.

  Global Instance frame_llctx_interp p L q1 q2 q3 :
    FrameFractionalQp q1 q2 q3 →
    Frame p (llctx_interp_noend L q1) (llctx_interp_noend L q2) (llctx_interp_noend L q3) | 5.
  Proof. apply: frame_fractional. Qed.


  (** This is a global invariant to be compatible with concurrency (we can't just put it in [llctx_interp]). *)
  Definition llctxN := rrustN .@ "llctx".
  Definition llctx_inv :=
    ((∃ (M : gmap lft gname) (M' : gmap lft (positive * lft * frac)),
      ghost_map_auth lctx_name 1 M ∗ ghost_map_auth lctx_decomp_name 1 M' ∗
      ⌜dom M = dom M'⌝))%I.
  Definition llctx_ctx_def : iProp Σ :=
    inv llctxN llctx_inv.
  Definition llctx_ctx_aux : seal (llctx_ctx_def). Proof. by eexists. Qed.
  Definition llctx_ctx := llctx_ctx_aux.(unseal).
  Definition llctx_ctx_eq : llctx_ctx = llctx_ctx_def := llctx_ctx_aux.(seal_eq).

  Global Instance llctx_ctx_pers : Persistent llctx_ctx.
  Proof. rewrite llctx_ctx_eq. apply _. Qed.

  Definition llctx_interp (L : llctx) : iProp Σ :=
    [∗ list] x ∈ L, llctx_elt_interp x.
  Global Instance llctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) (llctx_interp).
  Proof.
    intros ???. iSplit; iIntros "HL"; unfold llctx_interp.
    all: rewrite big_opL_permutation; done.
  Qed.
End lft_contexts.

Lemma lctx_init `{!lctxGPreS Σ, !invGS Σ, !lftGS Σ lft_userE} F :
  ↑llctxN ⊆ F →
  ⊢ |={F}=> ∃ H : lctxGS Σ, llctx_ctx ∗ llctx_interp [].
Proof.
  iIntros (?).
  iMod (ghost_map_alloc_empty (K:=lft) (V:=gname)) as "(%γname & Hname)".
  iMod (ghost_map_alloc_empty (K:=lft) (V:=positive*lft*frac)) as "(%γdecomp & Hdecomp)".
  set (LLCTXGS := LctxGS _ _ _ _ γname γdecomp).
  iMod (inv_alloc llctxN _ llctx_inv with "[Hname Hdecomp]") as "Hctx".
  { iNext. iExists ∅, ∅. iFrame. iPureIntro. set_solver. }
  iModIntro. iExists LLCTXGS. iSplitL.
  { rewrite llctx_ctx_eq. iApply "Hctx". }
  by iApply big_sepL_nil.
Qed.

Section lft_contexts.
  Context `{!invGS Σ, !lftGS Σ lft_userE, !lctxGS Σ}.

  Lemma llctx_elt_interp_acc_noend_big (L : llctx) :
    ([∗ list] κ ∈ L, llctx_elt_interp κ) ⊢
    llctx_interp_noend L 1 ∗ (llctx_interp_noend L 1 -∗ ([∗ list] κ ∈ L, llctx_elt_interp κ)).
  Proof.
    iIntros "HL". setoid_rewrite llctx_elt_interp_acc_noend at 1. rewrite big_sepL_sep.
    iDestruct "HL" as "($ & Hclose)".
    iIntros "Hnoend". iCombine "Hclose Hnoend" as "H".
    rewrite /llctx_interp_noend -big_sepL_sep.
    setoid_rewrite bi.wand_elim_l. eauto with iFrame.
  Qed.
  Lemma llctx_interp_acc_noend L :
    llctx_interp L -∗
    llctx_interp_noend L 1 ∗ (llctx_interp_noend L 1 -∗ llctx_interp L).
  Proof. iIntros "HL". by iApply llctx_elt_interp_acc_noend_big. Qed.


  (** Lifetime inclusion without id/count tracking *)
  Section fix_EL.
  Context (E : elctx) (L : llctx).

  Definition lctx_lft_incl κ κ' : Prop :=
    (* the proof must not use any information about the counts *)
    ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ κ ⊑ κ')%I.

  Definition lctx_lft_eq κ κ' : Prop :=
    lctx_lft_incl κ κ' ∧ lctx_lft_incl κ' κ.

  Lemma lctx_lft_incl_incl κ κ' :
    lctx_lft_incl κ κ' → llctx_interp L -∗ □ (elctx_interp E -∗ κ ⊑ κ')%I.
  Proof.
    iIntros (Hincl) "HL".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL _]".
    iApply Hincl. done.
  Qed.

  Lemma lctx_lft_incl_refl κ : lctx_lft_incl κ κ.
  Proof.
    iIntros (qL) "_ !> _".
    iApply lft_incl_refl.
  Qed.

  Global Instance lctx_lft_incl_preorder : PreOrder lctx_lft_incl.
  Proof.
    split; first by intros ?; apply lctx_lft_incl_refl.
    iIntros (??? H1 H2 ?) "HL".
    iDestruct (H1 with "HL") as "#H1".
    iDestruct (H2 with "HL") as "#H2".
    iClear "∗". iIntros "!> #HE".
    iDestruct ("H1" with "HE") as "#?". iDestruct ("H2" with "HE") as "#?".
    by iApply lft_incl_trans.
  Qed.

  Global Instance lctx_lft_incl_proper :
    Proper (lctx_lft_eq ==> lctx_lft_eq ==> iff) lctx_lft_incl.
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance lctx_lft_eq_equivalence : Equivalence lctx_lft_eq.
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma lctx_lft_incl_static κ : lctx_lft_incl κ static.
  Proof. iIntros (qL) "_ !> _". iApply lft_incl_static. Qed.

  Lemma lctx_lft_incl_elem κ κs :
    κ ∈ κs → lctx_lft_incl (lft_intersect_list κs) κ.
  Proof.
    iIntros (??) "HL !> _".
    by iApply lft_intersect_list_elem_of_incl.
  Qed.

  Lemma lctx_lft_incl_local_owned_full κ κ' κ'' c κs :
    κ ⊑ₗ{c} κs ∈ L → lctx_lft_incl (lft_intersect_list κs ⊓ κ') κ'' → lctx_lft_incl (κ ⊓ κ') κ''.
  Proof.
    intros Hin Hincl. etrans; last done.
    iIntros (?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iDestruct (big_sepL_elem_of with "HL") as "HL"; first done.
    iDestruct "HL" as (γ) "(Hname & Hauth & Hshape)".
    iDestruct "Hshape" as (i κextra ?) "(_ & ->)".
    iIntros "!>#HE". iDestruct ("Hincl" with "HE") as "#?".
    iClear "Hincl HE".
    rewrite -!lft_intersect_assoc.
    rewrite [κextra ⊓ _]lft_intersect_comm [positive_to_lft _ ⊓ _] lft_intersect_assoc [positive_to_lft _ ⊓ _]lft_intersect_comm.
    rewrite -!lft_intersect_assoc. rewrite lft_intersect_assoc.
    iApply lft_intersect_incl_l.
  Qed.

  Lemma lctx_lft_incl_local_owned κ κ' c κs :
    κ ⊑ₗ{c} κs ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    intros HL Hin. rewrite -(lft_intersect_right_id κ).
    eapply lctx_lft_incl_local_owned_full; first done.
    rewrite lft_intersect_right_id.
    by apply lctx_lft_incl_elem.
  Qed.

  Lemma lctx_lft_incl_local_owned' κ κ' κ'' c κs :
    κ ⊑ₗ{c} κs ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local_owned. Qed.

  Lemma lctx_lft_incl_local_alias_full κ κ' κ'' κs :
    κ ≡ₗ κs ∈ L → lctx_lft_incl (lft_intersect_list κs ⊓ κ') κ'' → lctx_lft_incl (κ ⊓ κ') κ''.
  Proof.
    intros Hin Hincl. etrans; last done.
    iIntros (?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iDestruct (big_sepL_elem_of with "HL") as "HL"; first done.
    iDestruct "HL" as "(#Hincl1 & #Hincl2)".
    iIntros "!>#HE".
    iApply lft_intersect_mono; first done. iApply lft_incl_refl.
  Qed.

  Lemma lctx_lft_incl_local_alias_reverse κ κ' κ'' κs :
    κ ≡ₗ κs ∈ L → lctx_lft_incl κ κ'' → lctx_lft_incl κ' (lft_intersect_list κs) → lctx_lft_incl κ' κ''.
  Proof.
    intros Hin Hincl1 Hincl2. etrans; first done.
    iIntros (?) "HL". iPoseProof (Hincl1 with "HL") as "#Hincl".
    iDestruct (big_sepL_elem_of with "HL") as "HL"; first done.
    iDestruct "HL" as "(#Hincl1 & #Hincl2)".
    iIntros "!>#HE".
    iApply lft_incl_trans; first done. by iApply "Hincl".
  Qed.

  Lemma lctx_lft_incl_local_alias κ κ' κs :
    κ ≡ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    intros HL Hin. rewrite -(lft_intersect_right_id κ).
    eapply lctx_lft_incl_local_alias_full; first done.
    rewrite lft_intersect_right_id.
    by apply lctx_lft_incl_elem.
  Qed.

  Lemma lctx_lft_incl_local_alias' κ κ' κ'' κs :
    κ ≡ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local_alias. Qed.

  Lemma lctx_lft_incl_external_full κ1 κ2 κ κ' :
    κ1 ⊑ₑ κ2 ∈ E → lctx_lft_incl (κ2 ⊓ κ) κ' → lctx_lft_incl (κ1 ⊓ κ) κ'.
  Proof.
    intros Hin Hincl. etrans; last done.
    iIntros (?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!>#HE". iDestruct ("Hincl" with "HE") as "#?".
    iDestruct (big_sepL_elem_of with "HE") as "#Hincl'"; first done.
    iApply lft_intersect_mono; first done.
    iApply lft_incl_refl.
  Qed.

  Lemma lctx_lft_incl_external κ κ' : κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ κ'.
  Proof.
    iIntros (??) "_ !> #HE".
    rewrite /elctx_interp /elctx_elt_interp big_sepL_elem_of //. done.
  Qed.

  Lemma lctx_lft_incl_external' κ κ' κ'' :
    κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_external. Qed.

  Lemma lctx_lft_incl_intersect κ1 κ2 κ' κ'' :
    lctx_lft_incl κ1 κ' → lctx_lft_incl κ2 κ'' →
    lctx_lft_incl (κ1 ⊓ κ2) (κ' ⊓ κ'').
  Proof.
    iIntros (Hκ' Hκ'' ?) "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iDestruct (Hκ'' with "HL") as "#Hκ''".
    iIntros "!> #HE".
    iDestruct ("Hκ'" with "HE") as "#?".
    iDestruct ("Hκ''" with "HE") as "#?".
    by iApply lft_intersect_mono.
  Qed.

  Lemma lctx_lft_incl_intersect_l κ κ' κ'' :
    lctx_lft_incl κ κ' →
    lctx_lft_incl (κ ⊓ κ'') κ'.
  Proof.
    iIntros (Hκ' ?) "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iDestruct ("Hκ'" with "HE") as "#?".
    iApply lft_incl_trans; last done.
    by iApply lft_intersect_incl_l.
  Qed.

  Lemma lctx_lft_incl_intersect_r κ κ' κ'' :
    lctx_lft_incl κ κ' →
    lctx_lft_incl (κ'' ⊓ κ) κ'.
  Proof.
    iIntros (Hκ' ?) "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iDestruct ("Hκ'" with "HE") as "#?".
    iApply lft_incl_trans; last done.
    by iApply lft_intersect_incl_r.
  Qed.

  Lemma lctx_lft_incl_incl_noend qL κ κ' :
    lctx_lft_incl κ κ' →
    llctx_interp_noend L qL -∗
    elctx_interp E -∗
    κ ⊑ κ'.
  Proof.
    iIntros (Hincl) "HL HE".
    iPoseProof (Hincl with "HL") as "#Hincl".
    by iApply "Hincl".
  Qed.

  Lemma big_sepL_lft_incl_incl κs κ :
    elctx_interp E -∗ llctx_interp L -∗
    ([∗ list] κ' ∈ κs, ⌜lctx_lft_incl κ' κ⌝) -∗
    ([∗ list] κ' ∈ κs, κ' ⊑ κ).
  Proof.
    iIntros "#HE HL #Hincl".
    iInduction κs as [ | κ' κs] "IH"; first done.
    simpl. iDestruct "Hincl" as "(%Hincl & Hincl)".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#$"; first apply Hincl.
    iApply ("IH" with "Hincl HL").
  Qed.

  (* Lifetime aliveness *)
  Definition lctx_lft_alive (κ : lft) : Prop :=
    (* the proof must not use any information about the counts *)
    (* TODO: why do we have masks here? can I also just make this a bupd?*)
    ∀ F qL, ↑lftN ⊆ F → elctx_interp E -∗ llctx_interp_noend L qL ={F}=∗
          ∃ q', q'.[κ] ∗ (q'.[κ] ={F}=∗ llctx_interp_noend L qL).

  Lemma lctx_lft_alive_tok_noend κ F q :
    ↑lftN ⊆ F →
    lctx_lft_alive κ → elctx_interp E -∗ llctx_interp_noend L q ={F}=∗
      ∃ q', q'.[κ] ∗ llctx_interp_noend L q' ∗
                   (q'.[κ] -∗ llctx_interp_noend L q' ={F}=∗ llctx_interp_noend L q).
  Proof.
    iIntros (? Hal) "#HE [HL1 HL2]".
    iMod (Hal with "HE HL1") as (q') "[Htok Hclose]"; [done | ].
    destruct (Qp.lower_bound (q/2) q') as (qq & q0  & q'0 & Hq & ->). rewrite Hq.
    iExists qq. iDestruct "HL2" as "[$ HL]". iDestruct "Htok" as "[$ Htok]".
    iIntros "!> Htok' HL'". iCombine "HL'" "HL" as "HL". rewrite -Hq. iFrame.

    iApply "Hclose". iFrame.
  Qed.

  Lemma lctx_lft_alive_tok_noend_list κs F q :
    ↑lftN ⊆ F → Forall lctx_lft_alive κs →
      elctx_interp E -∗ llctx_interp_noend L q ={F}=∗
         ∃ q', q'.[lft_intersect_list κs] ∗ llctx_interp_noend L q' ∗
                   (q'.[lft_intersect_list κs] -∗ llctx_interp_noend L q' ={F}=∗ llctx_interp_noend L q).
  Proof.
    iIntros (? Hκs) "#HE". iInduction κs as [|κ κs] "IH" forall (q Hκs).
    { iIntros "HL !>". iExists _. iFrame "HL". iSplitL; first iApply lft_tok_static.
      iIntros "_ $". done. }
    inversion_clear Hκs.
    iIntros "HL". iMod (lctx_lft_alive_tok_noend κ with "HE HL")as (q') "(Hκ & HL & Hclose1)"; [solve_typing..|].
    iMod ("IH" with "[//] HL") as (q'') "(Hκs & HL & Hclose2)".
    destruct (Qp.lower_bound q' q'') as (qq & q0  & q'0 & -> & ->).
    iExists qq. iDestruct "HL" as "[$ HL2]". iDestruct "Hκ" as "[Hκ1 Hκ2]".
    iDestruct "Hκs" as "[Hκs1 Hκs2]". iModIntro. simpl. rewrite -lft_tok_sep. iSplitL "Hκ1 Hκs1".
    { by iFrame. }
    iIntros "[Hκ1 Hκs1] HL1". iMod ("Hclose2" with "[$Hκs1 $Hκs2] [$HL1 $HL2]") as "HL".
    iMod ("Hclose1" with "[$Hκ1 $Hκ2] HL") as "HL". done.
  Qed.

  Lemma lctx_lft_alive_static : lctx_lft_alive static.
  Proof.
    iIntros (F qL ?) "_ $". iExists 1%Qp. iSplitL; last by auto.
    by iApply lft_tok_static.
  Qed.

  Lemma lctx_lft_alive_local_owned κ c κs:
    κ ⊑ₗ{c} κs ∈ L → Forall lctx_lft_alive κs → lctx_lft_alive κ.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs F qL ? ) "#HE HL".
    iDestruct "HL" as "[HL1 HL2]". rewrite {2}/llctx_interp_noend /llctx_elt_interp.
    iDestruct (big_sepL_lookup_acc with "HL2") as "[Hκ Hclose]"; first done.
    iDestruct "Hκ" as (γ) "(#Hname & Hauth & #Hshape)".
    iDestruct "Hshape" as (ic κextra qextra) "(#Hd & %Hde)".
    iAssert (∃ q', q'.[lft_intersect_list κs] ∗
      (q'.[lft_intersect_list κs] ={F}=∗ llctx_interp_noend L (qL / 2)))%I
      with "[> HE HL1]" as "H".
    { move:(qL/2)%Qp=>qL'. clear HL. iClear "Hd Hname". subst κ.
      iInduction Hκs as [|κ κs Hκ ?] "IH" forall (qL').
      - iExists 1%Qp. iFrame. iSplitR; last by auto. iApply lft_tok_static.
      - iDestruct "HL1" as "[HL1 HL2]".
        iMod (Hκ with "HE HL1") as (q') "[Htok' Hclose]"; [done | ].
        iMod ("IH" with "HL2") as (q'') "[Htok'' Hclose']".
        destruct (Qp.lower_bound q' q'') as (q0 & q'2 & q''2 & -> & ->).
        iExists q0. rewrite -lft_tok_sep. iDestruct "Htok'" as "[$ Hr']".
        iDestruct "Htok''" as "[$ Hr'']". iIntros "!>[Hκ Hfold]".
        iMod ("Hclose" with "[$Hκ $Hr']") as "$". iApply "Hclose'". iFrame. }
    iDestruct "H" as (q1) "[Htok' Hclose']". rewrite -{5}(Qp.div_2 qL).
    set (qeff := (1 `min` qextra)%Qp).
    (* basic proof structure:
      - get a fraction from the fraction_map_auth,
      - take the lower bound from the recursive q'
      - done
    *)
    iPoseProof (fraction_map_auth_access with "Hauth") as "(%q2 & Hfrac & Hauth & Hcl_auth)".
    iDestruct "Hfrac" as (???) "(Hd' & Hi & Hex)".
    iPoseProof (lft_decomp_agree with "Hd Hd'")as "(<- & <- & <-)".
    (* take the min of q1, q2, (q `min` qextra) * q2 *)
    destruct (Qp.lower_bound q1 (qeff * q2)%Qp) as (q0 & q'1 & q'2 & -> & Hmax). rewrite Hmax.
    destruct (Qp.lower_bound q0 q2) as (q0' & q'3 & q'4 & -> & ->).
    rewrite -!Qp.add_assoc.
    rewrite !(lft_tok_fractional _ q0').
    iDestruct "Htok'" as "(Hκs1 & Hκs2)".
    iDestruct "Hi" as "(Hi1 & Hi2)".
    iDestruct "Hex" as "(Hex1 & Hex2)".
    iModIntro. iExists q0'.
    iSplitL "Hi1 Hex1 Hκs1".
    { rewrite Hde. rewrite -!lft_tok_sep. iFrame. }
    (* close everything *)
    rewrite {9}Hde. rewrite -!lft_tok_sep. iIntros "((? & Hi1) & Hex1)".
    iMod ("Hclose'" with "[$]") as "$".
    iPoseProof ("Hcl_auth" with "[Hi1 Hex1 Hi2 Hex2] Hauth") as "Hauth".
    { iExists _, _, _. iFrame "Hd". rewrite Hmax !lft_tok_fractional. by iFrame. }
    iApply "Hclose". iModIntro. iExists γ. iFrame "#∗".
    iExists _, _, _. eauto with iFrame.
  Qed.

  Lemma lctx_lft_alive_intersect κ1 κ2 :
    lctx_lft_alive κ1 → lctx_lft_alive κ2 → lctx_lft_alive (κ1 ⊓ κ2).
  Proof.
    iIntros (Hal1 Hal2 F qL ? ) "#HE [HL1 HL2]".
    iMod (Hal1 F with "HE HL1") as (q1) "(Hκ1 & Hcl1)"; [done | ].
    iMod (Hal2 F with "HE HL2") as (q2) "(Hκ2 & Hcl2)"; [done | ].
    iModIntro.
    set (q' := (Qp.min q1 q2)%Qp).
    iExists q'.
    rewrite -lft_tok_sep.
    iPoseProof (Fractional_fractional_le (λ q, q.[κ1])%I q1 q' with "Hκ1") as "[$ Hvs1]".
    { apply Qp.le_min_l. }
    iPoseProof (Fractional_fractional_le (λ q, q.[κ2])%I q2 q' with "Hκ2") as "[$ Hvs2]".
    { apply Qp.le_min_r. }
    iIntros "[Hκ1 Hκ2]".
    iMod ("Hcl1" with "(Hvs1 Hκ1)") as "$".
    iMod ("Hcl2" with "(Hvs2 Hκ2)") as "$".
    done.
  Qed.
  End fix_EL.

  Lemma lctx_lft_alive_incl {E L} κ κ':
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' → lctx_lft_alive E L κ'.
  Proof.
    iIntros (Hal Hinc F qL ? ) "#HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl".
    { iApply (Hinc with "HL HE"). }
    iMod (Hal with "HE HL") as (q') "[Htok Hclose]"; [done | ].
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose']"; first done.
    iExists q''. iIntros "{$Htok}!>Htok". iApply ("Hclose" with "[> -]").
    by iApply "Hclose'".
  Qed.

  Lemma lctx_lft_alive_intersect_list {E L} κs :
    Forall (lctx_lft_alive E L) κs → lctx_lft_alive E L (lft_intersect_list κs).
  Proof.
    intros Hal.
    induction κs as [ | κ κs IH].
    { simpl. apply lctx_lft_alive_static. }
    inversion Hal; subst.
    eapply lctx_lft_alive_intersect; first done.
    by eapply IH.
  Qed.

  Lemma lctx_lft_alive_local_alias E L κ κs:
    κ ≡ₗ κs ∈ L → Forall (lctx_lft_alive E L) κs → (lctx_lft_alive E L) κ.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs).
    eapply (lctx_lft_alive_incl (lft_intersect_list κs)); first by apply lctx_lft_alive_intersect_list.
    iIntros (?) "HL".
    iDestruct (big_sepL_lookup_acc with "HL") as "[Hκ Hclose]"; first done.
    rewrite {1}/llctx_elt_interp_noend /=. iDestruct "Hκ" as "#[Hincl1 Hincl2]".
    eauto.
  Qed.

  Lemma lctx_lft_alive_external E L κ κ':
    κ ⊑ₑ κ' ∈ E → lctx_lft_alive E L κ → lctx_lft_alive E L κ'.
  Proof.
    intros. by eapply lctx_lft_alive_incl, lctx_lft_incl_external.
  Qed.

  (* External lifetime context satisfiability *)
  Definition elctx_sat E L E' : Prop :=
    ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ elctx_interp E').

  Lemma elctx_sat_nil E L : elctx_sat E L [].
  Proof. iIntros (?) "_ !> _". by rewrite /elctx_interp /=. Qed.

  Lemma elctx_sat_lft_incl E L E' κ κ' :
    lctx_lft_incl E L κ κ' → elctx_sat E L E' → elctx_sat E L ((κ ⊑ₑ κ') :: E').
  Proof.
    iIntros (Hκκ' HE' qL) "HL".
    iDestruct (Hκκ' with "HL") as "#Hincl".
    iDestruct (HE' with "HL") as "#HE'".
    iClear "∗". iIntros "!> #HE". iSplit.
    - by iApply "Hincl".
    - by iApply "HE'".
  Qed.

  Lemma elctx_sat_app E L E1 E2 :
    elctx_sat E L E1 → elctx_sat E L E2 → elctx_sat E L (E1 ++ E2).
  Proof.
    iIntros (HE1 HE2 ?) "HL".
    iDestruct (HE1 with "HL") as "#HE1".
    iDestruct (HE2 with "HL") as "#HE2".
    iClear "∗". iIntros "!> #HE".
    iDestruct ("HE1" with "HE") as "#$".
    iApply ("HE2" with "HE").
  Qed.

  Lemma elctx_sat_refl E L : elctx_sat E L E.
  Proof. iIntros (?) "_ !> ?". done. Qed.


  (* [κs] and [L'] are "outputs", as getting a token for κ has side-effects  *)
  Definition lctx_lft_alive_count E L (κ : lft) κs L' : Prop :=
    (∀ F, lftE ⊆ F →
      elctx_interp E -∗
      llctx_interp L ={F}=∗
      llft_elt_toks κs ∗
      (llft_elt_toks κs ={F}=∗ ∃ q, q.[κ] ∗ (q.[κ] ={F}=∗ llft_elt_toks κs)) ∗
      llctx_interp L').
  Lemma lctx_lft_alive_count_tok F E L κ κs L' :
    lftE ⊆ F →
    lctx_lft_alive_count E L κ κs L' →
    elctx_interp E -∗
    llctx_interp L ={F}=∗ ∃ q,
    q.[κ] ∗ (q.[κ] ={F}=∗ llft_elt_toks κs) ∗ llctx_interp L'.
  Proof.
    iIntros (? Hal) "HE HL".
    iMod (Hal with "HE HL") as "(Htoks & Hvs & $)"; first done.
    iMod ("Hvs" with "Htoks") as (q) "(Htok & Hvs)".
    eauto with iFrame.
  Qed.

  Lemma lctx_lft_alive_count_static E L : lctx_lft_alive_count E L static [] L.
  Proof.
    iIntros (F ?) "_ $".
    iModIntro. iSplitR; first by iApply big_sepL_nil.
    iIntros "_". iExists 1%Qp. iSplitL.
    - iApply lft_tok_static.
    - iIntros "!>_". by iApply big_sepL_nil.
  Qed.

  Fixpoint lctx_lft_alive_count_iter E L κs κs' L' : Prop :=
    match κs with
    | [] => κs' = [] ∧ L' = L
    | κ :: κs =>
        ∃ κs1 κs2 L1,
          lctx_lft_alive_count E L κ κs1 L1 ∧
          lctx_lft_alive_count_iter E L1 κs κs2 L' ∧
          κs' = κs1 ++ κs2
    end.
  Lemma lctx_lft_alive_count_iter_elim E L κs κs' L' :
    lctx_lft_alive_count_iter E L κs κs' L' →
    (∀ F, lftE ⊆ F →
    elctx_interp E -∗
    llctx_interp L ={F}=∗
    llft_elt_toks κs' ∗
    (llft_elt_toks κs' ={F}=∗ ∃ q, q.[lft_intersect_list κs] ∗ (q.[lft_intersect_list κs] ={F}=∗ llft_elt_toks κs')) ∗
    llctx_interp L').
  Proof.
    induction κs as [ | κ κs IH] in κs', L', L |-*.
    - simpl. intros [-> ->]. by apply lctx_lft_alive_count_static.
    - simpl. intros (κs1 & κs2 & L1 & Hal & Hi & ->).
      iIntros (? ?) "#HE HL". iMod (Hal with "HE HL") as "(Hκs1 & Hcl1 & HL1)"; first done.
      iMod (IH with "HE HL1") as "(Hκs2 & Hcl2 & HL2)"; [done.. | ].
      iModIntro. rewrite {1 2}llft_elt_toks_app. iFrame.
      iIntros "(Hκs1 & Hκs2)".
      iMod ("Hcl1" with "Hκs1") as "(%q1 & Htok1 & Hcl1)".
      iMod ("Hcl2" with "Hκs2") as "(%q2 & Htok2 & Hcl2)".
      set (q' := (Qp.min q1 q2)%Qp).
      iExists q'.
      rewrite -lft_tok_sep.
      iPoseProof (Fractional_fractional_le (λ q, q.[κ])%I q1 q' with "Htok1") as "[$ Hvs1]".
      { apply Qp.le_min_l. }
      iPoseProof (Fractional_fractional_le (λ q, q.[lft_intersect_list κs])%I q2 q' with "Htok2") as "[$ Hvs2]".
      { apply Qp.le_min_r. }
      iIntros "!>[Hκ1 Hκ2]".
      rewrite llft_elt_toks_app.
      iMod ("Hcl1" with "(Hvs1 Hκ1)") as "$".
      iMod ("Hcl2" with "(Hvs2 Hκ2)") as "$".
      done.
  Qed.
  Lemma lctx_lft_alive_count_local_owned E L κ i c κs κs' L' :
    lctx_lft_alive_count_iter E L κs κs' L' →
    (L' !! i = Some (κ ⊑ₗ{c} κs)) →
    lctx_lft_alive_count E L κ (κ :: κs') (<[i := κ ⊑ₗ{S c} κs]> L').
  Proof.
    iIntros (Hal Hlook).
    iIntros (F ?) "#HE HL".
    iMod (lctx_lft_alive_count_iter_elim with "HE HL") as "(Hκs & Hcl & HL)"; [done | done | ].
    (* now get the token for the local lifetime *)
    iDestruct "HL" as "HL".
    iPoseProof (big_sepL_insert_acc with "HL") as "(Hκ & HLcl)"; first done.
    iDestruct "Hκ" as (γ) "(#Hname & Hauth & #Hshape & Hkill)".
    iMod (fraction_map_auth_increase with "Hauth") as "(Hauth & Hel)".
    iSplitL "Hel Hκs".
    { iModIntro. rewrite /llft_elt_toks. iFrame.
      rewrite llft_elt_tok_eq. iExists γ. iFrame "#∗".
    }
    iSplitL "Hcl"; first last.
    { iModIntro. iApply "HLcl". iExists γ. eauto with iFrame. }
    iModIntro. rewrite {3 4}/llft_elt_toks. rewrite {1}big_sepL_cons.
    iIntros "(Hκ & Hκs)". iMod ("Hcl" with "Hκs") as (q1) "(Hκs & Hclκs)".
    rewrite {1}llft_elt_tok_eq. iClear "Hname". clear γ.
    iDestruct "Hκ" as (γ) "(#Hname & Hel)".
    iPoseProof (fraction_map_elem_acc with "Hel") as (q2) "(Hκ & Hclκ)".
    (* destruct the shape thing *)
    iDestruct "Hshape" as (ic κextra qextra)  "(#Hd & %Heq)".
    iDestruct "Hκ" as (???) "(Hd' & Hi & Hex)".
    iPoseProof (lft_decomp_agree with "Hd Hd'")as "(<- & <- & <-)".
    (* take the min of q1, q2, (q `min` qextra) * q2 *)
    set (qeff := (1 `min` qextra)%Qp).
    destruct (Qp.lower_bound q1 (qeff * q2)%Qp) as (q0 & q'1 & q'2 & -> & Hmax). rewrite Hmax.
    destruct (Qp.lower_bound q0 q2) as (q0' & q'3 & q'4 & -> & ->).
    rewrite -!Qp.add_assoc.
    rewrite !(lft_tok_fractional _ q0').
    iDestruct "Hκs" as "(Hκs1 & Hκs2)".
    iDestruct "Hi" as "(Hi1 & Hi2)".
    iDestruct "Hex" as "(Hex1 & Hex2)".
    iModIntro. iExists q0'.
    iSplitL "Hi1 Hex1 Hκs1".
    { rewrite Heq. rewrite -!lft_tok_sep. iFrame. }
    (* close everything *)
    rewrite {6}Heq. rewrite -!lft_tok_sep. iIntros "((? & ?) & ?)".
    iMod ("Hclκs" with "[$]") as "$".
    rewrite llft_elt_tok_eq.
    iModIntro. iExists γ. iFrame "Hname". iApply "Hclκ".
    iExists _, _, _. iFrame "Hd".
    rewrite Hmax !lft_tok_fractional. iFrame.
  Qed.

  Lemma lctx_lft_alive_count_local_alias E L L' κ κs κs' :
    κ ≡ₗ κs ∈ L → lctx_lft_alive_count_iter E L κs κs' L' → lctx_lft_alive_count E L κ κs' L'.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs).
    iIntros (F ?) "#HE HL".
    iDestruct (big_sepL_lookup_acc with "HL") as "[Hκ Hclose]"; first done.
    rewrite {1}/llctx_elt_interp /=. iDestruct "Hκ" as "#Hκ".
    iPoseProof ("Hclose" with "Hκ") as "HL". iDestruct "Hκ" as "[Hincl1 Hincl2]".
    iMod (lctx_lft_alive_count_iter_elim with "HE HL") as "($ & Hcl & $)"; [done | done | ].
    iModIntro. iIntros "Htoks". iMod ("Hcl" with "Htoks") as (q) "(Htok & Hcl)".
    iMod (lft_incl_acc with "Hincl2 Htok") as (q') "(Htok & Hcl2)"; first done.
    iModIntro. iExists q'. iFrame "Htok".
    iIntros "Htok". iMod ("Hcl2" with "Htok") as "Htok". by iApply "Hcl".
  Qed.

  Lemma lctx_lft_alive_count_intersect E L κ1 κ2 L1 L2 κs1 κs2 :
    lctx_lft_alive_count E L κ1 κs1 L1 → lctx_lft_alive_count E L1 κ2 κs2 L2 → lctx_lft_alive_count E L (κ1 ⊓ κ2) (κs1 ++ κs2) L2.
  Proof.
    iIntros (Hal1 Hal2).
    iIntros (F qL) "#HE HL".
    iMod (Hal1 F with "HE HL") as "(Hκs1 & Hcl1 & HL1)"; first done.
    iMod (Hal2 F with "HE HL1") as "(Hκs2 & Hcl2 & $)"; first done.
    iModIntro.
    rewrite {1 2}llft_elt_toks_app. iFrame. iIntros "(Hκs1 & Hκs2)".
    iMod ("Hcl1" with "Hκs1") as (q1) "(Hκ1 & Hcl1)".
    iMod ("Hcl2" with "Hκs2") as (q2) "(Hκ2 & Hcl2)".
    set (q' := (Qp.min q1 q2)%Qp).
    iExists q'.
    rewrite -lft_tok_sep.
    iPoseProof (Fractional_fractional_le (λ q, q.[κ1])%I q1 q' with "Hκ1") as "[$ Hvs1]".
    { apply Qp.le_min_l. }
    iPoseProof (Fractional_fractional_le (λ q, q.[κ2])%I q2 q' with "Hκ2") as "[$ Hvs2]".
    { apply Qp.le_min_r. }
    iIntros "!>[Hκ1 Hκ2]".
    rewrite llft_elt_toks_app.
    iMod ("Hcl1" with "(Hvs1 Hκ1)") as "$".
    iMod ("Hcl2" with "(Hvs2 Hκ2)") as "$".
    done.
  Qed.

  Lemma lctx_lft_alive_count_incl E L κ κ' κs L' :
    lctx_lft_alive_count E L κ κs L' → lctx_lft_incl E L κ κ' → lctx_lft_alive_count E L κ' κs L'.
  Proof.
    iIntros (Hal Hinc).
    iIntros (F qL) "#HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl".
    { iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
      iApply (Hinc with "HL HE"). }
    iMod (Hal with "HE HL") as "($ & Hcl & $)"; first done. iIntros "!> Hκs".
    iMod ("Hcl" with "Hκs") as (q) "(Htok & Hcl)".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose']"; first done.
    iExists q''. iIntros "{$Htok}!>Htok". iApply ("Hcl" with "[> -]").
    by iApply "Hclose'".
  Qed.

  Lemma lctx_lft_alive_count_external E L κ κ' κs L' :
    κ ⊑ₑ κ' ∈ E → lctx_lft_alive_count E L κ κs L' → lctx_lft_alive_count E L κ' κs L'.
  Proof.
    intros. by eapply lctx_lft_alive_count_incl, lctx_lft_incl_external.
  Qed.

  (* Once we are done, we can decrease the count again. *)
  Lemma llctx_return_elt_tok L i κ c κs :
    (L !! i = Some (κ ⊑ₗ{c} κs)) →
    llctx_interp L -∗
    llft_elt_tok κ ==∗
    llctx_interp (<[i := κ ⊑ₗ{pred c} κs]> L).
  Proof.
    iIntros (Hlook) "HL Htok".
    iDestruct "HL" as "HL".
    iPoseProof (big_sepL_insert_acc with "HL") as "(Hκ & HLclose)"; first done.
    iDestruct "Hκ" as (γ) "(#Hname & Hauth & Hshape & Hkill)".
    rewrite llft_elt_tok_eq. iDestruct "Htok" as (γ') "(Hname' & Htok)".
    iPoseProof (lft_has_gname_agree with "Hname Hname'") as "<-".
    iMod (fraction_map_auth_decrease with "Hauth Htok") as "Hauth".
    iApply "HLclose".
    iModIntro. iExists γ. iFrame "∗#".
    replace (pred c) with (c -1) by lia. done.
  Qed.

  Fixpoint llctx_release_toks (L : llctx) (κs : list lft) (L' : llctx) :=
    match κs with
    | [] => L = L'
    | κ :: κs =>
        (* we an choose to only release a subset, e.g. if κ is not in the context *)
        (∃ i c κs', L !! i = Some (κ ⊑ₗ{c} κs') ∧
        llctx_release_toks (<[i := κ ⊑ₗ{pred c} κs']> L) κs L')
        ∨ llctx_release_toks L κs L'
    end.
  Lemma llctx_return_elt_toks L κs L' :
    llctx_release_toks L κs L' →
    llctx_interp L -∗
    llft_elt_toks κs ==∗
    llctx_interp L'.
  Proof.
    induction κs as [ | κ κs IH] in L, L' |-*; simpl.
    - intros ->. eauto.
    - intros [(i & c & κs' & Hlook & Hi%IH) | Hi%IH].
      + iIntros "HL (Hκ & Hκs)".
        iMod (llctx_return_elt_tok with "HL Hκ") as "HL"; first done.
        iApply (Hi with "HL Hκs").
      + iIntros "HL (Hκ & Hκs)". iApply (Hi with "HL Hκs").
  Qed.

  (** a bit of machinery for choosing an atomic lifetime that doesn't conflict with our ghost state *)
  Lemma lft_set_fresh (M : gset lft) κ' :
    ∃ i : positive, ∀ m : positive, (i < m)%positive → (positive_to_lft m) ⊓ κ' ∉ M.
  Proof.
    setoid_rewrite <-elem_of_elements.
    generalize (elements M) as l.
    induction l as [ | κ l IH].
    - exists 1%positive. intros m ? []%elem_of_nil.
    - destruct IH as (i & IH). destruct (lft_fresh_strong κ κ') as (i' & Hi).
      exists (Pos.max i i'). intros m Hlt [ | ]%elem_of_cons.
      + eapply Hi; last done. lia.
      + eapply IH; last done. lia.
  Qed.
  Lemma pred_infinite_upclosed_pos (P : positive → Prop) :
    (∃ n, ∀ m, (n < m)%positive → P m) →
    pred_infinite P.
  Proof.
    intros (n & Hn).
    intros xs. exists (Pos.succ (foldr Pos.max (n)%positive xs))%positive.
    split.
    - apply Hn. induction xs as [ | k xs IH]; simpl; lia.
    - enough (∀ x, x ∈ xs → x < Pos.succ (foldr Pos.max n xs))%positive as H.
      { intros Hin%H. lia. }
      induction xs as [ | k xs IH]; simpl.
      + intros ? []%elem_of_nil.
      + intros ? [ | H ]%elem_of_cons; first lia.
        apply IH in H. lia.
  Qed.
  Definition startlft_choose_pred (M : gset lft) (κ' : lft) := (λ i : positive, positive_to_lft i ⊓ κ'  ∉ M).
  Lemma startlft_choose_pred_infinite M κ' : pred_infinite (startlft_choose_pred M κ').
  Proof.
    eapply pred_infinite_upclosed_pos. apply lft_set_fresh.
  Qed.

  Lemma llctx_elt_reclaim F qex κex κs κ κi :
    lftE ⊆ F →
    lft_userE ⊆ F →
    llctx_elt_interp (κ ⊑ₗ{0} κs) -∗
    lft_decomp κ κi κex qex -∗
    (1 `min` qex).[κex] ∗ (|={F}[lft_userE]▷=> [† κ]).
  Proof.
    iIntros (??) "Hel #Hde".
    iDestruct "Hel" as "(%γfrac' & Hname' & Hauth & Hshape & Hkill)".
    iDestruct "Hshape" as "(%i' & %κex' & %qex'' & Hde' & %Heq)".
    iPoseProof (lft_decomp_agree with "Hde Hde'") as "(<- & <- & <-)".
    iPoseProof (fraction_map_auth_acc_0 with "Hauth") as "(Hκ & _)".
    iDestruct "Hκ" as "(% & % & % & Hde'' & Hi & Hex)".
    iPoseProof (lft_decomp_agree with "Hde Hde''") as "(<- & <- & <-)".
    iDestruct "Hkill" as "(% & % & % & Hde''' & Hkill)".
    iPoseProof (lft_decomp_agree with "Hde Hde'''") as "(<- & <- & <-)".
    rewrite Qp.mul_1_r. iFrame. iApply step_fupd_fupd.
    iPoseProof (step_fupd_mask_mono with "(Hkill Hi)") as "Ha";
      last iApply (step_fupd_wand with "Ha"); [set_solver .. | ].
    iIntros "Hdead". iClear "Hname' Hde". rewrite Heq.
    iApply (lft_incl_dead with "[] Hdead"); first done.
    iApply lft_incl_trans; first iApply lft_intersect_incl_l.
    iApply lft_intersect_incl_r.
  Qed.

  (** find an item in the local lifetime context that matches a certain property *)
  Inductive llctx_find_llft_key : Type :=
    | LlctxFindLftFull
    | LlctxFindLftOwned
    | LlctxFindLftAlias.
  Definition llctx_find_lft_key_interp key (κ : lft) oc :=
    match key with
    | LlctxFindLftFull => oc = Some 0%nat
    | LlctxFindLftOwned => is_Some oc
    | LlctxFindLftAlias => oc = None
    end.
  Definition llctx_find_llft (L : llctx) (κ : lft) (key : llctx_find_llft_key) (κs : list lft) (L' : llctx) :=
    ∃ A B oc, L = A ++ ((oc, κ, κs)) :: B ∧ L' = A ++ B ∧ llctx_find_lft_key_interp key κ oc.

  Lemma llctx_end_llft F L L' κ κs :
    lftE ⊆ F →
    lft_userE ⊆ F →
    llctx_find_llft L κ LlctxFindLftFull κs L' →
    llctx_interp L ={F}[lft_userE]▷=∗
    [† κ] ∗ llctx_interp L'.
  Proof.
    iIntros (? ? Hfind) "HL".
    destruct Hfind as (A & B & oc & -> & -> & Hoc).
    simpl in Hoc. rewrite Hoc.
    iDestruct "HL" as "(? & Helt & ?)".
    iAssert (∃ κi κex qex, lft_decomp κ κi κex qex ∗ llctx_elt_interp (κ ⊑ₗ{ 0} κs))%I with "[Helt]" as "Ha".
    { iDestruct "Helt" as "(%γ & Hname & Hauth & #Hshape & Hkill)".
      iDestruct "Hshape" as "(% & % & % & Hde & ?)".
      iExists _, _, _. iFrame "Hde". iExists _. iFrame. iExists _, _, _. eauto with iFrame. }
    iDestruct "Ha" as "(% & % & % & Hde & Helt)".
    iFrame. iPoseProof (llctx_elt_reclaim with "Helt Hde") as "(_ & $)"; done.
  Qed.

  (** Start a lifetime with some [κex] that the lifetime is intersected with.
    We can keep track of this, and later on reclaim the fraction [qex] of [κex].
    This is primarily used for calling functions. *)
  Lemma llctx_startlft_extra F qex κex κs :
    lftE ⊆ F →
    ↑llctxN ⊆ F →
    lft_userE ⊆ F →
    lft_ctx -∗
    llctx_ctx -∗
    qex.[κex] ={F}=∗
    ∃ κ, llctx_elt_interp (κ ⊑ₗ{0} κs) ∗ ⌜κ ⊑ˢʸⁿ κex⌝ ∗
      (∀ κs', llctx_elt_interp (κ ⊑ₗ{0} κs') -∗ qex.[κex] ∗ |={F}[lft_userE]▷=> [† κ]).
  Proof.
    iIntros (???) "#LFT #LCTX Hex". rewrite llctx_ctx_eq.
    iInv "LCTX" as "(%M & %M' & >Hauth_name & >Hauth_decomp & >%Hdom)" "Hcl".
    set (κ' := lft_intersect_list κs ⊓ κex).
    set (P := startlft_choose_pred (dom M) κ').
    iMod (lft_create_strong P with "LFT") as "(%i & %Hfresh & Htok & Hkill)";
      [apply startlft_choose_pred_infinite | solve_ndisj | ].
    set (κ := positive_to_lft i ⊓ κ').
    assert (M !! κ = None) as Hfresh'.
    { apply not_elem_of_dom. apply Hfresh. }
    (* allocate ghost state *)
    destruct (Qp.lower_bound qex (1 `min` qex)) as (qex' & q1 & q2 & -> & Heq).
    assert (1 `min` qex' = qex')%Qp as Hle.
    { rewrite (proj2 (Qp.min_r_iff _ _)); first done.
      trans (qex' + q2)%Qp.
      - apply Qp.le_add_l.
      - rewrite -Heq. apply Qp.le_min_l.
    }
    iDestruct "Hex" as "(Hex1 & Hex2)".
    iMod (ghost_map_insert_persist κ (i, κex, qex') with "Hauth_decomp") as "(Hauth_decomp & #Hde)".
    { apply not_elem_of_dom. rewrite -Hdom. apply not_elem_of_dom. done. }
    iMod (fraction_map_auth_alloc (llft_own_frac κ) with "[Htok Hex1]") as "(%γfrac & Hfrac)".
    { iExists _, _, _. rewrite lft_decomp_eq. iFrame "#∗".
      rewrite Qp.mul_1_r. rewrite Hle. done. }
    fold (lft_decomp_def κ i κex qex'). rewrite -lft_decomp_eq.
    iMod (ghost_map_insert_persist κ γfrac with "Hauth_name") as "(Hauth_name & #Hname)".
    { done. }
    fold (lft_has_gname_def κ γfrac). rewrite -lft_has_gname_eq.
    iMod ("Hcl" with "[Hauth_name Hauth_decomp]") as "_".
    { iExists _, _. iFrame. rewrite !dom_insert_L Hdom. done. }
    iModIntro. iExists κ.
    iSplitL "Hkill Hfrac".
    { iExists γfrac. iFrame "# Hfrac".
      iSplitR.
      - iExists _, _, _. iFrame "Hde".
        rewrite [_ ⊓ positive_to_lft _]lft_intersect_comm -lft_intersect_assoc. done.
      - iExists _, _, _. iFrame "Hde". done.
    }
    iSplitR.
    { iPureIntro. subst κ κ'.
      eapply lft_incl_syn_trans; eapply lft_intersect_incl_syn_r.
    }
    iFrame. iIntros (κs') "Helt".
    iPoseProof (llctx_elt_reclaim F with "Helt Hde") as "(Htok & $)"; [set_solver.. | ].
    rewrite Hle. done.
  Qed.

  Lemma llctx_startlft L F κs :
    lftE ⊆ F →
    ↑llctxN ⊆ F →
    lft_userE ⊆ F →
    lft_ctx -∗
    llctx_ctx -∗
    llctx_interp L ={F}=∗
    ∃ κ : lft,
    llctx_interp ((κ ⊑ₗ{0} κs) :: L).
  Proof.
    iIntros (???) "LFT #LCTX HL".
    iMod (llctx_startlft_extra F 1 static κs with "LFT LCTX []") as "(%κ & Helt & _)"; [set_solver.. | | ].
    - iApply lft_tok_static.
    - iModIntro. iExists κ. iFrame.
  Qed.

  (* Equalize lifetimes (by giving up tokens) *)
  Lemma llctx_owned_elem_equalize_lft_sem c κ κs F `{!frac_borG Σ} :
    lftE ⊆ F →
    lft_ctx -∗
    llctx_elt_interp (κ ⊑ₗ{c} κs) ={F}=∗
    κ ⊑ (lft_intersect_list κs) ∗ (lft_intersect_list κs) ⊑ κ.
  Proof.
    iIntros (?) "#LFT". iDestruct 1 as (γ) "(Hname & Hfrac & Hshape & _)"; simplify_eq/=.
    iPoseProof (fraction_map_auth_access with "Hfrac") as "(%q' & Ha & _ & _)".
    iDestruct "Ha" as (i κextra qextra) "(Hd1 & Hi & Hex)".
    iDestruct "Hshape" as (? ? ?) "(Hd2 & ->)".
    iPoseProof (lft_decomp_agree with "Hd1 Hd2") as "(<- & <- & <-)".
    iMod (lft_eternalize with "Hi") as "#Hincl".
    iMod (lft_eternalize with "Hex") as "#Hincl'".
    iModIntro. iSplit.
    - iApply lft_incl_trans; first iApply lft_intersect_incl_l.
      iApply lft_incl_trans; first iApply lft_intersect_incl_l.
      iApply lft_incl_refl.
    - iApply (lft_incl_glb with "[]"); first iApply (lft_incl_glb with "[]").
      + iApply lft_incl_refl.
      + iApply lft_incl_trans; last done. iApply lft_incl_static.
      + iApply lft_incl_trans; last done. iApply lft_incl_static.
  Qed.

  (* Eternalize a lifetime (by giving up tokens) *)
  Lemma llctx_owned_elem_equalize_lft_sem_static c κ F `{!frac_borG Σ} :
    lftE ⊆ F →
    lft_ctx -∗
    llctx_elt_interp (κ ⊑ₗ{c} []%list) ={F}=∗
    static ⊑ κ.
  Proof.
    iIntros (?) "#LFT". iDestruct 1 as (γ) "(Hname & Hfrac & Hshape & _)"; simplify_eq/=.
    iPoseProof (fraction_map_auth_access with "Hfrac") as "(%q' & Ha & _)".
    iDestruct "Ha" as (i κextra qextra) "(Hd1 & Hi & Hex)".
    iDestruct "Hshape" as (? ? ?) "(Hd2 & ->)".
    iPoseProof (lft_decomp_agree with "Hd1 Hd2") as "(<- & <- & <-)".
    iMod (lft_eternalize with "Hi") as "#Hincl".
    iMod (lft_eternalize with "Hex") as "#Hincl'".
    iModIntro.
    iApply (lft_incl_glb with "[]"); simpl; last done.
    iApply (lft_incl_glb with "[]"); simpl; last done.
    iApply lft_incl_refl.
  Qed.

  (** Extend a local lifetime by making its atomic part static, but in turn taking the ability to directly kill it. *)
  Lemma llctx_extendlft_local_owned `{!frac_borG Σ} F L L' κ κs :
    lftE ⊆ F →
    llctx_find_llft L κ LlctxFindLftOwned κs L' →
    lft_ctx -∗
    llctx_interp L ={F}=∗
    llctx_interp ((κ ≡ₗ κs) :: L').
  Proof.
    iIntros (? Hfind) "#CTX HL".
    destruct Hfind as (L1 & L2 & oc  & -> & -> & (c & ->)).
    iDestruct "HL" as "($ & Hel & $)".
    iMod (llctx_owned_elem_equalize_lft_sem with "CTX Hel") as "(#Hincl1 & #Hincl2)"; first done.
    iModIntro. iSplit; done.
  Qed.

  (** Inheritance of timeless propositions *)
  (* The [key : K] helps automation *)
  Definition Inherit {K} (κ : lft) (key : K) (P : iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ [† κ] ={F}=∗ P.
  Global Arguments Inherit : simpl never.
  Global Typeclasses Opaque Inherit.

  Lemma Inherit_update Q P κ {K} (k : K) :
    (∀ F, P ={F}=∗ Q) -∗
    Inherit κ k P -∗
    Inherit κ k Q.
  Proof.
    iIntros "HP Hinh".
    rewrite /Inherit. iIntros (??) "Hdead". iMod ("Hinh" with "[//] Hdead") as "Ha".
    by iApply "HP".
  Qed.

  Definition MaybeInherit {K} (κm : option lft) (k : K) (P : iProp Σ) : iProp Σ :=
    if κm is Some κ
    then Inherit κ k P
    else (∀ F, ⌜lftE ⊆ F⌝ -∗ |={F}=> P).
  (* basically, should now use introduce_with_hooks to simplify it to one of the options *)
  Global Typeclasses Opaque MaybeInherit.
  Global Arguments MaybeInherit : simpl never.

  Lemma MaybeInherit_update Q P κm {K} (k : K) :
    (∀ F, P ={F}=∗ Q) -∗
    MaybeInherit κm k P -∗
    MaybeInherit κm k Q.
  Proof.
    iIntros "HP Hinh".
    rewrite /MaybeInherit.
    destruct κm as [κ | ].
    - rewrite /Inherit. iIntros (??) "Hdead". iMod ("Hinh" with "[//] Hdead") as "Ha". by iApply "HP".
    - iIntros (??). iMod ("Hinh" with "[//]") as "HP'". by iApply "HP".
  Qed.

  Lemma Inherit_mono {K} (k : K) κ κ' P :
    κ ⊑ κ' -∗
    Inherit κ k P -∗
    Inherit κ' k P.
  Proof.
    iIntros "Hincl Hinh".
    rewrite /Inherit. iIntros (??) "Hdead".
    iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
    iApply ("Hinh" with "[//] Hdead").
  Qed.


  (** Establishing dynamic inclusion of lifetimes *)
  Inductive inherit_dyn_incl := InheritDynIncl.
  Lemma lctx_include_lft_sem E L L' F κs κ1 κ2 `{!frac_borG Σ} :
    lftE ⊆ F →
    lctx_lft_alive_count E L κ2 κs L' →
    lft_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={F}=∗
    llctx_interp L' ∗ κ1 ⊑ κ2 ∗ Inherit κ1 InheritDynIncl (llft_elt_toks κs).
  Proof.
    iIntros (? Hal) "#LFT #HE HL".
    iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Htok & Hcl & HL')"; [done.. | ].
    iMod (bor_create lftE κ1 with "LFT Htok") as "(Hb & Hinh)"; first done.
    iMod "HclF" as "_".
    set (Φ := (λ q', (q * q').[κ2])%I).
    iMod (bor_fracture Φ with "LFT [Hb]") as "#Hfrac"; first done.
    { subst Φ. simpl. rewrite Qp.mul_1_r. iFrame. }
    iPoseProof (frac_bor_lft_incl with "LFT Hfrac") as "Hincl". iFrame "#∗".
    iModIntro. rewrite /Inherit. iIntros (F' ?) "Hdead".
    iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod ("Hinh" with "Hdead") as ">Htok".
    iMod ("Hcl" with "Htok") as "?".
    by iMod "HclF" as "_".
  Qed.

  Definition lft_dead_list (κs : list lft) : iProp Σ := [∗ list] κ ∈ κs, [† κ].
  Global Instance lft_dead_list_pers κs : Persistent (lft_dead_list κs).
  Proof. apply _. Qed.
  Lemma lft_dead_list_elem κ κs :
    κ ∈ κs → lft_dead_list κs -∗ [† κ].
  Proof.
    iIntros (Hel) "Hall". iApply (big_sepL_elem_of with "Hall"). done.
  Qed.

  Lemma lft_dead_list_nil :
    lft_dead_list [] ⊣⊢ True.
  Proof. done. Qed.
  Lemma lft_dead_list_cons κ κs :
    lft_dead_list (κ :: κs) ⊣⊢ [†κ] ∗ lft_dead_list κs.
  Proof. done. Qed.
  Lemma lft_dead_list_app κs1 κs2 :
    lft_dead_list (κs1 ++ κs2) ⊣⊢ lft_dead_list κs1 ∗ lft_dead_list κs2.
  Proof.
    induction κs1 as [ | κ κs1 IH]; simpl.
    { rewrite lft_dead_list_nil left_id. eauto. }
    rewrite lft_dead_list_cons IH. rewrite bi.sep_assoc //.
  Qed.
End lft_contexts.

Arguments lft_dead_list : simpl never.
Arguments llctx_elt_interp : simpl never.
Arguments lctx_lft_incl {_ _ _ _} _ _ _ _.
Arguments lctx_lft_eq {_ _ _ _} _ _ _ _.
Arguments lctx_lft_alive {_ _ _ _} _ _ _.
Arguments elctx_sat {_ _ _ _} _ _ _.
Arguments lctx_lft_incl_incl {_ _ _ _ _} _ _ _.
(*Arguments lctx_lft_incl_incl_noend {_ _ _ _} _ _.*)
(*Arguments lctx_lft_alive_tok {_ _ _ _ _} _ _ _.*)
Arguments lctx_lft_alive_tok_noend {_ _ _ _ _ _} _ _ _.

Lemma elctx_sat_submseteq `{!invGS Σ, !lctxGS Σ, !lftGS Σ lft_userE} E E' L :
  E' ⊆+ E → elctx_sat E L E'.
Proof. iIntros (HE' ?) "_ !> H". by iApply big_sepL_submseteq. Qed.

Global Hint Opaque elctx_sat lctx_lft_alive lctx_lft_alive_count lctx_lft_incl llft_elt_tok llft_elt_toks : refinedc_typing.
Global Arguments llft_elt_toks : simpl never.
Global Typeclasses Opaque llft_elt_toks.

Lemma lft_intersect_list_app κs κs' :
  lft_intersect_list (κs ++ κs') = (lft_intersect_list κs) ⊓ (lft_intersect_list κs').
Proof.
  induction κs as [ | κ κs IH]; simpl.
  { rewrite left_id. done. }
  rewrite -assoc IH //.
Qed.

Lemma list_incl_lft_incl_list `{!invGS Σ, !lctxGS Σ, !lftGS Σ lft_userE} κs1 κs2 :
  κs1 ⊆ κs2 →
  ⊢ lft_intersect_list κs2 ⊑ lft_intersect_list κs1.
Proof.
  induction κs1 as [ | κ κs1 IH]; simpl.
  { intros. iApply lft_incl_static. }
  intros Hincl.
  efeed pose proof (Hincl κ) as Helem.
  { apply elem_of_cons; by left. }
  iApply (lft_incl_trans _ (κ ⊓ lft_intersect_list κs2)); first last.
  { iApply lft_intersect_mono; first iApply lft_incl_refl.
    iApply IH. intros κ0 Hel. apply Hincl.
    apply elem_of_cons; by right. }
  clear -Helem.
  iInduction κs2 as [ | κ' κs2] "IH"; simpl.
  { apply elem_of_nil in Helem. done. }
  apply elem_of_cons in Helem as [ <- | Helem].
  - rewrite lft_intersect_assoc.
    iApply lft_intersect_mono; last iApply lft_incl_refl.
    iApply lft_incl_glb; iApply lft_incl_refl.
  - rewrite lft_intersect_assoc [κ ⊓ κ']lft_intersect_comm -lft_intersect_assoc.
    iApply lft_intersect_mono; first iApply lft_incl_refl.
    by iApply "IH".
Qed.
