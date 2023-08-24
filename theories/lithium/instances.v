From lithium Require Export base.
From lithium Require Import syntax definitions proof_state.

(** This file collects the default instances for the definitions in
[definitions.v]. Note that these instances must be in a separate file
since the instances are defined using the notation from
[proof_state.v]. *)

(** * [find_in_context] *)
Lemma find_in_context_direct {Σ B} P (T : B → iProp Σ):
  find_in_context (FindDirect P) T :- pattern: x, P x; return T x.
Proof. done. Qed.
Definition find_in_context_direct_inst := [instance @find_in_context_direct with FICSyntactic].
Global Existing Instance find_in_context_direct_inst | 1.

(** * Simplification *)
Lemma simplify_hyp_id {Σ} (P T : iProp Σ) :
  simplify_hyp P T :- return T.
Proof. iIntros "HT Hl". iFrame. Qed.
Definition simplify_hyp_id_inst Σ (P : iProp Σ) :=
  [instance simplify_hyp_id P as SimplifyHyp P None].
Global Existing Instance simplify_hyp_id_inst | 100.

Lemma simplify_goal_id {Σ} (P : iProp Σ) T :
  simplify_goal P T :- exhale P; return T.
Proof. iIntros "$". Qed.
Definition simplify_goal_id_inst Σ (P : iProp Σ) :=
  [instance simplify_goal_id P as SimplifyGoal P None].
Global Existing Instance simplify_goal_id_inst | 100.

(** * Subsumption *)
(** ** [subsume] *)
Lemma subsume_id {Σ} (P : iProp Σ) T:
  subsume P P T :- return T.
Proof. iIntros "$ $". Qed.
Definition subsume_id_inst := [instance @subsume_id].
Global Existing Instance subsume_id_inst | 1.

Lemma subsume_simplify {Σ} (P1 P2 : iProp Σ) o1 o2 T :
  ∀ {SH : SimplifyHyp P1 o1} {SG : SimplifyGoal P2 o2} `{!TCOneIsSome o1 o2},
    let GH := (SH (P2 ∗ T)%I).(i2p_P) in
    let GG := (P1 -∗ (SG T).(i2p_P))%I in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then GG else GH
     | Some n1, _ => GH
     | _, _ => GG
       end in
    subsume P1 P2 T :- return G.
Proof.
  iIntros (???) "/= Hs Hl".
  destruct o1 as [n1|], o2 as [n2|] => //. 1: case_match.
  1,3,4: by iDestruct (i2p_proof with "Hs Hl") as "Hsub".
  all: iDestruct ("Hs" with "Hl") as "HSG".
  all: iDestruct (i2p_proof with "HSG") as "$".
Qed.
Definition subsume_simplify_inst := [instance @subsume_simplify].
Global Existing Instance subsume_simplify_inst | 1000.

(** ** [subsume_list] *)
Lemma subsume_list_eq {Σ} A ig (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  subsume_list A ig l1 l2 f T :- exhale ⌜list_subequiv ig l1 l2⌝; return T.
Proof.
  iDestruct 1 as (Hequiv) "$". iIntros "Hl".
  have [Hlen _]:= Hequiv 0. iSplit; first done.
  iInduction l1 as [|x l1] "IH" forall (f ig l2 Hlen Hequiv); destruct l2 => //=.
  iDestruct "Hl" as "[Hx Hl]". move: Hlen => /= [?].
  iSplitL "Hx".
  - case_bool_decide as Hb => //. have [_ /= Heq]:= Hequiv 0. by  move: (Heq Hb) => [->].
  - iDestruct ("IH" $! (f ∘ S) (pred <$> (filter (λ x, x ≠ 0%nat) ig)) l2 with "[//] [%] [Hl]") as "Hl". {
      move => i. split => // Hin. move: (Hequiv (S i)) => [_ /= {}Hequiv]. apply: Hequiv.
      contradict Hin. apply elem_of_list_fmap. eexists (S i). split => //.
        by apply elem_of_list_filter.
    }
    + iApply (big_sepL_impl with "Hl"). iIntros "!>" (k ??) "Hl".
      case_bool_decide as Hb1; case_bool_decide as Hb2 => //.
      contradict Hb2. apply elem_of_list_fmap. eexists (S k). split => //.
        by apply elem_of_list_filter.
    + iApply (big_sepL_impl with "Hl"). iIntros "!>" (k ??) "Hl".
      case_bool_decide as Hb1; case_bool_decide as Hb2 => //.
      contradict Hb2. move: Hb1 => /elem_of_list_fmap[[|?][? /elem_of_list_filter [??]]] //.
      by simplify_eq/=.
Qed.
Definition subsume_list_eq_inst := [instance @subsume_list_eq].
Global Existing Instance subsume_list_eq_inst | 1000.

Lemma subsume_list_insert_in_ig {Σ} A ig i x (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  subsume_list A ig (<[i := x]>l1) l2 f T where `{!CanSolve (i ∈ ig)} :-
  return subsume_list A ig l1 l2 f T.
Proof.
  unfold CanSolve => ?. iIntros "Hsub Hl".
  rewrite insert_length. iApply "Hsub".
  destruct (decide (i < length l1)%nat). 2: { by rewrite list_insert_ge; [|lia]. }
  iDestruct (big_sepL_insert_acc with "Hl") as "[_ Hl]". { by apply: list_lookup_insert. }
  have [//|y ?]:= lookup_lt_is_Some_2 l1 i.
  iDestruct ("Hl" $! y with "[]") as "Hl". { by case_decide. }
  by rewrite list_insert_insert list_insert_id.
Qed.
Definition subsume_list_insert_in_ig_inst := [instance @subsume_list_insert_in_ig].
Global Existing Instance subsume_list_insert_in_ig_inst.

Lemma subsume_list_insert_not_in_ig {Σ} A ig i x (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  subsume_list A ig (<[i := x]>l1) l2 f T where `{!CanSolve (i ∉ ig)} :-
      exhale ⌜i < length l1⌝%nat;
      {subsume_list A (i :: ig) l1 l2 f};
      ∀ x2, inhale ⌜l2 !! i = Some x2⌝;
      (f i x) :> (f i x2);
      return T.
Proof.
  unfold CanSolve. iIntros (?) "[% Hsub] Hl". rewrite big_sepL_insert // insert_length.
  iDestruct "Hl" as "[Hx Hl]". case_bool_decide => //.
  iDestruct ("Hsub" with "[Hl]") as "[% [Hl HT]]". {
    iApply (big_sepL_impl with "Hl"). iIntros "!>" (???) "?".
    repeat case_decide => //; set_solver.
  }
  iSplit => //.
  have [//|y ?]:= lookup_lt_is_Some_2 l2 i. { lia. }
  iDestruct ("HT" with "[//] Hx") as "[Hf $]".
  rewrite -{2}(list_insert_id l2 i y) // big_sepL_insert; [|lia]. case_bool_decide => //. iFrame.
  iApply (big_sepL_impl with "Hl"). iIntros "!>" (???) "?".
  repeat case_decide => //; set_solver.
Qed.
Definition subsume_list_insert_not_in_ig_inst := [instance @subsume_list_insert_not_in_ig].
Global Existing Instance subsume_list_insert_not_in_ig_inst.

Lemma subsume_list_trivial_eq {Σ} A ig (l : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  subsume_list A ig l l f T :- return T.
Proof. by iIntros "$ $". Qed.
Definition subsume_list_trivial_eq_inst := [instance @subsume_list_trivial_eq].
Global Existing Instance subsume_list_trivial_eq_inst | 5.

Lemma subsume_list_cons_l {Σ} A ig (x1 : A) (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  subsume_list A ig (x1 :: l1) l2 f T :-
    exhale ⌜0 ∉ ig⌝;
    ∃ x2 l2', exhale ⌜l2 = x2 :: l2'⌝;
    (f 0%nat x1) :> (f 0%nat x2);
    {subsume_list A (pred <$> ig) l1 l2' (λ i, f (S i)) T}.
Proof.
  iIntros "[% Hs]". iDestruct "Hs" as (???) "Hs". subst.
  rewrite /subsume_list !big_sepL_cons /=.
  case_bool_decide => //. iIntros "[H0 H]".
  iDestruct ("Hs" with "H0") as "[$ Hs]".
  iDestruct ("Hs" with "[H]") as (->) "[H $]"; [|iSplit => //].
  all: iApply (big_sepL_impl with "H"); iIntros "!#" (???) "?".
  all: case_bool_decide as Hx1 => //; case_bool_decide as Hx2 => //; contradict Hx2.
  - set_unfold. eexists _. split; [|done]. done.
  - by move: Hx1 => /(elem_of_list_fmap_2 _ _ _)[[|?]//=[->?]].
Qed.
Definition subsume_list_cons_l_inst := [instance @subsume_list_cons_l].
Global Existing Instance subsume_list_cons_l_inst | 40.
