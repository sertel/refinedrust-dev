(** Main typeclasses of Lithium *)
From iris.base_logic.lib Require Export iprop.
From iris.proofmode Require Export tactics.
From lithium Require Export base infrastructure.

(** * [iProp_to_Prop] *)
Record iProp_to_Prop {Σ} (P : iProp Σ) : Type := i2p {
  i2p_P :> iProp Σ;
  i2p_proof : i2p_P -∗ P;
}.
Arguments i2p {_ _ _} _.
Arguments i2p_P {_ _} _.
Arguments i2p_proof {_ _} _.

(** * [find_in_context] *)
(** ** Definition  *)
Record find_in_context_info {Σ} : Type := {
  fic_A : Type;
  fic_Prop : fic_A → iProp Σ;
}.
(* The nat n is necessary to allow different options. *)
Definition find_in_context {Σ} (fic : find_in_context_info) (T : fic.(fic_A) → iProp Σ) : iProp Σ :=
  (∃ b, fic.(fic_Prop) b ∗ T b).
Class FindInContext {Σ} (fic : find_in_context_info) (key : Set) : Type :=
  find_in_context_proof T: iProp_to_Prop (Σ:=Σ) (find_in_context fic T)
.
Global Hint Mode FindInContext + + - : typeclass_instances.
Inductive FICSyntactic : Set :=.

(** ** Instances  *)
Definition FindDirect {Σ A} (P : A → iProp Σ) := {| fic_A := A; fic_Prop := P; |}.
Global Typeclasses Opaque FindDirect.

Lemma find_in_context_direct {Σ B} P (T : B → iProp Σ):
  (∃ x : B, P x ∗ T x) -∗
   find_in_context (FindDirect P) T.
Proof. done. Qed.
Global Instance find_in_context_direct_inst {Σ B} (P : _ → iProp Σ) :
  FindInContext (FindDirect P) FICSyntactic | 1 :=
  λ T : B → _, i2p (find_in_context_direct P T).

(** ** [FindHypEqual]  *)
Class FindHypEqual {Σ} (key : Type) (Q P P' : iProp Σ) := find_hyp_equal_equal: P = P'.
Global Hint Mode FindHypEqual + + + ! - : typeclass_instances.

(** * [find_related_in_context] *)
(** ** Definition  *)
Record find_related_in_context_info {Σ} : Type := {
  fric_A : Type;
  fric_Prop : fric_A → iProp Σ;
  fric_Cert : fric_A → Prop;
}.
Definition find_related_in_context {Σ} (fric : find_related_in_context_info) (T : fric.(fric_A) → iProp Σ) : iProp Σ :=
  (∃ b, fric.(fric_Prop) b ∗ ⌜fric.(fric_Cert) b⌝ ∗ T b).
Class FindRelatedInContext {Σ} (fric : find_related_in_context_info) (key : Set) : Type :=
  find_related_in_context_proof T: iProp_to_Prop (Σ:=Σ) (find_related_in_context fric T)
.
Global Hint Mode FindRelatedInContext + + - : typeclass_instances.

(** * [destruct_hint] *)
Inductive destruct_hint_info :=
| DHintInfo
| DHintDestruct (A : Type) (x : A)
| DHintDecide (P : Prop) `{!Decision P}.
Definition destruct_hint {Σ B} (hint : destruct_hint_info) (info : B) (T : iProp Σ) : iProp Σ := T.
Global Typeclasses Opaque destruct_hint.
Arguments destruct_hint : simpl never.

(** * [tactic_hint] *)
Class TacticHint {Σ A} (t : (A → iProp Σ) → iProp Σ) := {
  tactic_hint_P : (A → iProp Σ) → iProp Σ;
  tactic_hint_proof T : tactic_hint_P T -∗ t T;
}.
Arguments tactic_hint_proof {_ _ _} _ _.
Arguments tactic_hint_P {_ _ _} _ _.

Definition tactic_hint {Σ A} (t : (A → iProp Σ) → iProp Σ) (T : A → iProp Σ) : iProp Σ :=
  t T.
Arguments tactic_hint : simpl never.

(** ** [vm_compute_hint] *)
Definition vm_compute_hint {Σ A B} (f : A → option B) (x : A) (T : B → iProp Σ) : iProp Σ :=
  ∃ y, ⌜f x = Some y⌝ ∗ T y.
Arguments vm_compute_hint : simpl never.
Global Typeclasses Opaque vm_compute_hint.

Program Definition vm_compute_hint_hint {Σ A B} (f : A → option B) x a :
  f a = Some x →
  TacticHint (vm_compute_hint (Σ:=Σ) f a) := λ H, {|
    tactic_hint_P T := T x;
|}.
Next Obligation. move => ????????. iIntros "HT". iExists _. iFrame. iPureIntro. naive_solver. Qed.

Global Hint Extern 10 (TacticHint (vm_compute_hint _ _)) =>
  eapply vm_compute_hint_hint; evar_safe_vm_compute : typeclass_instances.

(** * [RelatedTo] *)
Class RelatedTo {Σ} (pat : iProp Σ) : Type := {
  rt_fic : find_in_context_info (Σ:=Σ);
}.
Global Hint Mode RelatedTo + + : typeclass_instances.
Arguments rt_fic {_ _} _.

(** * [IntroPersistent] *)
(** ** Definition *)
Class IntroPersistent {Σ} (P P' : iProp Σ) := {
  ip_persistent : P -∗ □ P'
}.
Global Hint Mode IntroPersistent + + - : typeclass_instances.
(** ** Instances *)
Global Instance intro_persistent_intuit Σ (P : iProp Σ) : IntroPersistent (□ P) P.
Proof. constructor. iIntros "$". Qed.

(** * [accu] *)
Definition accu {Σ} (f : iProp Σ → iProp Σ) : iProp Σ :=
  ∃ P, P ∗ □ f P.
Arguments accu : simpl never.
Global Typeclasses Opaque accu.


(** * Simplification *)
(** ** Definition *)
(* n:
   None: no simplification
   Some 0: simplification which is always safe
   Some n: lower n: should be done before higher n (when compared with simplifyGoal)   *)
Definition simplify_hyp {Σ} (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
  P -∗ T.
Class SimplifyHyp {Σ} (P : iProp Σ) (n : option N) : Type :=
  simplify_hyp_proof T : iProp_to_Prop (simplify_hyp P T).

Definition simplify_goal {Σ} (P : iProp Σ) (T : iProp Σ → iProp Σ) : iProp Σ :=
  (∃ P2, (P2 -∗ P) ∗ T P2).
Class SimplifyGoal {Σ} (P : iProp Σ) (n : option N) : Type :=
  simplify_goal_proof T : iProp_to_Prop (simplify_goal P T).

Global Hint Mode SimplifyHyp + + - : typeclass_instances.
Global Hint Mode SimplifyGoal + ! - : typeclass_instances.

(** ** Instances *)
Lemma simplify_hyp_id {Σ} (P : iProp Σ) T:
  T -∗ simplify_hyp P T.
Proof. iIntros "HT Hl". iFrame. Qed.
Global Instance simplify_hyp_id_inst {Σ} (P : iProp Σ):
  SimplifyHyp P None | 100 :=
  λ T, i2p (simplify_hyp_id P T).

Lemma simplify_goal_id {Σ} (P : iProp Σ) T:
  T P -∗ simplify_goal P T.
Proof. iIntros "HT". iExists _. iFrame. by iIntros "?". Qed.
Global Instance simplify_goal_id_inst {Σ} (P : iProp Σ):
  SimplifyGoal P None | 100 :=
  λ T, i2p (simplify_goal_id P T).

(* TODO: Is the following useful? *)
(* Lemma simplify_persistent_pure_goal {Σ} (Φ : Prop) T: *)
(*   T ⌜Φ⌝ -∗ simplify_goal (Σ := Σ) (□ ⌜Φ⌝) T. *)
(* Proof. iIntros "HT". iExists _. iFrame. by iIntros (?). Qed. *)
(* Global Instance simplify_persistent_pure_goal_id {Σ} (Φ : Prop): *)
(*   SimplifyGoal (Σ:=Σ) (□ ⌜Φ⌝) (Some 0%N) := *)
(*   λ T, i2p (simplify_persistent_pure_goal Φ T). *)

(* Lemma simplify_persistent_pure_hyp {Σ} (Φ : Prop) T: *)
(*   (⌜Φ⌝ -∗ T) -∗ simplify_hyp (Σ := Σ) (□ ⌜Φ⌝) T. *)
(* Proof. iIntros "HT" (?). by iApply "HT". Qed. *)
(* Global Instance simplify_persistent_pure_hyp_inst {Σ} (Φ : Prop): *)
(*   SimplifyHyp (Σ:=Σ) (□ ⌜Φ⌝) (Some 0%N) := *)
(*   λ T, i2p (simplify_persistent_pure_hyp Φ T). *)

(* Lemma simplify_persistent_sep_hyp {Σ} (P Q : iProp Σ) T: *)
(*   (□ P -∗ □ Q -∗ T) -∗ simplify_hyp (Σ := Σ) (□ (P ∗ Q)) T. *)
(* Proof. iIntros "HT [HP HQ]". iApply ("HT" with "HP HQ"). Qed. *)
(* Global Instance simplify_persistent_sep_hyp_inst {Σ} (P Q : iProp Σ): *)
(*   SimplifyHyp (Σ:=Σ) (□ (P ∗ Q)) (Some 0%N) := *)
(*   λ T, i2p (simplify_persistent_sep_hyp P Q T). *)

(** * Subsumption *)
(** ** Definition *)
Definition subsume {Σ} (P1 P2 T : iProp Σ) : iProp Σ :=
  P1 -∗ P2 ∗ T.
Class Subsume {Σ} (P1 P2 : iProp Σ) : Type :=
  subsume_proof T : iProp_to_Prop (subsume P1 P2 T).
Definition subsume_list {Σ} A (ig : list nat) (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) : iProp Σ :=
  ([∗ list] i↦x∈l1, if bool_decide (i ∈ ig) then True%I else f i x) -∗
       ⌜length l1 = length l2⌝ ∗ ([∗ list] i↦x∈l2, if bool_decide (i ∈ ig) then True%I else f i x) ∗ T.
Class SubsumeList {Σ} A (ig : list nat) (l1 l2 : list A) (f : nat → A → iProp Σ) :  Type :=
  subsume_list_proof T : iProp_to_Prop (subsume_list A ig l1 l2 f T).

Global Hint Mode Subsume + + ! : typeclass_instances.
Global Hint Mode SubsumeList + + + + + ! : typeclass_instances.

(** ** Instances *)
Lemma subsume_id {Σ} (P : iProp Σ) T:
  T -∗ subsume P P T.
Proof. iIntros "$ $". Qed.
Global Instance subsume_id_inst {Σ} (P : iProp Σ) : Subsume P P | 1 := λ T, i2p (subsume_id P T).

Lemma subsume_simplify {Σ} (P1 P2 : iProp Σ) T o1 o2 {SH : SimplifyHyp P1 o1} {SG : SimplifyGoal P2 o2}:
    let GH := (SH (P2 ∗ T)%I).(i2p_P) in
    let GG := (SG (λ P, P1 -∗ P ∗ T)%I).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then GG else GH
     | Some n1, _ => GH
     | _, _ => GG
       end in
    G -∗ subsume P1 P2 T.
Proof.
  iIntros "Hs Hl".
  destruct o1 as [n1|], o2 as [n2|] => //. case_match.
  1,3,4: by iDestruct (i2p_proof with "Hs Hl") as "Hsub".
  all: iDestruct (i2p_proof with "Hs") as (P) "[HP HT]".
  all: iDestruct ("HT" with "Hl") as "[HP' $]".
  all: by iApply "HP".
Qed.
Global Instance subsume_simplify_inst {Σ} (P1 P2 : iProp Σ) o1 o2 `{!SimplifyHyp P1 o1} `{!SimplifyGoal P2 o2} `{!TCOneIsSome o1 o2} :
  Subsume P1 P2 | 1000 :=
  λ T, i2p (subsume_simplify P1 P2 T o1 o2).

Lemma subsume_list_eq {Σ} A ig (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  ⌜list_subequiv ig l1 l2⌝ ∗ T -∗ subsume_list A ig l1 l2 f T.
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
Global Instance subsume_list_eq_inst {Σ} A ig l1 l2 f:
  SubsumeList A ig l1 l2 f | 1000 :=
  λ T : iProp Σ, i2p (subsume_list_eq A ig l1 l2 f T).

Lemma subsume_list_insert_in_ig {Σ} A ig i x (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) `{!CanSolve (i ∈ ig)} :
  subsume_list A ig l1 l2 f T -∗
  subsume_list A ig (<[i := x]>l1) l2 f T.
Proof.
  unfold CanSolve in *. iIntros "Hsub Hl".
  rewrite insert_length. iApply "Hsub".
  destruct (decide (i < length l1)%nat). 2: { by rewrite list_insert_ge; [|lia]. }
  iDestruct (big_sepL_insert_acc with "Hl") as "[_ Hl]". { by apply: list_lookup_insert. }
  have [//|y ?]:= lookup_lt_is_Some_2 l1 i.
  iDestruct ("Hl" $! y with "[]") as "Hl". { by case_decide. }
  by rewrite list_insert_insert list_insert_id.
Qed.
Global Instance subsume_list_insert_in_ig_inst {Σ} A ig i x (l1 l2 : list A) (f : nat → A → iProp Σ) `{!CanSolve (i ∈ ig)} :
  SubsumeList A ig (<[i := x]>l1) l2 f :=
  λ T, i2p (subsume_list_insert_in_ig A ig i x l1 l2 f T).

Lemma subsume_list_insert_not_in_ig {Σ} A ig i x (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) `{!CanSolve (i ∉ ig)} :
  ⌜i < length l1⌝%nat ∗ subsume_list A (i :: ig) l1 l2 f (∀ x2,
    ⌜l2 !! i = Some x2⌝ -∗ subsume (f i x) (f i x2) T) -∗
  subsume_list A ig (<[i := x]>l1) l2 f T.
Proof.
  unfold CanSolve in *. iIntros "[% Hsub] Hl". rewrite big_sepL_insert // insert_length.
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
Global Instance subsume_list_insert_not_in_ig_inst {Σ} A ig i x (l1 l2 : list A) (f : nat → A → iProp Σ) `{!CanSolve (i ∉ ig)} :
  SubsumeList A ig (<[i := x]>l1) l2 f :=
  λ T, i2p (subsume_list_insert_not_in_ig A ig i x l1 l2 f T).

Lemma subsume_list_trivial_eq {Σ} A ig (l : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  T -∗ subsume_list A ig l l f T.
Proof. by iIntros "$ $". Qed.
Global Instance subsume_list_trivial_eq_inst {Σ} A ig l f:
  SubsumeList A ig l l f | 5 :=
  λ T : iProp Σ, i2p (subsume_list_trivial_eq A ig l f T).

Lemma subsume_list_cons_l {Σ} A ig (x1 : A) (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  (⌜0 ∉ ig⌝ ∗ ∃ x2 l2', ⌜l2 = x2 :: l2'⌝ ∗
      subsume (f 0%nat x1) (f 0%nat x2) (subsume_list A (pred <$> ig) l1 l2' (λ i, f (S i)) T)) -∗
   subsume_list A ig (x1 :: l1) l2 f T.
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
Global Instance subsume_list_cons_inst {Σ} A ig x1 l1 l2 f:
  SubsumeList A ig (x1 :: l1) l2 f | 40 :=
  λ T : iProp Σ, i2p (subsume_list_cons_l A ig x1 l1 l2 f T).
