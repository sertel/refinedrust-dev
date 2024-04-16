From refinedrust Require Import base type ltypes programs shr_ref.
From iris.base_logic Require Import ghost_map.

Record btype `{!typeGS Σ} : Type := {
  btype_rt : Type;
  btype_ty : type btype_rt;
  btype_r : btype_rt;
}.

Definition btype_to_rtype `{!typeGS Σ} (ty : btype) : sigT type :=
  existT _ ty.(btype_ty).

(* TODO: should require that type is Send? *)
Class staticGS `{!typeGS Σ} := {
  static_locs : gmap string loc;
  static_types : gmap string btype;
}.
Global Arguments staticGS _ {_}.

Section statics.
  Context `{!typeGS Σ} `{!staticGS Σ}.

  Import EqNotations.

  (** Assertion stating that the static with name [x] has been registered for location [l] and type [ty]. *)
  (** We assume registration for the expected type and the location parameter in the context where we verify our code *)
  Definition static_is_registered (x : string) (l : loc) (ty : sigT type) :=
    static_locs !! x = Some l ∧ btype_to_rtype <$> (static_types !! x) = Some ty.

  (** In our specifications, we can use this assertion to assume a refinement for the static *)
  Definition static_has_refinement (x : string) {rt} (r : rt) :=
    ∃ ty, static_types !! x = Some ty ∧ ∃ (Heq : rt = ty.(btype_rt)), (rew [id] Heq in r) = ty.(btype_r).

  Lemma static_has_refinement_inj {rt1 rt2} (r1 : rt1) (r2 : rt2) name :
    static_has_refinement name r1 →
    static_has_refinement name r2 →
    ∃ (Heq : rt1 = rt2), rew Heq in r1 = r2.
  Proof.
    intros (ty1 & Hlook1 & Heq1 & Ha).
    intros (ty2 & Hlook2 & Heq2 & Hb).
    simplify_eq. exists eq_refl.
    simpl in *. by subst.
  Qed.

  Global Instance simpl_and_static_has_refinement {rt} (x y : rt) `{!TCFastDone (static_has_refinement name x)} :
    SimplBoth (static_has_refinement name y) (x = y).
  Proof.
    split; last naive_solver.
    rename select (TCFastDone _) into Hs. unfold TCFastDone in Hs.
    intros Ha. destruct (static_has_refinement_inj _ _ _ Hs Ha) as (Heq & <-).
    rewrite (UIP_refl _ _ Heq).
    done.
  Qed.

  (* The global variable "name" has been initialized with refinement "r" *)
  Definition initialized {rt} (π : thread_id) (name : string) (r : rt) : iProp Σ :=
    ∃ (l : loc) (ty : btype), ⌜static_locs !! name = Some l⌝ ∗ ⌜static_types !! name = Some ty⌝ ∗
      ∃ (Heq : rt = ty.(btype_rt)),
        ⌜(rew [id] Heq in r) = ty.(btype_r) ⌝ ∗
        (l ◁ᵥ{π} (#ty.(btype_r)) @ shr_ref ty.(btype_ty) static)%I.

  Global Instance initialized_persistent {rt} (π : thread_id) (name : string) (r : rt) :
    Persistent (initialized π name r).
  Proof. apply _. Qed.

  Global Instance initialized_intro_persistent {rt} (π : thread_id) name (r : rt) :
    IntroPersistent (initialized π name r) (initialized π name r).
  Proof. constructor. iIntros "#$". Qed.

  (* On introduction of `initialized`, destruct it *)
  Lemma simplify_initialized_hyp {rt} π (x : rt) name ty l
    `{!TCFastDone (static_is_registered name l ty)} T:
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew Heq in #x) @ shr_ref (projT2 ty) static -∗ ⌜static_has_refinement name x⌝ -∗ T)
    ⊢ simplify_hyp (initialized π name x) T.
  Proof.
    unfold TCFastDone in *. destruct ty as [rt' ty].
    iDestruct 1 as (?) "HT". subst; simpl in *.
    iIntros "Hinit".
    iDestruct "Hinit" as "(%l' & %ty' & %Hlook1 & %Hlook2 & %Heq & %Hrfn & Hl)".
    subst. simpl in *. subst.
    destruct ty'; simpl in *.
    repeat match goal with | H : static_is_registered _ _ _ |- _ => destruct H as [H1 H2] end.
    apply fmap_Some in H2 as ([] & H2 & Hb).
    simplify_eq. unfold btype_to_rtype in Hb; simpl in *.
    repeat match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end.
    subst. iApply ("HT" with "Hl").
    iPureIntro. eexists _. split; first done. exists eq_refl. done.
  Qed.
  Definition simplify_initialized_hyp_inst := [instance @simplify_initialized_hyp with 0%N].
  Global Existing Instance simplify_initialized_hyp_inst.

  Lemma initialized_intro {rt} π ty name l (x : rt) :
    static_is_registered name l ty →
    static_has_refinement name x →
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew Heq in #x) @ shr_ref (projT2 ty) static) -∗
    initialized π name x.
  Proof.
    iIntros ([Hl1 Hl2] (ty2 & Hl3 & Heq' & Hb)) "(%Heq & Hl)".
    subst. destruct ty. destruct ty2. simpl in *.
    apply fmap_Some in Hl2 as (bt & Hl2 & Ha). subst.
    destruct bt. simpl in *.
    unfold btype_to_rtype in Ha; simpl in *.
    simplify_eq.
    repeat match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end.
    subst.
    iExists _, _. iR. iR.
    iExists eq_refl. simpl. iR. by iFrame.
  Qed.

  Lemma simplify_initialized_goal {rt} π (x : rt) name l ty
    `{!TCFastDone (static_is_registered name l ty)} `{!TCFastDone (static_has_refinement name x)} T:
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew Heq in #x) @ shr_ref (projT2 ty) static ∗ T)
    ⊢ simplify_goal (initialized π name x) T.
  Proof.
    unfold TCFastDone in *. iIntros "[% [? $]]". subst.
    iApply initialized_intro; [done..|]. by iExists _.
  Qed.
  Definition simplify_initialized_goal_inst := [instance @simplify_initialized_goal with 0%N].
  Global Existing Instance simplify_initialized_goal_inst.

  (** Subsumption *)
  Definition FindInitialized (π : thread_id) (rt : Type) (name : string) :=
    {| fic_A := rt; fic_Prop r := (initialized π name r); |}.
  Global Instance related_to_initialized (π : thread_id) {rt} name (r : rt) :
    RelatedTo (initialized π name r) :=
    {| rt_fic := FindInitialized π rt name|}.

  Lemma find_in_context_initialized π name rt (T : rt → iProp Σ):
    (∃ x, initialized π name x ∗ T x)
    ⊢ find_in_context (FindInitialized π rt name) T.
  Proof. iDestruct 1 as (x) "[Hinit HT]". iExists _. iFrame. Qed.
  Definition find_in_context_initialized_inst :=
    [instance find_in_context_initialized with FICSyntactic].
  Global Existing Instance find_in_context_initialized_inst | 1.

  Lemma subsume_initialized π {rt} name (r1 r2 : rt) T:
    (⌜r1 = r2⌝ ∗ T)
    ⊢ subsume (initialized π name r1) (initialized π name r2) T.
  Proof. iIntros "(-> & HT) ?". iFrame. Qed.
  Definition subsume_initialized_inst := [instance subsume_initialized].
  Global Existing Instance subsume_initialized_inst.
End statics.
Global Typeclasses Opaque initialized.
Global Typeclasses Opaque static_has_refinement.

Global Arguments static_has_refinement : simpl never.
Global Arguments static_is_registered : simpl never.


(* After calling adequacy:
    we need to create initialized things.
    then we can provide them to the proof.

   Users of initialized should unpack that hypothesis to get access to the type assignment.
   This type assignment then allows us to call methods etc on the global variable.

 *)


