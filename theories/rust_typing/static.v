From refinedrust Require Import base type ltypes programs references.
From iris.base_logic Require Import ghost_map.

(* TODO: should require that type is Send? *)
Class staticGS `{!typeGS Σ} := {
  static_locs : gmap string loc;
  static_types : gmap string (sigT type);
}.
Global Arguments staticGS _ {_}.


Section statics.
  Context `{!typeGS Σ} `{!staticGS Σ}.

  (** Assertion stating that the static with name [x] has been registered for location [l] and type [ty]. *)
  (** We assume registration for the expected type and the location parameter in the context where we verify our code *)
  Definition static_is_registered (x : string) (l : loc) (ty : sigT type) :=
    static_locs !! x = Some l ∧ static_types !! x = Some ty.

  Import EqNotations.

  (* The global variable "name" has been initialized with refinement "r" *)
  Definition initialized {rt} (π : thread_id) (name : string) (r : rt) : iProp Σ :=
    ∃ (l : loc) (ty : sigT type), ⌜static_is_registered name l ty⌝ ∗
      ∃ (Heq : rt = projT1 ty),
        (l ◁ᵥ{π} (rew Heq in #r) @ shr_ref (projT2 ty) static)%I.

  Global Instance initialized_persistent {rt} (π : thread_id) (name : string) (r : rt) :
    Persistent (initialized π name r).
  Proof. apply _. Qed.

  Global Instance initialized_intro_persistent {rt} (π : thread_id) name (r : rt) :
    IntroPersistent (initialized π name r) (initialized π name r).
  Proof. constructor. iIntros "#$". Qed.

  (* On introduction of `initialized`, destruct it *)
  Lemma simplify_initialized_hyp {rt} π (x : rt) name ty l
    `{!TCFastDone (static_is_registered name l ty)} T:
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew Heq in #x) @ shr_ref (projT2 ty) static -∗ T)
    ⊢ simplify_hyp (initialized π name x) T.
  Proof.
    unfold TCFastDone in *. destruct ty as [rt' ty].
    iDestruct 1 as (?) "HT". subst; simpl in *.
    iIntros "Hinit".
    iDestruct "Hinit" as "(%l' & %ty' & %Hlook1' & %Heq & Hl)".
    destruct ty' as (rt & ty'). subst. simpl in *.
    repeat match goal with | H : static_is_registered _ _ _ |- _ => destruct H end.
    simplify_eq.
    match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end.
    subst. iApply ("HT" with "Hl").
  Qed.
  Definition simplify_initialized_hyp_inst := [instance @simplify_initialized_hyp with 0%N].
  Global Existing Instance simplify_initialized_hyp_inst.

  Lemma initialized_intro {rt} π ty name l (x : rt) :
    static_is_registered name l ty →
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew Heq in #x) @ shr_ref (projT2 ty) static) -∗
    initialized π name x.
  Proof. iIntros (?) "Hl". iExists _, _. by iFrame. Qed.

  Lemma simplify_initialized_goal {rt} π (x : rt) name l ty
    `{!TCFastDone (static_is_registered name l ty)} T:
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

  Set Printing Universes.
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

(* After calling adequacy:
    we need to create initialized things.
    then we can provide them to the proof.

   Users of initialized should unpack that hypothesis to get access to the type assignment.
   This type assignment then allows us to call methods etc on the global variable.

 *)


