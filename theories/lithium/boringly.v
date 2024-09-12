From iris.bi Require Import bi plainly notation derived_laws.
From iris.proofmode Require Import proofmode.

(** Defines the [Boringly] modality which carves out the part of a proposition [P] which is persistent. *)
Section boringly.
  Context {PROP : bi}.
  Context `{!BiAffine PROP}.
  Context `{!BiPlainly PROP}.
  Context `{!BiPersistentlyForall PROP}.
  Context `{!BiPersistentlyImplPlainly PROP}.
  Implicit Types (P Q : PROP).

  Definition boringly_def (P : PROP) : PROP :=
    ∀ Q : PROP, (■ (P → □ Q)) → □ Q.
  Definition boringly_aux (P : PROP) : seal (boringly_def P). Proof. by eexists. Qed.
  Definition boringly (P : PROP) := (boringly_aux P).(unseal).
  Definition boringly_unfold (P : PROP) : boringly P = boringly_def P := (boringly_aux P).(seal_eq).

  Notation "☒ P" := (boringly P) (at level 20, right associativity) : bi_scope.

  Lemma boringly_intro P :
    P ⊢ ☒ P.
  Proof.
    rewrite boringly_unfold.
    iIntros "P" (Q) "#HQ".
    by iApply "HQ".
  Qed.

  Lemma boringly_persistent_elim Q :
    Persistent Q →
    ☒ Q ⊢ Q.
  Proof.
    rewrite boringly_unfold.
    iIntros (?) "HQ".
    iPoseProof ("HQ" $! Q with "[]") as "#HQ".
    { iModIntro. eauto. }
    done.
  Qed.

  Lemma boringly_bind P Q :
    (☒ P) ∗ ■ (P → ☒ Q) ⊢ ☒ Q.
  Proof.
    rewrite !boringly_unfold/boringly_def.
    iIntros "[HP #HQ]".
    iIntros (R) "#HR".
    iApply ("HP" $! R).
    iModIntro.
    iIntros "Ha".
    iApply ("HQ" with "Ha").
    done.
  Qed.

  Global Instance boringly_pers P : Persistent (☒ P).
  Proof. rewrite boringly_unfold. apply _. Qed.

  Lemma boringly_exists_elim {X} (Φ : X → PROP) :
    (☒ ∃ x, Φ x) ⊢ ∃ x, ☒ Φ x.
  Proof.
    rewrite !boringly_unfold.
    iIntros "Ha".
    iDestruct ("Ha" $! (∃ x : X, ☒ Φ x)%I with "[]") as "#$".
    iModIntro.
    iIntros "(%x & Ha)".
    iPoseProof (boringly_intro with "Ha") as "#Ha2".
    iModIntro. eauto.
  Qed.

  (** Derived laws *)
  Lemma boringly_mono P Q :
    (P ⊢ Q) → (☒ P ⊢ ☒ Q).
  Proof.
    iIntros (Ha) "HP".
    iApply (boringly_bind with "[HP]").
    iFrame. iModIntro. iIntros "HP".
    iPoseProof (Ha with "HP") as "Hx".
    by iApply boringly_intro.
  Qed.

  Lemma boringly_persistent P `{!Persistent P} :
    (☒ P) ⊣⊢ P.
  Proof.
    iSplit.
    - iApply boringly_persistent_elim.
    - iApply boringly_intro.
  Qed.

  Lemma boringly_exists {X} (Φ : X → PROP) :
    (☒ ∃ x, Φ x) ⊣⊢ ∃ x, ☒ Φ x.
  Proof.
    iSplit.
    - iApply boringly_exists_elim.
    - iIntros "(%x & Ha)". iApply (boringly_mono); last done.
      eauto with iFrame.
  Qed.

  (** The other direction does not hold. *)
  Lemma boringly_forall {X} (Φ : X → PROP) :
    (☒ ∀ x, Φ x) ⊢ ∀ x, ☒ Φ x.
  Proof.
    iIntros "Ha" (x). iApply boringly_mono; last done. eauto.
  Qed.

  (** The other direction does not hold. *)
  Lemma boringly_sep P Q :
    ☒ (P ∗ Q) ⊢ ☒ P ∗ ☒ Q.
  Proof.
    iIntros "#Ha".
    iSplit; (iApply boringly_mono; last done); iIntros "(? & ?)"; eauto with iFrame.
  Qed.

  (* We cannot even prove this version:
     Counterexample: P is DfracDiscarded pointsto, Q is exclusive pointsto. *)
  Lemma boringly_sep_persistent_l P `{!Persistent P} Q :
    ☒ P ∗ ☒ Q ⊢ ☒ (P ∗ Q).
  Proof.
  Abort.

  (* But we can prove this lemma for introducing boring goals. *)
  Lemma boringly_intro_and P Q T :
    (P ⊢ Q) →
    (P ⊢ T) →
    P ⊢ (☒ Q) ∗ T.
  Proof.
    iIntros (HQ HT) "HP".
    iPoseProof (boringly_intro with "HP") as "#HbP".
    iSplitR.
    - by iApply (boringly_mono with "HbP").
    - by iApply HT.
  Qed.
End boringly.

Notation "☒ P" := (boringly P) (at level 20, right associativity) : bi_scope.
