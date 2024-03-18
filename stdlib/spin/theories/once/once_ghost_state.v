From iris Require Import prelude.
From iris.base_logic Require Import own.
From iris.algebra Require Import csum agree excl frac.
From iris.proofmode Require Import proofmode.
From refinedrust Require Import typing.
From iris Require Import options.


(** One shot *)
Class onceG Σ (A : Type) :=
  OnceG { onceG_inG : inG Σ (csumR (fracR) (agreeR (leibnizO A))); }.
#[export] Existing Instance onceG_inG.
Definition onceΣ A : gFunctors := #[ GFunctor (csumR fracR (agreeR (leibnizO A))) ].
Global Instance subG_onceΣ Σ A : subG (onceΣ A) Σ → onceG Σ A.
Proof. solve_inG. Qed.

Section once.
  Context {A : Type}.
  Context `{onceG Σ A}.

  Definition once_uninit_tok_def γ := own γ (Cinl (1/2)%Qp).

  Definition once_init_tok_def γ (a : A) := own γ (Cinr (to_agree (a : leibnizO A))).

  Definition once_status_tok_def γ (a : option A) :=
    match a with
    | None => once_uninit_tok_def γ
    | Some a => once_init_tok_def γ a
    end.
  Definition once_status_tok_aux : seal (@once_status_tok_def). Proof. by eexists. Qed.
  Definition once_status_tok := once_status_tok_aux.(unseal).
  Definition once_status_tok_eq : @once_status_tok = @once_status_tok_def := once_status_tok_aux.(seal_eq).


  Lemma once_uninit_tok_alloc :
    ⊢ |==> ∃ γ, once_status_tok γ None ∗ once_status_tok γ None.
  Proof.
    rewrite once_status_tok_eq /once_status_tok_def.
    setoid_rewrite <-own_op.
    rewrite -Cinl_op frac_op Qp.half_half.
    iApply own_alloc. done.
  Qed.

  Lemma once_uninit_tok_init γ a :
    once_status_tok γ None -∗ once_status_tok γ None -∗ |==> once_status_tok γ (Some a).
  Proof.
    rewrite once_status_tok_eq.
    iIntros "Ha Hb".
    iCombine "Ha Hb" as "Ha".
    rewrite -Cinl_op frac_op Qp.half_half.
    iApply own_update; last done.
    by apply cmra_update_exclusive.
  Qed.

  Global Instance once_status_tok_persistent γ a : Persistent (once_status_tok γ (Some a)).
  Proof. rewrite once_status_tok_eq. apply _. Qed.

  Lemma once_uninit_init_tok_False γ a :
    once_status_tok γ None -∗ once_status_tok γ (Some a) -∗ False.
  Proof.
    iIntros "H1 H2". rewrite once_status_tok_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    done.
  Qed.

  Lemma once_uninit_uninit_tok_False γ :
    once_status_tok γ None -∗ once_status_tok γ None -∗ once_status_tok γ None -∗ False.
  Proof.
    iIntros "H1 H2 H3". rewrite once_status_tok_eq.
    iDestruct (own_valid_3 with "H1 H2 H3") as %Hv.
    done.
  Qed.

  Lemma once_init_tok_agree γ a b :
    once_status_tok γ (Some a) -∗ once_status_tok γ (Some b) -∗ ⌜a = b⌝.
  Proof.
    iIntros "H1 H2". rewrite once_status_tok_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply to_agree_op_inv_L in Hv.
  Qed.

  Global Instance once_init_tok_timeless γ a : Timeless (once_status_tok γ a).
  Proof. rewrite once_status_tok_eq; destruct a; apply _. Qed.
End once.

Notation once_uninit_tok γ := (once_status_tok γ None).
Notation once_init_tok γ a := (once_status_tok γ (Some a)).

Section typing.
  Context {A} `{!typeGS Σ} `{!onceG Σ A}.

  Lemma subsume_once_status_tok γ a b T :
    subsume (once_status_tok γ a) (once_status_tok γ b) T :-
      exhale ⌜a = b⌝; return T.
  Proof.
    iIntros "(-> & HT)".
    iIntros "$"; done.
  Qed.
  Definition subsume_once_status_tok_inst := [instance subsume_once_status_tok].
  Global Existing Instance subsume_once_status_tok_inst.

  Definition FindOnceStatusTok γ : find_in_context_info :=
    {| fic_A := option A; fic_Prop a := once_status_tok γ a |}.
  Global Instance once_status_tok_related γ a : RelatedTo (once_status_tok γ a) := {| rt_fic := FindOnceStatusTok γ |}.
End typing.

(** Since a frequent use case of once is in conjunction with static variables, we provide some extra support for that *)
Section statics.
  Context {A} `{!typeGS Σ} `{!staticGS Σ} `{!onceG Σ A}.

  Definition once_status π (s : string) (a : option A) : iProp Σ :=
    ∃ γ, once_status_tok γ a ∗ initialized π s γ.
  Global Typeclasses Opaque once_status.

  Definition FindOnceStatus π s : find_in_context_info :=
    {| fic_A := option A; fic_Prop a := once_status π s a |}.
  Global Instance once_status_related π s a : RelatedTo (once_status π s a) := {| rt_fic := FindOnceStatus π s |}.
  Lemma subsume_once_status π s a b T :
    subsume (once_status π s a) (once_status π s b) T :-
      exhale ⌜a = b⌝; return T.
  Proof.
    iIntros "(-> & HT)".
    iIntros "$"; done.
  Qed.
End statics.
