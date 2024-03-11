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
  Definition once_uninit_tok_aux : seal (@once_uninit_tok_def). Proof. by eexists. Qed.
  Definition once_uninit_tok := once_uninit_tok_aux.(unseal).
  Definition once_uninit_tok_eq : @once_uninit_tok = @once_uninit_tok_def := once_uninit_tok_aux.(seal_eq).


  Definition once_init_tok_def γ (a : A) := own γ (Cinr (to_agree (a : leibnizO A))).
  Definition once_init_tok_aux : seal (@once_init_tok_def). Proof. by eexists. Qed.
  Definition once_init_tok := once_init_tok_aux.(unseal).
  Definition once_init_tok_eq : @once_init_tok = @once_init_tok_def := once_init_tok_aux.(seal_eq).

  Definition once_status_tok_def γ (a : option A) :=
    match a with
    | None => once_uninit_tok γ
    | Some a => once_init_tok γ a
    end.
  Definition once_status_tok_aux : seal (@once_status_tok_def). Proof. by eexists. Qed.
  Definition once_status_tok := once_status_tok_aux.(unseal).
  Definition once_status_tok_eq : @once_status_tok = @once_status_tok_def := once_status_tok_aux.(seal_eq).


  Lemma once_uninit_tok_alloc :
    ⊢ |==> ∃ γ, once_uninit_tok γ ∗ once_uninit_tok γ.
  Proof.
    rewrite once_uninit_tok_eq /once_uninit_tok_def. 
    setoid_rewrite <-own_op.
    rewrite -Cinl_op frac_op Qp.half_half.
    iApply own_alloc. done.
  Qed.

  Lemma once_uninit_tok_init γ a :
    once_uninit_tok γ -∗ once_uninit_tok γ -∗ |==> once_init_tok γ a.
  Proof.
    rewrite once_uninit_tok_eq once_init_tok_eq.
    iIntros "Ha Hb".
    iCombine "Ha Hb" as "Ha".
    rewrite -Cinl_op frac_op Qp.half_half.
    iApply own_update; last done.
    by apply cmra_update_exclusive.
  Qed.

  Global Instance once_init_tok_persistent γ a : Persistent (once_init_tok γ a).
  Proof. rewrite once_init_tok_eq. apply _. Qed.
  Global Instance once_status_tok_persistent γ a : Persistent (once_status_tok γ (Some a)).
  Proof. rewrite once_status_tok_eq. apply _. Qed.

  Lemma once_uninit_init_tok_False γ a :
    once_uninit_tok γ -∗ once_init_tok γ a -∗ False.
  Proof.
    iIntros "H1 H2". rewrite once_uninit_tok_eq once_init_tok_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    done.
  Qed.

  Lemma once_uninit_uninit_tok_False γ :
    once_uninit_tok γ -∗ once_uninit_tok γ -∗ once_uninit_tok γ -∗ False.
  Proof.
    iIntros "H1 H2 H3". rewrite once_uninit_tok_eq.
    iDestruct (own_valid_3 with "H1 H2 H3") as %Hv.
    done.
  Qed.

  Lemma once_init_tok_agree γ a b :
    once_init_tok γ a -∗ once_init_tok γ b -∗ ⌜a = b⌝.
  Proof.
    iIntros "H1 H2". rewrite once_init_tok_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply to_agree_op_inv_L in Hv.
  Qed.

  Global Instance once_init_tok_timeless γ a : Timeless (once_init_tok γ a).
  Proof. rewrite once_init_tok_eq. apply _. Qed.
  Global Instance once_uninit_tok_timeless γ : Timeless (once_uninit_tok γ).
  Proof. rewrite once_uninit_tok_eq. apply _. Qed.
End once.

Section typing.
  Context {A} `{!typeGS Σ} `{!onceG Σ A}.

  Lemma subsume_once_status γ a b T :
    subsume (once_status_tok γ a) (once_status_tok γ b) T :-
      exhale ⌜a = b⌝; return T.
  Proof.
    iIntros "(-> & HT)".
    iIntros "$"; done.
  Qed.
  Definition subsume_once_status_inst := [instance subsume_once_status].
  Global Existing Instance subsume_once_status_inst.

  Definition FindOnceStatus γ : find_in_context_info :=
    {| fic_A := option A; fic_Prop a := once_status_tok γ a |}.
  Global Instance once_status_related γ a : RelatedTo (once_status_tok γ a) := {| rt_fic := FindOnceStatus γ |}.

  (*
  Lemma subsume_once_init γ a b T :
    subsume (once_init_tok γ a) (once_init_tok γ b) T :-
      exhale ⌜a = b⌝; return T.
  Proof.
    iIntros "(-> & HT)".
    iIntros "$"; done.
  Qed.
  Definition subsume_once_init_inst := [instance subsume_once_init].
  Global Existing Instance subsume_once_init_inst.

  Lemma subsume_once_init_status γ a b T :
    subsume (once_init_tok γ a) (once_status_tok γ b) T :-
      exhale ⌜b = Some a⌝; return T.
  Proof.
    iIntros "(-> & HT)".
    rewrite once_status_tok_eq/=.
    iIntros "$"; done.
  Qed.
  Definition subsume_once_init_status_inst := [instance subsume_once_init_status].
  Global Existing Instance subsume_once_init_status_inst.

  Lemma subsume_once_uninit γ T :
    subsume (once_uninit_tok γ) (once_uninit_tok γ) T :-
      return T.
  Proof.
    iIntros "HT $"; done.
  Qed.
  Definition subsume_once_uninit_inst := [instance subsume_once_uninit].
  Global Existing Instance subsume_once_uninit_inst.

  Lemma subsume_once_uninit_status γ b T :
    subsume (once_uninit_tok γ) (once_status_tok γ b) T :-
      exhale ⌜b = None⌝; return T.
  Proof.
    iIntros "(-> & HT)".
    rewrite once_status_tok_eq/=.
    iIntros "$"; done.
  Qed.
  Definition subsume_once_uninit_status_inst := [instance subsume_once_uninit_status].
  Global Existing Instance subsume_once_uninit_status_inst.

  Definition FindOnceInit γ : find_in_context_info :=
    {| fic_A := A; fic_Prop a := once_init_tok γ a |}.
  Global Instance once_init_related γ a : RelatedTo (once_init_tok γ a) := {| rt_fic := FindOnceInit γ |}.

  Definition FindOnceUninit γ : find_in_context_info :=
    {| fic_A := unit; fic_Prop a := once_uninit_tok γ |}.
  Global Instance once_uninit_related γ : RelatedTo (once_uninit_tok γ) := {| rt_fic := FindOnceUninit γ |}.

  Definition simplify_hyp_once_status_init :
    simplify_hyp
    *)

  (* TODO: first add infrastructure for associating ghost state with locations
  Definition once_status (l : loc) (x : option A) :=
    ∃ γ, ghost_loc_map l γ ∗ once_status_tok γ x.
   *)
End typing.
