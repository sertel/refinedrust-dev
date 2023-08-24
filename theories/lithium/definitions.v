From iris.base_logic.lib Require Export iprop.
From iris.proofmode Require Export tactics.
From lithium Require Export base pure_definitions.

(** Definitions that are used by the Lithium automation. *)

(** * [iProp_to_Prop] *)
#[projections(primitive)]
Record iProp_to_Prop {Σ} (P : iProp Σ) : Type := i2p {
  i2p_P :> iProp Σ;
  i2p_proof : i2p_P ⊢ P;
}.
Arguments i2p {_ _ _} _.
Arguments i2p_P {_ _} _.
Arguments i2p_proof {_ _} _.

(** * Checking if a hyp in the context
  The implementation can be found in interpreter.v *)
Class CheckOwnInContext {Σ} (P : iProp Σ) : Prop := { check_own_in_context : True }.

(** * [find_in_context] *)
Record find_in_context_info {Σ} : Type := {
  fic_A : Type;
  fic_Prop : fic_A → iProp Σ;
}.
(* The nat n is necessary to allow different options, they are tried starting from 0. *)
Definition find_in_context {Σ} (fic : find_in_context_info) (T : fic.(fic_A) → iProp Σ) : iProp Σ :=
  (∃ b, fic.(fic_Prop) b ∗ T b).
Class FindInContext {Σ} (fic : find_in_context_info) (key : Set) : Type :=
  find_in_context_proof T: iProp_to_Prop (Σ:=Σ) (find_in_context fic T)
.
Global Hint Mode FindInContext + + - : typeclass_instances.
Inductive FICSyntactic : Set :=.

(** The instance for searching with [FindDirect] is in [instances.v].  *)
Definition FindDirect {Σ A} (P : A → iProp Σ) := {| fic_A := A; fic_Prop := P; |}.
Global Typeclasses Opaque FindDirect.

(** ** [FindHypEqual]  *)
(** [FindHypEqual] is called with find_in_context key [key], an
hypothesis [Q] and a desired pattern [P], and then the instance
(usually a tactic) should try to generate a new pattern [P'] equal to
[P] that can be later unified with [Q]. *)
Class FindHypEqual {Σ} (key : Type) (Q P P' : iProp Σ) := find_hyp_equal_equal: P = P'.
Global Hint Mode FindHypEqual + + + ! - : typeclass_instances.

(** * [RelatedTo] *)
Class RelatedTo {Σ} (pat : iProp Σ) : Type := {
  rt_fic : find_in_context_info (Σ:=Σ);
}.
Global Hint Mode RelatedTo + + : typeclass_instances.
Arguments rt_fic {_ _} _.

(** * [IntroPersistent] *)
(** ** Definition *)
Class IntroPersistent {Σ} (P P' : iProp Σ) := {
  ip_persistent : P ⊢ □ P'
}.
Global Hint Mode IntroPersistent + + - : typeclass_instances.
(** ** Instances *)
Global Instance intro_persistent_intuit Σ (P : iProp Σ) : IntroPersistent (□ P) P.
Proof. constructor. iIntros "$". Qed.

(** * Simplification *)
(* n:
   None: no simplification
   Some 0: simplification which is always safe
   Some n: lower n: should be done before higher n (when compared with simplifyGoal)   *)
Definition simplify_hyp {Σ} (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
  P -∗ T.
Class SimplifyHyp {Σ} (P : iProp Σ) (n : option N) : Type :=
  simplify_hyp_proof T : iProp_to_Prop (simplify_hyp P T).

Definition simplify_goal {Σ} (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
  (P ∗ T).
Class SimplifyGoal {Σ} (P : iProp Σ) (n : option N) : Type :=
  simplify_goal_proof T : iProp_to_Prop (simplify_goal P T).

Global Hint Mode SimplifyHyp + + - : typeclass_instances.
Global Hint Mode SimplifyGoal + ! - : typeclass_instances.

(** * Subsumption *)
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

(** * case distinction *)
Definition case_if {Σ} (P : Prop) (T1 T2 : iProp Σ) : iProp Σ :=
  (⌜P⌝ -∗ T1) ∧ (⌜¬ P⌝ -∗ T2).

Definition case_destruct {Σ} {A} (a : A) (T : A → bool → iProp Σ) : iProp Σ :=
  ∃ b, T a b.

(** * [li_tactic] *)
Class LiTactic {Σ A} (t : (A → iProp Σ) → iProp Σ) := {
  li_tactic_P : (A → iProp Σ) → iProp Σ;
  li_tactic_proof T : li_tactic_P T ⊢ t T;
}.
Arguments li_tactic_proof {_ _ _} _ _.
Arguments li_tactic_P {_ _ _} _ _.

Definition li_tactic {Σ A} (t : (A → iProp Σ) → iProp Σ) (T : A → iProp Σ) : iProp Σ :=
  t T.
Arguments li_tactic : simpl never.

(** ** [li_vm_compute] *)
Definition li_vm_compute {Σ A B} (f : A → option B) (x : A) (T : B → iProp Σ) : iProp Σ :=
  ∃ y, ⌜f x = Some y⌝ ∗ T y.
Arguments li_vm_compute : simpl never.
Global Typeclasses Opaque li_vm_compute.

Program Definition li_vm_compute_hint {Σ A B} (f : A → option B) x a :
  f a = Some x →
  LiTactic (li_vm_compute (Σ:=Σ) f a) := λ H, {|
    li_tactic_P T := T x;
|}.
Next Obligation. move => ????????. iIntros "HT". iExists _. iFrame. iPureIntro. naive_solver. Qed.

Global Hint Extern 10 (LiTactic (li_vm_compute _ _)) =>
  eapply li_vm_compute_hint; evar_safe_vm_compute : typeclass_instances.

(** * [accu] *)
Definition accu {Σ} (f : iProp Σ → iProp Σ) : iProp Σ :=
  ∃ P, P ∗ □ f P.
Arguments accu : simpl never.
Global Typeclasses Opaque accu.

(** * trace *)
Definition li_trace {Σ A} (t : A) (T : iProp Σ) : iProp Σ := T.
