From caesium Require Export base.

Class ConfidentialInterface := {
  slevel : Set;
  slevel_eqdec :: EqDecision slevel;
  slevel_countable :: Countable slevel;

  slevel_bot :: Bottom slevel;
  slevel_top :: Top slevel;
  slevel_meet :: Meet slevel;
  slevel_join :: Join slevel;

  slevel_le :: SqSubsetEq slevel;
  slevel_preorder :: PreOrder slevel_le;

  slevel_join_ge (s1 s2 : slevel) : slevel_le s1 (s1 ⊔ s2);
  slevel_meet_le (s1 s2 : slevel) : slevel_le (s1 ⊓ s2) s1;

  slevel_top_max (s : slevel) : slevel_le s ⊤;
  slevel_bot_min (s : slevel) : slevel_le ⊥ s;

  slevel_meet_idemp (s : slevel) : s ⊓ s = s;
  slevel_join_idemp (s : slevel) : s ⊔ s = s;
  slevel_join_comm : Comm (=) (slevel_join);
  slevel_meet_comm : Comm (=) (slevel_meet);

  slevel_bot_neutral_r (s : slevel) : s ⊔ ⊥ = s;
  slevel_top_neutral_r (s : slevel) : s ⊓ ⊤ = s;
}.
Global Instance inhabited_slevel `{!ConfidentialInterface}: Inhabited slevel := populate slevel_bot.

(** We can define one particular lattice over a set of principals in the following way: *)
Class Principals := {
  principals : Set;
  principals_eqdec :: EqDecision principals;
  principals_countable :: Countable principals;
}.
Section flow_tracking.
  Context `{Principals}.

  Inductive principal_set :=
    | AllPrincipals
    | SetOfPrincipals (p : gset principals).
  Global Instance principal_set_eqdec : EqDecision principal_set.
  Proof. solve_decision. Defined.
  Global Instance principal_set_countable : Countable principal_set.
  Proof.
  Admitted.
  Global Instance principal_set_empty : Empty principal_set := SetOfPrincipals ∅.
  Global Instance principal_set_intersection : Intersection principal_set :=
    λ ps1 ps2,
      match ps1, ps2 with
      | AllPrincipals, AllPrincipals => AllPrincipals
      | SetOfPrincipals s1, AllPrincipals => SetOfPrincipals s1
      | SetOfPrincipals s1, SetOfPrincipals s2 => SetOfPrincipals (s1 ∩ s2)
      | AllPrincipals, SetOfPrincipals s2 => SetOfPrincipals s2
      end.
  Global Instance principal_set_union : Union principal_set :=
    λ ps1 ps2,
      match ps1, ps2 with
      | AllPrincipals, AllPrincipals => AllPrincipals
      | SetOfPrincipals s1, AllPrincipals => AllPrincipals
      | SetOfPrincipals s1, SetOfPrincipals s2 => SetOfPrincipals (s1 ∪ s2)
      | AllPrincipals, SetOfPrincipals s2 => AllPrincipals
      end.
  Global Instance principal_set_subseteq : SubsetEq principal_set :=
    λ ps1 ps2,
      match ps1, ps2 with
      | AllPrincipals, AllPrincipals => True
      | SetOfPrincipals s1, AllPrincipals => True
      | SetOfPrincipals s1, SetOfPrincipals s2 => s1 ⊆ s2
      | AllPrincipals, SetOfPrincipals s2 => False
      end.
  Global Instance principal_set_union_right_id : RightId eq ∅ principal_set_union.
  Proof. intros []; simpl; first done. f_equiv. set_solver. Qed.
  Global Instance principal_set_union_left_id : LeftId eq ∅ principal_set_union.
  Proof. intros []; simpl; first done. f_equiv. set_solver. Qed.
  Global Instance principal_set_intersection_right_id : RightId eq AllPrincipals principal_set_intersection.
  Proof. intros []; simpl; done. Qed.
  Global Instance principal_set_intersection_left_id : LeftId eq AllPrincipals principal_set_intersection.
  Proof. intros []; simpl; done. Qed.

  Global Instance principal_set_preorder : PreOrder principal_set_subseteq.
  Proof.
    constructor.
    - intros []; rewrite /subseteq/principal_set_subseteq; simpl; set_solver.
    - intros [][][]; rewrite /subseteq/principal_set_subseteq; simpl; set_solver.
  Qed.

  (* Two lattices, integrity and confidentiality. sources and readers. *)
  Record conf_policy := mk_policy {
    conf_readers : principal_set;
    conf_sources : principal_set;
  }.
  Instance conf_policy_eqdec : EqDecision conf_policy.
  Proof. solve_decision. Defined.
  Instance conf_policy_countable : Countable conf_policy.
  Proof.
  Admitted.

  Instance conf_bot : Bottom conf_policy := mk_policy AllPrincipals ∅.
  Instance conf_top : Top conf_policy := mk_policy ∅ AllPrincipals.
  Instance: Inhabited conf_policy := populate ⊥.

  Instance conf_join : Join conf_policy :=
    λ (s1 s2 : conf_policy), {|
      conf_readers := s1.(conf_readers) ∩ s2.(conf_readers);
      conf_sources := s1.(conf_sources) ∪ s2.(conf_sources);
    |}.
  Instance conf_meet : Meet conf_policy :=
    λ (s1 s2 : conf_policy), {|
      conf_readers := s1.(conf_readers) ∪ s2.(conf_readers);
      conf_sources := s1.(conf_sources) ∩ s2.(conf_sources);
    |}.

  (* s1 ⊑ s2 holds iff s1 is less restrictive, i.e. s2 upholds all the constraints of s1. *)
  Instance conf_le : SqSubsetEq conf_policy :=
    λ s1 s2, s2.(conf_readers) ⊆ s1.(conf_readers) ∧ s1.(conf_sources) ⊆ s2.(conf_sources).

  Instance conf_le_partial_order : PreOrder conf_le.
  Proof.
    constructor.
    - intros [??]; rewrite /conf_le/=; done.
    - intros [??] [??] [??]; rewrite /conf_le/=; intros [] [];
      split; etrans; done.
  Qed.

  (** Declassification is allowed if:
     - the declassifiers cover all sources of the old policy
     - OR the set of readers does not grow and the set of sources can only be changed by removing declassifiers or adding additional sources
   *)
  Definition allow_declassification_group (declassifiers : principal_set) (from to : conf_policy) :=
    from.(conf_sources) ⊆ declassifiers ∨
    (to.(conf_readers) ⊆ from.(conf_readers) ∧ from.(conf_sources) ⊆ to.(conf_sources) ∪ declassifiers).
  Definition allow_declassification (declassifier : principals) :=
    allow_declassification_group (SetOfPrincipals {[ declassifier ]}).

  Instance allow_declassification_group_trans declassifiers :
    Transitive (allow_declassification_group declassifiers).
  Proof.
    destruct declassifiers as [];
    intros [[] []][[] []][[] []];
    rewrite /allow_declassification_group/=/subseteq/principal_set_subseteq/=;
    set_solver.
  Qed.
  Instance allow_declassification_group_refl declassifiers :
    Reflexive (allow_declassification_group declassifiers).
  Proof.
    destruct declassifiers as [];
    intros [[] []];
    rewrite /allow_declassification_group/=/subseteq/principal_set_subseteq/=;
    set_solver.
  Qed.

  (** We can get a simple declassification operation that has a neutral element by expanding the existing policy to allow a "required" set of readers *)
  Definition declassify_for (from : conf_policy) (require : conf_policy) : conf_policy :=
    from ⊓ require.
  (* This operation has a neutral element *)
  Lemma declassify_for_neutral declassifiers from :
    allow_declassification_group declassifiers from (declassify_for from ⊤).
  Proof.
    right. simpl. split.
    - destruct from as [readers sources]; simpl. rewrite right_id//.
    - rewrite right_id.
      destruct from as [[][]], declassifiers as []; rewrite /subseteq/principal_set_subseteq/=; set_solver.
  Qed.


  Program Definition flow_tracking_interface : ConfidentialInterface := {|
    slevel := conf_policy;
  |}.
  Solve Obligations with try apply _.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

End flow_tracking.
