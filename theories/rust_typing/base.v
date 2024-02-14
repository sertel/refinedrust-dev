From lrust.lifetime Require Export lifetime.
From lithium Require Export all.
From caesium Require Export proofmode notation syntypes.
From refinedrust Require Export axioms pinned_borrows.
From iris.prelude Require Import options.

Ltac iR := iSplitR; first done.
Ltac iL := iSplitL; last done.

Definition rrustN := nroot .@ "rrust".
Definition shrN  := rrustN .@ "shr".

Definition lft_userN : namespace := nroot .@ "lft_usr".

(* The "user mask" of the lifetime logic. This needs to be disjoint with ↑lftN.

   If a client library desires to put invariants in lft_userE, then it is
   encouraged to place it in the already defined lft_userN. On the other hand,
   extensions to the model of RustBelt itself (such as gpfsl for
   the weak-mem extension) can require extending [lft_userE] with the relevant
   namespaces. In that case all client libraries need to be re-checked to
   ensure disjointness of [lft_userE] with their masks is maintained where
   necessary. *)
Definition lft_userE : coPset := ↑lft_userN.

Definition rrustE : coPset := ↑rrustN.
Definition lftE : coPset := ↑lftN.
Definition timeE : coPset := ↑timeN.
Definition shrE : coPset := ↑shrN.

Definition unitt : Type := unit.
Definition ttt : unitt := tt.
Notation "()" := ttt.
Notation "()" := unitt : type_scope.

Create HintDb refinedc_typing.

Ltac solve_typing :=
  (typeclasses eauto with refinedc_typing typeclass_instances core).

Global Hint Constructors Forall Forall2 elem_of_list : refinedc_typing.
Global Hint Resolve submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : refinedc_typing.

(* done is there to handle equalities with constants *)
Global Hint Extern 100 (_ ≤ _) => simpl; first [done|lia] : refinedc_typing.
Global Hint Extern 100 (@eq Z _ _) => simpl; first [done|lia] : refinedc_typing.
Global Hint Extern 100 (@eq nat _ _) => simpl; first [done|lia] : refinedc_typing.

Class CoPsetFact (P : Prop) : Prop := copset_fact : P.
(* clear for performance reasons as there can be many hypothesis and they should not be needed for the goals which occur *)
Local Definition coPset_disjoint_empty_r := disjoint_empty_r (C:=coPset).
Local Definition coPset_disjoint_empty_l := disjoint_empty_l (C:=coPset).
Global Hint Extern 1 (CoPsetFact ?P) => (change P; clear; eauto using coPset_disjoint_empty_r, coPset_disjoint_empty_r with solve_ndisj) : typeclass_instances.


Class LayoutSizeEq (ly1 ly2 : layout) := layout_size_eq_proof : ly_size ly1 = ly_size ly2.
Global Instance layout_size_eq_refl ly : LayoutSizeEq ly ly.
Proof. constructor. Qed.

Class LayoutSizeLe (ly1 ly2 : layout) := layout_size_le_proof : ly_size ly1 ≤ ly_size ly2.
Global Instance layout_size_le_refl ly : LayoutSizeLe ly ly.
Proof. constructor. Qed.

Global Remove Hints int_elem_of_it : typeclass_instances.
Global Existing Instance int_elem_of_it'.
Lemma int_elem_of_it_iff z it :
  z ∈ it ↔ int_elem_of_it z it.
Proof.
  rewrite /elem_of/int_elem_of_it' MinInt_eq MaxInt_eq//.
Qed.


(** Block typeclass resolution for an argument *)
Definition TCNoResolve (P : Type) := P.
Global Typeclasses Opaque TCNoResolve.

(** [TCForall] but for [Type] instead of [Prop] *)
Inductive TCTForall {A} (P : A → Type) : list A → Type :=
  | TCTForall_nil : TCTForall P []
  | TCTForall_cons x xs : P x → TCTForall P xs → TCTForall P (x :: xs).
Existing Class TCTForall.
Global Existing Instance TCTForall_nil.
Global Existing Instance TCTForall_cons.
Global Hint Mode TCTForall ! ! ! : typeclass_instances.


Declare Scope printing_sugar.

(* Hints for unfolding type definitions used by some parts of the automation (e.g. [elctx_simplify]). *)
Create HintDb tyunfold.

(* Marker to prevent Lithium's machinery from simplifying a hypothesis. *)
Definition introduce_direct {Σ} (P : iProp Σ) := P.
Global Arguments introduce_direct : simpl never.
Global Typeclasses Opaque introduce_direct.

(* We override the lifetime logic's version with a direct fixpoint version for nicer unfolding + computation. *)
Fixpoint lft_intersect_list (κs : list lft) : lft :=
    match κs with
    | [] => static
    | κ :: κs => κ ⊓ lft_intersect_list κs
    end.
Lemma lft_intersect_list_iff κs :
  lft_intersect_list κs = lifetime.lft_intersect_list κs.
Proof.
  induction κs as [ | κ κs IH]; simpl; first done.
  destruct κs as [ | κ' κs]; simpl.
  { rewrite right_id //. }
  simpl in IH. rewrite IH //.
Qed.

Lemma lft_intersect_list_elem_of_incl_syn (κs : list lft) κ :
  κ ∈ κs → lft_intersect_list κs ⊑ˢʸⁿ κ.
Proof.
  rewrite lft_intersect_list_iff. apply lft_intersect_list_elem_of_incl_syn.
Qed.
Lemma lft_intersect_list_elem_of_incl `{!invGS Σ} {userE : coPset} `{!lftGS Σ userE} (κs : list lft) κ :
  κ ∈ κs → ⊢ lft_intersect_list κs ⊑ κ.
Proof.
  rewrite lft_intersect_list_iff. apply lft_intersect_list_elem_of_incl.
Qed.
