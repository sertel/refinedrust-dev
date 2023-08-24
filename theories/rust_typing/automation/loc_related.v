From lithium Require Import all.
From caesium Require Import base lang.
From refinedrust Require Import programs program_rules.

(** This file contains a solver for finding related locations. *)

(** * Definitions *)

(** Asserts that [l .. l +ₗ l_sz] is in range [l1 .. l1 +ₗ l1_sz].
  We have a range [l_sz] for the accessed part in order to support zero-sized accesses, which should be valid even if [l1_sz] is zero. *)
Definition loc_in_range (l : loc) (l_sz : nat) (l1 : loc) (l1_sz : nat) :=
  l.1 = l1.1 ∧ ((l.2 >= l1.2)%Z ∧ (l.2 + l_sz <= l1.2 + l1_sz)%Z).

(** * Tactics *)

(**
  Limitations for now:
   - assume that [l] and [l1] are of the form [l'] (for symbolic [l']) or [l' +ₗ o], where [o] may be one of:
     + [n] for a literal number [n]
     + [size_of_st st] for some syntype st
     +

  Strategy:
  - first show  that they both are in the same allocation (first conjunct)
    + reflexivity? If they are both symbolic locations, it should be able to see through offsets etc.
    + for concrete locations (e.g. obtained from ptr::dangling): same -- they have no provenance, which should be trivially okay by refl.
  - for showing that the offset is in range:
    + unfold offset in locations and sz.
    + simplify [size_of_st] occurrences
      * for trivial syntypes, simplify to concrete number
      * for array, simplify
      * for struct/enum/.., leave
    + compute with [simpl]
    + then call lia
*)

Ltac prove_prov_eq :=
  idtac.

Ltac prove_offset_in_range :=
  idtac.

Ltac solve_loc_in_range :=
  match goal with
  | |- loc_in_range _ _ _ _ =>
    split; [prove_prov_eq | prove_offset_in_range]
  end.

Section test.
  Context `{!typeGS Σ}.

  Lemma lir_test_1 l :
    loc_in_range l 1 l 1.
  Proof.
    solve_loc_in_range.
  Abort.

  Lemma lir_test_2 l :
    loc_in_range (l +ₗ2) 1 l 4.
  Proof.
    solve_loc_in_range.
  Abort.

  (* TODO move *)
  Definition mkloc (p : prov) (a : addr) : loc := (p, a).

  Lemma lir_test_3 :
    loc_in_range (mkloc (ProvAlloc None) 4) 0 (mkloc (ProvAlloc None) 4) 0.
  Proof.
    solve_loc_in_range.
  Abort.

  (*Lemma lir_test_4 T_st l : *)
    (*loc_in_range (l +ₗ size_of_st T_st) 1 *)


End test.

(** ** Typing rules using the semantic equality solver*)
Inductive FICLocRelated (l : loc) : Set :=.

(* TODO need a notion of size for ltypes i.e. lt1 here *)
(*
Lemma tac_solve_loc_related_eq `{!typeGS Σ} π {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k1 k2 l l1 l2 r1 r2 :
  l1 = l2 ∧ loc_in_range l l1 1 →
  FindHypEqual (FICLocRelated l) (l1 ◁ₗ[π, k1] r1 @ lt1) (l2 ◁ₗ[π, k2] r2 @ lt2) (l1 ◁ₗ[π, k2] r2 @ lt2).
Proof. by move => [-> _]. Qed.
 *)

(** Issues with zero-sized allocations:
  - in case of Vec: when we have the two chunks in the context, how do we decide which one to take anyways?
    Based on the the actual locations, we cannot possibly decide this since everything zeroes out.
    However, we can decide it by looking at the types + offset before doing the zero-sized multiplication.
    In our case, by looking at the arrays and their semantic length.

    Have a semantic judgment with custom rules for deciding whether a type and location/offset match?
      We could have a rule for array + offset by multiple of array_elsize.
      However, that seems a bit fragile, since it would match syntactically -- but the whole point is that syntactic matching is all we can do, because semantically there's no hint to be found here.
      This might help with duplicate/overlapping type assignments in general
        (I'm looking at you, MutexGuard)


    What if I had only one type assignment?
      Then I would have a offset rule just for arrays. At that point, we would also rely on the offset not having been simplified yet.
      But that would already be much easier.
      In general, though, especially with potential Uniq/Sharing overlap with custom types like Mutex, I won't be able to maintain that.
      This overlap is even more critical for the Mutex thing though: if we access the second field of the struct, we won't know that we should not find the base location, because we don't know yet which other place ops (e.g. offset to the data pointer) we will do.

    Can I synthesize some hints for that in some other way?
    - maybe one point is that I simply don't know that the size is zero at the point, if I don't make a case distinction.
      So it will not simplify anyways.
      But still, I need to syntactically extract some information then.
      Also: I should not rely on that too much. Gaining additional information (like size_of T = 0) should not break automation.



    More flexible multimatch context search, with custom rules to guide selection.
    - based on the context folder
    - input: FindMode, location



   But: This will not solve the issue with MutexGuard. There, we would need to find a new assignment in the middle of a place operation.
    - one thing we could try there is to find a new assignment in the context whenever as part of a place access rule. If we can find something stronger, use that instead. But that does not seem right.
      Also, we'd do spurious invariant unfolds in the Mutex Guard case (open the Mutex invariant to do the field access).
    - make place accesses operate on alias_ptr_t at least as far as offsets + field accesses are concerned?


 *)

(*Global Hint Extern 10 (FindHypEqual FICLocSemantic (_ ◁ₗ[_, _] _ @ _) (_ ◁ₗ[_, _] _ @ _) _) =>*)
  (*(notypeclasses refine (tac_solve_loc_eq _ _ _ _ _ _ _ _ _ _); solve_loc_eq) : typeclass_instances.*)

(** This triggers search without any constraints -- the above FindHypEqual instance is what's relevant to ensure relatedness, because Lithium will remember the [FICLocRelated l] key.
  It's important that we don't have any [FICSyntactic] or otherwise instances, since these would be too unconstrained and just match arbitrary location assignments. *)
Lemma find_in_context_type_loc_related_id `{!typeGS Σ} π T :
  (∃ (l' : loc) rt (lt : ltype rt) r (b : bor_kind), l' ◁ₗ[π, b] r @ lt ∗ T (existT _ ((l', lt, r, b))))
  ⊢ find_in_context (FindRelatedLoc π) T.
Proof. iDestruct 1 as (l' rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
Global Instance find_in_context_type_loc_related_inst `{!typeGS Σ} π l :
  FindInContext (FindRelatedLoc π) (FICLocRelated l) | 20 :=
  λ T, i2p (find_in_context_type_loc_related_id π T).


