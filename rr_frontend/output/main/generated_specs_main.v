From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.main Require Import generated_code_main extra_proofs_main.

Section specs.
Context `{!typeGS Σ}.

Definition type_of_box_add_42  :=
  fn(∀ (()) : 0 | (x) : (Z), (λ ϝ, []); #x @ (box (int I32)); (λ π : thread_id, (⌜(x + 42)%Z ∈ i32⌝)))
    → ∃ _ : unit, #(x + 42) @ (box (int I32)); (λ π : thread_id, True).

(* No specification provided for main *)

Definition type_of_mut_ref_add_42  :=
  fn(∀ ((), ulft__) : 1 | (x, γ) : (Z * _), (λ ϝ, []); (#x, γ) @ (mut_ref (int I32) ulft__); (λ π : thread_id, (⌜(x + 42)%Z ∈ i32⌝)))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, (gvar_pobs γ (x + 42))).

Definition type_of_mut_ref_add_client  :=
  fn(∀ (()) : 0 | _ : unit, (λ ϝ, []); (λ π : thread_id, True))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, True).

Definition type_of_assert_pair  :=
  fn(∀ (()) : 0 | _ : unit, (λ ϝ, []); (λ π : thread_id, True))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, True).

End specs.