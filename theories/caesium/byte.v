From caesium Require Import base.

(** Representation of a standard (8-bit) byte. *)

Definition bits_per_byte : Z := 8.

Definition byte_modulus : Z :=
  Eval cbv in 2 ^ bits_per_byte.

Record byte :=
  Byte {
    byte_val : Z;
    byte_constr : -1 < byte_val < byte_modulus;
  }.

Program Definition byte0 : byte := {| byte_val := 0; |}.
Next Obligation. done. Qed.

#[export] Instance byte_eq_dec : EqDecision byte.
Proof.
  move => [b1 H1] [b2 H2]. destruct (decide (b1 = b2)) as [->|].
  - left. assert (H1 = H2) as ->; [|done]. apply proof_irrel.
  - right. naive_solver.
Qed.

Lemma byte_eq (b1 b2 : byte) :
  b1 = b2 ↔ b1.(byte_val) = b2.(byte_val).
Proof.
  destruct b1, b2. split; simpl; [ naive_solver|].
  intros. subst. f_equal. apply proof_irrel.
Qed.
