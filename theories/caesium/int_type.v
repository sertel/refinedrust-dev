From caesium Require Import base byte layout.

(** Representation of an integer type (size and signedness). *)

Definition signed := bool.

Record int_type :=
  IntType {
    it_byte_size_log : nat;
    it_signed : signed;
  }.

Global Instance int_type_dec : EqDecision int_type.
Proof. solve_decision. Defined.

Definition bytes_per_int (it : int_type) : nat :=
  2 ^ it.(it_byte_size_log).

Definition bits_per_int (it : int_type) : Z :=
  bytes_per_int it * bits_per_byte.

Definition int_modulus (it : int_type) : Z :=
  2 ^ bits_per_int it.

Definition int_half_modulus (it : int_type) : Z :=
  2 ^ (bits_per_int it - 1).

(* Minimal representable integer. *)
Definition min_int (it : int_type) : Z :=
  if it.(it_signed) then - int_half_modulus it else 0.

(* Maximal representable integer. *)
Definition max_int (it : int_type) : Z :=
  (if it.(it_signed) then int_half_modulus it else int_modulus it) - 1.

Global Instance int_elem_of_it : ElemOf Z int_type :=
  λ z it, min_int it ≤ z ≤ max_int it.

Definition it_layout (it : int_type) :=
  Layout (bytes_per_int it) it.(it_byte_size_log).

Definition i8  := IntType 0 true.
Definition u8  := IntType 0 false.
Definition i16 := IntType 1 true.
Definition u16 := IntType 1 false.
Definition i32 := IntType 2 true.
Definition u32 := IntType 2 false.
Definition i64 := IntType 3 true.
Definition u64 := IntType 3 false.
Definition i128 := IntType 4 true.
Definition u128 := IntType 4 false.

(* hardcoding 64bit pointers for now *)
Definition bytes_per_addr_log : nat := 3%nat.
Definition bytes_per_addr : nat := (2 ^ bytes_per_addr_log)%nat.

Definition void_ptr : layout := {| ly_size := bytes_per_addr; ly_align_log := bytes_per_addr_log |}.
Notation "'void*'" := (void_ptr).

Definition intptr_t  := IntType bytes_per_addr_log true.
Definition uintptr_t := IntType bytes_per_addr_log false.

Definition usize_t  := uintptr_t.
Definition isize_t := intptr_t.
Definition ptrdiff_t := intptr_t.

Definition bool_layout : layout := {| ly_size := 1; ly_align_log := 0 |}.

(*** Lemmas about [int_type] *)
Lemma max_int_signed_lt_unsigned byte_log :
  (max_int (int_type.IntType byte_log true) < max_int (int_type.IntType byte_log false))%Z.
Proof.
  rewrite /max_int /int_half_modulus /int_modulus /= /bits_per_int /bytes_per_int /bits_per_byte /=.
  assert ((2 ^ byte_log)%nat ≥ 1)%Z as Hle.
  { induction byte_log; simpl; lia. }
  move : Hle.
  generalize (2^byte_log)%nat.
  intros ??.
  remember (n * 8)%nat as m.
  replace (n * 8)%Z with (Z.of_nat m) by lia.
  destruct m; first done.
  rewrite -(Nat2Z.inj_sub (S m) 1); last lia.
  simpl. rewrite Nat.sub_0_r.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r; last lia.
  nia.
Qed.
Lemma max_int_isize_lt_usize :
  (max_int isize_t < max_int usize_t)%Z.
Proof.
  apply max_int_signed_lt_unsigned.
Qed.

Lemma bytes_per_int_gt_0 it : bytes_per_int it > 0.
Proof.
  rewrite /bytes_per_int. move: it => [log ?] /=.
  rewrite Z2Nat.inj_pow. assert (0 < 2%nat ^ log); last lia.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma bits_per_int_gt_0 it : bits_per_int it > 0.
Proof.
  rewrite /bits_per_int /bits_per_byte.
  suff : (bytes_per_int it > 0) by lia.
  by apply: bytes_per_int_gt_0.
Qed.

Lemma int_modulus_twice_half_modulus (it : int_type) :
  int_modulus it = 2 * int_half_modulus it.
Proof.
  rewrite /int_modulus /int_half_modulus.
  rewrite -[X in X * _]Z.pow_1_r -Z.pow_add_r; try f_equal; try lia.
  rewrite /bits_per_int /bytes_per_int.
  apply Z.le_add_le_sub_l. rewrite Z.add_0_r.
  rewrite Z2Nat.inj_pow.
  assert (0 < 2%nat ^ it_byte_size_log it * bits_per_byte); last lia.
  apply Z.mul_pos_pos; last (rewrite /bits_per_byte; lia).
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma it_in_range_mod n it:
  n ∈ it → it_signed it = false →
  n `mod` int_modulus it = n.
Proof.
  move => [??] ?. rewrite Z.mod_small //.
  destruct it as [? []] => //. unfold min_int, max_int in *. simpl in *.
  lia.
Qed.

(* TODO move *)
Lemma Nat_pow_ge_1 (n : nat) :
  (1 ≤ 2^n)%nat.
Proof. induction n as [ | n IH]; simpl; lia. Qed.

Lemma int_half_modulus_ge_1 it :
  1 ≤ int_half_modulus it.
Proof.
  rewrite /int_half_modulus.
  assert (0 ≤ bits_per_int it -1).
  { rewrite /bits_per_int /bytes_per_int.
    specialize (Nat_pow_ge_1 (it_byte_size_log it)) => ?.
    rewrite /bits_per_byte. nia. }
  nia.
Qed.
Lemma int_modulus_ge_1 it :
  1 ≤ int_modulus it.
Proof.
  rewrite int_modulus_twice_half_modulus. specialize (int_half_modulus_ge_1 it). lia.
Qed.

Lemma min_int_le_0 (it : int_type) : min_int it ≤ 0.
Proof.
  have ? := bytes_per_int_gt_0 it. rewrite /min_int /int_half_modulus.
  destruct (it_signed it) => //. trans (- 2 ^ 7) => //.
  rewrite -Z.opp_le_mono. apply Z.pow_le_mono_r => //.
  rewrite /bits_per_int /bits_per_byte. lia.
Qed.

Lemma max_int_ge_127 (it : int_type) : 127 ≤ max_int it.
Proof.
  have ? := bytes_per_int_gt_0 it.
  rewrite /max_int /int_modulus /int_half_modulus.
  rewrite /bits_per_int /bits_per_byte.
  have ->: (127 = 2 ^ 7 - 1) by []. apply Z.sub_le_mono => //.
  destruct (it_signed it); apply Z.pow_le_mono_r; lia.
Qed.

Lemma int_modulus_mod_in_range n it:
  it_signed it = false →
  (n `mod` int_modulus it) ∈ it.
Proof.
  move => ?.
  have [|??]:= Z.mod_pos_bound n (int_modulus it). {
    apply: Z.pow_pos_nonneg => //. rewrite /bits_per_int/bits_per_byte/=. lia.
  }
  destruct it as [? []] => //.
  split; unfold min_int, max_int => /=; lia.
Qed.

Lemma elem_of_int_type_0_to_127 (n : Z) (it : int_type):
  0 ≤ n ≤ 127 → n ∈ it.
Proof.
  move => [??]. rewrite /elem_of /int_elem_of_it.
  have ? := min_int_le_0 it.
  have ? := max_int_ge_127 it.
  lia.
Qed.

Lemma min_int_unsigned_0 it :
  it_signed it = false → min_int it = 0.
Proof.
  destruct it; simpl; intros ->. done.
Qed.
Lemma min_int_le_n128_signed it :
  it_signed it = true → (min_int it ≤ -128%Z)%Z.
Proof.
  destruct it as [sz sgn]; simpl; intros ->.
  rewrite /min_int/=/int_half_modulus/bits_per_int/bytes_per_int/bits_per_byte/=.
  induction sz; simpl; first lia.
  rewrite Nat.add_0_r.
  rewrite Nat2Z.inj_add.
  rewrite Z.mul_add_distr_r.
  rewrite -Z.add_sub_assoc.
  rewrite Z.pow_add_r.
  - lia.
  - nia.
  - clear. induction sz; simpl; lia.
Qed.

Lemma bool_to_Z_elem_of_int_type (b : bool) (it : int_type):
  bool_to_Z b ∈ it.
Proof.
  apply elem_of_int_type_0_to_127.
  destruct b => /=; lia.
Qed.

Lemma int_type_layout_wf (it : int_type) :
  layout_wf (it_layout it).
Proof.
  rewrite /layout_wf //.
Qed.
Lemma ptr_layout_wf :
  layout_wf void*.
Proof.
  rewrite /layout_wf //.
Qed.

Definition wrap_unsigned (z : Z) (it : int_type) : Z :=
  z `mod` (int_modulus it).
Definition wrap_signed (z : Z) (it : int_type) : Z :=
  ((z + int_half_modulus it) `mod` (int_modulus it)) - int_half_modulus it.
Definition wrap_to_it (z : Z) (it : int_type) : Z :=
  if it.(it_signed) then wrap_signed z it else wrap_unsigned z it.

Lemma wrap_to_int_id z it :
  z ∈ it → wrap_to_it z it = z.
Proof.
  intros Hit. rewrite /wrap_to_it.
  destruct Hit. unfold min_int, max_int in *.
  destruct (it_signed it) eqn:Heq.
  - rewrite /wrap_signed.
    specialize (int_modulus_twice_half_modulus it) as ?.
    rewrite Zmod_small; lia.
  - rewrite /wrap_unsigned.
    rewrite Zmod_small; lia.
Qed.

Lemma wrap_to_it_in_range z it :
  wrap_to_it z it ∈ it.
Proof.
  rewrite /wrap_to_it /elem_of/int_elem_of_it.
  unfold min_int, max_int in *.
  destruct (it_signed it) eqn:Heq.
  - rewrite /wrap_signed.
    efeed pose proof (Z_mod_lt (z + int_half_modulus it) (int_modulus it)).
    { specialize (int_modulus_ge_1 it). lia. }
    specialize (int_modulus_twice_half_modulus it).
    lia.
  - rewrite /wrap_unsigned.
    efeed pose proof (Z_mod_lt (z) (int_modulus it)).
    { specialize (int_modulus_ge_1 it). lia. }
    lia.
Qed.
