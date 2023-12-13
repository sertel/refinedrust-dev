From stdpp Require Export strings.
From stdpp Require Import gmap list.
From caesium Require Export base layout int_type.
Set Default Proof Using "Type".

Definition char_it : int_type := u32.
Definition char_layout : layout := it_layout char_it.

(* From https://doc.rust-lang.org/std/primitive.char.html:
"A char is a ‘Unicode scalar value’, which is any ‘Unicode code point’ other than a surrogate code point. This has a fixed numerical definition: code points are in the range 0 to 0x10FFFF, inclusive. Surrogate code points, used by UTF-16, are in the range 0xD800 to 0xDFFF."
 *)
Definition is_valid_char (z : Z) :=
  (0 ≤ z ≤ 1114111)%Z ∧ ¬ (55296 ≤ z ≤ 57343)%Z.

Global Instance is_valid_char_dec z : Decision (is_valid_char z).
Proof. solve_decision. Defined.

Lemma is_valid_char_in_char_it z :
  is_valid_char z → z ∈ char_it.
Proof.
  rewrite /is_valid_char.
  rewrite /elem_of /int_elem_of_it.
  rewrite /char_it.
  rewrite /min_int/max_int/=/int_modulus.
  rewrite /bits_per_int/bytes_per_int/byte.bits_per_byte.
  simpl.
  nia.
Qed.

Lemma char_layout_wf : layout_wf char_layout.
Proof. apply int_type_layout_wf. Qed.
