From caesium Require Export base byte layout int_type loc struct.
Set Default Proof Using "Type".

(** * Bytes and values stored in memory *)

(** Representation of a byte stored in memory. *)
Inductive mbyte : Set :=
| MByte (b : byte) (p : option alloc_id) (** [p] is Some if this integer contains provenance *)
| MPtrFrag (l : loc) (n : nat) (** Fragment [n] for location [l]. *)
| MPoison.

#[export] Instance mbyte_dec_eq : EqDecision mbyte.
Proof. solve_decision. Qed.

Program Definition mbyte_to_byte (mb : mbyte) : option (byte * option alloc_id) :=
  match mb with
  | MByte b p => Some (b, p)
  | MPtrFrag l n => Some (
     {| byte_val := ((l.2 `div` 2^(8 * n)) `mod` byte_modulus) |},
     if l.1 is ProvAlloc a then a else None)
  | MPoison => None
  end.
Next Obligation. move => ? l n. have [] := Z_mod_lt (l.2 `div` 2 ^ (8 * n)) byte_modulus => //*. lia. Qed.

(** Representation of a value (list of bytes). *)
Definition val : Set := list mbyte.
Bind Scope val_scope with val.

(** void is the empty list *)
Definition VOID : val := [].

(** Predicate stating that value [v] has the right size according to layout [ly]. *)
Definition has_layout_val (v : val) (ly : layout) : Prop := length v = ly.(ly_size).
Notation "v `has_layout_val` n" := (has_layout_val v n) (at level 50) : stdpp_scope.
Arguments has_layout_val : simpl never.
Global Typeclasses Opaque has_layout_val.

(** ** Conversion to and from locations. *)
(* rev because we do little endian *)
Definition val_of_loc_n (n : nat) (l : loc) : val :=
  MPtrFrag l <$> rev (seq 0 n).

Definition val_of_loc : loc → val :=
  val_of_loc_n bytes_per_addr.

(* [NULL_bytes(_n)] is the alternative representation of NULL as integer 0 bytes. *)
Definition NULL_bytes_n (n : nat) : val := repeat (MByte byte0 None) n.
Definition NULL_bytes := NULL_bytes_n bytes_per_addr.

Definition val_to_loc_n (n : nat) (v : val) : option loc :=
  if v is MPtrFrag l _ :: _ then
    if (bool_decide (v = val_of_loc_n n l)) then Some l else None
  (* A list of 0s is interpreted as NULL. This is mainly useful when
  memcasting is turned off. Interpreting 0s as NULL does not cause the
  steps for pointers to overlap with the steps for integers since the
  steps are dispatched based on the op_type, not on val_to_loc. *)
  else if v is MByte b _ :: _ then
    if (bool_decide (v = NULL_bytes_n n)) then Some NULL_loc else None
  else None.

Definition val_to_loc : val → option loc :=
  val_to_loc_n bytes_per_addr.

Definition NULL : val := val_of_loc NULL_loc.
Global Typeclasses Opaque NULL.

Lemma val_of_loc_n_length n l:
  length (val_of_loc_n n l) = n.
Proof.
  by rewrite /val_of_loc_n fmap_length rev_length seq_length.
Qed.

Lemma val_to_of_loc_n n l:
  n ≠ 0%nat →
  val_to_loc_n n (val_of_loc_n n l) = Some l.
Proof.
  destruct n as [|n]; first done.
  rewrite /val_of_loc_n seq_S rev_unit /= bool_decide_true //.
  by rewrite /val_of_loc_n seq_S rev_unit.
Qed.

Lemma val_to_of_loc l:
  val_to_loc (val_of_loc l) = Some l.
Proof.
  by apply val_to_of_loc_n.
Qed.

Lemma val_of_to_loc_n n v l:
  val_to_loc_n n v = Some l → v = val_of_loc_n n l ∨ v = NULL_bytes_n n ∧ l = NULL_loc.
Proof.
  rewrite /val_to_loc_n.
  destruct v as [|b v'] eqn:Hv; first done.
  repeat case_match => //; case_bool_decide; naive_solver.
Qed.

Lemma val_of_to_loc v l:
  val_to_loc v = Some l → v = val_of_loc l ∨ v = NULL_bytes ∧ l = NULL_loc.
Proof. apply val_of_to_loc_n. Qed.

Lemma val_to_loc_n_length n v:
  is_Some (val_to_loc_n n v) → length v = n.
Proof.
  rewrite /val_to_loc_n. move => [? H]. repeat case_match => //; simplify_eq.
  - revert select (bool_decide _ = _) => /bool_decide_eq_true ->.
    rewrite /NULL_bytes_n. by rewrite repeat_length.
  - revert select (bool_decide _ = _) => /bool_decide_eq_true ->.
    by rewrite val_of_loc_n_length.
Qed.

Lemma val_to_loc_length v:
  is_Some (val_to_loc v) → length v = bytes_per_addr.
Proof. apply val_to_loc_n_length. Qed.

Global Instance val_of_loc_inj : Inj (=) (=) val_of_loc.
Proof. move => x y Heq. have := val_to_of_loc x. have := val_to_of_loc y. rewrite Heq. by simplify_eq. Qed.

Global Typeclasses Opaque val_of_loc_n val_to_loc_n val_of_loc val_to_loc.
Arguments val_of_loc : simpl never.
Arguments val_to_loc : simpl never.

Global Typeclasses Opaque val_of_loc val_to_loc.
Arguments val_of_loc : simpl never.
Arguments val_to_loc : simpl never.

(** ** Conversion to and from mathematical integers. *)

(* TODO: we currently assume little-endian, make this more generic. *)

Fixpoint val_to_Z_go v : option Z :=
  match v with
  | []           => Some 0
  | MByte b _ :: v => z ← val_to_Z_go v; Some (byte_modulus * z + b.(byte_val))
  | _            => None
  end.

Definition val_to_Z (v : val) (it : int_type) : option Z :=
  if bool_decide (length v = bytes_per_int it) then
    z ← val_to_Z_go v;
    if it.(it_signed) && bool_decide (int_half_modulus it ≤ z) then
      Some (z - int_modulus it)
    else
      Some z
  else None.

Definition val_to_byte_prov (v : val) : option alloc_id :=
  if v is MByte _ (Some p) :: _ then
    guard (Forall (λ e, Is_true (if e is MByte _ (Some p') then bool_decide (p = p') else false)) v); Some p
  else None.

Definition provs_in_bytes (v : val) : list alloc_id :=
  omap (λ b, if b is MByte _ (Some p) then Some p else None) v.

Definition val_to_bytes (v : val) : option val :=
  mapM (λ b, (λ '(v, a), MByte v a) <$> mbyte_to_byte b) v.

Program Fixpoint val_of_Z_go (n : Z) (sz : nat) (p : option alloc_id) : val :=
  match sz return _ with
  | O    => []
  | S sz => MByte {| byte_val := (n `mod` byte_modulus) |} p
            :: val_of_Z_go (n / byte_modulus) sz p
  end.
Next Obligation. move => n. have [] := Z_mod_lt n byte_modulus => //*. lia. Qed.

Definition val_of_Z (z : Z) (it : int_type) (p : option alloc_id) : option val :=
  if bool_decide (z ∈ it) then
    let n := if bool_decide (z < 0) then z + int_modulus it else z in
    Some (val_of_Z_go n (bytes_per_int it) p)
  else
    None.

Definition i2v (n : Z) (it : int_type) : val :=
  default (replicate (bytes_per_int it) MPoison) (val_of_Z n it None).

Lemma val_of_Z_go_length z sz p:
  length (val_of_Z_go z sz p) = sz.
Proof. elim: sz z => //= ? IH ?. by f_equal. Qed.

Lemma val_to_of_Z_go z (sz : nat) p:
  0 ≤ z < 2 ^ (sz * bits_per_byte) →
  val_to_Z_go (val_of_Z_go z sz p) = Some z.
Proof.
  rewrite /bits_per_byte.
  elim: sz z => /=. 1: rewrite /Z.of_nat; move => ??; f_equal; lia.
  move => sz IH z [? Hlt]. rewrite IH /byte_modulus /= -?Z_div_mod_eq_full //.
  split; [by apply Z_div_pos|]. apply Zdiv_lt_upper_bound => //.
  rewrite Nat2Z.inj_succ -Zmult_succ_l_reverse Z.pow_add_r // in Hlt.
  lia.
Qed.

Lemma val_of_Z_length z it v p:
  val_of_Z z it p = Some v → length v = bytes_per_int it.
Proof.
  rewrite /val_of_Z => Hv. case_bool_decide => //. simplify_eq.
  by rewrite val_of_Z_go_length.
Qed.

Lemma i2v_length n it: length (i2v n it) = bytes_per_int it.
Proof.
  rewrite /i2v. destruct (val_of_Z n it None) eqn:Heq.
  - by apply val_of_Z_length in Heq.
  - by rewrite replicate_length.
Qed.

Lemma val_to_Z_length v it z:
  val_to_Z v it = Some z → length v = bytes_per_int it.
Proof. rewrite /val_to_Z. by case_decide. Qed.

Lemma val_of_Z_is_Some p it z:
  z ∈ it → is_Some (val_of_Z z it p).
Proof. rewrite /val_of_Z. case_bool_decide; by eauto. Qed.

Lemma val_of_Z_in_range it z v p:
  val_of_Z z it p = Some v → z ∈ it.
Proof. rewrite /val_of_Z. case_bool_decide; by eauto. Qed.

Lemma val_to_Z_go_in_range v n:
  val_to_Z_go v = Some n → 0 ≤ n < 2 ^ (length v * bits_per_byte).
Proof.
  elim: v n => /=.
  - move => n [] <-. split; first lia.
    apply Z.pow_pos_nonneg; lia.
  - move => ? v IH n. case_match => //.
    destruct (val_to_Z_go v) => /=; last done.
    move => [] <-. move: (IH z eq_refl).
    move: (byte_constr b). rewrite /byte_modulus /bits_per_byte.
    move => [??] [??]. split; first lia.
    have ->: S (length v) * 8 = 8 + length v * 8 by lia.
    rewrite Z.pow_add_r; lia.
Qed.

Lemma val_to_Z_in_range v it n:
  val_to_Z v it = Some n → n ∈ it.
Proof.
  rewrite /val_to_Z. case_decide as Hlen; last done.
  destruct (val_to_Z_go v) eqn:Heq => /=; last done.
  move: Heq => /val_to_Z_go_in_range.
  rewrite Hlen /elem_of /int_elem_of_it /max_int /min_int.
  rewrite /int_half_modulus /int_modulus /bits_per_int.
  destruct (it_signed it) eqn:Hsigned => /=.
  - case_decide => /=.
    + move => [??] [] ?. simplify_eq.
      assert (2 ^ (bytes_per_int it * bits_per_byte) =
              2 * 2 ^ (bytes_per_int it * bits_per_byte - 1)) as Heq.
      { rewrite Z.sub_1_r. rewrite Z.pow_pred_r => //. rewrite /bits_per_byte.
        have ? := bytes_per_int_gt_0 it. lia. }
      rewrite Heq. lia.
    + move => [??] [] ?. lia.
  - move => [??] [] ?. lia.
Qed.

Lemma val_to_Z_unsigned_nonneg v z it :
  it.(it_signed) = false →
  val_to_Z v it = Some z →
  (0 ≤ z)%Z.
Proof.
  rewrite /val_to_Z.
  case_bool_decide; last done.
  intros Hs Hv.
  apply bind_Some in Hv as (z' & Hz & Ha).
  apply val_to_Z_go_in_range in Hz.
  rewrite Hs in Ha. simpl in Ha. simplify_eq.
  lia.
Qed.

Lemma val_to_of_Z z it v p:
  val_of_Z z it p = Some v → val_to_Z v it = Some z.
Proof.
  rewrite /val_of_Z /val_to_Z => Ht.
  destruct (bool_decide (z ∈ it)) eqn: Hr => //. simplify_eq.
  move: Hr => /bool_decide_eq_true[Hm HM].
  have Hlen := bytes_per_int_gt_0 it.
  rewrite /max_int in HM. rewrite /min_int in Hm.
  rewrite val_of_Z_go_length val_to_of_Z_go /=.
  - case_bool_decide as H => //. clear H.
    destruct (it_signed it) eqn:Hs => /=.
    + case_decide => /=; last (rewrite bool_decide_false //; lia).
      rewrite bool_decide_true; [f_equal; lia|].
      rewrite int_modulus_twice_half_modulus. move: Hm HM.
      generalize (int_half_modulus it). move => n Hm HM. lia.
    + rewrite bool_decide_false //. lia.
  - case_bool_decide as Hneg; case_match; split; try lia.
    + rewrite int_modulus_twice_half_modulus. lia.
    + rewrite /int_modulus /bits_per_int. lia.
    + rewrite /int_half_modulus in HM.
      transitivity (2 ^ (bits_per_int it -1)); first lia.
      rewrite /bits_per_int /bytes_per_int /bits_per_byte /=.
      apply Z.pow_lt_mono_r; try lia.
    + rewrite /int_modulus /bits_per_int in HM. lia.
Qed.

Lemma val_of_Z_go_to_prov z n p :
  n ≠ 0%nat →
  val_to_byte_prov (val_of_Z_go z n p) = p.
Proof.
  destruct n as [|n] => // _. destruct p as [a|] => //.
  rewrite /val_to_byte_prov/=. case_option_guard as Hf => //.
  contradict Hf. constructor; [by eauto|].
  move: (z `div` byte_modulus) => {}z.
  elim: n z => /=; eauto.
Qed.

Lemma val_of_Z_to_prov z it p v :
  val_of_Z z it p = Some v →
  val_to_byte_prov v = p.
Proof.
  rewrite /val_of_Z. case_bool_decide => // -[<-]. apply val_of_Z_go_to_prov.
  have := bytes_per_int_gt_0 it. lia.
Qed.

Lemma val_to_Z_val_of_loc_n_None n l it:
  val_to_Z (val_of_loc_n n l) it = None.
Proof.
  destruct n as [|n].
  - rewrite /val_of_loc_n /= /val_to_Z bool_decide_false //=.
    have ? := bytes_per_int_gt_0 it. lia.
  - rewrite /val_of_loc_n seq_S rev_app_distr /= /val_to_Z.
    by case_bool_decide.
Qed.

Lemma val_to_Z_val_of_loc_None l it:
  val_to_Z (val_of_loc l) it = None.
Proof. apply val_to_Z_val_of_loc_n_None. Qed.

Lemma val_to_loc_to_Z_overlap v l it z:
  val_to_loc v = Some l →
  val_to_Z v it = Some z →
  v = NULL_bytes.
Proof. move => /val_of_to_loc[->|[-> ?//]]. by rewrite val_to_Z_val_of_loc_None. Qed.

Lemma val_of_Z_bool_is_Some p it b:
  is_Some (val_of_Z (bool_to_Z b) it p).
Proof. apply: val_of_Z_is_Some. apply: bool_to_Z_elem_of_int_type. Qed.

Lemma val_of_Z_bool b it:
  val_of_Z (bool_to_Z b) it None = Some (i2v (bool_to_Z b) it).
Proof. rewrite /i2v. by have [? ->]:= val_of_Z_bool_is_Some None it b. Qed.

Program Definition val_of_bool (b : bool) : val :=
  [MByte (Byte (bool_to_Z b) _) None].
Next Obligation. by destruct b. Qed.

Definition val_to_bool (v : val) : option bool :=
  match v with
  | [MByte (Byte 0 _) _] => Some false
  | [MByte (Byte 1 _) _] => Some true
  | _                    => None
  end.

Lemma val_to_of_bool b :
  val_to_bool (val_of_bool b) = Some b.
Proof. by destruct b. Qed.

Lemma val_to_bool_length v b:
  val_to_bool v = Some b → length v = 1%nat.
Proof.
  rewrite /val_to_bool. repeat case_match => //.
Qed.

Lemma val_to_bool_iff_val_to_Z v b:
  val_to_bool v = Some b ↔ val_to_Z v u8 = Some (bool_to_Z b).
Proof.
  split.
  - destruct v as [|mb []] => //=; repeat case_match => //=; by move => [<-].
  - destruct v as [|mb []] => //=; repeat case_match => //=; destruct b => //.
Qed.

Lemma val_of_bool_iff_val_of_Z v b:
  val_of_bool b = v ↔ val_of_Z (bool_to_Z b) u8 None = Some v.
Proof.
  split.
  - move => <-. destruct b; cbv; do 3 f_equal; by apply byte_eq.
  - destruct b; cbv; move => [<-]; do 2 f_equal; by apply byte_eq.
Qed.

Lemma i2v_bool_Some b it:
  val_to_Z (i2v (bool_to_Z b) it) it = Some (bool_to_Z b).
Proof. apply: val_to_of_Z. apply val_of_Z_bool. Qed.

Lemma val_of_bool_i2v b :
  val_of_bool b = i2v (bool_to_Z b) u8.
Proof.
  apply val_of_bool_iff_val_of_Z.
  apply val_of_Z_bool.
Qed.

Definition val_to_Z_ot (v : val) (ot : op_type) : option Z :=
  match ot with
  | IntOp it => val_to_Z v it
  | BoolOp => bool_to_Z <$> val_to_bool v
  | _ => None
  end.

Lemma val_to_Z_ot_length v ot z:
  val_to_Z_ot v ot = Some z → length v = (ot_layout ot).(ly_size).
Proof.
  destruct ot => //=.
  - by move => /fmap_Some[?[/val_to_bool_length -> ?]].
  - by move => /val_to_Z_length ->.
Qed.

Lemma val_to_Z_ot_to_Z z it ot v:
  val_to_Z z it = Some v →
  match ot with | BoolOp => ∃ b, it = u8 ∧ v = bool_to_Z b | IntOp it' => it = it' | _ => False end →
  val_to_Z_ot z ot = Some v.
Proof.
  move => ? Hot. destruct ot => //; simplify_eq/= => //. move: Hot => [?[??]]. simplify_eq.
  apply fmap_Some. eexists _. split; [|done]. by apply val_to_bool_iff_val_to_Z.
Qed.

Definition val_to_char (v : val) : option Z :=
  z ← val_to_Z v char_it;
  if decide (is_valid_char z) then Some z else None.
Definition val_of_char (z : Z) :=
  val_of_Z z char_it.

Lemma val_to_char_length v z :
  val_to_char v = Some z → length v = 4%nat.
Proof.
  rewrite /val_to_char.
  intros (z' & Hv & Hvalid)%bind_Some.
  apply val_to_Z_length in Hv. done.
Qed.

Lemma val_to_bytes_id v it n:
  val_to_Z v it = Some n →
  val_to_bytes v = Some v.
Proof.
  rewrite /val_to_Z. case_bool_decide as Heq => // /bind_Some[z [Hgo _]]. clear Heq it.
  apply mapM_Some.
  elim: v z Hgo => //= b v IH z. case_match => // /bind_Some[? [? _]]; simplify_eq.
  constructor. 2: naive_solver. apply fmap_Some. naive_solver.
Qed.

Lemma val_to_bytes_id_bool v b:
  val_to_bool v = Some b →
  val_to_bytes v = Some v.
Proof.
  rewrite /val_to_bool. repeat case_match => //.
Qed.

Lemma val_to_bytes_id_char v z:
  val_to_char v = Some z →
  val_to_bytes v = Some v.
Proof.
  rewrite /val_to_char.
  destruct (val_to_Z v char_it) eqn:Heq; last done.
  simpl. repeat case_match => //.
  intros [= ->].
  by eapply val_to_bytes_id.
Qed.

Lemma val_to_bytes_idemp v v' :
  val_to_bytes v = Some v' →
  val_to_bytes v' = Some v'.
Proof.
  intros Ha.
  induction v as [ | b v IH] in v', Ha |-*; simpl in Ha.
  { injection Ha. intros <-. done. }
  apply bind_Some in Ha as (mb & Ha & Hb).
  apply fmap_Some in Ha as ((bt & aid) & Ha & ->).
  apply bind_Some in Hb as (v'' & Hb & [= <-]).
  apply IH in Hb. simpl. rewrite Hb. simpl. done.
Qed.

(** Rust: Erase provenance information from bytes. Needed to implement the EraseProv operation. *)
Definition erase_prov (v : val) : val :=
  fmap (λ byte,
    match byte with
    | MByte byte _ => MByte byte None
    | _ => byte
    end) v.
Lemma val_to_byte_prov_erase_prov v :
  val_to_byte_prov (erase_prov v) = None.
Proof.
  destruct v as [ | [] v]; done.
Qed.
Lemma erase_prov_length v :
  length (erase_prov v) = length v.
Proof.
  rewrite /erase_prov fmap_length //.
Qed.
Lemma val_to_Z_go_erase_prov v z :
  val_to_Z_go v = Some z →
  val_to_Z_go (erase_prov v) = Some z.
Proof.
  induction v as [ | mb v IH] in z |-*; simpl; first done.
  destruct mb; simpl; [ | done..].
  intros (? & Hz%IH & [= <-])%bind_Some.
  rewrite Hz //.
Qed.
Lemma val_to_Z_erase_prov v it z :
  val_to_Z v it = Some z →
  val_to_Z (erase_prov v) it = Some z.
Proof.
  rewrite /val_to_Z erase_prov_length.
  case_bool_decide as Ha; last done.
  intros (z' & Hz & Hb)%bind_Some.
  erewrite val_to_Z_go_erase_prov; last done.
  done.
Qed.

Arguments erase_prov : simpl never.
Arguments val_to_Z : simpl never.
Arguments val_of_Z : simpl never.
Arguments val_to_byte_prov : simpl never.
Global Typeclasses Opaque val_to_Z val_of_Z val_to_char val_of_char val_of_bool val_to_bool val_to_byte_prov val_to_bytes provs_in_bytes.
