From refinedrust Require Export type int.
From refinedrust Require Import programs.
Set Default Proof Using "Type".

(** * Rules for integer types *)

Open Scope Z_scope.

Section typing.
  Context `{typeGS Σ}.

  Global Program Instance learn_from_hyp_val_int_unsigned it z `{Hu : TCDone (it.(it_signed) = false)} :
    LearnFromHypVal (int it) z :=
    {| learn_from_hyp_val_Q := ⌜0 ≤ z ≤ MaxInt it⌝ |}.
  Next Obligation.
    iIntros (? z Hu ????) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%Hit & %)".
    specialize (val_to_Z_in_range _ _ _ Hit) as [Hran ?].
    iModIntro. iPureIntro. split_and!; [done.. | | ].
    { specialize (min_int_unsigned_0 it). lia. }
    { rewrite MaxInt_eq. done. }
  Qed.
  Global Program Instance learn_from_hyp_val_int_signed it z `{Hs : TCDone (it.(it_signed) = true)} :
    LearnFromHypVal (int it) z :=
    {| learn_from_hyp_val_Q := ⌜MinInt it ≤ z ≤ MaxInt it⌝ |}.
  Next Obligation.
    iIntros (? z Hs ????) "Hv".
    rewrite /ty_own_val/=.
    rewrite !MaxInt_eq !MinInt_eq.
    iDestruct "Hv" as "(%Hit & %)".
    specialize (val_to_Z_in_range _ _ _ Hit) as [Hran ?].
    iModIntro. iPureIntro. split_and!; done.
  Qed.

  Lemma type_int_val z (it : int_type) π :
    ly_size it ≤ max_int isize_t →
    z ∈ it → ⊢ i2v z it ◁ᵥ{π} z @ int it.
  Proof.
    rewrite int_elem_of_it_iff.
    intros ? Hn.
    move: Hn => /(val_of_Z_is_Some None) [v Hv].
    move: (Hv) => /val_to_of_Z Hn.
    rewrite /ty_own_val/=. iPureIntro.
    rewrite MaxInt_eq.
    split; last done. rewrite /i2v Hv/=//.
  Qed.

  Lemma type_val_int z (it : IntType) π (T : ∀ rt, type rt → rt → iProp Σ):
    ⌜z ∈ (it : int_type)⌝ ∗ T _ (int it) z ⊢ typed_value (I2v z it) π T.
  Proof.
    iIntros "[%Hn HT] #CTX".
    iExists Z, (int it), z. iFrame.
    iApply type_int_val; last done.
    apply IntType_to_it_size_bounded.
  Qed.
  Global Instance type_val_int_inst n (it : IntType) π : TypedValue (I2v n it) π :=
    λ T, i2p (type_val_int n it π T).

  Lemma type_relop_int_int E L it v1 (n1 : Z) v2 (n2 : Z) (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) b op π :
    match op with
    | EqOp rit => Some (bool_decide (n1 = n2)%Z, rit)
    | NeOp rit => Some (bool_decide (n1 ≠ n2)%Z, rit)
    | LtOp rit => Some (bool_decide (n1 < n2)%Z, rit)
    | GtOp rit => Some (bool_decide (n1 > n2)%Z, rit)
    | LeOp rit => Some (bool_decide (n1 <= n2)%Z, rit)
    | GeOp rit => Some (bool_decide (n1 >= n2)%Z, rit)
    | _ => None
    end = Some (b, u8) →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ T L (val_of_bool b) bool bool_t b) ⊢
      typed_bin_op π E L v1 (v1 ◁ᵥ{π} n1 @ int it) v2 (v2 ◁ᵥ{π} n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT [%Hv1 %] [%Hv2 _]" (Φ) "#CTX #HE HL Hna HΦ".
    rewrite !int_elem_of_it_iff.
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    iApply (wp_binop_det_pure (val_of_bool b)).
    { split.
      - destruct op => //; inversion 1; simplify_eq; symmetry;
        by apply val_of_bool_iff_val_of_Z.
      - move => ->. econstructor; [done.. | ].
        by apply val_of_bool_iff_val_of_Z. }
    iIntros "!> Hcred". iApply ("HΦ" with "HL Hna") => //.
    rewrite /ty_own_val/=. by destruct b.
  Qed.

  Global Program Instance type_eq_int_int_inst E L it v1 n1 v2 n2 π :
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 (EqOp u8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 = n2)) _ π _).
  Solve Obligations with done.
  Global Program Instance type_ne_int_int_inst E L it v1 n1 v2 n2 π :
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 (NeOp u8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 ≠ n2)) _ π _).
  Solve Obligations with done.
  Global Program Instance type_lt_int_int_inst E L it v1 n1 v2 n2 π :
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 (LtOp u8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 < n2)%Z) _ π _).
  Solve Obligations with done.
  Global Program Instance type_gt_int_int_inst E L it v1 n1 v2 n2 π :
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 (GtOp u8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 > n2)%Z) _ π _).
  Solve Obligations with done.
  Global Program Instance type_le_int_int_inst E L it v1 n1 v2 n2 π :
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 (LeOp u8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 <= n2)%Z) _ π _).
  Solve Obligations with done.
  Global Program Instance type_ge_int_int_inst E L it v1 n1 v2 n2 π :
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 (GeOp u8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 >= n2)%Z) _ π _).
  Solve Obligations with done.

  Definition arith_op_result (it : int_type) n1 n2 op : option Z :=
    match op with
    | AddOp => Some (n1 + n2)
    | SubOp => Some (n1 - n2)
    | MulOp => Some (n1 * n2)
    | AndOp => Some (Z.land n1 n2)
    | OrOp  => Some (Z.lor n1 n2)
    | XorOp => Some (Z.lxor n1 n2)
    | ShlOp => Some (n1 ≪ n2)
    | ShrOp => Some (n1 ≫ n2)
    | DivOp => Some (n1 `quot` n2)
    | ModOp => Some (n1 `rem` n2)
    | CheckedAddOp => Some (n1 + n2)
    | CheckedSubOp => Some (n1 - n2)
    | CheckedMulOp => Some (n1 * n2)
    | _     => None (* Relational operators. *)
    end.

  Definition arith_op_sidecond (it : int_type) (n1 n2 n : Z) op : Prop :=
    match op with
    (* these sideconditions are stronger than necessary and do not support the wrapping for unsigned unchecked ops that is allowed by the opsem *)
    | AddOp => n ∈ it
    | SubOp => n ∈ it
    | MulOp => n ∈ it
    | AndOp => True
    | OrOp  => True
    | XorOp => True
    (* TODO: check accuracy of shifting semantics *)
    | ShlOp => 0 ≤ n2 < bits_per_int it ∧ 0 ≤ n1 ∧ n ≤ MaxInt it
    | ShrOp => 0 ≤ n2 < bits_per_int it ∧ 0 ≤ n1
    | DivOp => n2 ≠ 0 ∧ n ∈ it
    | ModOp => n2 ≠ 0 ∧ n ∈ it
    | CheckedAddOp => n ∈ it
    | CheckedSubOp => n ∈ it
    | CheckedMulOp => n ∈ it
    | _     => True (* Relational operators. *)
    end.

  Lemma type_arithop_int_int E L π it v1 n1 v2 n2 (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) n op:
    int_arithop_result it n1 n2 op = Some n →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜arith_op_sidecond it n1 n2 n op⌝ ∗ T L (i2v n it) Z (int it) n) ⊢
      typed_bin_op π E L v1 (v1 ◁ᵥ{π} n1 @ int it) v2 (v2 ◁ᵥ{π} n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT [%Hv1 %] [%Hv2 _] %Φ #CTX #HE HL Hna HΦ".
    rewrite !int_elem_of_it_iff.
    iDestruct ("HT" with "[] []" ) as (Hsc) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    iApply wp_int_arithop; [done..| | ].
    { move: Hsc. rewrite /int_arithop_sidecond /arith_op_sidecond. destruct op; rewrite ?int_elem_of_it_iff ?MaxInt_eq; done. }

    iIntros (v Hv) "!> Hcred". rewrite /i2v Hv/=. iApply ("HΦ" with "HL Hna [] HT").
    rewrite /ty_own_val/=.
    iPureIntro. split; first by apply: val_to_of_Z. done.
  Qed.
  Global Program Instance type_add_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 AddOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 + n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_sub_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 SubOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 - n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_mul_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 MulOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 * n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_checked_add_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 CheckedAddOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 + n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_checked_sub_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 CheckedSubOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 - n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_checked_mul_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 CheckedMulOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 * n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_div_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 DivOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 `quot` n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_mod_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 ModOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 `rem` n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_and_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 AndOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (Z.land n1 n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_or_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 OrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (Z.lor n1 n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_xor_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 XorOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (Z.lxor n1 n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shl_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 ShlOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 ≪ n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shr_int_int_inst E L π it v1 n1 v2 n2:
    TypedBinOpVal π E L v1 (int it) n1 v2 (int it) n2 ShrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int E L π it v1 n1 v2 n2 T (n1 ≫ n2) _ _).
  Next Obligation. done. Qed.

  Inductive destruct_hint_switch_int :=
  | DestructHintSwitchIntCase (n : Z)
  | DestructHintSwitchIntDefault.

  Lemma type_switch_int π E L n it m ss def fn R ϝ v:
    ([∧ map] i↦mi ∈ m,
      li_trace (DestructHintSwitchIntCase i) (
             ⌜n = i⌝ -∗ ∃ s, ⌜ss !! mi = Some s⌝ ∗ typed_stmt π E L s fn R ϝ)) ∧
    (li_trace (DestructHintSwitchIntDefault) (
                     ⌜n ∉ (map_to_list m).*1⌝ -∗ typed_stmt π E L def fn R ϝ))
    ⊢ typed_switch π E L v _ (int it) n it m ss def fn R ϝ.
  Proof.
    unfold li_trace.
    iIntros "HT Hit". rewrite /ty_own_val/=. iDestruct "Hit" as "[%Hv %Hit]".
    iExists n. iSplit; first done.
    iInduction m as [] "IH" using map_ind; simplify_map_eq => //.
    { iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_empty. set_solver. }
    rewrite big_andM_insert //. destruct (decide (n = i)); subst.
    - rewrite lookup_insert. iDestruct "HT" as "[[HT _] _]". by iApply "HT".
    - rewrite lookup_insert_ne//. iApply "IH". iSplit; first by iDestruct "HT" as "[[_ HT] _]".
      iIntros (Hn). iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_insert //. set_solver.
  Qed.
  Global Instance type_switch_int_inst π E L n v it : TypedSwitch π E L v _ (int it) n it :=
    λ m ss def fn R ϝ, i2p (type_switch_int π E L n it m ss def fn R ϝ v).

  Lemma type_neg_int π E L n it v (T : typed_un_op_cont_t) :
    (⌜n ∈ it⌝ -∗ ⌜it.(it_signed)⌝ ∗ ⌜n ≠ MinInt it⌝ ∗ T L (i2v (-n) it) _ (int it) (-n))
    ⊢ typed_un_op π E L v (v ◁ᵥ{π} n @ int it)%I (NegOp) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    rewrite int_elem_of_it_iff MinInt_eq.
    iIntros "HT [%Hv %Hit] %Φ #CTX #HE HL Hna HΦ". move: (Hv) => /val_to_Z_in_range ?.
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    have [|v' Hv']:= val_of_Z_is_Some None it (- n). {
      unfold elem_of, int_elem_of_it, max_int, min_int in *.
      destruct it as [?[]] => //; simpl in *; lia.
    }
    rewrite /i2v Hv'/=.
    iApply wp_neg_int => //. iNext. iIntros "Hcred".
    iApply ("HΦ" with "HL Hna [] HT").
    rewrite /ty_own_val/=.
    iPureIntro. split; last done. by apply: val_to_of_Z.
  Qed.
  Global Instance type_neg_int_inst π E L n it v:
    TypedUnOpVal π E L v (int it)%I n NegOp (IntOp it) :=
    λ T, i2p (type_neg_int π E L n it v T).

  (*(if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n)*)
  Lemma type_not_int π E L n it v (T : typed_un_op_cont_t) :
    (⌜n ∈ it⌝ -∗ T L (i2v ((if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n)) it) _ (int it) ((if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n)))
    ⊢ typed_un_op π E L v (v ◁ᵥ{π} n @ int it)%I (NotIntOp) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    rewrite int_elem_of_it_iff.
    iIntros "HT [%Hv %Hit] %Φ #CTX #HE HL Hna HΦ". move: (Hv) => /val_to_Z_in_range ?.
    iDestruct ("HT" with "[//]") as "HT".
    set (nz := (if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n)).
    have [|v' Hv']:= val_of_Z_is_Some None it nz. {
      unfold elem_of, int_elem_of_it, max_int, min_int, Z_lunot, Z.lnot, Z.pred in *.
      destruct it as [?[]] => //; simpl in *; first lia.
      split.
      - apply Z.mod_pos. rewrite /bits_per_int/bytes_per_int/bits_per_byte. lia.
      - rewrite /int_modulus. subst nz.
        match goal with
        | |- ?a `mod` ?b ≤ _ => specialize (Z_mod_lt a b); lia
        end.
    }
    rewrite /i2v /=.
    iApply (wp_unop_det_pure v').
    { intros. subst nz. split; [inversion 1; simplify_eq/= | move => ->]; simplify_eq/=; first done.
      econstructor; done. }
    rewrite Hv' /=.
    iIntros "!> Hcred". iApply ("HΦ" with "HL Hna"); last done.
    rewrite /ty_own_val/=. iPureIntro.
    split; last done. by apply: val_to_of_Z.
  Qed.
  Global Instance type_not_int_inst π E L n it v:
    TypedUnOpVal π E L v (int it)%I n NotIntOp (IntOp it) :=
    λ T, i2p (type_not_int π E L n it v T).

  Lemma type_cast_int π E L n (it1 it2 : int_type) v (T : typed_un_op_cont_t) :
    ⌜ly_size it2 ≤ MaxInt isize_t⌝ ∗ (⌜n ∈ it1⌝ -∗ ∀ v, T L v _ (int it2) (wrap_to_it n it2))
    ⊢ typed_un_op π E L v (v ◁ᵥ{π} n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    rewrite /ty_own_val/=.
    rewrite int_elem_of_it_iff MaxInt_eq.
    iIntros "[%Hit2 HT] [%Hv %Hit] %Φ #CTX #HE HL Hna HΦ".
    iSpecialize ("HT" with "[]").
    { iPureIntro. by apply: val_to_Z_in_range. }
    destruct (val_of_Z_is_Some (val_to_byte_prov v) it2 (wrap_to_it n it2)) as (n' & Hit').
    { apply wrap_to_it_in_range. }
    iApply wp_cast_int => //.
    iNext. iIntros "Hcred". iApply ("HΦ" with "HL Hna [] HT") => //.
    rewrite /ty_own_val/= MaxInt_eq.
    iPureIntro. split; last done. by apply: val_to_of_Z.
  Qed.
  Global Instance type_cast_int_inst π E L n it1 it2 v:
    TypedUnOpVal π E L v (int it1)%I n (CastOp (IntOp it2)) (IntOp it1) :=
    λ T, i2p (type_cast_int π E L n it1 it2 v T).

  (** Bool *)
  Lemma type_val_bool' b π :
    ⊢ (val_of_bool b) ◁ᵥ{π} b @ bool_t.
  Proof. rewrite /ty_own_val/=. iIntros. by destruct b. Qed.
  Lemma type_val_bool b π (T : ∀ rt, type rt → rt → iProp Σ) :
    (T bool bool_t b) ⊢ typed_value (val_of_bool b) π T.
  Proof. iIntros "HT #LFT". iExists bool, bool_t, b. iFrame. iApply type_val_bool'. Qed.
  Global Instance type_val_bool_inst b π : TypedValue (val_of_bool b) π :=
    λ T, i2p (type_val_bool b π T).

  Lemma val_to_bool_val_to_Z v b :
    val_to_bool v = Some b →
    val_to_Z v u8 = Some (bool_to_Z b).
  Proof.
    intros Heq; unfold val_to_bool in Heq.
    destruct v as [ | m]; first done.
    destruct m as [ m | |]; [|done..].
    destruct m as [m  ].
    destruct (decide (m = 0)) as [ -> | ].
    { destruct v.
      - injection Heq as <-. done.
      - congruence. }
    destruct (decide (m = 1)) as [-> | ].
    { destruct v.
      - injection Heq as <-. done.
      - congruence. }
    destruct m as [ | [] | []]; congruence.
  Qed.

  (* TODO: we should maybe also support RelOp with BoolOp in Caesium and use BoolOp here.
     That would make the semantics maybe more realistic by triggering UB on invalid boolean input patterns.
  *)
  Lemma type_relop_bool_bool E L v1 b1 v2 b2 (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) b op π :
    match op with
    | EqOp rit => Some (eqb b1 b2, rit)
    | NeOp rit => Some (negb (eqb b1 b2), rit)
    | _ => None
    end = Some (b, u8) →
    (T L (val_of_bool b) bool bool_t b)
    ⊢ typed_bin_op π E L v1 (v1 ◁ᵥ{π} b1 @ bool_t) v2 (v2 ◁ᵥ{π} b2 @ bool_t) op (BoolOp) (BoolOp) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT %Hv1 %Hv2" (Φ) "#CTX #HE HL Hna HΦ".
    iApply (wp_binop_det_pure (val_of_bool b)).
    { destruct op, b1, b2; simplify_eq.
      all: split; [ inversion 1; simplify_eq/= | move => -> ]; simplify_eq/=.
      all: try by (symmetry; eapply val_of_bool_iff_val_of_Z).
      all: econstructor => //; case_bool_decide; try done.
      all: by apply val_of_bool_iff_val_of_Z. }
    iIntros "!> Hcred". iApply ("HΦ" with "HL Hna"); last done.
    rewrite /ty_own_val/=.
    iPureIntro. by destruct b.
  Qed.

  Global Program Instance type_eq_bool_bool_inst E L v1 b1 v2 b2 π :
    TypedBinOpVal π E L v1 (bool_t) b1 v2 (bool_t) b2 (EqOp u8) (BoolOp) (BoolOp) := λ T, i2p (type_relop_bool_bool E L v1 b1 v2 b2 T (eqb b1 b2) _ π _).
  Solve Obligations with done.
  Global Program Instance type_ne_bool_bool_inst E L v1 b1 v2 b2 π :
    TypedBinOpVal π E L v1 (bool_t) b1 v2 (bool_t) b2 (NeOp u8) (BoolOp) (BoolOp) := λ T, i2p (type_relop_bool_bool E L v1 b1 v2 b2 T (negb (eqb b1 b2)) _ π _).
  Solve Obligations with done.

  Lemma type_notop_bool π E L v b (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) :
    T L (val_of_bool (negb b)) bool bool_t (negb b)
    ⊢ typed_un_op π E L v (v ◁ᵥ{π} b @ bool_t) NotBoolOp BoolOp T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "HT %Hv" (Φ) "#CTX #HE HL Hna HΦ".
    iApply (wp_unop_det_pure (val_of_bool (negb b))).
    { intros. split; [inversion 1; simplify_eq/= | move => ->]; simplify_eq/=; first done.
      econstructor; done. }
    iIntros "!> Hcred". iApply ("HΦ" with "HL Hna"); last done.
    rewrite /ty_own_val/=. iPureIntro. by destruct b.
  Qed.
  Global Instance type_notop_bool_inst π E L v b :
    TypedUnOpVal π E L v bool_t b NotBoolOp BoolOp := λ T, i2p (type_notop_bool π E L v b T).

  (** Bitwise operators *)
  Definition bool_arith_op_result b1 b2 op : option bool :=
    match op with
    | AndOp => Some (andb b1 b2)
    | OrOp  => Some (orb b1 b2)
    | XorOp => Some (xorb b1 b2)
    | _     => None (* Other operators are not supported. *)
    end.

  Lemma type_arithop_bool_bool E L π v1 b1 v2 b2 (T : llctx → val → ∀ rt, type rt → rt → iProp Σ) b op:
    bool_arith_op_result b1 b2 op = Some b →
    T L (val_of_bool b) bool (bool_t) b ⊢
    typed_bin_op π E L v1 (v1 ◁ᵥ{π} b1 @ bool_t) v2 (v2 ◁ᵥ{π} b2 @ bool_t) op (BoolOp) (BoolOp) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT %Hv1 %Hv2 %Φ #CTX #HE HL Hna HΦ".
    iApply (wp_binop_det_pure (val_of_bool b)).
    { destruct op, b1, b2; simplify_eq.
      all: split; [ inversion 1; simplify_eq/= | move => -> ]; simplify_eq/=; try done.
      all: eapply ArithOpBB; done. }
    iIntros "!> Hcred". iApply ("HΦ" with "HL Hna [] HT").
    rewrite /ty_own_val/=. destruct b; done.
  Qed.

  Global Program Instance type_and_bool_bool_inst E L π v1 b1 v2 b2:
    TypedBinOpVal π E L v1 (bool_t) b1 v2 (bool_t) b2 AndOp (BoolOp) (BoolOp) := λ T, i2p (type_arithop_bool_bool E L π v1 b1 v2 b2 T (andb b1 b2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_or_bool_bool_inst E L π v1 b1 v2 b2:
    TypedBinOpVal π E L v1 (bool_t) b1 v2 (bool_t) b2 OrOp (BoolOp) (BoolOp) := λ T, i2p (type_arithop_bool_bool E L π v1 b1 v2 b2 T (orb b1 b2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_xor_bool_bool_inst E L π v1 b1 v2 b2:
    TypedBinOpVal π E L v1 (bool_t) b1 v2 (bool_t) b2 XorOp (BoolOp) (BoolOp) := λ T, i2p (type_arithop_bool_bool E L π v1 b1 v2 b2 T (xorb b1 b2) _ _).
  Next Obligation. done. Qed.

  Inductive trace_if_bool :=
  | TraceIfBool (b : bool).

  Lemma type_if_bool E L π b v T1 T2:
    (case_destruct b (λ b' _,
      li_trace (TraceIfBool b, b') (
      if b' then T1 else T2)))
    ⊢ typed_if E L v (v ◁ᵥ{π} b @ bool_t) T1 T2.
  Proof.
    unfold li_trace, case_destruct. rewrite /ty_own_val/=. iIntros "(% & Hs) Hv".
    iExists b. iSplit; first done. done.
  Qed.
  Global Instance type_if_bool_inst E L π b v : TypedIf E L v (v ◁ᵥ{π} b @ bool_t)%I :=
    λ T1 T2, i2p (type_if_bool E L π b v T1 T2).

  Lemma type_assert_bool E L π b s fn R v ϝ :
    (⌜b = true⌝ ∗ typed_stmt π E L s fn R ϝ)
    ⊢ typed_assert π E L v (bool_t) b s fn R ϝ.
  Proof.
    iIntros "[-> Hs] #CTX #HE HL Hna Hb". by iFrame.
  Qed.
  Global Instance type_assert_bool_inst E L π b v : TypedAssert π E L v (bool_t) b :=
    λ s fn R ϝ, i2p (type_assert_bool E L π b s fn R v ϝ).


  (** Char *)
  Lemma type_char_val z π :
    is_valid_char z → ⊢ i2v z char_it ◁ᵥ{π} z @ char_t.
  Proof.
    intros Hvalid.
    specialize (is_valid_char_in_char_it _ Hvalid) as Hn.
    move: Hn => /(val_of_Z_is_Some None) [v Hv].
    move: (Hv) => /val_to_of_Z Hn.
    rewrite /ty_own_val/=. iPureIntro.
    rewrite /val_to_char.
    apply bind_Some. exists z.
    split.
    - rewrite /i2v Hv/=//.
    - rewrite decide_True; done.
  Qed.

  Lemma type_val_char z π (T : ∀ rt, type rt → rt → iProp Σ):
    ⌜is_valid_char z⌝ ∗ T _ (char_t) z ⊢ typed_value (I2v z CharIt) π T.
  Proof.
    iIntros "[%Hn HT] #CTX".
    iExists Z, (char_t), z. iFrame.
    iApply type_char_val; last done.
  Qed.
  Global Instance type_val_char_inst n π : TypedValue (I2v n CharIt) π :=
    λ T, i2p (type_val_char n π T).
End typing.
