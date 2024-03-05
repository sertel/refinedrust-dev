From caesium Require Import lang.

(** * Syntactic types *)
(** Syntactic types determine abstract layout information (i.e. that a struct has certain fields), but do not determine a concrete data layout yet.
  For generic code, they capture all the operational layout information that the generic type needs to satisfy, i.e. we can verify generic code by parameterizing it over the syntactic type of the type parameters.
*)


(* TODO move *)
Lemma Nat_pow_max x n1 n2 :
  (1 ≤ x)%nat →
  (x^(Nat.max n1 n2))%nat = Nat.max (x^n1) (x^n2).
Proof.
  intros ?.
  destruct (Nat.max_spec n1 n2) as [[Hle ->] | [Hle ->]].
  - rewrite Nat.max_r; first lia. apply Nat.pow_le_mono_r; lia.
  - rewrite Nat.max_l; first lia. apply Nat.pow_le_mono_r; lia.
Qed.
(* TODO move *)
Lemma Nat_Z_in_bounds_max (l h : Z) (n1 n2 : nat) :
  (l ≤ n1 ≤ h) →
  (l ≤ n2 ≤ h) →
  (l ≤ (n1 `max` n2)%nat ≤ h).
Proof.
  intros Ha Hb. destruct (Nat.max_spec n1 n2) as [[Hle ->] | [Hle ->]]; lia.
Qed.

(* TODO move *)
Lemma max_alloc_end_le_usize :
  (max_alloc_end ≤ max_int usize_t)%Z.
Proof.
  unfold_common_caesium_defs. simpl. lia.
Qed.

Lemma mjoin_has_struct_layout sl vs :
  Forall2 (λ v ly, v `has_layout_val` ly) vs sl.(sl_members).*2 →
  mjoin vs `has_layout_val` sl.
Proof.
  rewrite /has_layout_val/layout_of{2}/ly_size/=.
  generalize (sl_members sl) => fields. clear sl.
  induction fields as [ | [n field] fields IH] in vs |-*; simpl; intros Hf.
  - apply Forall2_nil_inv_r in Hf as ->. done.
  - destruct vs as [ | v vs].
    { apply Forall2_nil_inv_l in Hf. naive_solver. }
    apply Forall2_cons_inv in Hf as (Hlen & Hf).
    simpl. rewrite app_length Hlen.
    rewrite IH; done.
Qed.

Lemma mjoin_pad_struct_layout sl els f :
  Forall2 (λ '(n, ly) v, v `has_layout_val` ly) (named_fields sl.(sl_members)) els →
  (∀ ly, length (f ly) = ly_size ly) →
  mjoin (pad_struct sl.(sl_members) els f) `has_layout_val` sl.
Proof.
  intros Ha Hb. apply mjoin_has_struct_layout.
  move: Ha. generalize (sl_members sl) => fields. clear sl.
  induction fields as [ | [[name | ] field] fields IH] in els |-*; simpl; first done.
  - destruct els as [ | v els]; simpl; first inversion 1.
    intros [Ha Hf]%Forall2_cons_inv. econstructor; first done. by apply IH.
  - intros Hf. econstructor; first apply Hb. by apply IH.
Qed.

(** We define a closed set of integer types that are allowed to appear as literals in the source code,
  in order to ensure that their size fits into [isize]. *)
(* TODO: maybe transition everything to that, so that we also don't get sideconditions in is_int_ot? *)
Inductive IntType : Set :=
  | I8 | I16 | I32 | I64 | I128
  | U8 | U16 | U32 | U64 | U128
  | ISize | USize.
Definition CharIt := U32.
Definition IntType_to_it (I : IntType) : int_type :=
  match I with
  | I8 => i8
  | I16 => i16
  | I32 => i32
  | I64 => i64
  | I128 => i128
  | U8 => u8
  | U16 => u16
  | U32 => u32
  | U64 => u64
  | U128 => u128
  | ISize => isize_t
  | USize => usize_t
  end.
Coercion IntType_to_it : IntType >-> int_type.
Lemma IntType_to_it_size_bounded I :
  (ly_size (it_layout (IntType_to_it I)) ≤ max_int isize_t)%Z.
Proof.
  destruct I; done.
Qed.
Global Instance IntType_eq_dec : EqDecision IntType.
Proof. solve_decision. Defined.

Lemma IntType_align_le (it : IntType) :
  ly_align (it_layout it) ≤ 16.
Proof.
  rewrite /it_layout /ly_align/ly_align_log/it_byte_size_log.
  destruct it => /=; lia.
Qed.
Lemma IntType_align_ge_1 (it : IntType) :
  1 ≤ ly_align (it_layout it).
Proof.
  rewrite /it_layout /ly_align/ly_align_log/it_byte_size_log.
  destruct it=> /=; lia.
Qed.
Lemma IntType_size_le (it : IntType) :
  ly_size (it_layout it) ≤ 16.
Proof.
  rewrite /it_layout /ly_size/bytes_per_int/it_byte_size_log.
  destruct it => /=; lia.
Qed.
Lemma IntType_size_ge_1 (it : IntType) :
  1 ≤ ly_size (it_layout it).
Proof.
  rewrite /it_layout /ly_size/bytes_per_int/it_byte_size_log.
  destruct it => /=; lia.
Qed.

(** Sealed versions of [max_int] / [min_int] in order to avoid Coq from choking on things like [max_int usize_t] *)
Definition MaxInt_def (it : int_type) := max_int it.
Definition MaxInt_aux it : seal (MaxInt_def it). by eexists. Qed.
Definition MaxInt it := (MaxInt_aux it).(unseal).
Definition MaxInt_eq it : MaxInt it = max_int it := (MaxInt_aux it).(seal_eq).

Definition MinInt_def (it : int_type) := min_int it.
Definition MinInt_aux it : seal (MinInt_def it). by eexists. Qed.
Definition MinInt it := (MinInt_aux it).(unseal).
Definition MinInt_eq it : MinInt it = min_int it := (MinInt_aux it).(seal_eq).

Definition int_elem_of_it' : ElemOf Z int_type := λ z it, (MinInt it ≤ z ≤ MaxInt it)%Z.
Lemma int_elem_of_it_iff z it :
  int_elem_of_it' z it ↔ int_elem_of_it z it.
Proof.
  rewrite /elem_of/int_elem_of_it' MinInt_eq MaxInt_eq//.
Qed.

Ltac unsafe_unfold_common_caesium_defs :=
  rewrite ?MaxInt_eq ?MinInt_eq;
  repeat match goal with
  | H : context[MaxInt ?it] |- _ => rewrite !MaxInt_eq in H
  | H : context[MinInt ?it] |- _ => rewrite !MinInt_eq in H
  end;
  unfold_common_caesium_defs.

(* integer literals in the code should use I2v *)
Definition I2v (z : Z) (I : IntType) : val := i2v z I.
Arguments I2v : simpl never.

(** Rust repr options *)
Inductive struct_repr :=
  (** repr(rust) *)
  | StructReprRust
  (** repr(C) *)
  | StructReprC
  (** repr(transparent) *)
  | StructReprTransparent.
Global Instance struct_repr_eqdec : EqDecision struct_repr.
Proof. solve_decision. Defined.
Global Instance struct_repr_inhabited : Inhabited struct_repr.
Proof. exact (populate StructReprRust). Qed.

Inductive union_repr :=
  (** repr(rust) *)
  | UnionReprRust
  (** repr(C) *)
  | UnionReprC.
Global Instance union_repr_eqdec : EqDecision union_repr.
Proof. solve_decision. Defined.
Global Instance union_repr_inhabited : Inhabited union_repr.
Proof. exact (populate UnionReprRust). Qed.

(** Rust already picks a representation for the tag at the MIR level, so we do not include this part. *)
Inductive enum_repr :=
  (** repr(rust) *)
  | EnumReprRust
  (** repr(C) *)
  | EnumReprC
  (** repr(transparent) *)
  | EnumReprTransparent.
Global Instance enum_repr_eqdec : EqDecision enum_repr.
Proof. solve_decision. Defined.
Global Instance enum_repr_inhabited : Inhabited enum_repr.
Proof. exact (populate EnumReprRust). Qed.

(** ** Syntactic types *)
(** Syntactic types describe primitive types relevant to the operational semantics *before* layouting.
  They are not to be confused with proper semantic types.
 *)
Inductive syn_type : Set :=
  (* integers *)
  | IntSynType (it : int_type)
  (* booleans *)
  | BoolSynType
  (* pointers. currently no distinction in terms of aliasing or so *)
  | PtrSynType
  (* function pointers *)
  | FnPtrSynType
  (* structs *)
  | StructSynType (sn : string) (field_list : list (string * syn_type)) (repr : struct_repr)
  (* unit *)
  | UnitSynType
  (* arrays of a specific length *)
  | ArraySynType (st : syn_type) (len : nat)
  (* UnsafeCell. Currently, it does not do anything exciting, but some day.. *)
  | UnsafeCell (st : syn_type)
  (* no type, using a literal layout *)
  (* we use this mostly to refer to untyped chunks of memory at runtime,
     especially around the uninit semtype *)
  | UntypedSynType (ly : layout)
  (* enums *)
  | EnumSynType (en : string) (tag_it : IntType) (variant_list : list (string * syn_type)) (repr : enum_repr)
  (* unions *)
  | UnionSynType (un : string) (variant_list : list (string * syn_type)) (repr : union_repr)
  (* char *)
  | CharSynType
.
Canonical Structure syn_typeO := leibnizO syn_type.
Global Instance syn_type_eq_dec : EqDecision syn_type.
Proof.
  refine (fix go (st1 st2 : syn_type) {struct st1} : Decision (st1 = st2) :=
    match st1, st2 with
    | IntSynType it1, IntSynType it2 => cast_if (decide (it1 = it2))
    | BoolSynType, BoolSynType => left _
    | PtrSynType, PtrSynType => left _
    | FnPtrSynType, FnPtrSynType => left _
    | StructSynType n1 fields1 repr1, StructSynType n2 fields2 repr2 =>
        if (decide (repr1 = repr2)) then
          cast_if_and (decide (n1 = n2))
            (List.list_eq_dec _ fields1 fields2)
          else right _
    | UnitSynType, UnitSynType => left _
    | ArraySynType st len, ArraySynType st' len' =>
        if (decide (len = len')) then
          cast_if (go st st')
        else right _
    | UntypedSynType ly1, UntypedSynType ly2 => cast_if (decide (ly1 = ly2))
    | UnsafeCell st1, UnsafeCell st2 =>
        cast_if (go st1 st2)
    | EnumSynType en1 tag1 vars1 repr1, EnumSynType en2 tag2 vars2 repr2 =>
        if decide (repr1 = repr2) then
        if (decide (en1 = en2)) then
          cast_if_and (decide (tag1 = tag2))
            (List.list_eq_dec _ vars1 vars2) else right _
        else right _
    | UnionSynType un1 vars1 repr1, UnionSynType un2 vars2 repr2 =>
        if decide (repr1 = repr2) then
        cast_if_and (decide (un1 = un2))
          (List.list_eq_dec _ vars1 vars2)
        else right _
    | CharSynType, CharSynType =>
        left _
    | _, _ => right _
    end);
    try (clear go; abstract intuition congruence).
    all: unshelve eapply prod_eq_dec; exact go.
Defined.

Lemma syn_type_strong_ind (P : syn_type → Prop) :
  (∀ it : int_type, P (IntSynType it)) →
  P BoolSynType →
  P PtrSynType →
  P FnPtrSynType →
  (∀ (sn : string) (field_list : list (string * syn_type)) repr,
    Forall (λ '(_, st), P st) field_list →
    P (StructSynType sn field_list repr)) →
  P UnitSynType →
  (∀ st : syn_type, P st → ∀ len : nat, P (ArraySynType st len)) →
  (∀ st : syn_type, P st → P (UnsafeCell st)) →
  (∀ ly : layout, P (UntypedSynType ly)) →
  (∀ (en : string) (tag_it : IntType) (variant_list : list (string * syn_type)) repr,
    Forall (λ '(_, st), P st) variant_list →
    P (EnumSynType en tag_it variant_list repr)) →
  (∀ (un : string) (variant_list : list (string * syn_type)) repr,
    Forall (λ '(_, st), P st) variant_list →
    P (UnionSynType un variant_list repr)) →
  P CharSynType →
  ∀ s : syn_type, P s.
Proof.
  intros Hint Hbool Hptr Hfptr Hstruct Hunit Harray Huc Huntyped Henum Hunion Hchar.
  refine (fix F (s : syn_type) : P s := _).
  destruct s.
  - apply Hint.
  - apply Hbool.
  - apply Hptr.
  - apply Hfptr.
  - apply Hstruct.
    induction field_list as [ | [f st] H IH]; first done.
    econstructor; first apply F. apply IH.
  - apply Hunit.
  - apply Harray. apply F.
  - apply Huc. apply F.
  - apply Huntyped.
  - apply Henum.
    induction variant_list as [ | [f st] H IH]; first done.
    econstructor; first apply F. apply IH.
  - apply Hunion.
    induction variant_list as [ | [f st] H IH]; first done.
    econstructor; first apply F. apply IH.
  - apply Hchar.
Qed.

Record struct_layout_spec : Set := mk_sls
  { sls_name : string; sls_fields : list (string * syn_type); sls_repr : struct_repr }.
Global Instance struct_layout_spec_eq_dec : EqDecision struct_layout_spec.
Proof. solve_decision. Defined.

Definition syn_type_of_sls (sls : struct_layout_spec) : syn_type :=
  StructSynType sls.(sls_name) sls.(sls_fields) sls.(sls_repr).
Coercion syn_type_of_sls : struct_layout_spec >-> syn_type.

Record union_layout_spec : Set := mk_uls
  { uls_name : string; uls_variants : list (string * syn_type); uls_repr : union_repr }.
Global Instance union_layout_spec_eq_dec : EqDecision union_layout_spec.
Proof. solve_decision. Defined.

Definition syn_type_of_uls (uls : union_layout_spec) : syn_type :=
  UnionSynType uls.(uls_name) uls.(uls_variants) uls.(uls_repr).
Coercion syn_type_of_uls : union_layout_spec >-> syn_type.

Record enum_layout_spec : Set := mk_els
  { els_name : string;
    (* This is fixed (and not something chooseable by the layout algorithm), because Rust's MIR already has this type fixed. *)
    els_tag_it : IntType;
    els_variants : list (string * syn_type);
    els_repr : enum_repr;
    (* This is additional information that doesn't affect the layout algorithm, but just the operational behavior of enum operations *)
    els_tag_int : list (var_name * Z);
    (* The variant list should have no duplicates *)
    els_variants_nodup :
      NoDup (fmap fst els_variants);
    (* The variant lists should agree *)
    els_tag_int_agree :
      fmap fst els_tag_int = fmap fst els_variants;
    (* the tags should have no duplicates *)
    els_tag_int_nodup:
      NoDup (fmap snd els_tag_int);
    (* the tags should be in range of the integer type for the tags *)
    els_tag_int_wf3 :
      Forall (λ '(_, tag), int_elem_of_it' tag (els_tag_it : int_type)) els_tag_int;
  }.

Definition syn_type_of_els (els : enum_layout_spec) : syn_type :=
  EnumSynType els.(els_name) els.(els_tag_it) els.(els_variants) els.(els_repr).
Coercion syn_type_of_els : enum_layout_spec >-> syn_type.

(** We currently represent enums by a struct containing the discriminant as well as a union of structs for the data.
  NOTE: This is not an accurate model, and fails to account for the following things:
   - if the enum is annotated with a repr(C), the exact padding
   - niche optimizations
*)
Definition enum_sls union_name variants (tag_it : int_type) urepr srepr : struct_layout_spec :=
  mk_sls union_name [("discriminant", IntSynType tag_it); ("data", UnionSynType union_name variants urepr)] srepr.

Definition struct_repr_of_enum_repr (r : enum_repr) : struct_repr :=
  match r with
  | EnumReprC => StructReprC
  | EnumReprRust => StructReprRust
  | EnumReprTransparent => StructReprTransparent
  end.
Definition union_repr_of_enum_repr (r : enum_repr) : union_repr :=
  UnionReprC.
Definition sls_of_els (els : enum_layout_spec) : struct_layout_spec :=
  (enum_sls els.(els_name) els.(els_variants) els.(els_tag_it) (union_repr_of_enum_repr els.(els_repr)) (struct_repr_of_enum_repr els.(els_repr))).
Definition uls_of_els (els : enum_layout_spec) : union_layout_spec :=
  (mk_uls els.(els_name) els.(els_variants) (union_repr_of_enum_repr els.(els_repr))).
Definition els_lookup_tag (els : enum_layout_spec) (f : string) : Z :=
  let discriminant_map : gmap _ _ := list_to_map (els.(els_tag_int)) in
  default 0%Z (discriminant_map !! f).

(* TODO: generalize to permutations + subset? (it should work even when we ignore some named fields, I think, and reordering is allowed) *)
Definition sl_has_members (sl : struct_layout) (fields : list (var_name * layout)) :=
  fields = named_fields (sl.(sl_members)).

(* TODO: union layouts should be allowed to have trailing padding -- this is not accomodated by caesium currently.
    Can we simulate that by adding a "__padding" variant?
*)
Definition ul_has_variants (ul : union_layout) (variants : list (var_name * layout)) :=
  variants = ul.(ul_members).


(** A layout algorithm takes a syn_type and produces a layout for it, if possible.
  The string arguments models that the algorithm may produce different layouts even for the same syn_type, in some case (e.g. structs).
 *)
Class LayoutAlg : Type := {
  (* Note that we assume that fields have already been layouted: this encodes a kind of coherence requirement on the fields, i.e. that the algorithm really first layouts the fields according to their layout rules. *)
  struct_layout_alg : string → list (string * layout) → struct_repr → option struct_layout;
  union_layout_alg : string → list (string * layout) → union_repr → option union_layout;
  (* the named (= non-padding) fields should be exactly the input fields *)
  struct_layout_alg_has_fields sn fields repr sl :
    struct_layout_alg sn fields repr = Some sl →
    sl_has_members sl fields;
  (* the total size should be divisible by the alignment *)
  struct_layout_alg_wf sn fields repr sl :
    struct_layout_alg sn fields repr = Some sl →
    layout_wf sl;
  (* the padding fields should pose no alignment requirements *)
  struct_layout_alg_pad_align sn fields repr sl :
    struct_layout_alg sn fields repr = Some sl →
    Forall (λ '(named, ly), if named is None then ly_align_log ly = 0%nat else True) (sl_members sl);
  (* TODO: add requirements on repr *)

  (* the variants should be exactly as given *)
  union_layout_alg_has_variants un variants repr ul :
    union_layout_alg un variants repr = Some ul →
    ul_has_variants ul variants;
  (* the total size should be divisible by the alignment *)
  union_layout_alg_wf un variants repr ul :
    union_layout_alg un variants repr = Some ul →
    layout_wf ul;
  (* TODO: add requirements on repr *)
}.
Global Program Instance LayoutAlg_inhabited : Inhabited LayoutAlg :=
  {| inhabitant := {| struct_layout_alg := λ _ _ _, None; union_layout_alg := λ _ _ _, None |} |}.
Solve Obligations with done.

(** We fix a specific layout for the unit type, since Rust gives layout guarantees for it. *)
Program Definition unit_sl : struct_layout := {|
  sl_members := [];
|}.
Solve Obligations with done.
(** A union layout that would be a valid layout for the never type (although Rust does not specify that it is the only possible one). *)
Program Definition neverlike_ul : union_layout := {|
  ul_members := [];
|}.
Solve Obligations with done.

(** The alignment has to fit in [usize].
   More restrictively, in order to make [NonNull::dangling] work, the alignment also needs to be a valid address. *)
Definition ly_align_in_bounds (ly : layout) :=
  min_alloc_start ≤ ly_align ly ≤ max_alloc_end.
Lemma ly_align_in_bounds_1 ly :
  ly_align_log ly = 0%nat → ly_align_in_bounds ly.
Proof.
  rewrite /ly_align_in_bounds/ly_align => ->.
  unfold_common_caesium_defs. simpl. nia.
Qed.

Lemma ly_align_log_in_u8 ly :
  ly_align_in_bounds ly → int_elem_of_it' (Z.of_nat (ly_align_log ly)) u8.
Proof.
  rewrite /ly_align_in_bounds/min_alloc_start/max_alloc_end/=/ly_align/bytes_per_addr/bytes_per_addr_log/=.
  rewrite /bits_per_byte/=.
  intros [Ha Hb].
  split. { unsafe_unfold_common_caesium_defs. simpl in *. lia. }
  assert ((2 ^ ly_align_log ly) ≤ 2 ^ (8%nat * 8))%nat as Hle.
  { apply Nat2Z.inj_le. etrans; first apply Hb.
    rewrite Nat2Z.inj_pow. nia.
  }
  apply PeanoNat.Nat.pow_le_mono_r_iff in Hle; last lia.
  unsafe_unfold_common_caesium_defs. simpl in *. lia.
Qed.
Lemma ly_align_log_in_usize ly :
  ly_align_in_bounds ly → int_elem_of_it' (Z.of_nat (ly_align_log ly)) usize_t.
Proof.
  intros [_ Ha]%ly_align_log_in_u8.
  split. { unsafe_unfold_common_caesium_defs. simpl in *. lia. }
  unsafe_unfold_common_caesium_defs. simpl in *. lia.
Qed.
Lemma ly_align_in_usize ly :
  ly_align_in_bounds ly → int_elem_of_it' (Z.of_nat (ly_align ly)) usize_t.
Proof.
  intros [Ha Hb].
  split; unsafe_unfold_common_caesium_defs; simpl in *; lia.
Qed.

Lemma ly_align_in_bounds_mono ly1 ly2 :
  (ly_align_log ly2 ≤ ly_align_log ly1)%nat →
  ly_align_in_bounds ly1 →
  ly_align_in_bounds ly2.
Proof.
  rewrite /ly_align_in_bounds.
  intros Hle. rewrite /ly_align/min_alloc_start. intros Ha.
  split.
  - specialize (Nat_pow_ge_1 (ly_align_log ly2)). lia.
  - etrans; last apply Ha.
    apply inj_le. apply Nat.pow_le_mono_r; last lia. done.
Qed.

(** Use a layout algorithm recursively on a layout spec. *)
(* NOTE on size limits from https://doc.rust-lang.org/stable/reference/types/numeric.html#machine-dependent-integer-types:
    "The isize type is a signed integer type with the same number of bits as the platform's pointer type. The theoretical upper bound on object and array size is the maximum isize value. This ensures that isize can be used to calculate differences between pointers into an object or array and can address every byte within an object along with one byte past the end." *)
Fixpoint use_layout_alg `{!LayoutAlg} (synty : syn_type) : option layout :=
  match synty with
  | IntSynType it =>
      (* make sure that we respect limits on object size *)
      if decide (ly_size (it_layout it) ≤ MaxInt isize_t) then
        Some (it_layout it)
      else None
  | BoolSynType => Some (it_layout u8)
  | CharSynType => Some (char_layout)
  | PtrSynType => Some void*
  | FnPtrSynType => Some void*
  | StructSynType sn fields repr =>
      field_lys ← list_map_option (λ '(field_name, field_spec),
        ly ← use_layout_alg field_spec;
        Some (field_name, ly)) fields;
      sl ← struct_layout_alg sn field_lys repr;
      Some (layout_of sl)
  | UnitSynType => Some (layout_of unit_sl)
  | ArraySynType st len =>
      ly ← use_layout_alg st;
      (* check that this is within the size limits *)
      if decide (ly_size (mk_array_layout ly len) ≤ MaxInt isize_t) then
        Some (mk_array_layout ly len)
      else None
  | UnsafeCell st => use_layout_alg st
  | UnionSynType un variants repr =>
      variant_lys ← list_map_option (λ '(variant_name, variant_spec),
        ly ← use_layout_alg variant_spec;
        Some (variant_name, ly)) variants;
      ul ← union_layout_alg un variant_lys repr;
      Some (ul_layout ul)
  | EnumSynType en tag variants repr =>
      (* NOTE: this interface currently relies on union layouting not changing the order of variants to correctly map it to the tags. *)
      variant_lys ← list_map_option (λ '(variant_name, variant_spec),
        ly ← use_layout_alg variant_spec;
        Some (variant_name, ly)) variants;
      ul ← union_layout_alg en variant_lys (union_repr_of_enum_repr repr);
      sl ← struct_layout_alg en [("discriminant", it_layout tag); ("data", ul_layout ul)] (struct_repr_of_enum_repr repr);
      Some (layout_of sl)
  | UntypedSynType ly =>
      if decide (layout_wf ly ∧ ly_size ly ≤ MaxInt isize_t ∧ ly_align_in_bounds ly) then Some ly else None
  end.
Arguments use_layout_alg : simpl never.

(** Under our current layout environment, [ly] is a valid layout for [synty]. *)
Definition syn_type_has_layout `{!LayoutAlg} (synty : syn_type) (ly : layout) : Prop :=
  use_layout_alg synty = Some ly.
Lemma syn_type_has_layout_inj `{!LayoutAlg} synty ly1 ly2 :
  syn_type_has_layout synty ly1 → syn_type_has_layout synty ly2 → ly1 = ly2.
Proof. rewrite /syn_type_has_layout => ??. simplify_option_eq => //. Qed.



(** Use a layout algorithm on a struct_layout_spec *)
Definition use_struct_layout_alg `{!LayoutAlg} (sl_spec : struct_layout_spec) : option struct_layout :=
  field_lys ← list_map_option (λ '(field_name, field_spec),
    ly ← use_layout_alg field_spec;
    Some (field_name, ly)) sl_spec.(sls_fields);
  struct_layout_alg sl_spec.(sls_name) field_lys (sl_spec.(sls_repr)).
Arguments use_struct_layout_alg : simpl never.

Lemma use_struct_layout_alg_Some_inv `{!LayoutAlg} (sls : struct_layout_spec) sl :
  use_struct_layout_alg sls = Some sl →
  use_layout_alg sls = Some (layout_of sl).
Proof.
  intros Hly.
  unfold use_struct_layout_alg in Hly. simplify_option_eq.
  unfold use_layout_alg. simpl. fold use_layout_alg.
  simplify_option_eq; eauto.
Qed.
Lemma use_layout_alg_struct_Some_inv `{!LayoutAlg} (sls : struct_layout_spec) ly :
  use_layout_alg sls = Some ly →
  ∃ sl, use_struct_layout_alg sls = Some sl ∧ ly = layout_of sl.
Proof.
  intros Hly.
  unfold use_layout_alg in Hly. simpl in Hly. fold use_layout_alg in Hly. simplify_option_eq.
  eexists _. unfold use_struct_layout_alg. simplify_option_eq; eauto.
Qed.

Lemma use_struct_layout_alg_Some `{!LayoutAlg} sls sl fields' :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ use_layout_alg fst = Some fly) sls.(sls_fields) fields' →
  struct_layout_alg sls.(sls_name) fields' sls.(sls_repr) = Some sl →
  use_struct_layout_alg sls = Some sl.
Proof.
  intros Ha Hb. rewrite /use_struct_layout_alg.
  apply bind_Some. exists fields'.
  split; last done.
  clear Hb. move: Ha. generalize (sls_fields sls) as fields. clear sls.
  induction fields as [ | [name st] fields IH] in fields' |-*; simpl.
  - by intros []%Forall2_nil_inv_l.
  - intros ([name' ly] & fields'' & [<- Hst] & Ha & ->)%Forall2_cons_inv_l.
    erewrite IH; last done. simpl. rewrite Hst//.
Qed.

Local Arguments use_layout_alg : simpl nomatch.
Lemma use_struct_layout_alg_inv `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  ∃ (field_lys : list (string * layout)),
    struct_layout_alg sls.(sls_name) field_lys sls.(sls_repr) = Some sl ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) sls.(sls_fields) field_lys.
Proof.
  intros (field_lys & Hfields%list_map_option_alt & Halg)%bind_Some.
  exists field_lys. split_and!; [done.. | ].
  eapply Forall2_impl; first done.
  intros [] []. intros (fly & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma syn_type_has_layout_struct_inv `{!LayoutAlg} name fields repr ly :
  syn_type_has_layout (StructSynType name fields repr) ly →
  ∃ (field_lys : list (string * layout)) (sl : struct_layout),
    ly = layout_of sl ∧
    struct_layout_alg name field_lys repr = Some sl ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) fields field_lys.
Proof.
  set (sls := mk_sls name fields repr).
  intros Ha. apply (use_layout_alg_struct_Some_inv sls) in Ha as (sl & Ha & ?).
  apply use_struct_layout_alg_inv in Ha as (? & ? & ?).
  naive_solver.
Qed.
Lemma syn_type_has_layout_struct `{!LayoutAlg} name fields fields' repr ly :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) fields fields' →
  struct_layout_alg name fields' repr = Some ly →
  syn_type_has_layout (StructSynType name fields repr) ly.
Proof.
  intros Ha Hb. rewrite /syn_type_has_layout /use_layout_alg /=;
  fold use_layout_alg.
  rewrite bind_Some. exists fields'.
  split.
  { rewrite list_map_option_alt.
    eapply Forall2_impl; first apply Ha. intros [] [] [-> ->] => //. }
  rewrite Hb. done.
Qed.

(** Union *)
Definition use_union_layout_alg `{!LayoutAlg} (uls : union_layout_spec) : option union_layout :=
  variant_lys ← list_map_option (λ '(variant_name, variant_spec),
    ly ← use_layout_alg variant_spec;
    Some (variant_name, ly)) uls.(uls_variants);
  union_layout_alg uls.(uls_name) variant_lys uls.(uls_repr).
Arguments use_union_layout_alg : simpl never.

Lemma use_union_layout_alg_Some_inv `{!LayoutAlg} (uls : union_layout_spec) ul :
  use_union_layout_alg uls = Some ul →
  use_layout_alg uls = Some (ul_layout ul).
Proof.
  intros Hly.
  unfold use_union_layout_alg in Hly. simplify_option_eq.
  unfold use_layout_alg. simpl. fold use_layout_alg.
  simplify_option_eq; eauto.
Qed.
Lemma use_layout_alg_union_Some_inv `{!LayoutAlg} (uls : union_layout_spec) ly :
  use_layout_alg uls = Some ly →
  ∃ ul, use_union_layout_alg uls = Some ul ∧ ly = ul_layout ul.
Proof.
  intros Hly.
  unfold use_layout_alg in Hly. simpl in Hly. fold use_layout_alg in Hly. simplify_option_eq.
  eexists _. unfold use_union_layout_alg. simplify_option_eq; eauto.
Qed.
Lemma use_union_layout_alg_Some `{!LayoutAlg} uls ul variants' :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ use_layout_alg fst = Some fly) uls.(uls_variants) variants' →
  union_layout_alg uls.(uls_name) variants' uls.(uls_repr) = Some ul →
  use_union_layout_alg uls = Some ul.
Proof.
  intros Ha Hb. rewrite /use_union_layout_alg.
  apply bind_Some. exists variants'.
  split; last done.
  clear Hb. move: Ha. generalize (uls_variants uls) as variants. clear uls.
  induction variants as [ | [name st] variants IH] in variants' |-*; simpl.
  - by intros []%Forall2_nil_inv_l.
  - intros ([name' ly] & variants'' & [<- Hst] & Ha & ->)%Forall2_cons_inv_l.
    erewrite IH; last done. simpl. rewrite Hst//.
Qed.
Lemma syn_type_has_layout_union `{!LayoutAlg} name variants variants' repr ly :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) variants variants' →
  union_layout_alg name variants' repr = Some ly →
  syn_type_has_layout (UnionSynType name variants repr) ly.
Proof.
  intros Ha Hb. rewrite /syn_type_has_layout /use_layout_alg /=;
  fold use_layout_alg.
  rewrite bind_Some. exists variants'.
  split.
  { rewrite list_map_option_alt.
    eapply Forall2_impl; first apply Ha. intros [] [] [-> ->] => //. }
  rewrite Hb. done.
Qed.
Lemma use_union_layout_alg_inv `{!LayoutAlg} uls ul :
  use_union_layout_alg uls = Some ul →
  ∃ (variant_lys : list (string * layout)),
    union_layout_alg uls.(uls_name) variant_lys uls.(uls_repr) = Some ul ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) uls.(uls_variants) variant_lys.
Proof.
  intros (variant_lys & Hvars%list_map_option_alt & Halg)%bind_Some.
  exists variant_lys. split_and!; [done.. | ].
  eapply Forall2_impl; first done.
  intros [] []. intros (fly & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma syn_type_has_layout_union_inv `{!LayoutAlg} name variants repr ly :
  syn_type_has_layout (UnionSynType name variants repr) ly →
  ∃ (variant_lys : list (string * layout)) (ul : union_layout),
  ly = ul_layout ul ∧
    union_layout_alg name variant_lys repr = Some ul ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) variants variant_lys.
Proof.
  set (uls := mk_uls name variants repr).
  intros Ha. apply (use_layout_alg_union_Some_inv uls) in Ha as (ul & Ha & ?).
  apply use_union_layout_alg_inv in Ha as (? & ? & ?).
  naive_solver.
Qed.

(** Enum *)
Definition use_enum_layout_alg `{!LayoutAlg} (els : enum_layout_spec) : option struct_layout :=
  use_struct_layout_alg (sls_of_els els).

Lemma els_tag_it_size (els : enum_layout_spec) :
  ly_size (it_layout $ els_tag_it els) ≤ MaxInt isize_t.
Proof.
  specialize (IntType_size_le els.(els_tag_it)).
  rewrite MaxInt_eq /max_int /isize_t /int_half_modulus/intptr_t/bits_per_int/bytes_per_int/bits_per_byte/=. lia.
Qed.

Lemma use_enum_layout_alg_Some_inv `{!LayoutAlg} (els : enum_layout_spec) el :
  use_enum_layout_alg els = Some el →
  use_layout_alg els = Some (layout_of el).
Proof.
  intros Hly.
  unfold use_enum_layout_alg in Hly.
  apply use_struct_layout_alg_Some_inv in Hly.
  unfold use_layout_alg. simpl. fold use_layout_alg.
  unfold use_layout_alg in Hly. simpl in Hly. fold use_layout_alg in Hly.
  rewrite -Hly. simplify_option_eq; eauto.
Qed.
Lemma use_layout_alg_enum_Some_inv `{!LayoutAlg} (els : enum_layout_spec) ly :
  use_layout_alg els = Some ly →
  ∃ el, use_enum_layout_alg els = Some el ∧ ly = layout_of el.
Proof.
  intros Hly.
  unfold use_layout_alg in Hly. simpl in Hly. fold use_layout_alg in Hly.
  apply bind_Some in Hly as (vars & Hvars & Hul).
  apply bind_Some in Hul as (ul & Hul & Hsl).
  apply bind_Some in Hsl as (sl & Hsl & [= <-]).
  eexists _. unfold use_enum_layout_alg, enum_sls, use_struct_layout_alg. simpl.
  unfold use_layout_alg; simpl; fold use_layout_alg.
  rewrite Hvars /= Hul /=.
  rewrite decide_True; last apply els_tag_it_size.
  simpl. rewrite Hsl //.
Qed.
Lemma use_enum_layout_alg_Some `{!LayoutAlg} els el ul variants' :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ use_layout_alg fst = Some fly) els.(els_variants) variants' →
  union_layout_alg els.(els_name) variants' (union_repr_of_enum_repr els.(els_repr)) = Some ul →
  struct_layout_alg els.(els_name) [("discriminant", it_layout els.(els_tag_it)); ("data", ul_layout ul)] (struct_repr_of_enum_repr els.(els_repr)) = Some el →
  use_enum_layout_alg els = Some el.
Proof.
  intros Ha Hb Hc. rewrite /use_enum_layout_alg.
  eapply use_struct_layout_alg_Some; last done.
  econstructor.
  { split; first done. rewrite /use_layout_alg. rewrite decide_True; first done.
    apply els_tag_it_size. }
  econstructor; last done.
  split; first done.
  eapply syn_type_has_layout_union; last done.
  done.
Qed.

Lemma syn_type_has_layout_array `{!LayoutAlg} st (len : nat) ly ly' :
  ly' = (mk_array_layout ly len) →
  syn_type_has_layout st ly →
  (ly_size ly * len) ≤ MaxInt isize_t →
  syn_type_has_layout (ArraySynType st len) ly'.
Proof.
  rewrite /syn_type_has_layout. intros -> Hst Hsize.
  unfold use_layout_alg. fold use_layout_alg.
  rewrite Hst //. simpl. rewrite decide_True; first done.
  rewrite /ly_size /=. lia.
Qed.

Lemma syn_type_has_layout_array_inv `{!LayoutAlg} st len ly :
  syn_type_has_layout (ArraySynType st len) ly →
  ∃ ly', syn_type_has_layout st ly' ∧ ly = mk_array_layout ly' len ∧ ly_size ly ≤ MaxInt isize_t.
Proof.
  rewrite /syn_type_has_layout {1}/use_layout_alg.
  fold use_layout_alg.
  destruct (use_layout_alg st) as [ ly' | ]; last done.
  simpl. case_decide; last done.
  intros [= <-]. eauto.
Qed.

Lemma syn_type_has_layout_untyped_inv `{!LayoutAlg} ly ly' :
  use_layout_alg (UntypedSynType ly) = Some ly' →
  ly' = ly ∧ layout_wf ly ∧ (ly_size ly ≤ MaxInt isize_t)%Z ∧ ly_align_in_bounds ly.
Proof.
  rewrite /use_layout_alg /=.
  case_decide; last done.
  intros [= <-]. naive_solver.
Qed.
Lemma syn_type_has_layout_untyped `{!LayoutAlg} ly ly' :
  ly = ly' →
  layout_wf ly →
  (ly_size ly ≤ MaxInt isize_t)%Z →
  ly_align_in_bounds ly →
  use_layout_alg (UntypedSynType ly) = Some ly'.
Proof.
  intros -> ???. rewrite /use_layout_alg decide_True; done.
Qed.

Lemma syn_type_has_layout_int `{!LayoutAlg} (it : int_type) (ly : layout) :
  ly = it_layout it →
  ly_size (it_layout it) ≤ MaxInt isize_t →
  syn_type_has_layout (IntSynType it) ly.
Proof.
  intros; subst. rewrite /syn_type_has_layout /use_layout_alg decide_True; done.
Qed.
Lemma syn_type_has_layout_int_inv `{!LayoutAlg} (it : int_type) (ly : layout) :
  syn_type_has_layout (IntSynType it) ly →
  ly = it_layout it ∧ ly_size (it_layout it) ≤ MaxInt isize_t.
Proof.
  rewrite /syn_type_has_layout /use_layout_alg.
  case_decide; naive_solver.
Qed.

Lemma syn_type_has_layout_bool_inv `{!LayoutAlg} ly :
  syn_type_has_layout BoolSynType ly → ly = it_layout u8.
Proof.
  rewrite /syn_type_has_layout /use_layout_alg => [= <-] //.
Qed.
Lemma syn_type_has_layout_bool `{!LayoutAlg} ly :
  ly = it_layout u8 → syn_type_has_layout BoolSynType ly.
Proof. intros -> => //. Qed.

Lemma syn_type_has_layout_char_inv `{!LayoutAlg} ly :
  syn_type_has_layout CharSynType ly → ly = char_layout.
Proof.
  rewrite /syn_type_has_layout /use_layout_alg => [= <-] //.
Qed.
Lemma syn_type_has_layout_char `{!LayoutAlg} ly :
  ly = char_layout → syn_type_has_layout CharSynType ly.
Proof. intros -> => //. Qed.

Lemma syn_type_has_layout_ptr_inv `{!LayoutAlg} ly :
  syn_type_has_layout PtrSynType ly → ly = void*.
Proof. rewrite /syn_type_has_layout /use_layout_alg => [= <-] //. Qed.
Lemma syn_type_has_layout_ptr `{!LayoutAlg} ly :
  ly = void* → syn_type_has_layout PtrSynType ly.
Proof. intros -> => //. Qed.

Lemma syn_type_has_layout_fnptr_inv `{!LayoutAlg} ly :
  syn_type_has_layout FnPtrSynType ly → ly = void*.
Proof. rewrite /syn_type_has_layout /use_layout_alg => [= <-] //. Qed.
Lemma syn_type_has_layout_fnptr `{!LayoutAlg} ly :
  ly = void* → syn_type_has_layout FnPtrSynType ly.
Proof. intros -> => //. Qed.

Lemma syn_type_has_layout_unit_inv `{!LayoutAlg} ly :
  syn_type_has_layout UnitSynType ly → ly = unit_sl.
Proof. rewrite /syn_type_has_layout /use_layout_alg => [= <-] //. Qed.
Lemma syn_type_has_layout_unit `{!LayoutAlg} ly :
  ly = unit_sl → syn_type_has_layout UnitSynType ly.
Proof. intros -> => //. Qed.

Lemma syn_type_has_layout_unsafecell_inv `{!LayoutAlg} st ly :
  syn_type_has_layout (UnsafeCell st) ly → syn_type_has_layout st ly.
Proof. done. Qed.
Lemma syn_type_has_layout_unsafecell `{!LayoutAlg} st ly :
  syn_type_has_layout st ly → syn_type_has_layout (UnsafeCell st) ly.
Proof. done. Qed.

(* More on structs *)
Definition struct_layout_spec_has_layout `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) : Prop :=
  use_struct_layout_alg sls = Some sl.
Lemma struct_layout_spec_has_layout_inj `{!LayoutAlg} sls sl1 sl2 :
  struct_layout_spec_has_layout sls sl1 → struct_layout_spec_has_layout sls sl2 → sl1 = sl2.
Proof. rewrite /struct_layout_spec_has_layout => ??. simplify_option_eq => //. Qed.


Lemma struct_layout_spec_has_layout_lookup `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) (x : var_name) (st : syn_type) i :
  struct_layout_spec_has_layout sls sl →
  sls.(sls_fields) !! i = Some (x, st) →
  field_index_of sl.(sl_members) x = Some i.
Proof.
  rewrite /struct_layout_spec_has_layout /use_struct_layout_alg. intros Halg.
  apply bind_Some in Halg as (fields & Heq1 & Heq2).
  apply struct_layout_alg_has_fields in Heq2. rewrite /sl_has_members in Heq2.
  intros Hlook. eapply list_map_option_lookup in Heq1; last apply Hlook.
  destruct Heq1 as ([n ly] & Heq1 & Heq3).
  symmetry in Heq3. apply bind_Some in Heq3 as (ly' & ? & [= -> ->]).
  rewrite Heq2 in Heq1.
  eapply named_fields_lookup_field_index_of; last done.
  specialize (sl_nodup sl). apply bool_decide_unpack.
Qed.

Lemma struct_layout_spec_has_layout_alt_1 `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  ∃ fields, Forall2 (λ '(name, st) '(name2, ly), use_layout_alg st = Some ly ∧ name2 = name) sls.(sls_fields) fields ∧
    struct_layout_alg sls.(sls_name) fields sls.(sls_repr) = Some sl.
Proof.
  rewrite /struct_layout_spec_has_layout /use_struct_layout_alg.
  intros (fields & Ha1 & Ha2)%bind_Some.
  eapply list_map_option_alt in Ha1.
  exists fields. split; last done.
  eapply Forall2_impl; first done.
  intros [name st] [name2 ly].
  intros (ly' & ? & [= <- <-])%bind_Some. done.
Qed.
Lemma struct_layout_spec_has_layout_alt_2 `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  Forall2 (λ '(name, st) '(name2, ly), use_layout_alg st = Some ly ∧ name2 = name) sls.(sls_fields) (named_fields sl.(sl_members)).
Proof.
  intros (fields & Hf & Halg%struct_layout_alg_has_fields)%struct_layout_spec_has_layout_alt_1.
  rewrite -Halg. done.
Qed.
Lemma struct_layout_spec_has_layout_fields_length' `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  length (sls.(sls_fields)) = length (named_fields sl.(sl_members)).
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2. by eapply Forall2_length.
Qed.
Lemma struct_layout_spec_has_layout_fields_length `{!LayoutAlg} sls sl :
  struct_layout_spec_has_layout sls sl →
  length (field_names (sl_members sl)) = length (sls_fields sls).
Proof.
  rewrite -named_fields_field_names_length.
  intros ?. erewrite struct_layout_spec_has_layout_fields_length'; done.
Qed.

Lemma struct_layout_spec_has_layout_members_lookup_1 `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) :
  struct_layout_spec_has_layout sls sl →
  ∀ x st i,
  sls.(sls_fields) !! i = Some (x, st) →
  ∃ ly j, sl.(sl_members) !! j = Some (Some x, ly) ∧ syn_type_has_layout st ly.
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2 ???.
  intros Hlook.
  eapply Forall2_lookup_l in Ha; last done.
  destruct Ha as ([name ly] & Hlook2 & [Halg ->]).
  eapply named_fields_lookup_1 in Hlook2 as (j & Hlook2).
  exists ly, j. done.
Qed.
Lemma struct_layout_spec_has_layout_members_lookup_2 `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout)  :
  struct_layout_spec_has_layout sls sl →
  ∀ i ly x,
  sl.(sl_members) !! i = Some (Some x, ly) →
  ∃ st j, sls.(sls_fields) !! j = Some (x, st) ∧ syn_type_has_layout st ly.
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2 ???.
  intros (j & Hlook)%named_fields_lookup_2.
  eapply Forall2_lookup_r in Ha; last done.
  destruct Ha as ([name st] & Hlook2 & [Halg ->]).
  eauto.
Qed.

Lemma struct_layout_spec_has_layout_members `{!LayoutAlg} (sls : struct_layout_spec) (sl : struct_layout) (x : var_name) (st : syn_type) :
  struct_layout_spec_has_layout sls sl →
  (x, st) ∈ sls.(sls_fields) →
  ∃ ly, (Some x, ly) ∈ sl.(sl_members) ∧ syn_type_has_layout st ly.
Proof.
  intros Ha%struct_layout_spec_has_layout_alt_2.
  intros (i & Hlook)%elem_of_list_lookup_1.
  eapply Forall2_lookup_l in Ha; last done.
  destruct Ha as ([name ly] & Hlook2 & [Halg ->]).
  exists ly. split; last done.
  eapply elem_of_named_fields.
  by eapply elem_of_list_lookup_2.
Qed.


(** [field_index_of]: version for struct_layout_spec *)
Fixpoint sls_field_index_of (fields : list (string * syn_type)) (x : string) : option nat :=
  match fields with
  | [] => None
  | (n', _) :: s =>
      if bool_decide (n' = x) then Some 0%nat
      else S <$> sls_field_index_of s x
  end.

Lemma sls_field_index_of_fmap fields x (f : nat → nat) i :
  f <$> (sls_field_index_of fields x) = Some i →
  ∃ j, sls_field_index_of fields x = Some j ∧ i = f j.
Proof.
  induction fields as [ | [y ly] fields IH] in i, f |-*; simpl; first done.
  case_bool_decide as Ha; subst.
  - intros [= <-]. eauto.
  - rewrite -option_fmap_compose. intros (j & Hlook & ->)%IH.
    rewrite Hlook. eauto.
Qed.
Lemma sls_field_index_of_lookup fields f i :
  sls_field_index_of fields f = Some i →
  ∃ ly, fields !! i = Some (f, ly).
Proof.
  induction fields as [ | [f0 ly] fields IH] in i |-*; simpl; first done.
  case_bool_decide as Ha; subst.
  - intros [= <-]. eauto.
  - intros (j & Hlook & ->)%sls_field_index_of_fmap. eauto.
Qed.

(** More on unions *)
Definition union_layout_spec_has_layout `{!LayoutAlg} (uls : union_layout_spec) (ul : union_layout) : Prop :=
  use_union_layout_alg uls = Some ul.
Lemma union_layout_spec_has_layout_inj `{!LayoutAlg} uls ul1 ul2 :
  union_layout_spec_has_layout uls ul1 → union_layout_spec_has_layout uls ul2 → ul1 = ul2.
Proof. rewrite /union_layout_spec_has_layout => ??. simplify_option_eq => //. Qed.


(** More on enums *)
Definition enum_layout_spec_has_layout `{!LayoutAlg} (els : enum_layout_spec) (el : struct_layout) : Prop :=
  use_enum_layout_alg els = Some el.
Lemma enum_layout_spec_has_layout_inj `{!LayoutAlg} els el1 el2 :
  enum_layout_spec_has_layout els el1 → enum_layout_spec_has_layout els el2 → el1 = el2.
Proof. rewrite /enum_layout_spec_has_layout => ??. simplify_option_eq => //. Qed.

Lemma use_enum_layout_alg_inv' `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  use_struct_layout_alg (sls_of_els els) = Some el.
Proof. done. Qed.
Lemma use_enum_layout_alg_inv `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  ∃ ul (variant_lys : list (string * layout)),
    union_layout_alg els.(els_name) variant_lys (union_repr_of_enum_repr els.(els_repr)) = Some ul ∧
    struct_layout_alg els.(els_name) [("discriminant", it_layout els.(els_tag_it)); ("data", ul : layout)] (struct_repr_of_enum_repr els.(els_repr)) = Some el ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) els.(els_variants) variant_lys.
Proof.
  intros Ha%use_enum_layout_alg_inv'.
  apply use_struct_layout_alg_inv in Ha as (field_ls & Halg & Hf).
  simpl in Hf.
  apply Forall2_cons_inv_l in Hf as ([? ly1] & lys & [<- Hly1] & Ha & ->).
  apply Forall2_cons_inv_l in Ha as ([? ly2] & lys' & [<- Hly2] & Ha & ->).
  apply Forall2_nil_inv_l in Ha as ->.
  apply syn_type_has_layout_union_inv in Hly2 as (variant_lys & ul & -> & Hul & Hvariants).
  apply syn_type_has_layout_int_inv in Hly1 as (-> & ?).
  exists ul, variant_lys. eauto.
Qed.
Lemma syn_type_has_layout_enum_inv `{!LayoutAlg} ly name it variants repr :
  syn_type_has_layout (EnumSynType name it variants repr) ly →
  ∃ el ul (variant_lys : list (string * layout)),
    union_layout_alg name variant_lys (union_repr_of_enum_repr repr) = Some ul ∧
    struct_layout_alg name [("discriminant", it_layout it); ("data", ul : layout)] (struct_repr_of_enum_repr repr) = Some el ∧
    ly = el ∧
    Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) variants variant_lys.
Proof.
  simpl. rewrite /syn_type_has_layout/=.
  intros (variant_lys & Hvariants & Ha)%bind_Some.
  apply list_map_option_alt in Hvariants.
  apply bind_Some in Ha as (ul & Hul & Ha).
  apply bind_Some in Ha as (sl & Hsl & [= <-]).
  exists sl, ul, variant_lys. split_and!; try done.
  eapply Forall2_impl; first done.
  intros [] [].
  intros (ly & Halg & [= -> ->])%bind_Some.
  eauto.
Qed.
Lemma syn_type_has_layout_enum `{!LayoutAlg} name (it : IntType) variants variants' repr ly ul sl :
  Forall2 (λ '(fname, fst) '(fname', fly), fname = fname' ∧ syn_type_has_layout fst fly) variants variants' →
  union_layout_alg name variants' (union_repr_of_enum_repr repr) = Some ul →
  struct_layout_alg name [("discriminant", it_layout it); ("data", ul_layout ul)] (struct_repr_of_enum_repr repr) = Some sl →
  ly = layout_of sl →
  syn_type_has_layout (EnumSynType name it variants repr) ly.
Proof.
  intros Ha Hb Hc ->.
  rewrite /syn_type_has_layout/use_layout_alg. fold use_layout_alg.
  eapply bind_Some. exists variants'.
  split. { apply list_map_option_alt. eapply Forall2_impl; first done. intros [] [] [-> ->]. done. }
  rewrite Hb/=Hc/=//.
Qed.
Lemma syn_type_has_layout_els_sls `{!LayoutAlg} (els : enum_layout_spec) (ly : layout) :
  syn_type_has_layout els ly →
  ∃ (sl : struct_layout), struct_layout_spec_has_layout (sls_of_els els) sl ∧ ly = sl.
Proof.
  intros (el & Ha & ->)%use_layout_alg_enum_Some_inv.
  exists el.
  split; last done. by apply use_enum_layout_alg_inv'.
Qed.

(** Well-formedness: the size is divisible by the alignment *)
Lemma use_struct_layout_alg_wf `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  layout_wf sl.
Proof.
  rewrite /use_struct_layout_alg => Ha.
  apply bind_Some in Ha as (lys & Ha & Halg).
  by apply struct_layout_alg_wf in Halg.
Qed.
Lemma use_union_layout_alg_wf `{!LayoutAlg} uls ul :
  use_union_layout_alg uls = Some ul →
  layout_wf ul.
Proof.
  rewrite /use_struct_layout_alg => Ha.
  apply bind_Some in Ha as (lys & Ha & Halg).
  by apply union_layout_alg_wf in Halg.
Qed.
Lemma use_enum_layout_alg_wf `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  layout_wf el.
Proof.
  apply use_struct_layout_alg_wf.
Qed.
Lemma use_layout_alg_wf `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  layout_wf ly.
Proof.
  induction st in ly |-*; rewrite /use_layout_alg => ?; simplify_option_eq; fold use_layout_alg in *.
  - apply int_type_layout_wf.
  - apply int_type_layout_wf.
  - apply ptr_layout_wf.
  - apply ptr_layout_wf.
  - by eapply struct_layout_alg_wf.
  - rewrite /layout_wf /unit_sl /layout_of /=.
    rewrite /ly_align /ly_size /=.
    apply Z.divide_0_r.
  - eapply array_layout_wf. eauto.
  - eauto.
  - naive_solver.
  - by eapply struct_layout_alg_wf.
  - by eapply union_layout_alg_wf.
  - apply char_layout_wf.
Qed.

(** Size limits: object size should be limited by isize *)
Lemma use_layout_alg_size `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  ly_size ly ≤ MaxInt isize_t.
Proof.
  induction st in ly |-*; rewrite /use_layout_alg => ?; simplify_option_eq; fold use_layout_alg in *.
  - done.
  - rewrite MaxInt_eq. done.
  - rewrite MaxInt_eq. done.
  - rewrite MaxInt_eq. done.
  - rewrite /ly_size /=.
    match goal with | H : struct_layout |- _ => specialize (sl_size H) end.
    rewrite MaxInt_eq. lia.
  - rewrite MaxInt_eq. done.
  - done.
  - naive_solver.
  - naive_solver.
  - rewrite /ly_size /=.
    match goal with | H : struct_layout |- _ => specialize (sl_size H) end.
    rewrite MaxInt_eq. lia.
  - match goal with | H : union_layout |- _ => rename H into ul end.
    specialize (ul_size ul) as Hsz.
    rewrite /ly_size /= MaxInt_eq. lia.
  - rewrite MaxInt_eq. done.
Qed.

Lemma use_struct_layout_alg_size `{!LayoutAlg} sls sl :
  use_struct_layout_alg sls = Some sl →
  ly_size sl ≤ MaxInt isize_t.
Proof.
  intros _.
  rewrite /ly_size /=.
  pose (sl_size sl) as Ha. rewrite MaxInt_eq. lia.
Qed.
Lemma use_union_layout_alg_size `{!LayoutAlg} uls ul :
  use_union_layout_alg uls = Some ul →
  ly_size ul ≤ MaxInt isize_t.
Proof.
  intros _. rewrite /ly_size /=.
  pose (ul_size ul) as Ha. rewrite MaxInt_eq. lia.
Qed.
Lemma use_enum_layout_alg_size `{!LayoutAlg} els el :
  use_enum_layout_alg els = Some el →
  ly_size el ≤ MaxInt isize_t.
Proof.
  intros _. rewrite /ly_size /=.
  pose (sl_size el) as Ha. rewrite MaxInt_eq. lia.
Qed.

(** Alignment limits *)


Lemma sl_align_eq (sl : struct_layout) :
  ly_align sl = max 1 (max_list (ly_align <$> (sl_members sl).*2)).
Proof.
  rewrite /ly_align{1}/ly_align_log/=.
  generalize (sl_members sl).*2 => lys.
  clear sl. induction lys as [ | ly lys IH]; simpl; first done.
  rewrite Nat_pow_max; last lia. rewrite IH.
  unfold fmap. lia.
Qed.
Lemma ul_align_eq (ul : union_layout) :
  ly_align ul = max 1 (max_list (ly_align <$> (ul_members ul).*2)).
Proof.
  rewrite /ly_align{1}/ly_align_log/=.
  generalize (ul_members ul).*2 => lys.
  clear ul. induction lys as [ | ly lys IH]; simpl; first done.
  rewrite Nat_pow_max; last lia. rewrite IH.
  unfold fmap. lia.
Qed.

Lemma struct_layout_alg_align_in_bounds `{!LayoutAlg} sn fields repr sl :
  Forall (λ '(_, ly), ly_align_in_bounds ly) fields →
  struct_layout_alg sn fields repr = Some sl →
  ly_align_in_bounds sl.
Proof.
  rewrite /ly_align_in_bounds.
  intros Hfields Halg.
  rewrite sl_align_eq.
  specialize (struct_layout_alg_has_fields _ _ _ _ Halg) as ->.
  specialize (struct_layout_alg_pad_align _ _ _ _ Halg) as Hpad.
  clear Halg.
  move: Hfields Hpad.
  generalize (sl_members sl) => mems. intros Halgs Hpad.
  clear sl. induction mems as [ | [n ly] mems IH'] in Halgs, Hpad |-*; simpl in *.
  { rewrite /min_alloc_start/max_alloc_end.
    rewrite /bytes_per_addr/bytes_per_addr_log/bits_per_byte. simpl. lia. }
  rewrite Nat.max_assoc. rewrite [(1 `max` _)%nat]Nat.max_comm. rewrite -Nat.max_assoc.
  destruct n as [ n | ].
  + (* named *)
    inversion Hpad; subst.
    inversion Halgs as [ | ? ? Hx Halgs']; subst.
    eapply Nat_Z_in_bounds_max. { apply Hx. }
    eapply IH'; done.
  + (* unnamed *)
    inversion Hpad; subst.
    rename select (ly_align_log ly = _) into Hly.
    eapply Nat_Z_in_bounds_max. {
      rewrite /ly_align Hly /min_alloc_start. rewrite /max_alloc_end/bytes_per_addr/bytes_per_addr_log/=/bits_per_byte. lia. }
    eapply IH'; done.
Qed.
Lemma union_layout_alg_align_in_bounds `{!LayoutAlg} sn variants repr ul :
  Forall (λ '(_, ly), ly_align_in_bounds ly) variants →
  union_layout_alg sn variants repr = Some ul →
  ly_align_in_bounds ul.
Proof.
  rewrite /ly_align_in_bounds.
  intros Hfields Halg.
  rewrite ul_align_eq.
  specialize (union_layout_alg_has_variants _ _ _ _ Halg) as ->.
  clear Halg.
  move: Hfields.
  generalize (ul_members ul) => mems. intros Halgs.
  clear ul. induction mems as [ | [n ly] mems IH'] in Halgs |-*; simpl in *.
  { rewrite /min_alloc_start/max_alloc_end.
    rewrite /bytes_per_addr/bytes_per_addr_log/bits_per_byte. simpl. lia. }
  rewrite Nat.max_assoc. rewrite [(1 `max` _)%nat]Nat.max_comm. rewrite -Nat.max_assoc.
  inversion Halgs as [ | ? ? Hx Halgs']; subst.
  eapply Nat_Z_in_bounds_max. { apply Hx. }
  eapply IH'; done.
Qed.

Lemma use_layout_alg_align `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  ly_align_in_bounds ly.
Proof.
  induction st as [ it | | | | sn fields repr IH | | st IH len | st IH | ly' | en tag_it variant_list repr IH | un variant_list repr IH | ] using syn_type_strong_ind in ly |-*; rewrite /use_layout_alg => ?; simplify_option_eq; fold use_layout_alg in *;
      rewrite /ly_align_in_bounds.
  - rewrite /ly_align/it_layout/=.
    revert select (ly_size _ ≤ _). rewrite /ly_size/=/bytes_per_int => Ha.
    split.
    + rewrite /min_alloc_start. specialize (Nat_pow_ge_1 (it_byte_size_log it)). lia.
    + etrans; first apply Ha. rewrite MaxInt_eq /max_int/=/int_half_modulus/=/bits_per_int/bytes_per_int/=.
      rewrite /max_alloc_end/bytes_per_addr/bytes_per_addr_log/=/bits_per_byte. lia.
  - done.
  - done.
  - done.
  - (* struct *)
    rename select (list_map_option _ _ = Some _) into Halgs.
    match type of Halgs with list_map_option _ _ = Some ?Ha => rename Ha into mems end.
    apply list_map_option_alt in Halgs.
    eapply struct_layout_alg_align_in_bounds; last done.
    clear -IH Halgs.
    induction mems as [ | [n ly] mems IH'] in fields, IH, Halgs |-*; simpl in *.
    { econstructor. }
    apply Forall2_cons_inv_r in Halgs as ([n' st] & fields' & Ha & Hb & ->).
    apply bind_Some in Ha as (ly' & Halg & [= -> ->]).
    inversion IH as [ | ? ? Hx IH1]; subst.
    specialize (Hx _ Halg).
    econstructor; first done. eapply IH'; done.
  - done.
  - rewrite /mk_array_layout/=/ly_mult/ly_align/=.
    apply IH. done.
  - naive_solver.
  - naive_solver.
  - (* enum *)
    rename select (list_map_option _ _ = Some _) into Halgs.
    match type of Halgs with list_map_option _ _ = Some ?Ha => rename Ha into mems end.
    apply list_map_option_alt in Halgs.
    rename select (struct_layout_alg _ _ _ = _) into Hstruct.
    rename select (union_layout_alg _ _ _ = _) into Hunion.
    eapply struct_layout_alg_align_in_bounds; last done.
    econstructor.
    { rewrite /ly_align_in_bounds.
      rewrite /min_alloc_start /max_alloc_end.
      rewrite /bytes_per_addr/bytes_per_addr_log/bits_per_byte.
      split.
      - apply IntType_align_ge_1.
      - specialize (IntType_align_le tag_it). simpl. lia.
    }
    econstructor; last econstructor.
    eapply union_layout_alg_align_in_bounds; last done.
    clear -IH Halgs.
    induction mems as [ | [n ly] mems IH'] in variant_list, IH, Halgs |-*; simpl in *.
    { econstructor. }
    apply Forall2_cons_inv_r in Halgs as ([n' st] & fields' & Ha & Hb & ->).
    apply bind_Some in Ha as (ly' & Halg & [= -> ->]).
    inversion IH as [ | ? ? Hx IH1]; subst.
    specialize (Hx _ Halg).
    econstructor; first done. eapply IH'; done.
  - (* union *)
    rename select (list_map_option _ _ = Some _) into Halgs.
    match type of Halgs with list_map_option _ _ = Some ?Ha => rename Ha into mems end.
    apply list_map_option_alt in Halgs.
    rename select (union_layout_alg _ _ _ = _) into Hunion.
    eapply union_layout_alg_align_in_bounds; last done.
    clear -IH Halgs.
    induction mems as [ | [n ly] mems IH'] in variant_list, IH, Halgs |-*; simpl in *.
    { econstructor. }
    apply Forall2_cons_inv_r in Halgs as ([n' st] & fields' & Ha & Hb & ->).
    apply bind_Some in Ha as (ly' & Halg & [= -> ->]).
    inversion IH as [ | ? ? Hx IH1]; subst.
    specialize (Hx _ Halg).
    econstructor; first done. eapply IH'; done.
  - (* char *)
    done.
Qed.

Lemma syn_type_has_layout_make_untyped `{!LayoutAlg} st ly ly' :
  ly = ly' →
  syn_type_has_layout st ly →
  syn_type_has_layout (UntypedSynType ly) ly'.
Proof.
  intros <- Hst.
  apply syn_type_has_layout_untyped.
  - done.
  - eapply use_layout_alg_wf; done.
  - eapply use_layout_alg_size; done.
  - by eapply use_layout_alg_align.
Qed.


(** Infallible versions *)
Definition use_layout_alg' `{!LayoutAlg} (st : syn_type) : layout :=
  default inhabitant (use_layout_alg st).
(*Coercion use_layout_alg' : syn_type >-> layout.*)

Lemma use_layout_alg_eq' `{!LayoutAlg} st ly :
  use_layout_alg st = Some ly →
  use_layout_alg' st = ly.
Proof.
  rewrite /use_layout_alg' => -> //.
Qed.

Global Instance struct_layout_inhabited : Inhabited struct_layout := populate unit_sl.
Definition use_struct_layout_alg' `{!LayoutAlg} (sls : struct_layout_spec) : struct_layout :=
  default inhabitant (use_struct_layout_alg sls).

Global Instance union_layout_inhabited : Inhabited union_layout := populate neverlike_ul.
Definition use_union_layout_alg' `{!LayoutAlg} (uls : union_layout_spec) : union_layout :=
  default inhabitant (use_union_layout_alg uls).

Definition use_enum_layout_alg' `{!LayoutAlg} (els : enum_layout_spec) : struct_layout :=
  default inhabitant (use_enum_layout_alg els).

(** Existential versions *)
Definition syn_type_is_layoutable `{!LayoutAlg} (st : syn_type) : Prop :=
  is_Some (use_layout_alg st).
Definition struct_layout_spec_is_layoutable `{!LayoutAlg} (sls : struct_layout_spec) : Prop :=
  is_Some (use_struct_layout_alg sls).
Definition union_layout_spec_is_layoutable `{!LayoutAlg} (uls : union_layout_spec) : Prop :=
  is_Some (use_union_layout_alg uls).
Definition enum_layout_spec_is_layoutable `{!LayoutAlg} (els : enum_layout_spec) : Prop :=
  is_Some (use_enum_layout_alg els).


(** Size of syn_types *)
Definition size_of_st `{!LayoutAlg} (st : syn_type) : nat :=
  ly_size (use_layout_alg' st).

Section size_of.
  Context `{!LayoutAlg}.

  Ltac unfold_st := rewrite /size_of_st /use_layout_alg' /use_layout_alg.

  Lemma size_of_st_ptr :
    size_of_st PtrSynType = ly_size void*.
  Proof. done. Qed.
  Lemma size_of_st_int (it : int_type) :
    (ly_size (it_layout it) ≤ MaxInt isize_t)%Z → size_of_st (IntSynType it) = ly_size (it_layout it).
  Proof.
    intros. unfold_st. rewrite decide_True; done.
  Qed.
  Lemma size_of_st_Int (it : IntType) :
    size_of_st (IntSynType it) = ly_size (it_layout it).
  Proof.
    apply size_of_st_int. rewrite MaxInt_eq. apply IntType_to_it_size_bounded.
  Qed.
  Lemma size_of_st_bool :
    size_of_st BoolSynType = 1%nat.
  Proof. done. Qed.
  Lemma size_of_st_unit :
    size_of_st UnitSynType = 0%nat.
  Proof. done. Qed.
  Lemma size_of_st_array st sz n :
    syn_type_is_layoutable (ArraySynType st n) →
    size_of_st st = sz →
    size_of_st (ArraySynType st n) = (n * sz)%nat.
  Proof.
    intros [ly Halg].
    apply syn_type_has_layout_array_inv in Halg as (ly' & Hst & -> & Hsz).
    intros <-.
    unfold_st; fold use_layout_alg.
    rewrite Hst. simpl.
    rewrite decide_True; last done.
    simpl. rewrite /mk_array_layout /ly_mult /ly_size; destruct ly'; lia.
  Qed.

  (* For struct, enum, and union, we will have to treat this opaquely, since it is the layout algorithm's choice. *)
End size_of.

(** We can compute a canonical optype for every syntype that should be used when accessing an element of this syntype in a safe read/write *)
Fixpoint use_op_alg `{!LayoutAlg} (st : syn_type) : option op_type :=
  match st with
  | IntSynType it => Some $ IntOp it
  | BoolSynType => Some BoolOp
  | CharSynType => Some CharOp
  | PtrSynType => Some PtrOp
  | FnPtrSynType => Some PtrOp
  | StructSynType name fields repr =>
    sl ← use_struct_layout_alg (mk_sls name fields repr);
    ots ← list_map_option (λ '(name, st), use_op_alg st) fields;
    Some $ StructOp sl ots
  | UnitSynType => Some $ StructOp unit_sl []
  | ArraySynType st n =>
    (* NOTE ideally, we'd have an ArrayOp -- however, reading a whole array in one go with a typed op is not something we usually do. *)
    ly ← use_layout_alg st;
    Some $ UntypedOp (mk_array_layout ly n)
  | UnsafeCell st =>
      use_op_alg st
  | UntypedSynType ly =>
      Some $ UntypedOp ly
  | EnumSynType _ _ _ _ =>
      (* TODO this does not match Rust semantics -- ops on enums in Rust enforce validity *)
      ly ← use_layout_alg st;
      Some $ UntypedOp ly
  | UnionSynType _ _ _ =>
      ly ← use_layout_alg st;
      Some $ UntypedOp ly
  end.
Definition use_op_alg' `{!LayoutAlg} (st : syn_type) : op_type :=
  default (UntypedOp unit_sl) (use_op_alg st).

Lemma use_op_alg_inj `{!LayoutAlg} st ot ot' :
  use_op_alg st = Some ot →
  use_op_alg st = Some ot' →
  ot' = ot.
Proof.
  congruence.
Qed.

Definition use_op_alg_struct_pred `{!LayoutAlg} : (string * syn_type) → op_type → Prop := (λ '(_, fst) (fop : op_type), use_op_alg fst = Some fop).
Lemma use_op_alg_struct `{!LayoutAlg} name fields sl ots ot repr :
  Forall2 use_op_alg_struct_pred (fields) ots →
  use_struct_layout_alg (mk_sls name fields repr) = Some sl →
  ot = StructOp sl ots →
  use_op_alg (StructSynType name fields repr) = Some ot.
Proof.
  intros Ha Hb ->. rewrite /use_op_alg Hb /=. fold (use_op_alg).
  apply bind_Some. exists ots.
  split; last done.
  apply list_map_option_alt.
  eapply Forall2_impl; first done.
  intros [] ?; done.
Qed.
Lemma use_op_alg_int `{!LayoutAlg} it ot:
  ot = IntOp it →
  use_op_alg (IntSynType it) = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_bool `{!LayoutAlg} ot :
  ot = BoolOp →
  use_op_alg BoolSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_char `{!LayoutAlg} ot :
  ot = CharOp →
  use_op_alg CharSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_ptr `{!LayoutAlg} ot :
  ot = PtrOp →
  use_op_alg PtrSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_fnptr `{!LayoutAlg} ot :
  ot = PtrOp →
  use_op_alg FnPtrSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_unit `{!LayoutAlg} ot :
  ot = (StructOp unit_sl []) →
  use_op_alg UnitSynType = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_unsafecell `{!LayoutAlg} st op :
  use_op_alg st = Some op →
  use_op_alg (UnsafeCell st) = Some op.
Proof. simpl. done. Qed.
Lemma use_op_alg_untyped `{!LayoutAlg} ly ot :
  ot = (UntypedOp ly) →
  use_op_alg (UntypedSynType ly) = Some ot.
Proof. intros ->. done. Qed.
Lemma use_op_alg_enum `{!LayoutAlg} name it variants ly ot repr :
  use_layout_alg (EnumSynType name it variants repr) = Some ly →
  ot = (UntypedOp ly) →
  use_op_alg (EnumSynType name it variants repr) = Some ot.
Proof.
  intros Halg ->.
  rewrite /use_op_alg Halg//.
Qed.
Lemma use_op_alg_union `{!LayoutAlg} name variants ly ot repr :
  use_layout_alg (UnionSynType name variants repr) = Some ly →
  ot = (UntypedOp ly) →
  use_op_alg (UnionSynType name variants repr) = Some ot.
Proof.
  intros Halg ->.
  rewrite /use_op_alg Halg//.
Qed.

Lemma use_op_alg_untyped_inv `{!LayoutAlg} ly ot :
  use_op_alg (UntypedSynType ly) = Some ot → ot = (UntypedOp ly).
Proof.
  rewrite /use_op_alg. intros [= <-]; done.
Qed.



(** Prevent simplification from unfolding it too eagerly. *)
Arguments use_op_alg : simpl never.


(* NOTE: does not hold currently because we are lacking some of the safety checks regarding size. *)
(*
Lemma use_op_alg_layout_alg `{!LayoutAlg} st op :
  use_op_alg st = Some op →
  use_layout_alg st = Some (ot_layout op).
Proof.
  induction st in op |-*; simpl; intros Ha; simplify_eq; try done.
 *)

Lemma use_struct_layout_alg_op_alg `{!LayoutAlg} (sls : struct_layout_spec) (sl: struct_layout) :
  use_struct_layout_alg sls = Some sl →
  Forall (λ '(_, st), ∀ ly, syn_type_has_layout st ly → ∃ ot : op_type, use_op_alg st = Some ot ∧ ot_layout ot = ly) (sls_fields sls) →
  ∃ ot, use_op_alg sls = Some ot ∧ ot_layout ot = layout_of sl.
Proof.
  intros (field_lys & Halg & Hfields)%use_struct_layout_alg_inv.
  destruct sls as [sn fields].
  rewrite {2}/use_op_alg/=. fold use_op_alg.
  move: Hfields Halg. simpl. intros Hfields Halg IH.
  assert (∃ ots : list op_type, Forall3 (λ '(_, ly) '(_, st) ot, use_op_alg st = Some ot ∧ ot_layout ot = ly) field_lys fields ots) as (ots & Hots).
  {
    clear -IH Hfields.
    induction fields as [ | [n st] fields IH'] in field_lys, IH, Hfields |-*; simpl.
    { exists []. apply Forall2_nil_inv_l in Hfields. subst. econstructor. }
    inversion IH as [ | ?? Hst IH1]; subst.
    apply Forall2_cons_inv_l in Hfields as ([n' ly] & fields' & [<- Hst'] & Hfields & ->).
    apply Hst in Hst' as (ot & Hot & <-).
    efeed pose proof (IH') as Ha; [done.. | ].
    destruct Ha as (ots & Hots').
    exists (ot :: ots). econstructor; done.
  }
  exists (StructOp sl ots). split; last done.
  rewrite /use_op_alg. fold use_op_alg.
  erewrite use_struct_layout_alg_Some; [ | done..].
  simpl.
  apply bind_Some. exists ots. split; last done.
  apply list_map_option_alt.
  clear -Hots.
  eapply Forall3_Forall2_impl; last done.
  intros [] [] ? []. done.
Qed.
Lemma use_union_layout_alg_op_alg `{!LayoutAlg} (uls : union_layout_spec) (ul: union_layout) :
  use_union_layout_alg uls = Some ul →
  ∃ ot, use_op_alg uls = Some ot ∧ ot_layout ot = ul_layout ul.
Proof.
  intros (variant_lys & Halg & Hvariants)%use_union_layout_alg_inv.
  destruct uls as [un variants].
  exists (UntypedOp ul). split; last done.
  rewrite /use_op_alg. simpl. fold use_op_alg.
  apply bind_Some. exists ul. split; last done.
  apply bind_Some. exists variant_lys.
  split. { apply list_map_option_alt. eapply Forall2_impl; first done. intros [] [] [-> ->]. done. }
  rewrite Halg. done.
Qed.

Lemma syn_type_has_layout_op_alg `{!LayoutAlg} st ly :
  syn_type_has_layout st ly →
  ∃ ot, use_op_alg st = Some ot ∧ ot_layout ot = ly.
Proof.
  induction st as [ it | | | | sn fields IH | | st IH len | st IH | ly' | en tag_it variant_list IH | un variant_list IH | ] using syn_type_strong_ind in ly |-*.
  - intros [-> ?]%syn_type_has_layout_int_inv.
    exists (IntOp it). split; last done. done.
  - intros ->%syn_type_has_layout_bool_inv.
    exists BoolOp. split; last done. done.
  - intros ->%syn_type_has_layout_ptr_inv.
    exists PtrOp. split; last done. done.
  - intros ->%syn_type_has_layout_ptr_inv.
    exists PtrOp. split; last done. done.
  - intros Hsl.
    specialize (syn_type_has_layout_struct_inv _ _ _ _ Hsl) as (field_lys & sl & -> & Halg & Hfields).
    eapply (use_struct_layout_alg_op_alg (mk_sls _ _ _)); last done.
    eapply use_struct_layout_alg_Some; done.
  - intros ->%syn_type_has_layout_unit_inv. exists (StructOp unit_sl []). done.
  - intros (ly' & Ha & -> & Hb)%syn_type_has_layout_array_inv.
    exists (UntypedOp (mk_array_layout ly' len)). split; last done.
    rewrite /use_op_alg. rewrite Ha. done.
  - intros Ha%syn_type_has_layout_unsafecell_inv. by apply IH.
  - intros (<- & ? & ? & ?)%syn_type_has_layout_untyped_inv.
    exists (UntypedOp ly). done.
  - intros Halg. exists (UntypedOp ly).
    split; last done.
    rewrite /use_op_alg.
    rewrite Halg. done.
    (* TODO: maybe we should at least make the read of the top-level struct typed? *)
    (*
    intros Halg%syn_type_has_layout_enum_inv.
    destruct Halg as (el & ul & variants & Hunion & Hstruct & -> & Hvariants).
    efeed pose proof (use_union_layout_alg_op_alg) as Ha.
    { eapply (use_union_layout_alg_Some (mk_uls _ _)); done. }
    destruct Ha as (ot & Hot & ?).
    efeed pose proof (use_struct_layout_alg_op_alg) as Ha.
    { eapply (use_struct_layout_alg_Some (mk_sls _ [(_, IntSynType tag_it); (_, UnionSynType _ _)])); last done.
      econstructor; simpl.
      { split; first done. eapply syn_type_has_layout_int; [done | apply IntType_to_it_size_bounded]. }
      econstructor; last constructor.
      split; first done.
      eapply syn_type_has_layout_union; done. }
    { simpl. econstructor.
      { intros ly (-> & Ha)%syn_type_has_layout_int_inv. eauto. }
      econstructor; last constructor.
      intros ly Hly.
      exists (UntypedOp ly). split; last done.
      rewrite /use_op_alg. apply bind_Some. rewrite Hly. eauto. }
    destruct Ha as (ot' & Hot' & <-).
    exists ot'. split; last done.
    simpl in Hot'.
    rewrite /use_op_alg.
     *)
  - intros (variant_lys & ul & -> & Halg & Hvariants)%syn_type_has_layout_union_inv.
    eapply (use_union_layout_alg_op_alg (mk_uls _ _ _)).
    eapply use_union_layout_alg_Some; done.
  - intros ->%syn_type_has_layout_char_inv.
    exists CharOp. split; last done. done.
Qed.

Lemma use_op_alg_wf `{!LayoutAlg} st ot :
  use_op_alg st = Some ot →
  op_type_wf ot.
Proof.
  induction st as [ | | | | sn fields repr IH | | | | | en tag_it variants repr IH | un variants repr IH | ] in ot |-* using syn_type_strong_ind; rewrite /use_op_alg; simpl; fold use_op_alg; try naive_solver.
  - intros (sl & Halg & Hfields)%bind_Some.
    apply bind_Some in Hfields as (ots & Hots & [= <-]). simpl.
    apply use_struct_layout_alg_inv in Halg as (field_lys & Halg & Hfields).
    simpl in *. apply struct_layout_alg_has_fields in Halg.
    move : Halg. rewrite /sl_has_members. generalize (sl_members sl) as members => members. clear sl.
    intros ->.
    move: Hfields. generalize (named_fields members) as named => named Hfields.

    induction fields as [ | [name st] fields IH2] in named, ots, Hots, Hfields, IH |-*; simpl in *.
    { injection Hots as <-. apply Forall2_nil_inv_l in Hfields as ->. done. }
    simpl in IH. apply Forall_cons in IH as (Hot & IH).
    apply Forall2_cons_inv_l in Hfields as ([n' ly] & named' & [<- Hst] & Hfields & ->).
    apply bind_Some in Hots as (ots' & Hots & Hot1).
    apply bind_Some in Hot1 as (ot1 & Hot1 & [= <-]).
    simpl.
    split.
    + split; first by apply Hot.
      apply syn_type_has_layout_op_alg in Hst as (ot' & Hot' & <-).
      f_equiv. by eapply use_op_alg_inj.
    + apply IH2; done.
  - intros (ly & Halg & [= <-])%bind_Some. done.
  - intros (ly & Halg & [= <-])%bind_Some. done.
  - intros (ly & Halg & [= <-])%bind_Some. done.
Qed.




(* We can convert a value at [st1] into a value at [st2]:
   either if both values have the same syntype, or if the second syntype just needs to support untyped operations ([UntypedSynType]) and has the same layout as [st1]. *)
Definition syn_type_compat `{!LayoutAlg} (st1 st2 : syn_type) : Prop :=
  st1 = st2 ∨ ∃ ly1, syn_type_has_layout st1 ly1 ∧ st2 = UntypedSynType ly1.

Lemma syn_type_compat_layout_trans `{!LayoutAlg} st1 st2 ly :
  syn_type_compat st1 st2 →
  syn_type_has_layout st2 ly →
  syn_type_has_layout st1 ly.
Proof.
  intros [-> | (ly' & Hly & ->)]; first done.
  intros (-> & _)%syn_type_has_layout_untyped_inv. done.
Qed.

Definition syn_type_size_eq `{!LayoutAlg} st1 st2 := ∀ ly1 ly2, syn_type_has_layout st1 ly1 → syn_type_has_layout st2 ly2 → ly_size ly1 = ly_size ly2.
Lemma syn_type_size_eq_refl `{!LayoutAlg} st :
  syn_type_size_eq st st.
Proof.
  intros ly1 ly2 ? ?. assert (ly1 = ly2) as <- by by eapply syn_type_has_layout_inj. done.
Qed.


