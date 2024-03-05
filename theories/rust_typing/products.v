From refinedrust Require Export type ltypes.
From refinedrust Require Import util hlist.
From refinedrust Require Import uninit_def.
From refinedrust Require Import uninit programs ltype_rules.
Set Default Proof Using "Type".

(** * Struct types *)
(** Basic design notes:
   - parameterized by a (heterogeneous) list of [type]s.
   - for refinements, use a heterogeneous list, indexed by the refinement.
   - parameterize by the [struct_layout_spec] *)

(** We define [is_struct_ot] not just on the syntactic type, but also directly involve the component types [tys],
  because this stratifies the recursion going on and we anyways need to define a relation involving the [mt] for the semantic types. *)
Definition is_struct_ot `{typeGS Σ} (sls : struct_layout_spec) (tys : list rtype) (ot : op_type) (mt : memcast_compat_type) :=
  length (sls.(sls_fields)) = length tys ∧
  match ot with
  | StructOp sl ots =>
      (* padding bits will be garbled, so we cannot fulfill MCId *)
      mt ≠ MCId ∧
      (* sl is a valid layout for this sls *)
      use_struct_layout_alg sls = Some sl ∧
      length ots = length tys ∧
      (* pointwise, the members have the right op_type and a layout matching the optype *)
      foldr (λ ty, and (let '(ty, ot) := ty in
          ty_has_op_type (ty.(rt_ty) : type _) ot mt ∧
          syn_type_has_layout (ty.(rt_ty).(ty_syn_type)) (ot_layout ot)))
        True (zip tys ots)
  | UntypedOp ly =>
      (* ly is a valid layout for this sls *)
      ∃ sl, use_struct_layout_alg sls = Some sl ∧ ly = sl ∧
      (* pointwise, the members have the right op type *)
      foldr (λ ty, and (∃ ly,
            syn_type_has_layout (ty.(rt_ty).(ty_syn_type)) ly ∧ ty_has_op_type (ty.(rt_ty) : type _) (UntypedOp ly) mt
          ))
        True tys
  | _ => False
  end.
Global Typeclasses Opaque is_struct_ot.

Lemma is_struct_ot_layout `{typeGS Σ} sls sl tys ot mt :
  use_struct_layout_alg sls = Some sl →
  is_struct_ot sls tys ot mt → ot_layout ot = sl.
Proof. move => ? [?]. destruct ot => //; naive_solver. Qed.

(** ** Unit type *)
(** [unit_t] gets some special treatment, because it occurs frequently and is specced to be a ZST *)
Section unit.
  Context `{!typeGS Σ}.

  Program Definition unit_t : type unit := {|
    st_own π _ v := ⌜v = zst_val⌝;
    st_syn_type := UnitSynType;
    st_has_op_type ot mt := is_unit_ot ot;
  |}%I.
  Next Obligation.
    iIntros (π _ v ->). eauto.
  Qed.
  Next Obligation.
    intros ot mt ->%is_unit_ot_layout. done.
  Qed.
  Next Obligation.
    simpl. iIntros (ot ?? _ _  v Hot ->).
    destruct mt.
    - done.
    - destruct ot; try by destruct Hot. destruct Hot as [-> ->]. done.
    - iApply (mem_cast_compat_unit (λ _, True)%I); eauto.
  Qed.

  Global Instance unit_copyable : Copyable unit_t.
  Proof. apply _. Qed.

  Global Instance unit_timeless l z π:
    Timeless (l ◁ᵥ{π} z @ unit_t)%I.
  Proof. apply _. Qed.

  Lemma type_val_unit π (T : ∀ rt, type rt → rt → iProp Σ):
    T _ (unit_t) () ⊢ typed_value (zst_val) π T.
  Proof.
    iIntros "HT #LFT".
    iExists _, unit_t, (). iFrame "HT". done.
  Qed.
  Global Instance type_val_unit_inst π : TypedValue zst_val π :=
    λ T, i2p (type_val_unit π T).
End unit.

Global Hint Unfold unit_t : tyunfold.

(** ** Full structs *)
Section structs.
  Context `{!typeGS Σ}.

  Polymorphic Definition zip_to_rtype (rt : list Type) (tys : hlist type rt) :=
    (fmap (λ x, mk_rtype (projT2 x)) (hzipl rt tys)).

  Definition struct_own_el_val (π : thread_id) (i : nat) (fields : field_list) (v : val) {rt} (r : place_rfn rt) (ty : type rt) : iProp Σ :=
    ∃ (r' : rt) (ly0 : layout), place_rfn_interp_owned r r' ∗
      ⌜snd <$> fields !! i = Some ly0⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type ty) ly0⌝ ∗
      v ◁ᵥ{ π} r' @ ty.
  Definition struct_own_el_loc (π : thread_id) (q : Qp) (v : val) (i : nat) (fields : field_list) (l : loc) {rt} (r : place_rfn rt) (ty : type rt) : iProp Σ :=
    ∃ (r' : rt) (ly : layout), place_rfn_interp_owned r r' ∗
      ⌜snd <$> fields !! i = Some ly⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗
      ty_sidecond ty ∗
      (l +ₗ offset_of_idx fields i) ↦{q} v ∗
      ⌜v `has_layout_val` ly ⌝ ∗
      v ◁ᵥ{ π} r' @ ty.
  Definition struct_own_el_loc' (π : thread_id) (q : Qp) (v : val) (i : nat) (fields : field_list) (l : loc) {rt} (r : place_rfn rt) (ty : type rt) (ly : layout) : iProp Σ :=
    ⌜v `has_layout_val` ly⌝ ∗
    ⌜snd <$> fields !! i = Some ly⌝ ∗
    (l +ₗ offset_of_idx fields i) ↦{q} v ∗
    ∃ (r' : rt), place_rfn_interp_owned r r' ∗
      ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗
      ty_sidecond ty ∗
      v ◁ᵥ{ π} r' @ ty.
  Definition struct_own_el_shr (π : thread_id) (κ : lft) (i : nat) (fields : field_list) (l : loc) {rt} (r : place_rfn rt) (ty : type rt) : iProp Σ :=
    ∃ (r' : rt) (ly : layout), place_rfn_interp_shared r r' ∗
      ⌜snd <$> fields !! i = Some ly⌝ ∗
      ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗
      ty_sidecond ty ∗
      (l +ₗ Z.of_nat (offset_of_idx fields i)) ◁ₗ{π, κ} r' @ ty.

  Definition struct_make_uninit_type (ly : layout) : sigT (λ rt : Type, (type rt * place_rfn rt)%type) :=
    existT (unit : Type) (uninit (UntypedSynType ly), #()).

  Lemma struct_own_val_extract_mapsto' π q sls sl l (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) ys :
    use_struct_layout_alg sls = Some sl →
    length tys = length (sls_fields sls) →
    loc_in_bounds l 0 (ly_size sl) -∗
    ([∗ list] i↦a;x ∈ pad_struct (sl_members sl) tys struct_make_uninit_type;ys,
      struct_own_el_loc' π q x.1 i (sl_members sl) l (projT2 a).2 (projT2 a).1 x.2) -∗
    l ↦{q} (mjoin ys.*1) ∗ ⌜Forall2 (λ (v : val) (ly : layout), v `has_layout_val` ly) ys.*1 ((sl_members sl).*2)⌝ ∗
      ([∗ list] i↦v';ty ∈ reshape (ly_size <$> (sl_members sl).*2) (mjoin ys.*1);
            pad_struct (sl_members sl) tys (λ ly0 : layout, existT (unit : Type) (uninit (UntypedSynType ly0), # ())),
      struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1).
  Proof.
    iIntros (??) "#Hlb Hl".

    do 3 rewrite big_sepL2_sep. iDestruct "Hl" as "(Hlyv & Hsl & Hl & Hb)".
    rewrite !big_sepL2_elim_l.
    iDestruct "Hlyv" as "%Hlyv". iDestruct "Hsl" as "%Hsl".
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite pad_struct_length in Hlen_eq.

    set (vs := ys.*1). set (lys := ys.*2).

    assert (Forall2 (λ (v : val) (ly : layout), v `has_layout_val` ly) vs ((sl_members sl).*2)).
    { rewrite Forall2_fmap_r.
      apply Forall2_same_length_lookup.
      split. { rewrite Hlen_eq /vs fmap_length//. }
      intros i v' [n ly'] Hlook1 Hlook2.
      apply list_lookup_fmap_Some in Hlook1 as ([v1 ly1] & Hlook1 & ->) .
      simpl. specialize (Hsl _ _ Hlook1). move: Hsl.
      rewrite Hlook2 /= => [= ->]. apply (Hlyv _ _ Hlook1). }

    iSplitL "Hl".
    { iApply heap_mapsto_reshape_sl. { apply mjoin_has_struct_layout. done. }
      rewrite reshape_join. { iFrame "Hlb". by iApply big_sepL_fmap. }
      apply Forall2_same_length_lookup.
      split. { rewrite !fmap_length//. }
      intros i v' sz Hlook1 Hlook2.
      apply list_lookup_fmap_Some in Hlook1 as ([v1 ly1] & Hlook1 & ->) .
      simpl. specialize (Hsl _ _ Hlook1). move: Hsl.
      apply list_lookup_fmap_Some in Hlook2 as (ly' & Hlook & ->).
      rewrite list_lookup_fmap in Hlook. rewrite Hlook => [=->].
      apply (Hlyv _ _ Hlook1). }

    iR.
    iAssert (
      [∗ list] i ↦ y2; y1 ∈ vs; pad_struct (sl_members sl) tys struct_make_uninit_type,
        let 'existT rt (ty, r0) := y1 in ∃ (r' : rt) (ly : layout), place_rfn_interp_owned r0 r' ∗
            ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗ ty_sidecond ty ∗ y2 ◁ᵥ{ π} r' @ ty)%I with "[Hb]" as "Hb".
    { iApply big_sepL2_flip. rewrite big_sepL2_fmap_r. iApply (big_sepL2_wand with "Hb").
      iApply big_sepL2_intro. { rewrite pad_struct_length Hlen_eq //. }
      iModIntro. iIntros (k [? []] [v1 ly1] ? Hlook2) "(%r' & ? & ? & ? & ?)".
      iExists _,_. iFrame. iPureIntro. apply (Hsl _ _ Hlook2). }
    rewrite reshape_join; first last.
    { apply Forall2_same_length_lookup. rewrite !fmap_length Hlen_eq. split; first done.
      intros ??? Hlook1 Hlook2.
      apply list_lookup_fmap_Some in Hlook1 as ([v1 ly1] & Hlook1 & ->).
      specialize (Hlyv _ _ Hlook1). rewrite Hlyv.
      specialize (Hsl _ _ Hlook1). simpl in *.
      apply list_lookup_fmap_Some in Hlook2 as (ly2 & Hlook2 & ->).
      rewrite list_lookup_fmap in Hlook2. f_equiv.
      rewrite Hsl in Hlook2. injection Hlook2 as [= ->]; done. }
    iApply (big_sepL2_wand with "Hb").
    iApply big_sepL2_intro. { rewrite pad_struct_length Hlen_eq fmap_length //. }
    iModIntro. iIntros (?? [? []] ? ?). iIntros "(% & % & ? & ? & ? & ? & ?)".
    rewrite /struct_own_el_val.
    eauto with iFrame.
  Qed.

  Lemma struct_own_val_extract_mapsto π q sls sl l (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) :
    use_struct_layout_alg sls = Some sl →
    length tys = length (sls_fields sls) →
    loc_in_bounds l 0 (ly_size sl) -∗
    ([∗ list] i↦ty ∈ pad_struct (sl_members sl) tys struct_make_uninit_type,
      ∃ v, struct_own_el_loc π q v i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1) -∗
    ∃ v : val, l ↦{q} v ∗ ⌜v `has_layout_val` sl⌝ ∗
      ([∗ list] i↦v';ty ∈ reshape (ly_size <$> (sl_members sl).*2) v; pad_struct (sl_members sl) tys struct_make_uninit_type,
      struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1).
  Proof.
    iIntros (??) "#Hlb Hl".
    iAssert (
      [∗ list] i↦ty ∈ pad_struct (sl_members sl) tys (λ ly0, existT (unit : Type) (uninit (UntypedSynType ly0), # ())),
      ∃ (y : val * layout),
      struct_own_el_loc' π q y.1 i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1 y.2)%I with "[Hl]" as "Hl".
    { iApply (big_sepL_wand with "Hl"). iApply big_sepL_intro.
      iModIntro. iIntros (k [? []] Hlook). iIntros "(%v & % & %ly0 & ? & ? & ? & ? & ? & ? & ?)".
      iExists (v, ly0). rewrite /struct_own_el_loc'. eauto with iFrame. }
    rewrite big_sepL_exists. iDestruct "Hl" as "(%ys & Hl)".
    iExists (mjoin ys.*1).
    iPoseProof (struct_own_val_extract_mapsto' with "Hlb Hl") as "(Hl & %Ha & Hs)"; [done.. | ].
    iFrame. iPureIntro. by apply mjoin_has_struct_layout.
  Qed.

  Lemma struct_own_val_join_mapsto π q sls sl l v (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) :
    use_struct_layout_alg sls = Some sl →
    length tys = length (sls_fields sls) →
    v `has_layout_val` sl →
    l ↦{q} v -∗
    ([∗ list] i↦v';ty ∈ reshape (ly_size <$> (sl_members sl).*2) v; pad_struct (sl_members sl) tys struct_make_uninit_type,
        struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1) -∗
    ([∗ list] i↦ty ∈ pad_struct (sl_members sl) tys struct_make_uninit_type,
      ∃ v, struct_own_el_loc π q v i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1).
  Proof.
    iIntros (???) "Hl Hv".
    rewrite heap_mapsto_reshape_sl; last done.
    iDestruct "Hl" as "(_ & Hp)".
    iPoseProof (big_sepL_extend_r (pad_struct (sl_members sl) tys struct_make_uninit_type) with "Hp") as "Hp".
    { rewrite pad_struct_length reshape_length !fmap_length//. }
    iPoseProof (big_sepL2_sep_1 with "Hv Hp") as "Ha".
    iApply big_sepL2_elim_l. iApply (big_sepL2_wand with "Ha").
    iApply big_sepL2_intro.
    { rewrite pad_struct_length reshape_length !fmap_length//. }
    iModIntro. iIntros (k v' [rt [ty r']] Hlook1 Hlook2).
    iIntros "((%r'' & %ly' & Hrfn & %Hlook3 & %Hst & Hv) & Hp)".
    iExists v', r'', ly'. iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    iFrame. done.
  Qed.


  (** We use a [hlist] for the list of types and a [plist] for the refinement, to work around universe problems.
     See also the [ltype] definition. Using just [hlist] will cause universe problems, while using [plist] in the [lty]
     inductive will cause strict positivity problems. *)
  Program Definition struct_t {rts : list Type} (sls : struct_layout_spec) (tys : hlist type rts) : type (plist place_rfn rts) := {|
    ty_own_val π r v :=
      (∃ sl,
        ⌜use_struct_layout_alg sls = Some sl⌝ ∗
        ⌜length rts = length sls.(sls_fields)⌝ ∗
        ⌜v `has_layout_val` sl⌝ ∗
        (* the padding fields get the uninit type *)
        [∗ list] i ↦ v';ty ∈ reshape (ly_size <$> sl.(sl_members).*2) v; pad_struct sl.(sl_members) (hpzipl rts tys r) struct_make_uninit_type,
          struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1
          )%I;
    ty_sidecond := ⌜length rts = length (sls_fields sls)⌝;
    _ty_has_op_type ot mt := is_struct_ot sls (zip_to_rtype rts tys) ot mt;
    ty_syn_type := sls : syn_type;
    ty_shr κ π r l :=
      (∃ sl,
        ⌜use_struct_layout_alg sls = Some sl⌝ ∗
        ⌜length rts = length sls.(sls_fields)⌝ ∗
        ⌜l `has_layout_loc` sl⌝ ∗
        loc_in_bounds l 0 (ly_size sl) ∗
        [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts tys r) struct_make_uninit_type,
          struct_own_el_shr π κ i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1)%I;
    ty_ghost_drop π r := True%I; (* TODO *)
    ty_lfts := mjoin (fmap (λ ty, (projT2 ty).(ty_lfts)) (hzipl rts tys));
    ty_wf_E := mjoin (fmap (λ ty, (projT2 ty).(ty_wf_E)) (hzipl rts tys));
  |}.
  Next Obligation.
    intros rts _ _. apply inhabited_plist.
    induction rts as [ | rt rts IH]; first apply _.
    econstructor; first apply _. apply IH.
  Qed.
  Next Obligation.
    iIntros (rts sls tys π r v) "(%sl & %Halg & %Hlen & %Hly & ?)".
    iExists sl. iPureIntro. split; last done.
    by apply use_struct_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rts sls tys ot mt Hot).
    destruct Hot as [Hlen Hot].
    destruct ot; try done.
    - destruct Hot as (Halg & Hlen' & Hmem).
      simpl. by apply use_struct_layout_alg_Some_inv.
    - destruct Hot as (sl & Halg & -> & Hmem).
      simpl. by apply use_struct_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rts sls tys π r v) "(%sl & ? & $ & _)".
  Qed.
  Next Obligation.
    iIntros (rts sls tys ? π r v) "(%sl & ? & $ & _)".
  Qed.
  Next Obligation.
    iIntros (rts sls tys κ π l r) "(%sl & %Halg & %Hly & % & Hmem)".
    iExists sl. iSplitR; first done. iPureIntro.
    by apply use_struct_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    (* sharing *)
    iIntros (rts sls tys E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Hst %Hly #Hlb Hl".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok')".
    iApply fupd_logical_step.

    (* reshape the borrow - we must not freeze the existential over v to initiate recursive sharing *)
    iPoseProof (bor_iff _ _ (∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗ ⌜length rts = length (sls_fields sls)⌝ ∗
      [∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type,
        ∃ v, struct_own_el_loc π 1 v i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1)%I with "[] Hl") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & %sl & %Hst' & %Hlen & %Hv & Hv)".
        iExists sl. iR. iR.
        iApply (struct_own_val_join_mapsto with "Hl Hv"); [done | | done].
        rewrite hpzipl_length//.

      - iIntros "(%sl & %Hst' & %Hlen & Hl)".
        assert (ly = sl) as ->.
        { apply use_struct_layout_alg_Some_inv in Hst'. by eapply syn_type_has_layout_inj. }

        iPoseProof (struct_own_val_extract_mapsto with "Hlb Hl") as "(%v & Hl & %Hlyv & Hv)".
        { done. }
        { rewrite hpzipl_length//. }
        iExists v. iFrame. iExists sl. iR. iR. iR. done.
    }

    iMod (bor_exists with "LFT Hb") as "(%sl & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst' & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hlen & Hb)"; first done.
    iMod (bor_persistent with "LFT Hlen Htok") as "(>%Hlen & Htok)"; first done.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iCombine "Htok Htok'" as "Htok". rewrite lft_tok_sep.
    (* fracture the tokens over the big_sep *)
    set (len := length (sl_members sl)).
    set (κ' := lft_intersect_list (mjoin ((λ ty, ty_lfts (projT2 ty)) <$> hzipl rts tys))).
    iPoseProof (Fractional_split_big_sepL (λ q, q.[_]%I) len with "Htok") as "(%qs & %Hlen' & Htoks & Hcl_toks)".
    iAssert ([∗ list] i ↦ ty; q' ∈ (pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type); qs,
      &{κ} ((∃ (r' : projT1 ty) (ly : layout), place_rfn_interp_owned (projT2 ty).2 r' ∗ ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type (projT2 ty).1) ly⌝ ∗ ty_sidecond (projT2 ty).1 ∗ ∃ v, (l +ₗ offset_of_idx sl.(sl_members) i) ↦ v ∗ ⌜v `has_layout_val` ly⌝ ∗ v ◁ᵥ{ π} r' @ (projT2 ty).1)) ∗
      q'.[κ ⊓ κ'])%I with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r; iFrame. iApply big_sepL2_const_sepL_l.
      iSplitR. { rewrite pad_struct_length Hlen' //. }
      (* we also need to push down the existential over v *)
      iApply (big_sepL_wand with "Hb"); iApply big_sepL_intro.
      iModIntro. iIntros (? [? []] ?) "Ha". iApply (bor_iff with "[] Ha").
      iNext. iModIntro. iSplit.
      - iIntros "(%v & % & % & ? & ? & ? & ? & ? & ? & ?)". eauto with iFrame.
      - iIntros "(% & % & ? & ? & ? & ? & Hl)". iDestruct "Hl" as "(%v & ? & ? & ?)".
        rewrite /struct_own_el_loc; eauto with iFrame.
    }

    assert (ly = sl) as ->.
    { apply use_struct_layout_alg_Some_inv in Hst'. by eapply syn_type_has_layout_inj. }
    iAssert ([∗ list] i ↦ ty; q' ∈ (pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type); qs,
      logical_step E (
        struct_own_el_shr π κ i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1 ∗ q'.[κ ⊓ κ']))%I with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro.
      { rewrite pad_struct_length Hlen' //. }
      iModIntro. iIntros (k x q0 Hlook1 Hlook2) "(Hb & Htok)".
      iApply fupd_logical_step.
      destruct x as [rt [ty r']]. set (κ'' := lft_intersect_list (ty_lfts ty)).
      iMod (lft_incl_acc _ _ (κ ⊓ κ'') with "[] Htok") as "(%q' & Htok & Hvs)"; first done.
      { iApply lft_intersect_mono; first iApply lft_incl_refl.
        rewrite /κ' /κ''.
        iApply list_incl_lft_incl_list.
        apply pad_struct_lookup_Some in Hlook1; first last.
        { rewrite hpzipl_length Hlen. erewrite struct_layout_spec_has_layout_fields_length; done. }
        destruct Hlook1 as (n & ly & ? & [ (? & Hlook) | (-> & Heq)]).
        - apply hpzipl_lookup_inv_hzipl_pzipl in Hlook as (Hlook & _).
          apply list_subseteq_mjoin. apply elem_of_list_fmap.
          exists (existT _ ty). split; first done.
          apply elem_of_list_lookup_2 in Hlook. done.
        - injection Heq => Heq1 Heq2 ?. subst.
          apply existT_inj in Heq1 as ->.
          apply existT_inj in Heq2 as ->.
          simpl. set_solver.
      }
      rewrite -{1}lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r'' & Hb & Htok1)"; first done.
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%ly' & Hb & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Ha & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hly & Hb)"; first done.
      iMod (bor_persistent with "LFT Hly Htok1") as "(>%Hly' & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
      iMod (bor_persistent with "LFT Hst Htok1") as "(>%Hst'' & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hsc & Hb)"; first done.
      iMod (bor_persistent with "LFT Hsc Htok1") as "(>Hsc & Htok1)"; first done.

      iPoseProof (bor_iff _ _ (∃ v : val, (l +ₗ offset_of_idx (sl_members sl) k) ↦ v ∗ v ◁ᵥ{π} r'' @ ty) with "[] Hb") as "Hb".
      { iNext. iModIntro. iSplit.
        - iIntros "(%v & Hl & %Hlyv & Hv)". iExists v. iFrame.
        - iIntros "(%v & Hl & Hv)". iExists v.
          iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
          iFrame. done. }

      iCombine "Htok1 Htok2" as "Htok". rewrite lft_tok_sep. iModIntro.
      iPoseProof (ty_share with "[$LFT $TIME $LLCTX] Htok [] [] [] Hb") as "Hb"; first done.
      - done.
      - iPureIntro. by apply struct_layout_field_aligned.
      - iApply loc_in_bounds_sl_offset; done.
      - iApply logical_step_fupd.
        iApply (logical_step_wand with "Hb"). iIntros "(? & Htok)".
        iMod ("Hvs" with "Htok").
        iFrame. iModIntro. simpl.
        iExists _, _. iFrame. done.
    }
    iPoseProof (logical_step_big_sepL2 with "Hb") as "Hb".
    iModIntro. iApply (logical_step_wand with "Hb"). iIntros "Hb".
    iPoseProof (big_sepL2_sep_sepL_r with "Hb") as "(Hb & Htok)".
    iPoseProof ("Hcl_toks" with "Htok") as "$".
    iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & Hb)".
    iExists _. do 4 iR. done.
  Qed.
  Next Obligation.
    (* monotonicity of sharing *)
    iIntros (rts sls tys κ κ' π r l) "#Hincl (%sl & %Hsl & %Hlen & %Hly & Hlb & Hb)".
    iExists sl. do 3 iR. iFrame.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iModIntro. iIntros (k [rt [ty r']] Hlook).
    iIntros "(%r'' & %ly & ? & ? & ? & ? & Hb)".
    iExists _, _. iFrame.
    iApply (ty_shr_mono with "Hincl Hb").
  Qed.
  Next Obligation.
    iIntros (rts sls tys π r v F ?) "(%sl & %Halg & Hlen & %Hly & Hmem)".
    by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (rts sls tys ot mt st π r v Hot).
    apply (mem_cast_compat_Untyped) => ?.
    iIntros "(%sl & %Halg & %Hlen & %Hsl & Hmem)".
    destruct Hot as [? Hot]. destruct ot as [ | | | sl' ots | | ]; try done.
    destruct Hot as (? & Halg' & Hlen_ots & Hot%Forall_fold_right).
    assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }
    destruct mt.
    - done.
    - iExists sl. iSplitR; first done. iSplitR; first done.
      iSplitR. { rewrite /has_layout_val mem_cast_length. done. }
      assert (length (field_names (sl_members sl)) = length (sls_fields sls)) as Hlen2.
      { by eapply struct_layout_spec_has_layout_fields_length. }
      (* we memcast the value and need to show that it is preserved *)
      iAssert ⌜∀ i v' n ly,
           reshape (ly_size <$> (sl_members sl).*2) v !! i = Some v' →
           sl_members sl !! i = Some (Some n, ly) → v' `has_layout_val` ly⌝%I as %?. {
        iIntros (i v' n ly Hv' Hly).
        (* lookup the corresponding index and type assignment for the member *)
        have [|rt Hlook]:= lookup_lt_is_Some_2 rts (field_idx_of_idx (sl_members sl) i).
        { have := field_idx_of_idx_bound sl i _ _ ltac:(done). lia. }
        edestruct (hpzipl_lookup rts tys r) as [ty [r' Hlook2]]; first done.
        iDestruct (big_sepL2_lookup with "Hmem") as "Hv"; [done| |].
        { apply/pad_struct_lookup_Some. { rewrite hpzipl_length Hlen. done. }
          naive_solver. }
        (* lookup the ot *)
        have [|ot ?]:= lookup_lt_is_Some_2 ots (field_idx_of_idx (sl_members sl) i).
        { have := field_idx_of_idx_bound sl i _ _ ltac:(done). lia. }
        iDestruct "Hv" as "(%r'' & %ly0 & Hrfn & %Ha & % & Hv)".
        iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Halg'' & %Hly')".
        enough (ly' = ly) as ->; first done.
        assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
        rewrite Hly in Ha. by injection Ha.
      }
      iFrame. iApply (big_sepL2_impl' with "Hmem"); [by rewrite !reshape_length |done|].
      iIntros "!>" (k v1 ty1 v2 ty2 Hv1 Hty1 Hv2 Hty2) "Hv"; simplify_eq.
      destruct ty1 as (rt1 & ty1 & r1).
      rewrite mem_cast_struct_reshape // in Hv2; last congruence.
      move: Hv2 => /lookup_zip_with_Some [?[?[?[Hpad Hv']]]]. simplify_eq.
      rewrite Hv1 in Hv'. simplify_eq.
      iDestruct "Hv" as "(%r' & % & Hrfn & %Hlook & % & Hv)". iExists r', _. iFrame.
      move: Hty1 => /pad_struct_lookup_Some[|n[?[Hlook2 Hor1]]].
      { rewrite hpzipl_length Hlen. done. }
      move: Hpad => /pad_struct_lookup_Some[|?[?[? Hor2]]]. { rewrite fmap_length. congruence. } simplify_eq.
      destruct Hor1 as [[??] | [? ?]], Hor2 as [[? Hl] |[? ?]]; simplify_eq.
      + rewrite list_lookup_fmap in Hl. move: Hl => /fmap_Some[ot [??]]. simplify_eq.
        iSplitR; first done. iSplitR; first done.
        iApply ty_memcast_compat_copy; [|done]. destruct n as [n|] => //.
        (* lookup layout in sl *)
        (*have [|p ?]:= lookup_lt_is_Some_2 (field_members (sl_members sl)) (field_idx_of_idx (sl_members sl) k).*)
        (*{ have := field_idx_of_idx_bound sl k _ _ ltac:(done). rewrite field_members_length. lia. }*)
        move: Hot => /(Forall_lookup_1 _ _ (field_idx_of_idx (sl_members sl) k) (mk_rtype ty1, ot)).
        (*destruct p as [p ?].*)
        move => [|??]; last done.
        apply/lookup_zip_with_Some. eexists _, _. split_and!; [done| |done].
        (*apply/lookup_zip_with_Some. eexists _, _.*)
        (*split; first done. split; last done.*)
        rewrite list_lookup_fmap.
        match goal with
        | H : hpzipl rts _ _ !! _ = Some _ |- _ => eapply (hpzipl_lookup_inv_hzipl_pzipl rts tys r) in H as [-> _]
        end. done.
      + unfold struct_make_uninit_type in *.
        match goal with | H : existT _ _ = existT _ _ |- _ => rename H into Heq end.
        injection Heq => Heq1 Heq2 ?. subst.
        apply existT_inj in Heq1. apply existT_inj in Heq2. subst.
        iSplitR; first done. iSplitR; first done.
        iExists _; iPureIntro. split; first done.
        rewrite /has_layout_val replicate_length.
        rewrite Hlook2 in Hlook. injection Hlook as [= ->].
        split; first done. by apply Forall_true.
    - iPureIntro. done.
  Qed.

  Global Instance struct_t_ne {rts : list Type} n : Proper ((=) ==> (dist n) ==> (dist n)) (struct_t (rts := rts)).
  Proof.
    intros ? sls -> tys1 tys2 Htys.
    constructor.
    - done.
    - move => ot mt /=. rewrite ty_has_op_type_unfold/= /is_struct_ot. rewrite !fmap_length !hzipl_length.
      apply and_proper => Hsl.
      destruct ot as [ | | | sl ots | ly | ] => //=.
      + f_equiv. apply and_proper => Halg. apply and_proper => Hots. rewrite -!Forall_fold_right.
        erewrite <-struct_layout_spec_has_layout_fields_length in Hsl; last done.
        rewrite -field_members_length in Hsl.
        elim: (field_members (sl_members sl)) ots rts tys1 tys2 Htys Hsl Hots => //; csimpl.
        { intros ots rts tys1 tys2 Heq Hlen. destruct rts; last done.
          inv_hlist tys1. inv_hlist tys2. intros _ ?. destruct ots; done. }
        move => [m ?] s IH ots rts tys1 tys2 Htys Hlen1 Hlen2.
        destruct rts as [ | rt rts]; first done. destruct ots as [ | ot ots]; first done.
        inv_hlist tys1 => ty1 tys1. inv_hlist tys2 => ty2 tys2.
        intros Heq.
        eapply HForallTwo_cons_inv in Heq as [Hty1_ty2 Heq].
        simplify_eq/=; rewrite !Forall_cons/=; f_equiv.
        { f_equiv; first apply Hty1_ty2.
          f_equiv. apply Hty1_ty2. }
        eapply IH; done.
      + f_equiv. intros sl. apply and_proper => Halg.
        apply and_proper => Heq. subst ly.
        rewrite -!Forall_fold_right.
        specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen.
        rewrite -field_members_length Hsl in Hlen. clear Hsl.
        elim: (field_members (sl_members sl)) rts tys1 tys2 Htys Hlen => //; csimpl.
        { intros rts tys1 tys2 Heq Hlen. destruct rts; last done.
          inv_hlist tys1; inv_hlist tys2; intros _. done. }
        move => [m ?] s IH rts tys1 tys2 Heq Hlen.
        destruct rts as [ | rt rts]; first done.
        inv_hlist tys1 => ty1 tys1. inv_hlist tys2 => ty2 tys2 Heq.
        apply HForallTwo_cons_inv in Heq as [Hty1_ty2 Heq].
        rewrite !Forall_cons/=; f_equiv.
        { f_equiv; f_equiv; f_equiv; last apply Hty1_ty2.
          f_equiv; apply Hty1_ty2. }
        eapply IH; first done. by simplify_eq/=.
    - iIntros (π r v). rewrite /ty_own_val/=.
      f_equiv => sl.
      rewrite /struct_own_el_val.
      apply sep_ne_proper => Halg. apply sep_ne_proper => Hlen.
      f_equiv.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
      rewrite -field_members_length -Hlen in Hlen2. clear Hlen.
      elim: (sl_members sl) rts tys1 tys2 r Htys Hlen2 v => //. intros [m ?] s IH rts tys1 tys2 r Htys Hlen v; csimpl.
      destruct m; simpl in *.
      + destruct rts as [ | rt rts]; first done.
        inv_hlist tys1 => ty1 tys1. inv_hlist tys2 => ty2 tys2.
        intros [Hty1_ty2 Heq]%HForallTwo_cons_inv.
        simpl. f_equiv. { rewrite /struct_own_el_val. do 8 f_equiv; [f_equiv | ]; apply Hty1_ty2. }
        eapply IH; first done. simpl in Hlen. lia.
      + f_equiv. eapply IH; done.
    - iIntros (κ π r l). rewrite /ty_shr /= /struct_own_el_shr/=.
      f_equiv => sl. apply sep_ne_proper => Halg. apply sep_ne_proper => Hlen.
      f_equiv.
      f_equiv.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
      rewrite -field_members_length -Hlen in Hlen2. clear Hlen.
      elim: (sl_members sl) rts tys1 tys2 r Htys Hlen2 l => //. intros [m ly] s IH rts tys1 tys2 r Htys Hlen l; csimpl.
      destruct m; simpl in *.
      + destruct rts as [ | rt rts]; first done.
        inv_hlist tys1 => ty1 tys1. inv_hlist tys2 => ty2 tys2.
        intros [Hty1_ty2 Heq]%HForallTwo_cons_inv.
        simpl. f_equiv. { do 8 f_equiv; [f_equiv | | ]; apply Hty1_ty2. }
        cbn. setoid_rewrite <-shift_loc_assoc_nat.
        eapply IH; first done. simpl in Hlen. lia.
      + f_equiv. setoid_rewrite <-shift_loc_assoc_nat. apply IH; done.
    - done.
    - done.
    - done.
    - rewrite /ty_lfts /=.
      induction rts as [ | rt rts IH] in tys1, tys2, Htys |-*; inv_hlist tys1; inv_hlist tys2; simpl; first done.
      intros ty2 tys2 ty1 tys1 [Hty1_ty2 Heq]%HForallTwo_cons_inv.
      f_equiv. { apply Hty1_ty2. }
      eapply IH; done.
    - rewrite /ty_wf_E /=.
      induction rts as [ | rt rts IH] in tys1, tys2, Htys |-*; inv_hlist tys1; inv_hlist tys2; simpl; first done.
      intros ty2 tys2 ty1 tys1 [Hty1_ty2 Heq]%HForallTwo_cons_inv.
      f_equiv. { apply Hty1_ty2. }
      eapply IH; done.
  Qed.
  Global Instance struct_t_proper {rts : list Type} : Proper ((=) ==> (≡) ==> (≡)) (struct_t (rts := rts)).
  Proof.
    move => ??->  tys1 tys2 Htys.
    apply equiv_dist. rewrite equiv_dist in Htys. intros n. by rewrite Htys.
  Qed.
End structs.

Global Hint Unfold struct_t : tyunfold.

Section init.
  Context `{!typeGS Σ}.
  Lemma struct_val_has_layout sls sl vs :
    Forall3 (λ '(_, ly) '(_, st) v, syn_type_has_layout st ly ∧ v `has_layout_val` ly) (named_fields (sl_members sl)) (sls_fields sls)  vs →
    mjoin (pad_struct (sl_members sl) vs (λ ly : layout, replicate (ly_size ly) ☠%V)) `has_layout_val` sl.
  Proof.
    rewrite {2}/has_layout_val{2}/ly_size/=.
    generalize (sls_fields sls) as fields => fields. clear sls.
    generalize (sl_members sl) as mems => mems. clear sl.
    induction mems as [ | [oname ly] mems IH] in vs, fields |-*; simpl; first done.
    destruct oname as [ name | ].
    - (* named *)
      intros Hf. apply Forall3_cons_inv_l in Hf as ([name2 st] & fields' & v & vs' & -> & -> & [Hst Hv] & Hf).
      rewrite app_length. erewrite IH; last done.
      simpl. rewrite Hv. done.
    - intros Hf. rewrite app_length replicate_length. erewrite IH; last done. done.
  Qed.

  Lemma struct_init_val π sls sl vs {rts} (tys : hlist type rts) (rs : plist id rts) :
    use_struct_layout_alg sls = Some sl →
    length rts = length (sls_fields sls) →
    ([∗ list] i↦v;Ty ∈ vs;hpzipl rts tys rs, let 'existT rt (ty, r) := Ty in
      ∃ (name : string) (st : syn_type) (ly : layout),
        ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ ⌜syn_type_has_layout st ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗ v ◁ᵥ{ π} r @ ty) -∗
    mjoin (pad_struct (sl_members sl) vs (λ ly : layout, replicate (ly_size ly) ☠%V)) ◁ᵥ{ π} (λ (X : Type) (a : X), # a) -<$> rs @ struct_t sls tys.
  Proof.
    iIntros (Hsl Hlen) "Hv".
    rewrite {2}/ty_own_val /=/struct_own_el_val/=.
    iExists sl. iR. iR.

    apply use_struct_layout_alg_inv in Hsl as (field_lys & Halg & Hfields).
    specialize (struct_layout_alg_pad_align _ _ _ _ Halg) as Hpad.
    specialize (sl_size sl) as Hsize.
    apply struct_layout_alg_has_fields in Halg.
    move: Halg Hfields Hlen Hpad Hsize.
    rewrite /sl_has_members. intros ->.
    rewrite /has_layout_val [ly_size sl]/ly_size/=.
    intros Hsts Hlen Hpad Hsize.

    iSplit.
    { iApply bi.pure_mono; first apply (struct_val_has_layout sls).
      move: Hsts Hlen.
      generalize (sls_fields sls) as sts. generalize (sl_members sl) as mems.
      intros mems sts.
      generalize (named_fields mems) as lys. clear mems. intros lys Hsts Hlen.
      iInduction vs as [ | v vs] "IH" forall (rts tys rs sts lys Hsts Hlen).
      { destruct rts as [ | rt rts]; inv_hlist tys; [destruct rs | destruct rs as [r rs]]; simpl; last done.
        destruct sts; last done. apply Forall2_nil_inv_l in Hsts as ->. iPureIntro. constructor. }
      destruct rts as [ | rt rts]; inv_hlist tys; [destruct rs | destruct rs as [r rs]]; simpl; first done.
      intros ty tys.
      destruct sts as [ | st sts]; first done. simpl.
      iDestruct "Hv" as "((%name & %st' & %ly & %Hst & %Hst' & %Hst'' & Hv) & Hvs)".
      injection Hst as [= ->].
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hly"; first done.
      apply Forall2_cons_inv_l in Hsts as ([name2 ly'] & lys' & [-> Hst] & Hsts & ->).
      simpl. assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      iPoseProof ("IH" with "[//] [] Hvs") as "%Hf".
      { iPureIntro. simpl in *. lia. }
      iPureIntro. econstructor; last done. split; done. }
    move: Hsts Hlen Hpad Hsize.
    generalize (sls_fields sls) as sts. generalize (sl_members sl) as mems.
    intros mems sts Hsts Hlen Hpad Hsize.
    iInduction mems as [ | [name ly] mems] "IH" forall (rts tys rs sts vs Hsts Hlen Hpad Hsize); first done.
    destruct name as [ name | ].
    - (* named field *)
      simpl in Hsts. apply Forall2_cons_inv_r in Hsts as ([name2 st] & sts' & [-> Hst] & Hsts & ->).
      destruct rts as [ | rt rts]; first done.
      inv_hlist tys. intros ty tys. destruct rs as [r rs].
      simpl. destruct vs as [ | v vs]; first done. simpl.
      iDestruct "Hv" as "((%name3 & %st' & %ly' & %Heq & %Hst1 & %Hst2 & Hv) & Hvs)".
      injection Heq as [= <- <-].
      assert (ly' = ly) as -> by by eapply (syn_type_has_layout_inj st).
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hly"; first done.
      rewrite -Hly.
      iSplitL "Hv".
      { iExists _, _. iR.  iR. iR. rewrite take_app. done. }
      rewrite drop_app.
      iApply ("IH" with "[//] [] [] [] Hvs").
      + simpl in *. iPureIntro. lia.
      + inversion Hpad. done.
      + simpl in Hsize. iPureIntro. rewrite /fmap. lia.
    - (* padding *)
      simpl in Hsts. simpl.
      iSplitR; first last.
      { rewrite drop_app'; first last. { rewrite replicate_length//. }
        iApply ("IH" with "[//] [//] [] [] Hv").
        - inversion Hpad. done.
        - simpl in Hsize. rewrite /fmap. iPureIntro. lia. }
      iExists tt, _. iR. iR.
      assert (syn_type_has_layout (UntypedSynType ly) ly).
      { apply syn_type_has_layout_untyped; first done.
        - inversion Hpad; subst. apply layout_wf_align_log_0. done.
        - simpl in Hsize. rewrite MaxInt_eq. lia.
        - apply ly_align_in_bounds_1. inversion Hpad; subst. done. }
      iR. rewrite take_app'; first last. { rewrite replicate_length//. }
      rewrite uninit_own_spec.
      iExists ly. iR.
      rewrite /has_layout_val replicate_length //.
  Qed.

  Lemma struct_zst_empty_typed π sls sl :
    struct_layout_spec_has_layout sls sl →
    sls.(sls_fields) = [] →
    sl.(sl_members) = [] →
    ⊢ zst_val ◁ᵥ{π} -[] @ struct_t sls +[].
  Proof.
    intros Hsl Hfields Hmem.
    rewrite /ty_own_val/=.
    iExists sl. iR. rewrite Hfields. iR.
    iSplitR. { iPureIntro. rewrite /has_layout_val /ly_size /layout_of Hmem //. }
    by rewrite Hmem.
  Qed.
End init.


Section copy.
  Context `{!typeGS Σ}.


  Local Instance struct_t_copy_pers {rts} (tys : hlist type rts) sls :
    TCHForall (λ _, Copyable) tys →
    ∀ π v r, Persistent (v ◁ᵥ{π} r @ struct_t sls tys).
  Proof.
    iIntros (Hcopy).
    iIntros (???).
      apply bi.exist_persistent => sl. apply bi_sep_persistent_pure_l => Halg.
      apply bi_sep_persistent_pure_l => Hlen. apply bi.sep_persistent; first apply _.
      apply big_sepL2_persistent_strong => _ k v' [rt [ty r']] Hlook1 Hlook2.
      apply pad_struct_lookup_Some in Hlook2 as (n & ly & ? & Hlook2); first last.
      { rewrite hpzipl_length. erewrite struct_layout_spec_has_layout_fields_length; done. }
      destruct Hlook2 as [[? Hlook2] | [-> Hlook2]].
      + apply hpzipl_lookup_inv_hzipl_pzipl in Hlook2 as [Hlook21 Hlook22].
        eapply TCHForall_nth_hzipl in Hcopy; last apply Hlook21.
        eapply bi.exist_persistent => r0.
        eapply bi.exist_persistent => ly'.
        eapply bi.sep_persistent.
        { apply _. }
        apply _.
      + injection Hlook2 => [= ? _] _ _; subst.
        apply existT_inj in Hlook2 as [= -> ->].
        simpl. apply _.
  Qed.

  Local Definition fields_size (fields : list (option string * layout)) :=
    sum_list (ly_size <$> fields.*2).

  (*
    Problem :
     I have the wands for all the components.
      At that point, I need to know that the na_own for all the components after are already there again.
      Go via index?

     Problem: place_rfn?

     Points here:
     - I get location ownership from the Copy lemma, with a different fraction for each element
     - In the end, I want struct_own_el_val for the elements
     - finally, I want to return the location ownership. I don't need to return the value ownership itself, because that is persistent.

     Options:
     - change copyable to be about same values. I can't think of a case where it would be relevant that the value can change. It anyways can't change because we only get one fraction.
     - take care to give back the same refinement
    => Just the values should be enough to link up.

     Procedure:
     1. apply the copy lemmas for all elements
     2.



     Problem: if I have struct_own_el_loc, I cannot link this up with the closing VS, since we need agreement on the values
      So I should directly pull the values.

   *)

  Lemma struct_t_copy_ind π (qs1 qs2 qs1' : list Qp) vs1 (tys1 : list (sigT (λ rt, type rt * place_rfn rt)%type)) (tys2 : list (sigT (λ rt, type rt * place_rfn rt)%type)) fields1 fields2 all_fields κ l E F  :
    Forall (λ ty, Copyable (projT2 ty).1) tys2 →
    lftE ∪ ↑shrN ⊆ E →
    all_fields = fields1 ++ fields2 →
    shr_locsE l (fields_size all_fields + 1) ⊆ F →
    length (named_fields fields2) = length tys2 →
    length (named_fields fields1) = length tys1 →
    length vs1 = length qs1 →
    length qs1 = length qs1' →
    length vs1 = length fields1 →
    rrust_ctx -∗
    na_own π (F ∖ shr_locsE l (fields_size fields1)) -∗
    ([∗ list] i↦ty;q ∈ pad_struct fields2 tys2 struct_make_uninit_type; qs2,
      struct_own_el_shr π κ (length fields1 + i) all_fields l (projT2 ty).2 (projT2 ty).1 ∗ q.[κ]) -∗

    (▷ [∗ list] i ↦ ty; '(v', q') ∈ pad_struct fields1 tys1 struct_make_uninit_type; zip vs1 qs1',
      struct_own_el_loc π q' v' i all_fields l (projT2 ty).2 (projT2 ty).1
    ) -∗

    ([∗ list] i ↦ v; '(q, q') ∈ vs1; (zip qs1 qs1'),
    na_own π (F ∖ shr_locsE l (fields_size (take (S i) all_fields))) -∗
      (▷ (l +ₗ offset_of_idx all_fields i) ↦{q'} v) ={E}=∗
      na_own π (F ∖ shr_locsE l (fields_size (take i all_fields) )) ∗ q.[κ]
    ) -∗

    |={E}=> ∃ qs2' vs2,
    ⌜length qs2' = length qs2⌝ ∗ ⌜length vs2 = length qs2⌝ ∗
    (* we get ownership of all the components *)
    (▷ [∗ list] i ↦ ty; '(v', q') ∈ pad_struct all_fields (tys1 ++ tys2) struct_make_uninit_type; zip (vs1 ++ vs2) (qs1' ++ qs2'),
        struct_own_el_loc π q' v' i all_fields l (projT2 ty).2 (projT2 ty).1) ∗
    (* if we give back the components, we get back the na token and lifetime tokens *)
    ([∗ list] i ↦ v; '(q, q') ∈ vs1 ++ vs2; (zip (qs1 ++ qs2) (qs1' ++ qs2')),
      na_own π (F ∖ shr_locsE l (fields_size (take (S i) all_fields))) -∗
      (▷ (l +ₗ offset_of_idx all_fields i) ↦{q'} v) ={E}=∗
      na_own π (F ∖ shr_locsE l (fields_size (take i all_fields))) ∗ q.[κ]
    ) ∗
    (*(([∗ list] i ↦ ty; q ∈ pad_struct all_fields (tys1 ++ tys2) (λ ly : layout, existT (unit : Type) (uninit (UntypedSynType ly), # ())); qs1' ++ qs2',*)
      (*▷ (l +ₗ offset_of_idx all_fields i) ↦{q}: ty_own_val (projT2 ty).1 π (projT2 ty).2) -∗*)
      (*na_own π (F ∖ shr_locsE l (fields_size all_fields)) ={E}=∗ na_own π F)*)
    (*∗*)
    na_own π (F ∖ shr_locsE l (fields_size all_fields)).
  Proof.
    iIntros (Hcopy ? Hf Hshr Hlen1 Hlen2 Hlen3 Hlen4 Hlen5) "#CTX Hna Hshr Hloc Hcl". subst all_fields.
    iInduction fields2 as [ | field2 fields2] "IH" forall (tys2 fields1 tys1 vs1 qs1 qs1' qs2 Hshr Hlen1 Hlen2 Hlen3 Hlen4 Hlen5 Hcopy); simpl.
    { destruct qs2; last done. iModIntro.
      iExists [], []. simpl. destruct tys2; last done.
      rewrite !right_id.
      iFrame. done. }

    destruct field2 as [[n | ] ly]; simpl.
    - (* named field *)
      destruct tys2 as [ | ty2 tys2]; simpl; first done.
      destruct qs2 as [ | q2 qs2]; first done.
      simpl. iDestruct "Hshr" as "((Hshr1 & Htok1) & Hshr)".
      inversion Hcopy; subst.
      (* now we share this element *)
      iDestruct "Hshr1" as "(%r'1 & %ly1 & Hrfn & %Hly1' & %Hly1 & Hsc & Hshr1)".
      assert (ly1 = ly) as ->.
      { move: Hly1'. rewrite !lookup_app_r; [ | lia..].
        rewrite !right_id !Nat.sub_diag. simpl. intros [= ->]; done. }

      iMod (copy_shr_acc with "CTX Hshr1 Hna Htok1") as "Ha".
      { done. }
      { done. }
      { simpl. rewrite right_id.
        rewrite /offset_of_idx /fields_size.
        rewrite -!fmap_take.
        rewrite take_app.
        eapply shr_locsE_offset; last done.
        - lia.
        - rewrite /fields_size !fmap_app !sum_list_with_app. simpl. lia.
      }
      iDestruct "Ha" as "(>%Hlyl & %q2' & %v1 & Hna & (Hl & Hv) & Hlcl)".
      rewrite difference_difference_l_L.
      set (fields1' := fields1 ++ [(Some n, ly)]).
      set (tys1' := tys1 ++ [ty2]).
      set (vs1' := vs1 ++ [v1]).
      set (qs1a := qs1 ++ [q2]).
      set (qs1a' := qs1' ++ [q2']).
      iPoseProof (ty_own_val_has_layout with "Hv") as "#Ha"; first done.
      iDestruct "Ha" as ">%Hlyv".
      iSpecialize ("IH" $! tys2 fields1' tys1' vs1' qs1a qs1a' qs2 with "[] [] [] [] [] [] [] [Hna] [Hshr] [Hloc Hl Hv Hrfn Hsc] [Hcl Hlcl]").
      { subst fields1'. rewrite -app_assoc. done. }
      { iPureIntro. simpl in *. lia. }
      { iPureIntro. simpl in *.  subst fields1' tys1'.
        move: Hlen2. rewrite !named_fields_field_names_length.
        rewrite /field_names omap_app/= !app_length /=. lia. }
      { iPureIntro. subst vs1' qs1a. rewrite !app_length/=. lia. }
      { iPureIntro. subst qs1a qs1a'. rewrite !app_length/=. lia. }
      { iPureIntro. subst vs1' fields1'. rewrite !app_length/=. lia. }
      { done. }
      { rewrite /fields1'.
        iEval (rewrite /fields_size !fmap_app sum_list_with_app /= !Nat.add_0_r).
        iEval (rewrite /offset_of_idx -!fmap_take Nat.add_0_r take_app) in "Hna".
        rewrite shr_locsE_add. done. }
      { (* need to shift the indices etc *)
        iPoseProof (big_sepL2_length with "Hshr") as "%Hlen7".
        iApply (big_sepL2_wand with "Hshr"). iApply big_sepL2_intro; first done.
        iModIntro. iIntros (? [? []] ? ? ?).
        rewrite /struct_own_el_shr. simpl.
        iIntros "((% & % & ? & Hlook & ? & ? & Hl) & $)".
        iExists _, _. iFrame.
        rewrite /fields1' app_length -Nat.add_assoc -!app_assoc/=. iFrame. }
      { iNext. subst tys1' fields1' vs1' qs1a'.
        rewrite zip_app; last lia.
        rewrite pad_struct_snoc_Some; first last.
        { move: Hlen2. rewrite !named_fields_field_names_length. lia. }
        iApply (big_sepL2_app with "[Hloc]").
        { rewrite -app_assoc. done. }
        simpl. iSplitL; last done.
        rewrite /struct_own_el_loc.
        iExists _, _. iFrame "∗ %".
        iSplitR. {
          iPureIntro. rewrite pad_struct_length. rewrite lookup_app_l.
          - rewrite !lookup_app_r; [ | lia..]. rewrite !right_id !Nat.sub_diag//.
          - rewrite app_length/=. lia.
        }
        rewrite pad_struct_length -app_assoc/=. iFrame.
      }
      { rewrite /vs1' /qs1a /qs1a'.
        rewrite zip_app; last done.
        subst fields1'. rewrite -!app_assoc.
        iApply (big_sepL2_app with "Hcl").
        simpl. iSplitL; last done.
        iIntros "Hna Hl".
        rewrite Hlen5.
        iMod ("Hlcl" with "[Hna] Hl") as "(Hna & $)".
        - iEval (rewrite /fields_size (app_assoc _ [_]) Nat.add_0_r) in "Hna".
          rewrite take_app'; first last. { rewrite app_length/=. lia. }
          rewrite !fmap_app sum_list_with_app /= Nat.add_0_r.
          rewrite shr_locsE_add.
          iEval (rewrite /offset_of_idx Nat.add_0_r -!fmap_take take_app).
          done.
        - iModIntro. iEval (rewrite /fields_size Nat.add_0_r take_app). done.
      }
      { iMod "IH" as "(%qs2' & %vs2 & % & % & Hl & Hcl & Hna)".
        iModIntro. iExists (q2' :: qs2'), (v1 :: vs2).
        rewrite /vs1'/qs1a'/= -!app_assoc /=. iFrame.
        iPureIntro. split; lia.
      }
    - (* unnamed fields *)
      (*destruct tys2 as [ | ty2 tys2]; simpl; first done.*)
      destruct qs2 as [ | q2 qs2]; first done.
      simpl. iDestruct "Hshr" as "((Hshr1 & Htok1) & Hshr)".
      (* now we share this element *)
      iDestruct "Hshr1" as "(%r'1 & %ly1 & Hrfn & %Hly1' & %Hly1 & Hsc & Hshr1)".
      assert (ly1 = ly) as ->.
      { move: Hly1'. rewrite !lookup_app_r; [ | lia..].
        rewrite !right_id !Nat.sub_diag. simpl. intros [= ->]; done. }

      iMod (copy_shr_acc with "CTX Hshr1 Hna Htok1") as "Ha".
      { done. }
      { done. }
      { simpl. rewrite right_id.
        rewrite /offset_of_idx /fields_size.
        rewrite -!fmap_take.
        rewrite take_app.
        eapply shr_locsE_offset; last done.
        - lia.
        - rewrite /fields_size !fmap_app !sum_list_with_app. simpl. lia.
      }
      iDestruct "Ha" as "(>%Hlyl & %q2' & %v1 & Hna & (Hl & Hv) & Hlcl)".
      rewrite difference_difference_l_L.
      set (fields1' := fields1 ++ [(None, ly)]).
      (*set (tys1' := tys1 ++ [ty2]).*)
      set (vs1' := vs1 ++ [v1]).
      set (qs1a := qs1 ++ [q2]).
      set (qs1a' := qs1' ++ [q2']).
      iPoseProof (ty_own_val_has_layout with "Hv") as "#Ha"; first done.
      iDestruct "Ha" as ">%Hlyv".
      iSpecialize ("IH" $! tys2 fields1' tys1 vs1' qs1a qs1a' qs2 with "[] [] [] [] [] [] [] [Hna] [Hshr] [Hloc Hl Hv Hrfn Hsc] [Hcl Hlcl]").
      { subst fields1'. rewrite -app_assoc. done. }
      { iPureIntro. simpl in *. lia. }
      { iPureIntro. simpl in *.  subst fields1'.
        move: Hlen2. rewrite !named_fields_field_names_length.
        rewrite /field_names omap_app/= !app_length /=. lia. }
      { iPureIntro. subst vs1' qs1a. rewrite !app_length/=. lia. }
      { iPureIntro. subst qs1a qs1a'. rewrite !app_length/=. lia. }
      { iPureIntro. subst vs1' fields1'. rewrite !app_length/=. lia. }
      { iPureIntro. done. }
      { rewrite /fields1'.
        iEval (rewrite /fields_size !fmap_app sum_list_with_app /= !Nat.add_0_r).
        iEval (rewrite /offset_of_idx -!fmap_take Nat.add_0_r take_app) in "Hna".
        rewrite shr_locsE_add. done. }
      { (* need to shift the indices etc *)
        iPoseProof (big_sepL2_length with "Hshr") as "%Hlen7".
        iApply (big_sepL2_wand with "Hshr"). iApply big_sepL2_intro; first done.
        iModIntro. iIntros (? [? []] ? ? ?).
        rewrite /struct_own_el_shr. simpl.
        iIntros "((% & % & ? & Hlook & ? & ? & Hl) & $)".
        iExists _, _. iFrame.
        rewrite /fields1' app_length -Nat.add_assoc -!app_assoc/=. iFrame. }
      { iNext. subst fields1' vs1' qs1a'.
        rewrite zip_app; last lia.
        rewrite pad_struct_snoc_None; first last.
        iApply (big_sepL2_app with "[Hloc]").
        { rewrite -app_assoc. done. }
        simpl. iSplitL; last done.
        rewrite /struct_own_el_loc.
        iExists _, _. iFrame "∗ %".
        iSplitR. {
          iPureIntro. rewrite pad_struct_length. rewrite lookup_app_l.
          - rewrite !lookup_app_r; [ | lia..]. rewrite !right_id !Nat.sub_diag//.
          - rewrite app_length/=. lia.
        }
        rewrite pad_struct_length -app_assoc/=. iFrame.
      }
      { rewrite /vs1' /qs1a /qs1a'.
        rewrite zip_app; last done.
        subst fields1'. rewrite -!app_assoc.
        iApply (big_sepL2_app with "Hcl").
        simpl. iSplitL; last done.
        iIntros "Hna Hl".
        rewrite Hlen5.
        iMod ("Hlcl" with "[Hna] Hl") as "(Hna & $)".
        - iEval (rewrite /fields_size (app_assoc _ [_]) Nat.add_0_r) in "Hna".
          rewrite take_app'; first last. { rewrite app_length/=. lia. }
          rewrite !fmap_app sum_list_with_app /= Nat.add_0_r.
          rewrite shr_locsE_add.
          iEval (rewrite /offset_of_idx Nat.add_0_r -!fmap_take take_app).
          done.
        - iModIntro. iEval (rewrite /fields_size Nat.add_0_r take_app). done.
      }
      { iMod "IH" as "(%qs2' & %vs2 & % & % & Hl & Hcl & Hna)".
        iModIntro. iExists (q2' :: qs2'), (v1 :: vs2).
        rewrite /vs1'/qs1a'/= -!app_assoc /=. iFrame.
        iPureIntro. split; lia.
      }
  Qed.

  Lemma struct_t_copy_ind' π (qs : list Qp) (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) fields κ l E F  :
    Forall (λ ty, Copyable (projT2 ty).1) tys →
    lftE ∪ ↑shrN ⊆ E →
    shr_locsE l (fields_size fields + 1) ⊆ F →
    length (named_fields fields) = length tys →
    rrust_ctx -∗
    na_own π F -∗
    ([∗ list] i↦ty;q ∈ pad_struct fields tys struct_make_uninit_type; qs,
      struct_own_el_shr π κ i fields l (projT2 ty).2 (projT2 ty).1 ∗ q.[κ]) -∗
    |={E}=> ∃ qs' vs,
    ⌜length qs' = length qs⌝ ∗ ⌜length vs = length qs⌝ ∗
    (* we get ownership of all the components *)
    (▷ [∗ list] i ↦ ty; '(v', q') ∈ pad_struct fields tys struct_make_uninit_type; zip vs qs',
        struct_own_el_loc π q' v' i fields l (projT2 ty).2 (projT2 ty).1) ∗
    (* if we give back the components, we get back the na token and lifetime tokens *)
    ([∗ list] i ↦ v; '(q, q') ∈ vs; zip qs qs',
      na_own π (F ∖ shr_locsE l (fields_size (take (S i) fields))) -∗
      (▷ (l +ₗ offset_of_idx fields i) ↦{q'} v) ={E}=∗
      na_own π (F ∖ shr_locsE l (fields_size (take i fields))) ∗ q.[κ]
    ) ∗
    na_own π (F ∖ shr_locsE l (fields_size fields)).
  Proof.
    iIntros (????) "CTX Hna Hloc".
    iMod (struct_t_copy_ind _ [] qs [] [] [] tys [] fields fields  with "CTX [Hna] Hloc [] []") as "Ha".
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { done. }
    { simpl. rewrite difference_empty_L. done. }
    { iNext. done. }
    { done. }
    simpl. done.
  Qed.


  Lemma struct_t_copy_acc π (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) fields q κ l E F  :
    Forall (λ ty, Copyable (projT2 ty).1) tys →
    lftE ∪ ↑shrN ⊆ E →
    shr_locsE l (fields_size fields + 1) ⊆ F →
    length (named_fields fields) = length tys →
    rrust_ctx -∗
    na_own π F -∗
    q.[κ] -∗
    ([∗ list] i↦ty ∈ pad_struct fields tys struct_make_uninit_type, struct_own_el_shr π κ i fields l (projT2 ty).2 (projT2 ty).1) -∗
    |={E}=> ∃ q' vs,
    ⌜length vs = length fields⌝ ∗
    (* we get ownership of all the components *)
    (▷ [∗ list] i ↦ ty; v' ∈ pad_struct fields tys struct_make_uninit_type; vs,
        struct_own_el_loc π q' v' i fields l (projT2 ty).2 (projT2 ty).1) ∗
    (* if we give back the components, we get back the na token and lifetime tokens *)
    (([∗ list] i ↦ v ∈ vs, (▷ (l +ₗ offset_of_idx fields i) ↦{q'} v)) -∗
     na_own π (F ∖ shr_locsE l (fields_size fields)) ={E}=∗
     na_own π F ∗ q.[κ]) ∗
    na_own π (F ∖ shr_locsE l (fields_size fields)).
  Proof.
    iIntros (????) "#CTX Hna Htok Hloc".
    iPoseProof (Fractional_split_big_sepL (λ q, q.[κ])%I (length fields) with "Htok") as "(%qs & %Hlen_eq & Htoks & Htoks_cl)".
    iMod (struct_t_copy_ind' with "CTX Hna [Hloc Htoks]") as "(%qs' & %vs & %Hlen1 & %Hlen2 & Hloc & Hcl & Hna)"; [ done.. | | ].
    { iApply big_sepL2_sep. iSplitL "Hloc".
      1: iApply big_sepL_extend_r; last done.
      2: iApply big_sepL_extend_l; last iApply "Htoks".
      all: rewrite pad_struct_length; done. }

    set (q' := foldr Qp.min 1%Qp qs').
    assert (∀ i q, qs' !! i = Some q → (q' ≤ q)%Qp) as Hmin.
    { intros i q0 Hlook.
      induction qs' as [ | q2 qs' IH] in i, Hlook, q' |-*; first done.
      subst q'. destruct i as [ | i]; simpl in *.
      - injection Hlook as ->. apply Qp.le_min_l.
      - etrans;first  apply Qp.le_min_r. by eapply IH.  }

    iAssert (([∗ list] i↦ty;vq ∈ pad_struct fields tys struct_make_uninit_type; zip vs qs',
       ▷ struct_own_el_loc π q' vq.1 i fields l (projT2 ty).2 (projT2 ty).1 ∗
      (▷ (l +ₗ offset_of_idx fields i) ↦{q'} vq.1 -∗ ▷ (l +ₗ offset_of_idx fields i) ↦{vq.2} vq.1)))%I with "[Hloc]" as "Hloc".
    { rewrite big_sepL2_later; first last. { rewrite pad_struct_length zip_with_length. lia. }
      iApply (big_sepL2_wand with "Hloc"). iApply big_sepL2_intro. { rewrite pad_struct_length zip_with_length. lia. }
      iModIntro. iIntros (k [rt [ty r]] [v q''] Hlook1 Hlook2) "Hloc".
      simpl. rewrite /struct_own_el_loc.
      iDestruct "Hloc" as "(%r' & %ly & Hrfn & Hlook & Hst & Hty & Hl & Hlyv & Hv)".
      iPoseProof (Fractional_fractional_le (λ q, _) q'' q' with "Hl") as "(Hl & Hal)".
      { eapply (Hmin k). apply lookup_zip in Hlook2. apply Hlook2. }
      iFrame. iNext. eauto with iFrame.
    }

    rewrite big_sepL2_sep. iDestruct "Hloc" as "(Hloc & Hcl_loc)".
    iPoseProof (big_sepL2_elim_l with "Hcl_loc") as "Hcl_loc".
    rewrite -big_sepL2_later; first last. { rewrite pad_struct_length zip_with_length. lia. }
    rewrite -(big_sepL2_fmap_r (λ x, x.1) (λ _ _ y2, struct_own_el_loc _ _ y2 _ _ _ _ _)).
    rewrite fst_zip; first last. { lia. }

    iModIntro. iExists q', vs. iFrame.
    iSplitR. { iPureIntro. lia. }


    iIntros "Hloc Hna".
    iPoseProof (big_sepL2_length with "Hcl") as "%Hlen".
    rewrite zip_with_length in Hlen.
    iPoseProof (big_sepL2_to_zip with "Hcl") as "Hcl".
    rewrite [zip qs qs']zip_flip zip_fmap_r zip_assoc_r -list_fmap_compose big_sepL_fmap.

    iPoseProof (big_sepL_extend_r qs with "Hcl_loc") as "Hcl_loc".
    { rewrite zip_with_length. lia. }
    iPoseProof (big_sepL2_to_zip with "Hcl_loc") as "Hcl_loc".
    iPoseProof (big_sepL_sep_2 with "Hcl Hcl_loc") as "Hcl".

    iPoseProof (big_sepL_extend_r qs' with "Hloc") as "Hloc".
    { lia. }
    iPoseProof (big_sepL2_to_zip with "Hloc") as "Hloc".
    iPoseProof (big_sepL_extend_r qs with "Hloc") as "Hloc".
    { rewrite zip_with_length. lia. }
    iPoseProof (big_sepL2_to_zip with "Hloc") as "Hloc".
    iPoseProof (big_sepL_sep_2 with "Hcl Hloc") as "Hcl".
    rewrite zip_assoc_l big_sepL_fmap.
    iAssert ([∗ list] i ↦ y ∈ qs, na_own π (F ∖ shr_locsE l (fields_size (take (S i) fields))) ={E}=∗ na_own π (F ∖ shr_locsE l (fields_size (take i fields))) ∗ (y).[κ])%I with "[Hcl]" as "Hcl".
    { iApply big_sepL2_elim_l. iApply big_sepL2_from_zip; first last.
      { iApply (big_sepL2_elim_l). iApply big_sepL2_from_zip; first last.
        { iApply (big_sepL_wand with "Hcl").
          iApply big_sepL_intro. iModIntro. iIntros (k [v [q1' q1]] Hlook) "Ha Hna"; simpl.
          iDestruct "Ha" as "((Ha & Hcl) & Hl)".
          iPoseProof ("Hcl" with "Hl") as "Hl".
          iApply ("Ha" with "Hna Hl"). }
        rewrite zip_with_length. lia. }
      lia. }

    (* now collapse the whole sequence *)
    set (P i := (|={E}=> (na_own π (F ∖ shr_locsE l (fields_size (take i fields))) ∗ [∗ list] q ∈ (drop i qs), q.[κ]))%I).
    iPoseProof (big_sepL_eliminate_sequence_rev P  with "Hcl [Hna] []") as "Ha".
    { iModIntro. rewrite drop_all. iSplitL; last done.
      assert (length qs = length fields) as -> by lia. rewrite firstn_all. iFrame.
    }
    { rewrite /P. iModIntro. iIntros (i q1 Hlook) ">(Hna & Htoks) Hvs".
      iMod ("Hvs" with "Hna") as "(Hna & Htok)".
      iFrame. erewrite (drop_S _ _ i); last done; simpl. by iFrame.
    }
    iMod "Ha" as "(Hna & Htoks)".
    iPoseProof ("Htoks_cl" with "Htoks") as "$".
    simpl. rewrite difference_empty_L. done.
  Qed.

  Global Instance struct_t_copy {rts} (tys : hlist type rts) sls :
    TCHForall (λ _, Copyable) tys →
    Copyable (struct_t sls tys).
  Proof.
    iIntros (Hcopy). split; first apply _.
    iIntros (κ π E F l ly r q ? Halg ?) "#CTX Hshr Hna Htok".
    rewrite /ty_shr /=.
    iDestruct "Hshr" as (sl) "(%Halg' & %Hlen & %Hly & #Hlb & #Hb)".
    simpl in Halg.
    specialize (use_struct_layout_alg_Some_inv _ _ Halg') as Halg2.
    assert (ly = sl) as -> by by eapply syn_type_has_layout_inj.
    iR.
    iMod (struct_t_copy_acc _ (hpzipl rts tys r) (sl_members sl) with "CTX Hna Htok Hb") as "(%q' & %vs & % & Hs & Hcl & Hna)".
    { clear -Hcopy. induction rts as [ | rt rts IH] in tys, r, Hcopy |-*; simpl.
      - inv_hlist tys. destruct r. constructor.
      - inv_hlist tys => ty tys. destruct r as [r1 r].
        inversion 1. subst. repeat match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end. subst.
        econstructor; first done. by apply IH.
    }
    { done. }
    { done. }
    { rewrite hpzipl_length. rewrite named_fields_field_names_length. erewrite struct_layout_spec_has_layout_fields_length; done. }

    (* now we need to pull the pointsto *)
    (*iPoseProof (big_sepL2_impl _ (λ i (ty : sigT (λ rt : Type, type rt * place_rfn rt)%type) v', struct_own_el_loc' _ π q' v' i (sl_members sl) l (projT2 ty).2 (projT2 ty).1) with "Hs") as "Hs".*)
    iAssert ((|={E}=> ∃ lys, ⌜length lys = length vs⌝ ∗ ▷ [∗ list] i↦ty;v' ∈ pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type;(zip vs lys),
      struct_own_el_loc' π q' v'.1 i (sl_members sl) l (projT2 ty).2 (projT2 ty).1 v'.2)%I) with "[Hs]" as ">(%lys & % & Hs)".
    { iAssert ((▷ ([∗ list] i↦ty;v' ∈ pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type;vs,
        ∃ ly : layout, struct_own_el_loc' π q' v' i (sl_members sl) l (projT2 ty).2 (projT2 ty).1 ly))%I) with "[Hs]" as "Hs".
        { iNext.  iApply (big_sepL2_wand with "Hs"). iApply big_sepL2_intro. { rewrite pad_struct_length. lia. }
          iModIntro. iIntros (? [? []] ? ? ?) "(% & % & ? & ? & ? & ? & ? & ? & ?)". rewrite /struct_own_el_loc'. eauto with iFrame. }
        rewrite big_sepL2_exists_r. iDestruct "Hs" as "(%l3 & >%Hlen2 & Ha)".
        iExists l3. iR. iModIntro. iNext. done. }
    iPoseProof (struct_own_val_extract_mapsto' with "Hlb Hs") as "(Hl & >%Hlyv & Hs)".
    { done. }
    { rewrite hpzipl_length. done. }

    rewrite fst_zip in Hlyv; last lia.
    iExists q', (mjoin vs). simpl. iFrame.
    iSplitL "Hl Hs".
    { iModIntro. iNext. rewrite fst_zip; last lia. iFrame. iExists _. iR. iR.
      iSplitR. { iPureIntro. by apply mjoin_has_struct_layout. }
      done. }
    iModIntro. iIntros "Hna Hpts".
    iApply ("Hcl" with "[Hpts]"); last done.
    iApply big_sepL_later. iNext. rewrite heap_mapsto_reshape_sl; last by apply mjoin_has_struct_layout.
    iDestruct "Hpts" as "(_ & Hpts)". rewrite reshape_join; first done.
    rewrite Forall2_fmap_r. eapply Forall2_impl; first done.
    done.
  Qed.

End copy.

Section subtype.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Definition struct_t_incl_precond {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 :=
    ([∗ list] t1; t2 ∈ hpzipl _ tys1 rs1; hpzipl _ tys2 rs2,
      match (projT2 t1).2, (projT2 t2).2 with
      | #r1, #r2 => type_incl r1 r2 (projT2 t1).1 (projT2 t2).1
      | _, _ => ∃ (Heq : projT1 t1 = projT1 t2), ⌜(projT2 t1).2 = rew <-Heq in (projT2 t2).2⌝ ∗ ∀ (r : projT1 t1), type_incl r (rew [id] Heq in r) (projT2 t1).1 (projT2 t2).1
      end)%I.
  Global Instance struct_t_incl_precond_pers {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 :
    Persistent (struct_t_incl_precond tys1 tys2 rs1 rs2).
  Proof.
    apply big_sepL2_persistent. intros ? [? [? []]] [? [? []]]; simpl; apply _.
  Qed.

  Lemma struct_t_own_val_mono {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls v π :
    struct_t_incl_precond tys1 tys2 rs1 rs2 -∗
    v ◁ᵥ{π} rs1 @ struct_t sls tys1 -∗
    v ◁ᵥ{π} rs2 @ struct_t sls tys2.
  Proof.
    iIntros "#Hincl Hv".
    iPoseProof (big_sepL2_length with "Hincl") as "%Hlen".
    rewrite !hpzipl_length in Hlen.
    iDestruct "Hv" as "(%sl & %Halg & %Hlen1 & %Hly & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR.
    iApply (big_sepL2_impl' with "Hb").
    { done. }
    { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k v1 [rt1 [ty1 r1]] v2 [rt2 [ty2 r2]] Hlook_v1 Hlook_ty1 Hlook_v2 Hlook_ty2) "Hv".
    iDestruct "Hv" as "(%r' & %ly & Hrfn & %Hly' & %Hst' & Hv)".
    rewrite Hlook_v2 in Hlook_v1. injection Hlook_v1 as ->.
    apply pad_struct_lookup_Some in Hlook_ty1 as (n & ly' & Hly'' & Hlook_ty1).
    2: { rewrite hpzipl_length Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    rewrite Hly'' in Hly'. injection Hly' as ->.
    eapply pad_struct_lookup_Some_1' in Hlook_ty2; last done; first last.
    { rewrite hpzipl_length -Hlen Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    destruct Hlook_ty1 as [ [? Hlook_ty1] | (-> & Hlook_ty1)]; first last.
    { (* padding *)
      destruct Hlook_ty2 as [ [? ?] | [_ Hlook_ty2]]; first congruence.
      injection Hlook_ty1 => _ _ ?; subst.
      injection Hlook_ty2 => _ _ ?; subst.
      apply existT_inj in Hlook_ty1. injection Hlook_ty1 as -> ->.
      apply existT_inj in Hlook_ty2. injection Hlook_ty2 as -> ->.
      iExists r', ly. rewrite Hly''. iFrame. done. }
    (* element *)
    destruct Hlook_ty2 as [[_ Hlook_ty2] | [? _]]; last congruence.
    rewrite /struct_own_el_val.
    iPoseProof (big_sepL2_lookup with "Hincl") as "Ha"; [apply Hlook_ty1 | apply Hlook_ty2 | ]; simpl.
    destruct r1 as [r1 | ]; first destruct r2 as [r2 | ].
    + iDestruct "Hrfn" as "<-".
      iDestruct "Ha" as "(%Hst & _ & #Ha & _)". iPoseProof ("Ha" with "Hv") as "Hv".
      rewrite Hly'' -Hst. eauto with iFrame.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst.
      iDestruct "Hrfn" as "<-". done.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst. cbn in Heq'. subst.
      iDestruct ("Ha" $! r') as "(%Hst & _ & #Ha' & _)". iPoseProof ("Ha'" with "Hv") as "Hv".
      rewrite Hly'' -Hst. eauto with iFrame.
  Qed.

  Lemma struct_t_shr_mono {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls l κ π :
    struct_t_incl_precond tys1 tys2 rs1 rs2 -∗
    l ◁ₗ{π, κ} rs1 @ struct_t sls tys1 -∗
    l ◁ₗ{π, κ} rs2 @ struct_t sls tys2.
  Proof.
    iIntros "#Hincl Hl".
    iPoseProof (big_sepL2_length with "Hincl") as "%Hlen".
    rewrite !hpzipl_length in Hlen.
    iDestruct "Hl" as "(%sl & %Halg & %Hlen1 & %Hly & #Hlb & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR. iR.
    iApply (big_sepL_impl' with "Hb").
    { rewrite !pad_struct_length //. }
    iModIntro.
    iIntros (k [rt1 [ty1 r1]] [rt2 [ty2 r2]] Hlook_ty1 Hlook_ty2) "Hl".
    iDestruct "Hl" as "(%r' & %ly & Hrfn & %Hly' & %Hst' & #Hsc1 & Hl)".
    apply pad_struct_lookup_Some in Hlook_ty1 as (n & ly' & Hly'' & Hlook_ty1).
    2: { rewrite hpzipl_length Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    rewrite Hly'' in Hly'. injection Hly' as ->.
    eapply pad_struct_lookup_Some_1' in Hlook_ty2; last done; first last.
    { rewrite hpzipl_length -Hlen Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    destruct Hlook_ty1 as [ [? Hlook_ty1] | (-> & Hlook_ty1)]; first last.
    { (* padding *)
      destruct Hlook_ty2 as [ [? ?] | [_ Hlook_ty2]]; first congruence.
      injection Hlook_ty1 => _ _ ?; subst.
      injection Hlook_ty2 => _ _ ?; subst.
      apply existT_inj in Hlook_ty1. injection Hlook_ty1 as -> ->.
      apply existT_inj in Hlook_ty2. injection Hlook_ty2 as -> ->.
      iExists r', ly. rewrite Hly''. iFrame. simpl. done. }
    (* element *)
    destruct Hlook_ty2 as [[_ Hlook_ty2] | [? _]]; last congruence.
    iPoseProof (big_sepL2_lookup with "Hincl") as "Ha"; [apply Hlook_ty1 | apply Hlook_ty2 | ]; simpl.
    rewrite /struct_own_el_shr.
    destruct r1 as [r1 | ]; first destruct r2 as [r2 | ].
    + iDestruct "Hrfn" as "<-".
      iDestruct "Ha" as "(%Hst & #Hsc & _ & #Ha)". iPoseProof ("Ha" with "Hl") as "Hl".
      iPoseProof ("Hsc" with "Hsc1") as "Hsc2".
      rewrite Hly'' -Hst. iFrame "#". eauto with iFrame.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst.
      iDestruct "Hrfn" as "<-". done.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst. cbn in Heq'. subst.
      iDestruct ("Ha" $! r') as "(%Hst & #Hsc & _ & #Ha')". iPoseProof ("Ha'" with "Hl") as "Hl".
      iPoseProof ("Hsc" with "Hsc1") as "Hsc2".
      rewrite Hly'' -Hst. iFrame "#". eauto with iFrame.
  Qed.

  Lemma struct_t_type_incl {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls :
    struct_t_incl_precond tys1 tys2 rs1 rs2 -∗
    type_incl rs1 rs2 (struct_t sls tys1) (struct_t sls tys2).
  Proof.
    iIntros "#Hincl".
    iPoseProof (big_sepL2_length with "Hincl") as "%Hlen".
    rewrite !hpzipl_length in Hlen.
    iSplitR; first done. iSplitR. { simpl. rewrite Hlen. done. }
    iSplit; iModIntro.
    - iIntros (??). by iApply struct_t_own_val_mono.
    - iIntros (???). by iApply struct_t_shr_mono.
  Qed.

  Lemma struct_t_full_subtype E L {rts} (tys1 : hlist type rts) (tys2 : hlist type rts) sls :
    Forall (λ '(existT _ (ty1, ty2)), full_subtype E L ty1 ty2) (hzipl2 _ tys1 tys2) →
    full_subtype E L (struct_t sls tys1) (struct_t sls tys2).
  Proof.
    intros Hsubt r. iIntros (?) "HL #HE".
    iApply struct_t_type_incl.
    iApply big_sepL2_forall.
    { intros ? [? [? []]] [? [? []]]; apply _. }
    iSplit. { iPureIntro. rewrite !hpzipl_length. done. }
    iIntros (? [rt1 [ty1 r1]] [rt2 [ty2 r2]] Hlook1 Hlook2); simpl.
    specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook1) as Hlook1'.
    specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook2) as Hlook2'.
    rewrite Hlook2' in Hlook1'. injection Hlook1' as ->.
    apply hpzipl_lookup_inv_hzipl_pzipl in Hlook1 as (Hlook11 & Hlook12).
    apply hpzipl_lookup_inv_hzipl_pzipl in Hlook2 as (Hlook21 & Hlook22).
    rewrite Hlook22 in Hlook12. injection Hlook12 as [= <-%existT_inj].
    efeed pose proof (hzipl_hzipl2_lookup _ tys1 tys2) as Hlook; [done.. | ].
    specialize (Forall_lookup_1 _ _ _ _ Hsubt Hlook) as Hx.
    iPoseProof (full_subtype_acc_noend with "HE HL") as "Ha"; first apply Hx.
    destruct r2.
    - iApply "Ha".
    - iExists eq_refl. iR. done.
  Qed.
End subtype.

Section subltype.
  Context `{!typeGS Σ}.
  Local Lemma pad_struct_hpzipl_2_inv {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) (rs1 : plist place_rfn rts1) (rs2 : plist place_rfn rts2) sl f k lt1 lt2 :
    length rts1 = length rts2 →
    pad_struct (sl_members sl) (hpzipl rts1 lts1 rs1) f !! k = Some lt1 →
    pad_struct (sl_members sl) (hpzipl rts2 lts2 rs2) f !! k = Some lt2 →
    (∃ rt1 rt2 lt1' lt2' r1 r2,
      lt1 = existT rt1 (lt1', r1) ∧ lt2 = existT rt2 (lt2', r2) ∧
      hpzipl _ lts1 rs1 !! field_idx_of_idx (sl_members sl) k = Some (existT rt1 (lt1', r1)) ∧
      hpzipl _ lts2 rs2 !! field_idx_of_idx (sl_members sl) k = Some (existT rt2 (lt2', r2))) ∨
    (∃ ly, lt1 = f ly ∧ lt2 = f ly).
  Proof.
    intros Hlen Hlook1 Hlook2.
    apply pad_struct_lookup_Some_1 in Hlook1.
    destruct Hlook1 as (n & ly & Hmem & Hlook1).
    destruct Hlook1 as [ [ ? Hlook1] | Hlook1].
    - apply pad_struct_lookup_Some_1 in Hlook2.
      destruct Hlook2 as (n' & ly' & Hmem' & Hlook2). simplify_eq.
      destruct Hlook2 as [ (_ & Hlook2) | (Hc & _) ]; first last.
      { destruct Hc as [ | Hc]; first done.
        exfalso. apply lookup_lt_Some in Hlook1.
        move: Hc Hlook1. rewrite !hpzipl_length. lia. }
      destruct lt1 as [rt1 [lt1 r1]]. destruct lt2 as [rt2 [lt2 r2]].
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook1) as Hrt1.
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook2) as Hrt2.
      left. eauto 10.
    - destruct Hlook1 as (Hnone & ->).
      erewrite pad_struct_lookup_field_None_2 in Hlook2; [ | done | reflexivity | ]; first last.
      { move : Hnone. rewrite !hpzipl_length Hlen. done. }
      injection Hlook2 as [= <-]. eauto.
  Qed.
  Local Lemma pad_struct_hpzipl_2_inv' {rts} (lts1 lts2 : hlist ltype rts) (rs : plist place_rfn rts) sl f k lt1 lt2 :
    pad_struct (sl_members sl) (hpzipl rts lts1 rs) f !! k = Some lt1 →
    pad_struct (sl_members sl) (hpzipl rts lts2 rs) f !! k = Some lt2 →
    (∃ rt lt1' lt2' r,
      lt1 = existT rt (lt1', r) ∧ lt2 = existT rt (lt2', r) ∧
      hzipl2 rts lts1 lts2 !! field_idx_of_idx (sl_members sl) k = Some (existT rt (lt1', lt2'))) ∨
    (∃ ly, lt1 = f ly ∧ lt2 = f ly).
  Proof.
    intros Hlook1 Hlook2.
    apply pad_struct_lookup_Some_1 in Hlook1.
    destruct Hlook1 as (n & ly & Hmem & Hlook1).
    destruct Hlook1 as [ [ ? Hlook1] | Hlook1].
    - apply pad_struct_lookup_Some_1 in Hlook2.
      destruct Hlook2 as (n' & ly' & Hmem' & Hlook2). simplify_eq.
      destruct Hlook2 as [ (_ & Hlook2) | (Hc & _) ]; first last.
      { destruct Hc as [ | Hc]; first done.
        exfalso. apply lookup_lt_Some in Hlook1.
        move: Hc Hlook1. rewrite !hpzipl_length. lia. }
      destruct lt1 as [rt1 [lt1 r1]]. destruct lt2 as [rt2 [lt2 r2]].
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook1) as Hrt1.
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook2) as Hrt2.
      rewrite Hrt1 in Hrt2. injection Hrt2 as [= <-].
      specialize (hpzipl_hzipl2_lookup _ _ _ _ _ _ _ _ _ Hlook1 Hlook2) as Hlook. simpl in Hlook.
      specialize (hpzipl_hpzipl_lookup_2_eq _ _ _ _ _ _ _ _ _ _ Hlook1 Hlook2) as ->.
      eauto 10.
    - destruct Hlook1 as (Hnone & ->).
      erewrite pad_struct_lookup_field_None_2 in Hlook2; [ | done | reflexivity | ]; first last.
      { move : Hnone. rewrite !hpzipl_length. done. }
      injection Hlook2 as [= <-]. eauto.
  Qed.

  Local Lemma struct_ltype_incl'_shared_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) κ' rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2,
      ltype_incl (Shared κ') (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl' (Shared κ') #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iPoseProof (big_sepL2_length with "Heq") as "%Hlen".
    rewrite !hpzipl_length in Hlen.
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen1 & %Hly & Hlb & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)". iExists rs2. iFrame.
    iDestruct "Hb" as "#Hb". iDestruct "Hrfn" as "<-". iSplitR; first done.
    iModIntro. iMod "Hb". iModIntro.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv _ _ _ _ _ _ _ _ _ Hlen Hlook1 Hlook2) as
      [ (rt1 & rt2 & lt1' & lt2' & r1 & r2 & -> & -> & Hlook1' & Hlook2') | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL2_lookup with "Heq") as "Hb"; [done.. | ]. simpl.
    iDestruct "Hb" as "(%Hst & #Hb & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iApply "Hb".
  Qed.
  Lemma struct_ltype_incl_shared_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) κ' rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2,
      ltype_incl (Shared κ') (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl (Shared κ') #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_shared_in).
    - done.
    - rewrite !hpzipl_hmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
        iIntros (k [rt1 [lt1 r1]] [rt2 [lt2 r2]] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_shared {rts} (lts1 lts2 : hlist ltype rts) κ' rs sls :
    (([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Shared κ') r r (projT2 ltp).1 (projT2 ltp).2)) -∗
    ltype_incl' (Shared κ') rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & Hb)".
    iExists sl. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)". iExists r'. iFrame.
    iDestruct "Hb" as "#Hb".
    iModIntro. iMod "Hb". iModIntro.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
      [ (rt & lt1' & lt2' & r & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
    iDestruct ("Hb" $! r) as "(%Hst & #Hb' & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iApply "Hb'".
  Qed.
  Lemma struct_ltype_incl_shared {rts} (lts1 lts2 : hlist ltype rts) κ' rs sls :
    ([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Shared κ') r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl (Shared κ') rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_shared).
    - done.
    - rewrite hzipl2_fmap big_sepL_fmap. iApply (big_sepL_mono with "Heq").
      iIntros (k [rt [lt1 lt2]] ?). simpl.
      iIntros "Heq" (r). iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_owned_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) wl rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ (hpzipl _ lts1 rs1); hpzipl _ lts2 rs2,
      ltype_incl (Owned false) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl' (Owned wl) #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iPoseProof (big_sepL2_length with "Heq") as "%Hlen". rewrite !hpzipl_length in Hlen.
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen1 & %Hly & Hlb & ? & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR. iFrame.
    iDestruct "Hb" as "(%r' & <- & Hb)". iExists rs2. iSplitR; first done.
    iModIntro. iNext. iMod "Hb". rewrite -big_sepL_fupd.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv _ _ _ _ _ _ _ _ _ Hlen Hlook1 Hlook2) as
      [ (rt1 & rt2 & lt1' & lt2' & r1 & r2 & -> & -> & Hlook1' & Hlook2') | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL2_lookup with "Heq") as "Hb"; [done.. | ]. simpl.
    iDestruct "Hb" as "(%Hst & #Hb & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iMod ("Hb" with "Hc").
  Qed.
  Lemma struct_ltype_incl_owned_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) wl rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2,
      ltype_incl (Owned false) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl (Owned wl) #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_owned_in).
    - done.
    - rewrite !hpzipl_hmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
        iIntros (k [rt1 [lt1 r1]] [rt2 [lt2 r2]] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_owned {rts} (lts1 lts2 : hlist ltype rts) wl rs sls :
    (([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Owned false) r r (projT2 ltp).1 (projT2 ltp).2)) -∗
    ltype_incl' (Owned wl) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & ? & Hb)".
    iExists sl. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)". iExists r'. iFrame.
    iModIntro. iNext. iMod "Hb". rewrite -big_sepL_fupd.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
      [ (rt & lt1' & lt2' & r & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
    iDestruct ("Hb" $! r) as "(%Hst & #Hb' & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iApply "Hb'".
  Qed.
  Lemma struct_ltype_incl_owned {rts} (lts1 lts2 : hlist ltype rts) wl rs sls :
    ([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Owned false) r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl (Owned wl) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_owned).
    - done.
    - rewrite hzipl2_fmap big_sepL_fmap. iApply (big_sepL_mono with "Heq").
      iIntros (k [rt [lt1 lt2]] ?). simpl.
      iIntros "Heq" (r). iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_uniq {rts} (lts1 lts2 : hlist ltype rts) κ γ rs sls :
    (([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq (Owned false) r r (projT2 ltp).1 (projT2 ltp).2)) -∗
    ltype_incl' (Uniq κ γ) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & ? & Hrfn & Hb)".
    iExists sl. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "((%Hst & #Hb' & _) & _)".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        by iApply "Hb'".
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook2 Hlook1) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "(_ & (%Hst & #Hb' & _))".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        by iApply "Hb'".
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "((%Hst & _ & #Hb') & _)".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        rewrite !ltype_own_core_equiv. by iApply "Hb'".
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook2 Hlook1) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "(_ & (%Hst & _ & #Hb'))".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        rewrite !ltype_own_core_equiv. by iApply "Hb'".
  Qed.
  Lemma struct_ltype_incl_uniq {rts} (lts1 lts2 : hlist ltype rts) κ γ rs sls :
    ([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq (Owned false) r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl (Uniq κ γ) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_uniq).
    - done.
    - rewrite hzipl2_fmap big_sepL_fmap. iApply (big_sepL_mono with "Heq").
      iIntros (k [rt [lt1 lt2]] ?). simpl.
      iIntros "Heq" (r). iApply ltype_eq_core; done.
  Qed.

  Lemma struct_ltype_incl {rts} (lts1 lts2 : hlist ltype rts) k rs sls :
    (∀ k, [∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl k rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    destruct k.
    - iApply (struct_ltype_incl_owned lts1 lts2) .
      iApply (big_sepL_wand with "Heq"). iApply big_sepL_intro.
      iIntros "!>" (? [rt [lt1 lt2]] ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply struct_ltype_incl_shared.
      iApply (big_sepL_wand with "Heq"). iApply big_sepL_intro.
      iIntros "!>" (? [rt [lt1 lt2]] ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply struct_ltype_incl_uniq. done.
  Qed.
  Lemma struct_ltype_eq {rts} (lts1 lts2 : hlist ltype rts) k rs sls :
    (∀ k, [∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_eq k rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplit.
    - iApply (struct_ltype_incl lts1 lts2); done.
    - iApply struct_ltype_incl. iIntros (k').
      iSpecialize ("Heq" $! k').
      rewrite hzipl2_swap big_sepL_fmap.
      iApply (big_sepL_wand with "Heq").
      iApply big_sepL_intro. iIntros "!>" (? [? []] ?) "Heq'".
      iIntros (?). iApply ltype_eq_sym. done.
  Qed.

  Lemma struct_full_subltype E L {rts} (lts1 lts2 : hlist ltype rts) sls :
    Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2) →
    full_subltype E L (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    intros Hsub.
    iIntros (qL) "HL #CTX #HE".
    iAssert (∀ k, [∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2)%I with "[HL]" as "#Heq".
    { iIntros (k). iInduction rts as [ | rt rts] "IH"; first done.
      inv_hlist lts1 => lt1 lts1. inv_hlist lts2 => lt2 lts2.
      rewrite hzipl2_cons. rewrite Forall_cons.
      intros [Heq Heqs].
      iPoseProof (Heq with "HL CTX HE") as "#Heq".
      iPoseProof ("IH" with "[//] HL") as "Heqs".
      iApply big_sepL_cons. iFrame. done.
    }
    iIntros (k r). iApply (struct_ltype_incl lts1 lts2). done.
  Qed.
  Lemma struct_full_eqltype E L {rts} (lts1 lts2 : hlist ltype rts) sls :
    Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2) →
    full_eqltype E L (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    intros Hsub.
    apply full_subltype_eqltype. { by apply (struct_full_subltype _ _ lts1 lts2). }
    apply (struct_full_subltype _ _ lts2 lts1).
    rewrite hzipl2_swap. rewrite Forall_fmap.
    eapply Forall_impl; first done.
    intros [rt []]; naive_solver.
  Qed.
End subltype.

Section unfold.
  Context `{!typeGS Σ}.
  Lemma struct_t_unfold_1_owned {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%ly & %Halg & %Hly & %Hsc & #Hlb & ? & %r' & Hrfn & Hv)".
    eapply use_layout_alg_struct_Some_inv in Halg as (sl & Halg & ->).
    (*assert (ly = sl) as ->. { eapply syn_type_has_layout_inj; first done.*)
      (*eapply use_struct_layout_alg_Some_inv. done. }*)
    iExists sl. do 4 iR.
    iFrame. iExists r'. iFrame.
    iModIntro. iNext. iMod "Hv" as "(%v & Hl & Hv)".
    iDestruct "Hv" as "(%sl' & %Halg' & _ & %Hly' & Hb)".
    assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }
    rewrite hpzipl_hmap.
    set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
    rewrite (pad_struct_ext _ _ _ (λ ly, f (struct_make_uninit_type ly))); last done.
    rewrite pad_struct_fmap big_sepL_fmap.
    rewrite /struct_own_el_val heap_mapsto_reshape_sl; last done.
    iDestruct "Hl" as "(_ & Hl)".
    iPoseProof (big_sepL2_sep_sepL_l with "[$Hl $Hb]") as "Ha".

    iApply (big_sepL2_elim_l). iApply big_sepL2_fupd.
    iApply (big_sepL2_wand with "Ha").
    iApply big_sepL2_intro.
    { rewrite reshape_length pad_struct_length fmap_length fmap_length //. }
    iIntros "!>" (k w [rt [ty r0]] Hlook1 Hlook2) => /=.
    iIntros "(Hl & %r0' & %ly & Hrfn & %Hmem & %st & Hty)".
    iExists ly. iSplitR; first done. simp_ltypes.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iSplitR; first done.
    iExists ly. iSplitR; first done.
    iSplitR. { iPureIntro. eapply struct_layout_field_aligned; done. }
    iPoseProof (ty_own_val_sidecond with "Hty") as "#$".
    iSplitR. { iApply loc_in_bounds_sl_offset; done. }
    iSplitR; first done.
    iExists _. iFrame. iModIntro. iNext. iModIntro. iExists w. iFrame.
  Qed.

  Lemma struct_t_unfold_1_shared {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) κ r :
    ⊢ ltype_incl' (Shared κ) r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%ly & %Halg & %Hly & %Hsc & #Hlb & %r' & Hrfn & #Hb)".
    apply use_layout_alg_struct_Some_inv in Halg as (sl & Halg & ->).
    iExists sl. iSplitR; first done.
    iSplitR; first done. iSplitR; first done. iFrame "Hlb".
    iExists r'. iFrame "Hrfn". iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%sl' & %Halg' & _ & %Hly' & Hlb' & Hb)".
    assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }

    rewrite hpzipl_hmap.
    set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
    rewrite (pad_struct_ext _ _ _ (λ ly, f $ struct_make_uninit_type ly)); last done.
    rewrite pad_struct_fmap big_sepL_fmap.
    iModIntro. iApply (big_sepL_wand with "Hb").
    iApply big_sepL_intro. iIntros "!>" (k [rt0 [ty0 r0]] Hlook).
    iIntros "(%r0' & %ly & Hrfn & %Hmem & %Hst & #Hsc & #Hb)".
    iExists ly. iSplitR; first done. iSplitR; first done.
    simpl in *. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. iSplitR; first done.
    iSplitR.
    { iPureIntro. eapply struct_layout_field_aligned; done. }
    iSplitR; first done.
    iSplitR. { iApply loc_in_bounds_sl_offset; done. }
    iExists r0'. iFrame "Hrfn". iModIntro. iModIntro. done.
  Qed.

  (* The lemma stating the main unfolding condition for the Uniq case *)
  (* TODO: maybe we can refactor this a bit *)
  Local Lemma unfold_case_uniq {rts} π (tys : hlist type rts) sls sl l γ wl (b : bool) :
    wl = false →
    use_struct_layout_alg sls = Some sl →
    l `has_layout_loc` sl →
    length rts = length (sls_fields sls) →
    ⊢ loc_in_bounds l 0 (ly_size sl) -∗
      (∃ r' : plist place_rfn rts, gvar_auth γ r' ∗
        (|={lftE}=> ∃ v : val, l ↦ v ∗ v ◁ᵥ{ π} r' @ struct_t sls tys)) ↔
      (∃ r' : plist place_rfn rts, gvar_auth γ r' ∗ (|={lftE}=>
        [∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts ((λ X : Type, OfTy) +<$> tys) r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗
            ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, Owned wl] (projT2 ty).2 @ if b then ltype_core (projT2 ty).1 else (projT2 ty).1)).
  Proof.
    intros -> Hst Hly Hsc. iIntros "#Hlb".
    iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iDestruct "Hb" as ">(%v & Hl & Hb)".
      iApply big_sepL_fupd.
      iDestruct "Hb" as "(%sl' & %Halg & %Hlen & %Hly' & Hb)".
      assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }
      rewrite hpzipl_hmap.
      set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
      rewrite (pad_struct_ext _ _ _ (λ ly, f $ struct_make_uninit_type ly)); last done.
      rewrite pad_struct_fmap big_sepL_fmap.
      rewrite heap_mapsto_reshape_sl; last done. iDestruct "Hl" as "(_ & Hl)".
      iPoseProof (big_sepL2_sep_sepL_l with "[$Hl $Hb]") as "Ha".

      iApply big_sepL2_elim_l.
      iApply (big_sepL2_wand with "Ha").
      iApply big_sepL2_intro.
      { rewrite reshape_length pad_struct_length fmap_length fmap_length //. }
      iIntros "!>" (k w [rt [ty r0]] Hlook1 Hlook2) => /=.
      iIntros "(Hl & %r0' & %ly & Hrfn & %Hmem & %st & Hty)".
      iExists ly. iSplitR; first done. simp_ltypes.
      rewrite Tauto.if_same.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iSplitR; first done.
      iExists ly. iSplitR; first done.
      iSplitR. { iPureIntro. eapply struct_layout_field_aligned; done. }
      iPoseProof (ty_own_val_sidecond with "Hty") as "#$".
      iSplitR. { iApply loc_in_bounds_sl_offset; done. }
      iSplitR; first done.
      iExists _. iFrame. iModIntro. iModIntro. iExists w. iFrame.
    * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
      iMod "Hb".
      specialize (struct_layout_field_aligned _ _ Hly) as Hfield_ly.
      (* generalize sl_members before initiating induction *)
      rewrite /ty_own_val /=.
      setoid_rewrite bi.sep_exist_l. rewrite bi_exist_comm.
      iExists sl. iFrame "%".
      rewrite /has_layout_val {1 2}/ly_size {1 2}/layout_of /=.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Hst).
      remember (sl_members sl) as slm eqn:Heqslm.
      remember (sls_fields sls) as slsm eqn:Heqslsm.
      clear Heqslsm Heqslm Hst sls sl Hly => Hlen.

      iInduction (slm) as [ | [m ly] slm] "IH" forall (l slsm rts tys r' Hlen Hsc Hfield_ly); simpl.
      { iExists [].
        iSplitR. { iApply heap_mapsto_nil. iApply loc_in_bounds_shorten_suf; last done. lia. }
        iSplitR; first done. done. }
      rewrite -Hsc in Hlen.
      iDestruct "Hb" as "(Hb0 & Hb)".
      destruct m as [ m | ].
      --  simpl in Hlen. destruct rts as [ | rt rts]; first done.
          simpl in Hsc, Hlen. destruct slsm as [ | st slsm]; first done.
          inv_hlist tys => ty tys. destruct r' as [r0 r]. simpl.
          (* use the IH *)
          iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r).
          simpl in *.
          iSpecialize ("IH" with "[] [] [] [] [Hb]").
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. intros k ly' Hlook.
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eapply (Hfield_ly (S k)). done. }
          { iModIntro.
            iApply loc_in_bounds_offset; last done.
            - done.
            - simpl. lia.
            - simpl. rewrite /fmap. lia. }
          { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
            iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eauto. }
          iMod "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
          (* destruct the head *)
          iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
          injection Heq0 as [= <-].
          simp_ltypes. rewrite Tauto.if_same.
          rewrite ltype_own_ofty_unfold /lty_of_ty_own.
          iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & Hb0)".
          (* TODO need the v also under there. *)
          iMod "Hb0" as "(%v0 & Hl0 & Hb0)".
          move: Halg0. simp_ltypes. intros Halg0.
          assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
          iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
          iExists (v0 ++ v1). rewrite heap_mapsto_app.
          iSplitL "Hl0 Hl1".
          { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
            rewrite Hly0'. done. }
          iSplitR. { iPureIntro. rewrite app_length Hv1_len Hly0'. done. }
          iSplitL "Hb0 Hrfn0".
          { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
            rewrite -Hly0'. rewrite take_app. done. }
          rewrite -Hly0'. rewrite drop_app. done.
      -- simpl in Hlen. simpl.
         (* use the iH *)
          iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r').
          simpl in *.
          iSpecialize ("IH" with "[] [] [] [] [Hb]").
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. intros k ly' Hlook.
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eapply (Hfield_ly (S k)). done. }
          { iModIntro.
            iApply loc_in_bounds_offset; last done.
            - done.
            - simpl. lia.
            - simpl. rewrite /fmap. lia. }
          { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
            iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eauto. }
          iMod "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
          (* destruct the head *)
          iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
          injection Heq0 as [= <-].
          rewrite /UninitLtype. simp_ltypes. rewrite Tauto.if_same.
          rewrite ltype_own_ofty_unfold /lty_of_ty_own.
          iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & >(%v0 & Hl0 & Hb0))".
          move: Halg0. simp_ltypes. intros Halg0.
          assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
          iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
          iExists (v0 ++ v1). rewrite heap_mapsto_app.
          iSplitL "Hl0 Hl1".
          { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
            rewrite Hly0'. done. }
          iSplitR. { iPureIntro. rewrite app_length Hv1_len Hly0'. done. }
          iSplitL "Hb0 Hrfn0".
          { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
            rewrite -Hly0'. rewrite take_app. done. }
          rewrite -Hly0'. rewrite drop_app. done.
  Qed.

  Lemma struct_t_unfold_1_uniq {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%ly & %Hst & %Hly & %Hsc & #Hlb & Hrfn & ? & Hb)". simpl in Hst.
    apply use_layout_alg_struct_Some_inv in Hst as (sl & Hst & ->).
    iExists sl. iSplitR; first done.
    (* NOTE: here we really need the ty_sidecond; we would not be able to just extract this info out from under the borrow! *)
    iSplitR. { rewrite Hsc. done. }
    iSplitR; first done.
    iSplitR; first done.
    iFrame. iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv.
    iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false false with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false true with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
  Qed.

  Local Lemma struct_t_unfold_1' {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl' k r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    destruct k.
    - iApply struct_t_unfold_1_owned.
    - iApply struct_t_unfold_1_shared.
    - iApply struct_t_unfold_1_uniq.
  Qed.

  Local Lemma ltype_core_hmap_ofty {rts : list Type} (tys : hlist type rts) :
    @ltype_core _ _ +<$> ((λ _, OfTy) +<$> tys) = ((λ _, OfTy) +<$> tys).
  Proof.
    induction tys as [ | rt rts ty tys IH]; simpl; first done. f_equiv. { simp_ltypes. done. } eapply IH.
  Qed.

  Lemma struct_t_unfold_1 {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl k r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    + iApply struct_t_unfold_1'.
    + simp_ltypes. rewrite ltype_core_hmap_ofty. by iApply struct_t_unfold_1'.
  Qed.

  Lemma struct_t_unfold_2_owned {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) wl r :
    ⊢ ltype_incl' (Owned wl) r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hsc & %Hly & #Hlb & ? & %r' & Hrfn & Hb)".
    iExists sl. iSplitR. { iPureIntro. eapply use_struct_layout_alg_Some_inv. done. }
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iModIntro. iFrame. iExists r'. iFrame "Hrfn".
    iNext. iMod "Hb".
    specialize (struct_layout_field_aligned _ _ Hly) as Hfield_ly.
    (* generalize *)
    (* TODO mostly duplicated with the Uniq lemma above *)
    rewrite /ty_own_val /=.
    setoid_rewrite bi.sep_exist_l. rewrite bi_exist_comm.
    iExists sl. symmetry in Hsc. iFrame "%".
    rewrite /has_layout_val {1 2}/ly_size {1 2}/layout_of /=.
    specialize (struct_layout_spec_has_layout_fields_length _ _ Halg).
    remember (sl_members sl) as slm eqn:Heqslm.
    remember (sls_fields sls) as slsm eqn:Heqslsm.
    clear Heqslsm Heqslm Halg sls r sl Hly => Hlen.

    iInduction (slm) as [ | [m ly] slm] "IH" forall (l slsm rts tys r' Hsc Hlen Hfield_ly); simpl.
    { iExists [].
      iSplitR. { iApply heap_mapsto_nil. iApply loc_in_bounds_shorten_suf; last done. lia. }
      iSplitR; first done. iModIntro. done. }
    rewrite -Hsc in Hlen.
    iDestruct "Hb" as "(Hb0 & Hb)".
    destruct m as [ m | ].
    --  simpl in Hlen. destruct rts as [ | rt rts]; first done.
        simpl in Hsc, Hlen. destruct slsm as [ | st slsm]; first done.
        inv_hlist tys => ty tys. destruct r' as [r0 r]. simpl.
        (* use the IH *)
        iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r).
        simpl in *.
        iSpecialize ("IH" with "[] [] [] [] [Hb]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. intros k ly' Hlook.
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eapply (Hfield_ly (S k)). done. }
        { iModIntro.
          iApply loc_in_bounds_offset; last done.
          - done.
          - simpl. lia.
          - simpl. rewrite /fmap. lia. }
        { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
          iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eauto. }
        iMod "IH".
        iDestruct "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
        (* destruct the head *)
        iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
        injection Heq0 as [= <-].
        simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & >(%v0 & Hl0 & Hb0))".
        move: Halg0. simp_ltypes. intros Halg0.
        assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
        iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
        iModIntro.
        iExists (v0 ++ v1). rewrite heap_mapsto_app.
        iSplitL "Hl0 Hl1".
        { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
          rewrite Hly0'. done. }
        iSplitR. { iPureIntro. rewrite app_length Hv1_len Hly0'. done. }
        iSplitL "Hb0 Hrfn0".
        { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
          rewrite -Hly0'. rewrite take_app. done. }
        rewrite -Hly0'. rewrite drop_app. done.
    -- simpl in Hlen. simpl.
       (* use the iH *)
        iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r').
        simpl in *.
        iSpecialize ("IH" with "[] [] [] [] [Hb]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. intros k ly' Hlook.
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eapply (Hfield_ly (S k)). done. }
        { iModIntro.
          iApply loc_in_bounds_offset; last done.
          - done.
          - simpl. lia.
          - simpl. rewrite /fmap. lia. }
        { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
          iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eauto. }
        iMod "IH".
        iDestruct "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
        (* destruct the head *)
        iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
        injection Heq0 as [= <-].
        rewrite /UninitLtype. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & >(%v0 & Hl0 & Hb0))".
        move: Halg0. simp_ltypes. intros Halg0.
        assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
        iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
        iExists (v0 ++ v1). rewrite heap_mapsto_app.
        iSplitL "Hl0 Hl1".
        { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
          rewrite Hly0'. done. }
        iSplitR. { iPureIntro. rewrite app_length Hv1_len Hly0'. done. }
        iSplitL "Hb0 Hrfn0".
        { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
          rewrite -Hly0'. rewrite take_app. done. }
        rewrite -Hly0'. rewrite drop_app. done.
  Qed.
  Lemma struct_t_unfold_2_shared {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) κ r :
    ⊢ ltype_incl' (Shared κ) r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & #Hlb & %r' & Hrfn & #Hb)".
    iExists sl. iSplitR. { iPureIntro. by eapply use_struct_layout_alg_Some_inv. }
    iSplitR; first done. iSplitR; first done. iFrame "Hlb".
    iExists r'. iFrame "Hrfn". iModIntro. iMod "Hb".

    rewrite /ty_shr /=. iExists sl. do 4 iR.
    rewrite -big_sepL_fupd.
    rewrite hpzipl_hmap.
    set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
    rewrite (pad_struct_ext _ _ _ (λ ly, f $ struct_make_uninit_type ly)); last done.
    rewrite pad_struct_fmap big_sepL_fmap.
    iApply (big_sepL_wand with "Hb").
    iApply big_sepL_intro. iIntros "!>" (k [rt0 [ty0 r0]] Hlook).
    iIntros "(%ly & %Hmem & %Hst & Hb)". simpl in *.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & %r0' & Hrfn0 & #>#Hb)".
    iModIntro. iExists r0', ly0.
    move: Hst. simp_ltypes => Hst. assert (ly0 = ly) as ->. { by eapply syn_type_has_layout_inj. }
    iFrame "# ∗". iSplit; done.
  Qed.
  Lemma struct_t_unfold_2_uniq {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%sl & %Hst & %Hlen & %Hly & #Hlb & Hrfn & ? & Hb)".
    iExists sl.
    iSplitR. { iPureIntro. eapply use_struct_layout_alg_Some_inv; done. }
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    iFrame "∗". iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv.
    iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false false with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false true with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
  Qed.

  Local Lemma struct_t_unfold_2' {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl' k r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    destruct k.
    - iApply struct_t_unfold_2_owned.
    - iApply struct_t_unfold_2_shared.
    - iApply struct_t_unfold_2_uniq.
  Qed.
  Lemma struct_t_unfold_2 {rts : list Type} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl k r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    + iApply struct_t_unfold_2'.
    + simp_ltypes. rewrite ltype_core_hmap_ofty. iApply struct_t_unfold_2'.
  Qed.

  Lemma struct_t_unfold {rts} (tys : hlist type rts) sls k r :
    ⊢ ltype_eq k r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iSplit.
    - iApply struct_t_unfold_1.
    - iApply struct_t_unfold_2.
  Qed.

  Lemma struct_t_unfold_full_eqltype' E L {rts} (tys : hlist type rts) lts sls :
    (Forall (λ ltp, full_eqltype E L (projT2 ltp).1 (◁ (projT2 ltp).2)%I) (hzipl2 rts lts tys)) →
    full_eqltype E L (StructLtype lts sls) (◁ (struct_t sls tys))%I.
  Proof.
    iIntros (Heq ?) "HL #CTX #HE".
    iAssert ([∗ list] ltp ∈ hzipl2 rts lts tys, ∀ k r, ltype_eq k r r (projT2 ltp).1 (◁ (projT2 ltp).2)%I)%I with "[HL]" as "Ha".
    { iInduction rts as [ | rt rts] "IH"; first done.
      inv_hlist tys. inv_hlist lts. intros lt lts ty tys.
      rewrite hzipl2_cons. rewrite Forall_cons. intros [Heq Heqs].
      iPoseProof (Heq with "HL CTX HE") as "#Heq".
      iPoseProof ("IH" with "[//] HL") as "Heqs".
      iFrame. simpl. done. }
    iIntros (b r).
    iApply (ltype_eq_trans with "[Ha]"); last (iApply ltype_eq_sym; iApply struct_t_unfold).
    iApply (struct_ltype_eq lts).
    iIntros (k). rewrite hzipl2_fmap_r big_sepL_fmap.
    iApply (big_sepL_impl with "Ha").
    iModIntro. iIntros (? [? []] ?) "Ha".
    iIntros (r'). iApply "Ha".
  Qed.

  Lemma struct_t_unfold_full_eqltype E L {rts} (tys : hlist type rts) sls :
    (*full_eqltype E L lt (◁ ty)%I →*)
    full_eqltype E L (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iIntros (?) "HL #CTX #HE". iIntros (b r).
    iApply ltype_eq_sym.
    iApply struct_t_unfold.
  Qed.
End unfold.

Section lemmas.
  Context `{!typeGS Σ}.

  (** Focusing lemmas for pad_struct big_seps *)
  Lemma focus_struct_component {rts} (lts : hlist ltype rts) (r : plist place_rfn rts) sl π k l i x rto lto ro :
    field_index_of (sl_members sl) x = Some i →
    hpzipl rts lts r !! i = Some (existT rto (lto, ro)) →
    (* assume the big sep of components *)
    ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) (λ ly, existT (unit : Type) (UninitLtype (UntypedSynType ly), PlaceIn ())),
      ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
      (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1) -∗
    ⌜rto = lnth (unit : Type) rts i⌝ ∗
    (* get the component *)
    ∃ ly : layout, ⌜syn_type_has_layout (ltype_st lto) ly⌝ ∗ (l at{sl}ₗ x) ◁ₗ[ π, k] ro @ lto ∗
    (* for any strong update, get the corresponding big_sep back *)
    (∀ rt' lt' r',
      (l at{sl}ₗ x) ◁ₗ[ π, k] r' @ lt' -∗
      ⌜syn_type_has_layout (ltype_st lt') ly⌝ -∗
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl (<[i := rt']> rts) (hlist_insert rts lts i rt' lt') (plist_insert rts r i rt' r')) (λ ly, existT (unit : Type) (UninitLtype (UntypedSynType ly), PlaceIn ())),
        ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
        (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1)) ∧
    (* alternatively, for any weak (non-rt-changing) update: *)
    (∀ (lt' : ltype (lnth (unit : Type) rts i)) (r' : place_rfn (lnth (unit : Type) rts i)),
      (l at{sl}ₗ x) ◁ₗ[ π, k] r' @ lt' -∗
       ⌜syn_type_has_layout (ltype_st lt') ly⌝ -∗
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl (rts) (hlist_insert_id (unit : Type) rts lts i lt') (plist_insert_id (unit : Type) rts r i r')) (λ ly, existT (unit : Type) (UninitLtype (UntypedSynType ly), PlaceIn ())),
        ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
        (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1)).
  Proof.
    iIntros (Hfield Hlook) "Hb".
    edestruct (field_index_of_to_index_of _ _ _ Hfield) as (j & Hindex).
    iPoseProof (big_sepL_insert_acc with "Hb") as "((%ly & %Hly & %Hst & Hl) & Hclose)".
    { eapply pad_struct_lookup_field_Some_2'; done. }
    specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook) as Hlook'.
    simpl. iSplitR. { eapply lookup_lnth in Hlook'. done. }
    iExists ly. iSplitR; first done.
    rewrite /GetMemberLoc /offset_of Hindex. simpl. iFrame.
    iSplit.
    - iIntros (rt' lt' r') "He %Hst'".
      set (ra := existT (P := λ rt, (ltype rt * place_rfn rt)%type) rt' (lt', r')).
      iSpecialize ("Hclose" $! ra with "[He]").
      { iExists ly. iSplitR; first done. iSplitR; done. }
      erewrite pad_struct_insert_field; [ | done | done | ].
      2: { eapply lookup_lt_Some. done. }
      rewrite insert_hpzipl. done.
    - iIntros (lt' r') "He %Hst'".
      set (ra := existT (P := λ rt, (ltype rt * place_rfn rt)%type) _ (lt', r')).
      iSpecialize ("Hclose" $! ra with "[He]").
      { iExists ly. iSplitR; first done. iSplitR; done. }
      erewrite pad_struct_insert_field; [ | done | done | ].
      2: { eapply lookup_lt_Some. done. }
      rewrite insert_hpzipl.
      enough (hpzipl rts (hlist_insert_id (unit : Type) rts lts i lt') (plist_insert_id (unit : Type) rts r i r') =
        (hpzipl (<[i:=lnth (unit : Type) rts i]> rts) (hlist_insert rts lts i (lnth (unit : Type) rts i) lt') (plist_insert rts r i (lnth (unit : Type) rts i) r'))) as -> by done.
      unfold hlist_insert_id, plist_insert_id.
      generalize (list_insert_lnth rts (unit : Type) i).
      intros <-. done.
  Qed.


  Fixpoint uninit_struct_hlist (fields : list (var_name * syn_type)) : hlist type (replicate (length fields) (unit : Type)) :=
    match fields with
    | [] => +[]
    | (_, st) :: fields => uninit st +:: uninit_struct_hlist fields
    end.
  Lemma uninit_struct_hlist_hzipl_lookup fields i :
    i < length fields →
    ∃ x st, fields !! i = Some (x, st) ∧ hzipl _ (uninit_struct_hlist fields) !! i = Some (existT _ $ uninit st).
  Proof.
    induction fields as [ | [x st] fields IH] in i |-*; simpl; first lia.
    intros Ha. destruct i; first by eauto.
    efeed pose proof (IH i) as Hb; first lia.
    destruct Hb as (? & ? & Hlook & Hlook'). eauto.
  Qed.

  Definition uninit_struct_plist (fields : list (var_name * syn_type)) : plist place_rfn (replicate (length fields) (unit : Type)) :=
    mk_const_plist (unit : Type) #() (length fields).

  Lemma struct_uninit_equiv_val1 π v (sls : struct_layout_spec) :
    v ◁ᵥ{π} .@ uninit sls -∗
    v ◁ᵥ{π} uninit_struct_plist (sls.(sls_fields)) @ struct_t sls (uninit_struct_hlist sls.(sls_fields)).
  Proof.
    rewrite /ty_own_val /=.
    iIntros "(%ly & %Halg & %Hly & _)".
    apply use_layout_alg_struct_Some_inv in Halg as (sl & Halg & ->).
    iExists sl. iR. rewrite replicate_length. iR. iR.
    iApply big_sepL2_intro.
    { rewrite pad_struct_length reshape_length !fmap_length //. }
    iModIntro. iIntros (k v1 [rt [ty r]] Hlook1 Hlook2).
    apply pad_struct_lookup_Some in Hlook2; first last.
    { rewrite hpzipl_length replicate_length.
      erewrite struct_layout_spec_has_layout_fields_length; done. }
    destruct Hlook2 as (n & ly & Hlook2 & [ [? Hlook3] | [-> Heq]]).
    - apply hpzipl_lookup_inv_hzipl_pzipl in Hlook3 as [Hlook31 Hlook32].
      (* strategy:
         - sls lookup gives us something
       *)
  Abort.
  Lemma struct_uninit_equiv_val2 π v (sls : struct_layout_spec) {rts} (rs : plist place_rfn rts) (tys : hlist type rts) :
    v ◁ᵥ{π} rs @ struct_t sls tys -∗
    v ◁ᵥ{π} .@ uninit sls.
  Proof.
    rewrite /ty_own_val /=. iIntros "(%sl & %Halg & %Hlen & %Hly & Hb)".
    iExists sl. eapply use_struct_layout_alg_Some_inv in Halg. iR. iR.
    iPureIntro. apply Forall_true. done.
  Qed.

  Lemma struct_uninit_equiv_place1 π l wl (sls : struct_layout_spec) :
    l ◁ₗ[π, Owned wl] .@ (◁ uninit sls) -∗
    l ◁ₗ[π, Owned wl] #(uninit_struct_plist sls.(sls_fields)) @ ◁ struct_t sls (uninit_struct_hlist sls.(sls_fields)).
  Proof.
  Abort.


  Lemma struct_uninit_equiv_place2 π l wl (sls : struct_layout_spec) {rts} (lts : hlist ltype rts) (rs : plist place_rfn rts) :
    l ◁ₗ[π, Owned wl] #rs @ StructLtype lts sls -∗
    l ◁ₗ[π, Owned wl] .@ ◁ uninit sls.
  Proof.
    (* TODO: also need to know that the lts are all deinitializable.
        We could do one of the following:
       - have a pure predicate doing a syntactic check
       - require a semantic VS via a bigsep.
     *)
  Abort.


  (** Focus the initialized fields of a struct, disregarding the padding fields *)
  Lemma struct_ltype_focus_components π {rts : list Type} (lts : hlist ltype rts) (rs : plist place_rfn rts) sls sl k l :
    length rts = length (sls_fields sls) →
    struct_layout_spec_has_layout sls sl →
    ([∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts lts rs) struct_make_uninit_ltype,
       ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗
         ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
         (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1) -∗
    (* we get access to the named fields *)
    ([∗ list] i↦p ∈ hpzipl rts lts rs, let 'existT rt (lt, r) := p in ∃ (name : var_name) (st : syn_type), ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ l atst{sls}ₗ name ◁ₗ[ π, k] r @ lt) ∗
    (* we can update the named fields: *)
    (∀ (rts' : list Type) (lts' : hlist ltype rts') rs',
      (* syn types need to be the same *)
      ⌜length rts = length rts'⌝ -∗
      (⌜Forall2 (λ p p2, let 'existT rt (lt, _) := p in let 'existT rt' (lt', _) := p2 in ltype_st lt = ltype_st lt') (hpzipl rts lts rs) (hpzipl rts' lts' rs')⌝)  -∗
      (* ownership *)
      ([∗ list] i↦p ∈ hpzipl rts' lts' rs', let 'existT rt (lt, r) := p in ∃ (name : var_name) (st : syn_type), ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ l atst{sls}ₗ name ◁ₗ[ π, k] r @ lt) -∗
      (* we get back the full struct ownership *)
      ([∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' rs') struct_make_uninit_ltype,
       ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗
         ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
         (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1)).
  Proof.
    iIntros (Hlen Halg) "Hl".
    iPoseProof (pad_struct_focus_no_uninit with "Hl") as "(Hl & Hl_cl)".
    { rewrite hpzipl_length. rewrite named_fields_field_names_length (struct_layout_spec_has_layout_fields_length sls); done. }
    { specialize (sl_nodup sl). rewrite bool_decide_spec. done. }
    (* remember the layouts *)
    iAssert ([∗ list] i↦x ∈ hpzipl rts lts rs, ∃ (ly : layout) (n : string), ⌜named_fields (sl_members sl) !! i = Some (n, ly)⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 x).1) ly⌝)%I with "[Hl]" as "%Hly_agree".
    { iApply (big_sepL_impl with "Hl").
      iModIntro. iIntros (j [rt [lt r]] Hlook).
      iIntros "(%j' & %ly & %n & %Hmem & %Hnamed & %ly' & %Hmem' & %Hst & Hl)".
      rewrite Hmem in Hmem'. simpl in *. injection Hmem' as <-.
      specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
      eapply Forall2_lookup_r in Halg2; last done.
      destruct Halg2 as ([n' st'] & Hfields & Hst' & <-).
      rewrite Hnamed. iExists _, _. done. }

    iSplitL "Hl".
    { iApply (big_sepL_impl with "Hl").
      iModIntro. iIntros (j [rt [lt r]] Hlook).
      iIntros "(%j' & %ly & %n & %Hmem & %Hnamed & %ly' & %Hmem' & %Hst & Hl)".
      rewrite Hmem in Hmem'. simpl in *. injection Hmem' as <-.
      specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
      eapply Forall2_lookup_r in Halg2; last done.
      destruct Halg2 as ([n' st'] & Hfields & Hst' & <-).
      iExists _, _. rewrite /GetMemberLocSt.
      rewrite /use_struct_layout_alg'.
      iR. rewrite Halg. simpl.
      rewrite /offset_of.
      erewrite sl_index_of_lookup_2; last done.
      done. }
   iIntros (rts' lts' rs') "%Hlen_eq %Hst Hb".
   iApply "Hl_cl". { rewrite !hpzipl_length//. }

   iApply (big_sepL_impl with "Hb").
   iModIntro. iIntros (ka [rt [lt r]] Hlook) "(%n & %st & %Hst' & Hl)".
   simpl.
   specialize (struct_layout_spec_has_layout_lookup sls sl n _ _ Halg Hst') as Hidx.
   specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
   eapply Forall2_lookup_l in Halg2 as ([n' ly'] & Hlook' & Hly); last done.
   simpl in Hly. destruct Hly as (Hly & ->).
   specialize (named_fields_lookup_1 _ _ _ _ Hlook') as (ka' & Hlook'').

   eapply Forall2_lookup_r in Hst; last done.
   destruct Hst as ([rt' [lt' r']] & Hlook2 & Hst).
   rewrite -Hst.
   eapply Hly_agree in Hlook2 as (ly2 & n2 & Hlook2 & Hst2).
   simpl in *. rewrite Hlook' in Hlook2. injection Hlook2 as [= <- <-].
   iExists ka',  ly', n. iR. iR.
   iExists _. rewrite Hlook''. iR. iR.
   rewrite /GetMemberLocSt /use_struct_layout_alg' Halg /=.
   rewrite /offset_of. erewrite sl_index_of_lookup_2; done.
  Qed.

End lemmas.

Section rules.
  Context `{!typeGS Σ}.

  Local Lemma Forall2_place_access_rt_rel b rts rts' :
    (match b with | Owned _ => False | _ => True end) →
    Forall2 (place_access_rt_rel b) rts rts' → rts = rts'.
  Proof.
    intros Hb Hrel.
    induction rts as [ | rt rts IH] in rts', Hrel |-*; destruct rts' as [ | rt' rts'];
      [done | inversion Hrel | inversion Hrel | ].
    inversion Hrel; subst.
    destruct b; first done.
    all: match goal with
    | H : place_access_rt_rel _ _ _ |- _ => unfold place_access_rt_rel in H; rewrite H
    end; f_equiv; by apply IH.
  Qed.

  (** Note: regrettably, this does not allow us to just preserve one component trivially.
    This is due to the way how mutable references of products are setup.
    Effectively, this means that our place access lemmas for products will have some sideconditions on when borrows beneath other components will end.
    TODO is there are smarter setup for this? (e.g. by tracking this as a sidecondition in ltypes so that it does not need to reproved over and over again?)
  *)
  Import EqNotations.
  Lemma struct_ltype_place_cond_ty b {rts rts'} (lts : hlist ltype rts) (lts' : hlist ltype rts') sls :
    Forall2 (place_access_rt_rel b) rts rts' →
    ([∗ list] lt; lt' ∈ hzipl rts lts; hzipl rts' lts', typed_place_cond_ty b (projT2 lt) (projT2 lt')) -∗
    typed_place_cond_ty b (StructLtype lts sls) (StructLtype lts' sls).
  Proof.
    iIntros (Hrel). destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Hrel".
      specialize (Forall2_place_access_rt_rel (Shared κ) _ _ I Hrel) as <-.
      simp_ltypes. done.
    - iIntros "Hrel".
      specialize (Forall2_place_access_rt_rel (Uniq κ γ) _ _ I Hrel) as <-.
      iExists eq_refl.
      setoid_rewrite <-bi.sep_exist_r.
      rewrite big_sepL2_sep_sepL_r. iDestruct "Hrel" as "(#Heq & #Hub)".
      iSplitL.
      + cbn. simp_ltypes. iIntros (k r). iApply struct_ltype_eq. iIntros (k').
        rewrite hzipl2_fmap big_sepL_fmap.
        rewrite (big_sepL2_hzipl_hzipl_sepL_hzipl2 _ _ _
          (λ _ a b, ∃ Heq, ∀ k r, ltype_eq k r r (ltype_core $ projT2 a) (ltype_core $ rew <-[ltype] Heq in projT2 b))%I
          (λ _ ltp, ∀ k r, ltype_eq k r r (ltype_core (projT2 ltp).1) (ltype_core (projT2 ltp).2))%I 0).
        { iApply big_sepL_mono; last done. iIntros (? [? [??]] ?). eauto. }
        intros _ x a b. iSplit.
        * iIntros "(%Heq & Heq)". rewrite (UIP_refl _ _ Heq). done.
        * iIntros "Heq". iExists eq_refl. done.
      + iApply struct_ltype_imp_unblockable. done.
  Qed.
  Lemma struct_ltype_place_cond_ty_strong wl {rts rts'} (lts : hlist ltype rts) (lts' : hlist ltype rts') sls :
    ([∗ list] lt; lt' ∈ hzipl rts lts; hzipl rts' lts', typed_place_cond_ty (Owned wl) (projT2 lt) (projT2 lt')) -∗
    typed_place_cond_ty (Owned wl) (StructLtype lts sls) (StructLtype lts' sls).
  Proof.
    iIntros "_". done.
  Qed.

  Lemma typed_place_cond_rfn_lift_struct {rts} (rs rs' : plist place_rfn rts) k :
    ([∗ list] ty1;ty2 ∈ pzipl rts rs;pzipl rts rs', typed_place_cond_rfn k (projT2 ty1) (projT2 ty2)) ⊢@{iProp Σ} typed_place_cond_rfn k (#rs) (#rs').
  Proof.
    iIntros "Ha". destruct k; done.
    (*
    iInduction rts as [ | rt rts] "IH"; simpl.
    { destruct rs, rs'. iApply typed_place_cond_rfn_refl. }
    destruct rs as [ r rs]. destruct rs' as [r' rs']. simpl.
    iDestruct "Ha" as "(Hcond & Ha)".
    iPoseProof ("IH" with "Ha") as "Ha".
    destruct k; simpl; [ done | | done].
    iDestruct "Hcond" as "(%Heq & <-)".
    iDestruct "Ha" as "(%Heq' & Heq2)".
    rewrite (UIP_refl _ _ Heq).
    rewrite (UIP_refl _ _ Heq').
    cbn. iDestruct "Heq2" as "%Heq2". injection Heq2 as ->.
    iExists eq_refl. done.
     *)
  Qed.

  Lemma typed_place_cond_struct_lift {rts rts'} (lts : hlist ltype rts) (lts' : hlist ltype rts') r r' sls bmin:
    ([∗ list] ty1; ty2 ∈ hzipl rts lts; hzipl rts' lts', typed_place_cond_ty bmin (projT2 ty1) (projT2 ty2)) -∗
    ([∗ list] ty1; ty2 ∈ pzipl rts r; pzipl rts' r', typed_place_cond_rfn bmin (projT2 ty1) (projT2 ty2)) -∗
    ⌜Forall2 (place_access_rt_rel bmin) rts rts'⌝ -∗
    typed_place_cond bmin (StructLtype lts sls) (StructLtype lts' sls) (#r) (#r').
  Proof.
    iIntros "Hcond_ty Hcond_rfn %Hrt".
    rewrite /typed_place_cond.
    iSplitL "Hcond_ty".
    { iApply struct_ltype_place_cond_ty; done. }
    destruct bmin; simpl; [done | | done].
    assert (rts = rts') as <-.
    { clear -Hrt. rewrite /place_access_rt_rel in Hrt.
      induction rts as [ | ?? IH] in rts', Hrt |-*; destruct rts' as [ | ??]; inversion Hrt; try done.
      subst. f_equiv. by eapply IH. }
    done.
  Qed.

  Lemma struct_ltype_acc_owned {rts} F π (lts : hlist ltype rts) (r : plist place_rfn rts) l sls wl :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] #r @ StructLtype lts sls -∗
    ∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length sls.(sls_fields) = length rts⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗ |={F}=>
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) ∗
      logical_step F
      (∀ rts' (lts' : hlist ltype rts') (r' : plist place_rfn rts'),
        (* the number of fields should remain equal *)
        ⌜length rts' = length rts⌝ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) ={F}=∗
        l ◁ₗ[π, Owned wl] #r' @ StructLtype lts' sls).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hb" as "(%sl & %Halg & %Hlen & %Hly & #Hlb & Hcred & %r' & -> & Hb)".
    iExists sl. iFrame "#%".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_maybe with "Hat"). iIntros "Hcred' !>".
    iIntros (rts' lts' r) "%Hlen_eq Hb".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iExists sl. rewrite Hlen_eq. iFrame "%#∗".
    iExists r. iSplitR; first done. iModIntro. done.
  Qed.

  Definition sigT_ltype_core : (sigT (λ rt, ltype rt * place_rfn rt)%type) → (sigT (λ rt, ltype rt * place_rfn rt)%type) := λ '(existT _ (lt, r)), existT _ (ltype_core lt, r).
  Local Lemma pad_struct_pull_core {rts} (lts : hlist ltype rts) (rs : plist place_rfn rts) fields (Φ : nat → (sigT (λ rt, ltype rt * place_rfn rt)%type) → iProp Σ) :
    ([∗ list] i↦ty ∈ pad_struct fields (hpzipl rts (@ltype_core Σ typeGS0 +<$> lts) rs) struct_make_uninit_ltype, Φ i ty)%I ⊣⊢
    ([∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts rs) struct_make_uninit_ltype, Φ i (sigT_ltype_core ty))%I.
  Proof.
    rewrite hpzipl_hmap.
    rewrite (pad_struct_ext _ _ _ (λ ly, sigT_ltype_core (struct_make_uninit_ltype ly))); first last.
    { intros ly. simpl. rewrite ltype_core_uninit. reflexivity. }
    rewrite (pad_struct_fmap _ _ _ sigT_ltype_core) big_sepL_fmap.
    done.
  Qed.
  Lemma ltype_core_sigT_ltype_core_idemp ty :
    ltype_core ((projT2 $ sigT_ltype_core ty).1) = (projT2 $ sigT_ltype_core ty).1.
  Proof.
    destruct ty as [? []]; simpl. rewrite ltype_core_idemp //.
  Qed.
  Lemma ltype_st_sigT_ltype_core ty :
    ltype_st ((projT2 $ sigT_ltype_core ty).1) = ltype_st (projT2 ty).1.
  Proof.
    destruct ty as [? []]; simpl. rewrite ltype_core_syn_type_eq //.
  Qed.

  Local Lemma typed_place_cond_ty_uniq_core_eq_struct {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) κ γ :
    ([∗ list] ty1; ty2 ∈ hzipl rts lts1; hzipl rts lts2, typed_place_cond_ty (Uniq κ γ) (projT2 ty1) (projT2 ty2)) -∗
    ([∗ list] ty ∈ hzipl2 rts lts1 lts2, ∀ b' r, ltype_eq b' r r (ltype_core (projT2 ty).1) (ltype_core (projT2 ty).2)).
  Proof.
    iIntros "Hcond".
    iPoseProof (big_sepL2_to_zip with "Hcond") as "Hcond".
    rewrite zip_hzipl_hzipl2 big_sepL_fmap.
    iApply (big_sepL_impl with "Hcond"). iModIntro. iIntros (? [rt [lt1 lt2]] Hlook).
    iApply typed_place_cond_ty_uniq_core_eq.
  Qed.
  Local Lemma typed_place_cond_ty_uniq_unblockable_struct {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) κ γ :
    ([∗ list] ty1; ty2 ∈ hzipl rts lts1; hzipl rts lts2, typed_place_cond_ty (Uniq κ γ) (projT2 ty1) (projT2 ty2)) -∗
    ([∗ list] ty ∈ hzipl2 rts lts1 lts2, imp_unblockable [κ] (projT2 ty).2).
  Proof.
    iIntros "Hcond".
    iPoseProof (big_sepL2_to_zip with "Hcond") as "Hcond".
    rewrite zip_hzipl_hzipl2 big_sepL_fmap.
    iApply (big_sepL_impl with "Hcond").
    iModIntro. iIntros (? [rt [lt1 lt2]] Hlook).
    iApply typed_place_cond_ty_uniq_unblockable.
  Qed.

  Local Lemma struct_acc_uniq_elems_core π l {rts} (lts lts' : hlist ltype rts) (rs : plist place_rfn rts) fields :
    length (field_names fields) = length rts →
    ([∗ list] ty ∈ hzipl2 rts lts lts', ∀ b' r, ltype_eq b' r r (ltype_core (projT2 ty).1) (ltype_core (projT2 ty).2)) -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts rs) struct_make_uninit_ltype,
      ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ ltype_core (projT2 ty).1)) -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts' rs) struct_make_uninit_ltype,
        ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ ltype_core (projT2 ty).1)).
  Proof.
    iIntros (Ha) "#Hcond >Hb". iApply big_sepL_fupd.
    iApply big_sepL2_elim_l.
    iPoseProof (big_sepL_extend_r with "Hb") as "Hb"; first last.
    { iApply (big_sepL2_impl with "Hb").
      iModIntro. iIntros (? [? []] [? []] Hlook1 Hlook2).
      simpl. iIntros "(%ly & ? & ? & Hl)".
      apply pad_struct_lookup_Some in Hlook1 as (n & ly1 & Hlook & Hlook1); first last.
      { rewrite hpzipl_length Ha. lia. }
      destruct Hlook1 as [(? & Hlook1) | (-> & Hlook1)].
      - apply hpzipl_lookup_inv_hzipl_pzipl in Hlook1 as (Hlook1 & Hlook1').
        destruct n; last done.
        eapply pad_struct_lookup_Some_Some in Hlook2; cycle -2.
        { rewrite hpzipl_length Ha. lia. }
        { done. }
        apply hpzipl_lookup_inv_hzipl_pzipl in Hlook2 as (Hlook2 & Hlook2').
        rewrite Hlook1' in Hlook2'. injection Hlook2' => Heq1 ?. subst.
        apply existT_inj in Heq1 as ->.
        iPoseProof (big_sepL_lookup with "Hcond")as "Heq".
        { apply hzipl_hzipl2_lookup; done. }
        (*iPoseProof (typed_place_cond_ty_incl _ (Uniq κ γ) with "Hincl_k Hcond'") as "Hcond''".*)
        iDestruct ("Heq" $! (Owned _) _) as "((%Hst1 & #Heq1 & _) & (_ & #Heq2 & _))".
        (*setoid_rewrite ltype_own_core_equiv. *)
        iPoseProof ("Heq1" with "Hl") as "Hb".
        simpl in Hst1. rewrite !ltype_core_syn_type_eq in Hst1.
        iMod "Hb". iModIntro. rewrite Hst1. cbn. eauto with iFrame.
      - injection Hlook1 => Hlook1_1 Hlook1_2 ?. subst.
        apply existT_inj in Hlook1_2. apply existT_inj in Hlook1_1. subst.
        eapply pad_struct_lookup_Some_None in Hlook2; cycle 1.
        { rewrite hpzipl_length Ha. lia. }
        { done. }
        injection Hlook2 => Hlook2_1 Hlook2_2 ?. subst.
        apply existT_inj in Hlook2_1. apply existT_inj in Hlook2_2. subst.
        eauto with iFrame.
    }
    rewrite !pad_struct_length //.
  Qed.

  Local Lemma struct_acc_uniq_elems_unblock π l {rts} (lts lts' : hlist ltype rts) (rs : plist place_rfn rts) fields κ γ :
    length (field_names fields) = length rts →
    ([∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts lts', typed_place_cond_ty (Uniq κ γ) (projT2 ty1) (projT2 ty2)) -∗
    [† κ] -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts' rs) struct_make_uninit_ltype,
      ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ (projT2 ty).1)) -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts rs) struct_make_uninit_ltype,
        ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ ltype_core (projT2 ty).1)).
  Proof.
    iIntros (Ha) "#Hcond #Hdead >Hb". iApply big_sepL_fupd.
    iApply big_sepL2_elim_l.
    iPoseProof (big_sepL_extend_r with "Hb") as "Hb"; first last.
    { iApply (big_sepL2_impl with "Hb").
      iModIntro. iIntros (? [? []] [? []] Hlook1 Hlook2).
      simpl. iIntros "(%ly & ? & ? & Hl)".
      apply pad_struct_lookup_Some in Hlook1 as (n & ly1 & Hlook & Hlook1); first last.
      { rewrite hpzipl_length Ha. lia. }
      destruct Hlook1 as [(? & Hlook1) | (-> & Hlook1)].
      - apply hpzipl_lookup_inv_hzipl_pzipl in Hlook1 as (Hlook1 & Hlook1').
        destruct n; last done.
        eapply pad_struct_lookup_Some_Some in Hlook2; cycle -2.
        { rewrite hpzipl_length Ha. lia. }
        { done. }
        apply hpzipl_lookup_inv_hzipl_pzipl in Hlook2 as (Hlook2 & Hlook2').
        rewrite Hlook1' in Hlook2'. injection Hlook2' => Heq1 ?. subst.
        apply existT_inj in Heq1 as ->.
        iPoseProof (typed_place_cond_ty_uniq_core_eq_struct _ _ κ γ with "Hcond") as "Heq".
        iPoseProof (typed_place_cond_ty_uniq_unblockable_struct _ _ κ γ with "Hcond") as "Hub".

        iPoseProof (big_sepL_lookup with "Heq") as "Heq1".
        { apply hzipl_hzipl2_lookup; done. }
        iPoseProof (big_sepL_lookup with "Hub") as "Hub1".
        { apply hzipl_hzipl2_lookup; done. }
        cbn.
        iMod (imp_unblockable_use with "Hub1 [] Hl") as "Hl"; first done.
        { iFrame "Hdead"; done. }
        iDestruct ("Heq1" $! (Owned _) _) as "((%Hst1 & #Heq1' & _) & (_ & #Heq2 & _))".
        iMod ("Heq2" with "Hl") as "Hl".
        rewrite !ltype_core_syn_type_eq in Hst1.
        rewrite -Hst1.
        eauto with iFrame.
      - injection Hlook1 => Hlook1_1 Hlook1_2 ?. subst.
        apply existT_inj in Hlook1_2. apply existT_inj in Hlook1_1. subst.
        eapply pad_struct_lookup_Some_None in Hlook2; cycle 1.
        { rewrite hpzipl_length Ha. lia. }
        { done. }
        injection Hlook2 => Hlook2_1 Hlook2_2 ?. subst.
        apply existT_inj in Hlook2_1. apply existT_inj in Hlook2_2. subst.
        setoid_rewrite ltype_core_uninit. eauto with iFrame.
    }
    rewrite !pad_struct_length //.
  Qed.

  Lemma struct_ltype_acc_uniq {rts} F π (lts : hlist ltype rts) (r : plist place_rfn rts) l sls κ γ q R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] PlaceIn r @ StructLtype lts sls -∗
    ∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length sls.(sls_fields) = length rts⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗ |={F}=>
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
        (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) ∗
      logical_step F
      (((* weak access *)
        ∀ bmin (lts' : hlist ltype rts) (r' : plist place_rfn rts),
        bmin ⊑ₖ Uniq κ γ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) -∗
        ([∗ list] ty1; ty2 ∈ hzipl rts lts; hzipl rts lts', typed_place_cond_ty (bmin) (projT2 ty1) (projT2 ty2)) -∗
        ([∗ list] ty1; ty2 ∈ pzipl rts r; pzipl rts r', typed_place_cond_rfn (bmin) (projT2 ty1) (projT2 ty2)) ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r' @ StructLtype lts' sls ∗
        R ∗
        typed_place_cond (Uniq κ γ ⊓ₖ bmin) (StructLtype lts sls) (StructLtype lts' sls) (PlaceIn r) (PlaceIn r')) ∧
      ((* strong access, go to OpenedLtype *)
        ∀ rts' (lts' : hlist ltype rts') (r' : plist place_rfn rts'),
        (* same number of fields *)
        ⌜length rts' = length rts⌝ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) -∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn r' @ OpenedLtype (StructLtype lts' sls) (StructLtype lts sls) (StructLtype lts sls)
            (λ ri ri', ⌜ri = ri'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ HR Hb". rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hb" as "(%sl & %Halg & %Hlen & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    iExists sl. iFrame "#%".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    (* NOTE: we are currently throwing away the existing "coring"-viewshift that we get *)
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ'' & #Hincl & Hb & _ & Hb_cl)"; first done.
    iMod "Hcl_F" as "_".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' &  Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat".
    iModIntro.
    iSplit.
    - (* close *)
      iIntros (bmin lts' rs') "#Hincl_k Hl #Hcond #Hrcond".
      iMod (gvar_update rs' with "Hauth Hrfn") as "(Hauth & Hrfn)".
      set (V := (∃ r', gvar_auth γ r' ∗
        (|={lftE}=> [∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ ltype_own (projT2 ty).1 (Owned false) π (projT2 ty).2 (l +ₗ offset_of_idx (sl_members sl) i)))%I).
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      efeed pose proof struct_layout_spec_has_layout_fields_length as Ha; first done.
      iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hl]") as "(Hb & Htok)".
      { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
        iModIntro. iNext. iExists r'. iFrame "Hauth".
        rewrite Hlen in Ha. clear -Ha.
        iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
        setoid_rewrite ltype_own_core_equiv.
        iApply (struct_acc_uniq_elems_unblock with "[Hcond] Hdead Hb").
        { done. }
        iApply (big_sepL2_impl with "Hcond").
        iModIntro. iIntros (? [] [] ? ?).
        iApply typed_place_cond_ty_incl; done.
      }
      { iModIntro. rewrite /V. iExists rs'. iFrame. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_struct_unfold /struct_ltype_own.
        iExists sl. iFrame. do 4 iR.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        iModIntro. subst V.
        (* need to adapt the pinned part, too *)
        iApply (pinned_bor_iff with "[] [] Hb").
        { iNext. iModIntro. eauto. }
        iNext. iModIntro.
        setoid_rewrite ltype_own_core_equiv.
        iAssert ([∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts lts', typed_place_cond_ty (Uniq κ γ) (projT2 ty1) (projT2 ty2))%I with "[Hcond]" as "Ha".
        { iApply (big_sepL2_impl with "Hcond"). iModIntro. iIntros (k [] [] ? ?). by iApply typed_place_cond_ty_incl. }
        iSplit.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb".
          iApply (struct_acc_uniq_elems_core with "[] Hb"); [ lia | ].
          iApply typed_place_cond_ty_uniq_core_eq_struct.
          iApply (big_sepL2_impl with "Hcond").
          iModIntro. iIntros (? [] [] ? ?). iApply (typed_place_cond_ty_incl with "Hincl_k").
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb".
          iApply (struct_acc_uniq_elems_core with "[] Hb"); [ lia | ].
          rewrite hzipl2_swap big_sepL_fmap.
          iPoseProof (typed_place_cond_ty_uniq_core_eq_struct with "Ha") as "Hb".
          iApply (big_sepL_impl with "Hb").
          iModIntro. iIntros (? [? []] ?) "Heq" => /=.
          iIntros (??). iApply ltype_eq_sym. iApply "Heq".
      }
      iApply (typed_place_cond_incl bmin).
      { iApply bor_kind_incl_glb; first done. iApply bor_kind_incl_refl. }
      iSplit.
      + iApply (struct_ltype_place_cond_ty _ _ lts' sls with "Hcond").
        clear. induction rts as [ | rt rts IH]; simpl; econstructor; last apply IH.
        apply place_access_rt_rel_refl.
      + by iApply (typed_place_cond_rfn_lift_struct).
    - (* shift to OpenedLtype *)
      iIntros (rts' lts' rs') "%Hlen' Hl".
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_struct_unfold /struct_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(%sl' & %Hsl' & _ & _ & _ & _ & %r' & -> & >Hb)".
        assert (sl' = sl) as ->. { rewrite Halg in Hsl'. injection Hsl' as ->. done. }
        iModIntro. setoid_rewrite ltype_own_core_equiv.

        rewrite pad_struct_pull_core. iApply (big_sepL_impl with "Hb").
        iModIntro. iIntros (? [? []] ?). simpl. rewrite ltype_core_syn_type_eq. eauto. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_struct_unfold /struct_ltype_own.
        setoid_rewrite ltype_own_core_equiv.
        iModIntro. iExists sl. iFrame "% ∗". iR.
        iModIntro.
        setoid_rewrite pad_struct_pull_core.
        setoid_rewrite ltype_core_sigT_ltype_core_idemp.
        setoid_rewrite ltype_st_sigT_ltype_core.
        iApply (pinned_bor_iff with "[] [] Hp").
        - iNext. iModIntro. iSplit.
          all: iIntros "(%r'' & ? & Hb)"; iExists r''; iFrame;
            iMod "Hb"; iModIntro; iApply (big_sepL_impl with "Hb");
            iIntros "!>" (? [? []] ?); eauto.
        - iNext. iModIntro. iSplit.
          all: iIntros "(%r'' & ? & Hb)"; iExists r''; iFrame;
            iMod "Hb"; iModIntro; iApply (big_sepL_impl with "Hb");
            iIntros "!>" (? [? []] ?); eauto. }
      { rewrite ltype_own_struct_unfold /struct_ltype_own.
        iExists sl. iFrame "% ∗". rewrite Hlen'. iR. iR. iR.
        iExists rs'. iR. iModIntro. iFrame. }
  Qed.

  Lemma struct_ltype_acc_shared {rts} F π (lts : hlist ltype rts) (r : plist place_rfn rts) l sls κ :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] #r @ StructLtype lts sls -∗
    ∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length sls.(sls_fields) = length rts⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗ |={F}=>
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Shared κ] (projT2 ty).2 @ (projT2 ty).1) ∗
      (∀ rts' (lts' : hlist ltype rts') (r' : plist place_rfn rts'),
        (* the number of fields should remain equal *)
        ⌜length rts' = length rts⌝ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Shared κ] (projT2 ty).2 @ (projT2 ty).1) ={F}=∗
        l ◁ₗ[π, Shared κ] #r' @ StructLtype lts' sls).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hb" as "(%sl & %Halg & %Hlen & %Hly & #Hlb & %r' & -> & #Hb)".
    iExists sl. iFrame "#%". iMod (fupd_mask_mono with "Hb") as "Hb'"; first done.
    iModIntro. iFrame.
    iIntros (rts' lts' r) "%Hlen_eq #Hb'".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iExists sl. rewrite Hlen_eq. iFrame "%#∗".
    iExists r. iSplitR; first done. iModIntro. done.
  Qed.

   (** Place lemmas for products *)
  (* NOTE: these lemmas require sideconditions for the unaffected components of the product that state that we can keep blocked subplaces blocked because the outer bor_kinds outlive the the blocking lifetimes.
    It would be good if we could remove this sidecondition with a smarter setup of ltypes... TODO
      But it's not clear that that is possible: We can arbitrarily shorten the lifetime of outer things -- then at the later point we just don't knwo anymore that really the lender expects it back at a later point.
    *)

  Local Lemma struct_lift_place_cond_ty_homo {rts} (lts : hlist ltype rts) i (lto lto' : ltype (lnth (unit : Type) rts i)) bmin0 :
    hnth (UninitLtype UnitSynType) lts i = lto →
    i < length rts →
    ([∗ list] κ0 ∈ concat ((λ X : Type, ltype_blocked_lfts) +c<$> lts), bor_kind_outlives bmin0 κ0) -∗
    typed_place_cond_ty bmin0 lto lto' -∗
    [∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts (hlist_insert_id (unit : Type) rts lts i lto'), typed_place_cond_ty bmin0 (projT2 ty1) (projT2 ty2).
  Proof.
    iIntros (Hlto ?) "#Houtl Hcond".
    rewrite hzipl_hlist_insert_id.
    rewrite -(list_insert_id (hzipl rts lts) i (existT _ lto)).
    2: { rewrite -Hlto. apply hzipl_lookup_hnth. done. }
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ a b, typed_place_cond_ty _ _ _) 0%nat); simpl.
    2: { rewrite hzipl_length. lia. }
    2: { rewrite insert_length hzipl_length. lia. }
    iSplitL "Hcond"; first done.
    iApply big_sepL2_intro. { rewrite insert_length; done. }
    iIntros "!>" (k [rt1 lt1] [rt2 lt2] Hlook1 Hlook2).
    case_decide as Heqki; first done.
    rewrite list_lookup_insert_ne in Hlook2; last done.
    rewrite Hlook2 in Hlook1. injection Hlook1 as [= -> Heq2].
    apply existT_inj in Heq2 as ->.
    iApply typed_place_cond_ty_refl.
    iPoseProof (big_sepL_concat_lookup _ _ k with "Houtl") as "Ha".
    { eapply hcmap_lookup_hzipl. done. }
    simpl. done.
  Qed.
  Local Lemma struct_lift_place_cond_rfn_homo {rts} (rs : plist place_rfn rts) i (ro ro' : place_rfn (lnth (unit : Type) rts i)) bmin0 :
    pnth (#tt) rs i = ro →
    i < length rts →
    ⊢@{iProp Σ} typed_place_cond_rfn bmin0 ro ro' -∗
    ([∗ list] ty1;ty2 ∈ pzipl rts rs;pzipl rts (plist_insert_id (unit : Type) rts rs i ro'), typed_place_cond_rfn bmin0 (projT2 ty1) (projT2 ty2)).
  Proof.
    (* plan: first separate the first one also into an insert, then show a general lemma about inserting into big_sepL2 *)
    iIntros (Hro ?) "Hcond".
    rewrite pzipl_plist_insert_id.
    rewrite -(list_insert_id (pzipl rts rs) i (existT _ ro)).
    2: { rewrite -Hro. apply pzipl_lookup_pnth. done. }
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ a b, _) 0%nat); simpl.
    2: { rewrite pzipl_length. lia. }
    2: { rewrite insert_length pzipl_length. lia. }
    iSplitL "Hcond"; first done.
    iApply big_sepL2_intro. { rewrite insert_length; done. }
    iIntros "!>" (k [rt1 r1] [rt2 r2] Hlook1 Hlook2).
    case_decide as Heqki; first done.
    rewrite list_lookup_insert_ne in Hlook2; last done.
    rewrite Hlook2 in Hlook1. injection Hlook1 as [= -> Heq2].
    apply existT_inj in Heq2 as ->.
    destruct bmin0; done.
    (*iApply typed_place_cond_rfn_refl.*)
  Qed.

  (* needs to have lower priority than the id instance *)
  Lemma typed_place_ofty_struct {rts} π E L l (tys : hlist type rts) (r : place_rfn (plist place_rfn rts)) sls bmin0 b P T :
    typed_place π E L l (StructLtype (hmap (λ _, OfTy) tys) sls) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (struct_t sls tys)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last iFrame.
    iIntros (?) "HL CTX HE".
    iIntros (??). iApply struct_t_unfold.
  Qed.
  Global Instance typed_place_ofty_struct_inst {rts} π E L l (tys : hlist type rts) (r : place_rfn (plist place_rfn rts)) sls bmin0 b P :
    TypedPlace E L π l (◁ (struct_t sls tys))%I r bmin0 b P | 30 :=
        λ T, i2p (typed_place_ofty_struct π E L l tys r sls bmin0 b P T).

  Lemma typed_place_struct_owned {rts} (lts : hlist ltype rts) π E L (r : plist place_rfn rts) sls f wl bmin0 P l
    (T : place_cont_t (plist place_rfn rts)) :
    ((* sidecondition for other components *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (concat ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : Type) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L (l atst{sls}ₗ f) lto ro bmin0 (Owned false) P
        (λ L' κs l1 b2 bmin rti ltyi ri strong weak,
          T L' κs l1 b2 bmin rti ltyi ri
          (fmap (λ strong, mk_strong
            (λ rt', plist place_rfn (<[i := strong.(strong_rt) rt']> rts))
            (λ rt' lt' r', StructLtype (hlist_insert rts lts i _ (strong.(strong_lt) _ lt' r')) sls)
            (λ rt' (r' : place_rfn rt'), #(plist_insert rts r i _ (strong.(strong_rfn) _ r')))
            strong.(strong_R)) strong)
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, StructLtype (hlist_insert_id (unit : Type) rts lts i (weak.(weak_lt) lti2 ri2)) sls)
            (λ (r' : place_rfn rti), #(plist_insert_id (unit : Type) rts r i (weak.(weak_rfn) r')))
            weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Owned wl) (GetMemberPCtx sls f :: P) T.
  Proof.
    iIntros "(%Houtl & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL #Hincl0 Hl HΦ/=".
    iPoseProof (struct_ltype_acc_owned F with "Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".

    eapply (sls_field_index_of_lookup) in Hfield as (ly & Hfield).
    assert (i < length rts)%nat. { rewrite -Hmem. eapply lookup_lt_Some. done. }
    (* Note: if we later on want to allow the struct alg to change order of fields, then we need to change pad_struct (or use something else here), because it currently relies on the order of the types and the order of the sl members matching up *)
    assert (field_index_of (sl_members sl) f = Some i) as Hfield'.
    { eapply struct_layout_spec_has_layout_lookup; done. }
    iApply (wp_logical_step with "TIME Hcl"); [done | solve_ndisj.. | ].
    iApply (wp_get_member).
    { apply val_to_of_loc. }
    { done. }
    { by eapply field_index_of_to_index_of. }
    { done. }
    iModIntro. iNext. iIntros "Hcred Hcl". iExists _. iSplitR; first done.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : Type) (UninitLtype UnitSynType) (PlaceIn ())); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 [Hb]").
    { rewrite -Hlto -Hro. done. }
    iModIntro. iIntros (L' κs l2 b2 bmin rti ltyi ri strong weak) "#Hincl1 Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hli").
    simpl. iSplit.
    - (* strong *)
      destruct strong as [strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hli %Hst'".
      iDestruct "Hcont" as "(Hcont & _)".
      iMod ("Hcont" with "Hli [//]") as "(Hb1 & %Hst2 & HR)".
      iDestruct "Hc_close" as "[Hc_close _]".
      iPoseProof ("Hc_close" with "Hb1 []") as "Hb".
      { rewrite -Hst2. done. }
      iFrame.
      iMod ("Hcl" with "[] Hb") as "Hb".
      { rewrite insert_length //. }
      iFrame. iPureIntro. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hcont" as "[_ Hcont]".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hli Hcond".
      iMod ("Hcont" $! _ _ bmin' with "Hincl2 Hli Hcond") as "(Hb1 & Hcond & HL & HR)".
      simpl. iDestruct "Hc_close" as "[_ Hc_close]".
      iPoseProof ("Hc_close" with "Hb1") as "Hb".
      iFrame "HL HR".
      iDestruct "Hcond" as "(#Hcond_ty & Hcond_rfn)".
      iMod ("Hcl" with "[] [Hb]") as "Hb".
      { done. }
      { iApply "Hb". iPoseProof (typed_place_cond_ty_syn_type_eq with "Hcond_ty") as "<-". done. }
      iFrame "Hb".
      iApply (typed_place_cond_struct_lift with "[] [Hcond_rfn] []").
      + iApply (struct_lift_place_cond_ty_homo with "Houtl Hcond_ty"); [done | lia].
      + iApply (struct_lift_place_cond_rfn_homo with "Hcond_rfn"); [done | lia].
      + iPureIntro. clear. induction rts; simpl; first done.
        constructor; first apply place_access_rt_rel_refl. done.
  Qed.
  Global Instance typed_place_struct_owned_inst π E L {rts} (lts : hlist ltype rts) (r : plist place_rfn rts) sls wl bmin0 f l P :
    TypedPlace E L π l (StructLtype lts sls) (PlaceIn r) bmin0 (Owned wl) (GetMemberPCtx sls f :: P) | 30 :=
        λ T, i2p (typed_place_struct_owned lts π E L r sls f wl bmin0 P l T).

  Lemma typed_place_struct_uniq {rts} (lts : hlist ltype rts) π E L (r : plist place_rfn rts) sls f κ γ bmin0 P l
    (T : place_cont_t (plist place_rfn rts)) :
    ((* sidecondition for other components *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (concat ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* get lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : Type) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L2 (l atst{sls}ₗ f) lto ro bmin0 (Owned false) P
        (λ L' κs' l1 b2 bmin rti ltyi ri strong weak,
          T L' (κs ++ κs') l1 b2 bmin rti ltyi ri
          None
          (* TODO allow strong by opening *)
          (*
          (fmap (λ strong, mk_strong
            (λ rt', plist place_rfn (<[i := strong.(strong_rt) rt']> rts))
            (λ rt' lt' r', StructLtype (hlist_insert rts lts i _ (strong.(strong_lt) _ lt' r')) sls)
            (λ rt' (r' : place_rfn rt'), #(plist_insert rts r i _ (strong.(strong_rfn) _ r')))
            strong.(strong_R)) strong)
            *)
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, StructLtype (hlist_insert_id (unit : Type) rts lts i (weak.(weak_lt) lti2 ri2)) sls)
            (λ (r' : place_rfn rti), #(plist_insert_id (unit : Type) rts r i (weak.(weak_rfn) r')))
            weak.(weak_R)) weak)))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Uniq κ γ) (GetMemberPCtx sls f :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%Houtl & %κs & %L' &  %Hal & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL #Hincl0 Hl HΦ/=".

    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".
    iApply fupd_wp.
    iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcltok & HL)"; [done.. | ].
    iMod "HclF" as "_".

    iPoseProof (struct_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Htok Hcltok Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.

    eapply (sls_field_index_of_lookup) in Hfield as (ly & Hfield).
    assert (i < length rts)%nat. { rewrite -Hmem. eapply lookup_lt_Some. done. }
    (* Note: if we later on want to allow the struct alg to change order of fields, then we need to change pad_struct (or use something else here), because it currently relies on the order of the types and the order of the sl members matching up *)
    assert (field_index_of (sl_members sl) f = Some i) as Hfield'.
    { eapply struct_layout_spec_has_layout_lookup; done. }
    iApply (wp_logical_step with "TIME Hcl"); [done | solve_ndisj.. | ].
    iApply (wp_get_member).
    { apply val_to_of_loc. }
    { done. }
    { by eapply field_index_of_to_index_of. }
    { done. }
    iModIntro. iModIntro. iNext. iIntros "Hcred Hcl". iExists _. iSplitR; first done.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : Type) (UninitLtype UnitSynType) (PlaceIn ())); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [Hincl0] [Hb]").
    { destruct bmin0; done. }
    { rewrite -Hlto -Hro. done. }
    iModIntro. iIntros (L2 κs' l2 b2 bmin rti ltyi ri strong weak) "#Hincl1 Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hli").
    simpl. iSplit.
    - (* strong *)
      destruct strong as [strong | ]; last done.
      done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hcont" as "[_ Hcont]".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hli Hcond".
      iMod ("Hcont" $! _ _ bmin' with "Hincl2 Hli Hcond") as "(Hb1 & Hcond & HL & HR)".
      simpl. iDestruct "Hc_close" as "[_ Hc_close]".
      iPoseProof ("Hc_close" with "Hb1") as "Hb".
      iFrame "HR".
      iDestruct "Hcond" as "(#Hcond_ty & #Hcond_rfn)".
      iDestruct "Hcl" as "(Hcl & _)".
      iMod ("Hcl" with "[] [Hb] [] [] ") as "(Hb & Htoks & Hcond)".
      { done. }
      { iApply "Hb". iPoseProof (typed_place_cond_ty_syn_type_eq with "Hcond_ty") as "<-". done. }
      { iApply (struct_lift_place_cond_ty_homo with "Houtl Hcond_ty"); [done | lia]. }
      { iApply (struct_lift_place_cond_rfn_homo with "Hcond_rfn"); [done | lia]. }
      iFrame "Hb".
      rewrite llft_elt_toks_app. iFrame.
      iApply typed_place_cond_incl; last done.
      iApply bor_kind_min_incl_r.
  Qed.
  Global Instance typed_place_struct_uniq_inst π E L {rts} (lts : hlist ltype rts) (r : plist place_rfn rts) sls κ γ bmin0 f l P :
    TypedPlace E L π l (StructLtype lts sls) (PlaceIn r) bmin0 (Uniq κ γ) (GetMemberPCtx sls f :: P) | 30 :=
        λ T, i2p (typed_place_struct_uniq lts π E L r sls f κ γ bmin0 P l T).

  Lemma typed_place_struct_shared {rts} (lts : hlist ltype rts) π E L (r : plist place_rfn rts) sls f κ bmin0 P l
    (T : place_cont_t (plist place_rfn rts)) :
    ((* sidecondition for other components *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (concat ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : Type) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L (l atst{sls}ₗ f) lto ro bmin0 (Shared κ) P
        (λ L' κs l1 b2 bmin rti ltyi ri strong weak,
          T L' κs l1 b2 bmin rti ltyi ri
          None (* TODO *)
          (*(fmap (λ strong, mk_strong*)
            (*(λ rt', plist place_rfn (<[i := strong.(strong_rt) rt']> rts))*)
            (*(λ rt' lt' r', StructLtype (hlist_insert rts lts i _ (strong.(strong_lt) _ lt' r')) sls)*)
            (*(λ rt' (r' : place_rfn rt'), #(plist_insert rts r i _ (strong.(strong_rfn) _ r')))*)
            (*strong.(strong_R)) strong)*)
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, StructLtype (hlist_insert_id (unit : Type) rts lts i (weak.(weak_lt) lti2 ri2)) sls)
            (λ (r' : place_rfn rti), #(plist_insert_id (unit : Type) rts r i (weak.(weak_rfn) r')))
            weak.(weak_R)) weak))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Shared κ) (GetMemberPCtx sls f :: P) T.
  Proof.
    iIntros "(% & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL #Hincl0 Hl HΦ/=".
    iPoseProof (struct_ltype_acc_shared F with "Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".

    eapply (sls_field_index_of_lookup) in Hfield as (ly & Hfield).
    assert (i < length rts)%nat. { rewrite -Hmem. eapply lookup_lt_Some. done. }
    (* Note: if we later on want to allow the struct alg to change order of fields, then we need to change pad_struct (or use something else here), because it currently relies on the order of the types and the order of the sl members matching up *)
    assert (field_index_of (sl_members sl) f = Some i) as Hfield'.
    { eapply struct_layout_spec_has_layout_lookup; done. }
    (*iApply (wp_logical_step with "TIME Hcl"); [done | solve_ndisj.. | ].*)
    iApply (wp_get_member).
    { apply val_to_of_loc. }
    { done. }
    { by eapply field_index_of_to_index_of. }
    { done. }
    iModIntro. iNext. iIntros "Hcred". iExists _. iR.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : Type) (UninitLtype UnitSynType) (PlaceIn ())); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 [Hb]").
    { rewrite -Hlto -Hro. done. }
    iIntros (L' κs l2 b2 bmin rti ltyi ri strong weak) "#Hincl1 Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ _ with "Hincl1 Hli").
    simpl. iSplit.
    - (* strong *)
      done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hcont" as "[_ Hcont]".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hli Hcond".
      iMod ("Hcont" $! _ _ bmin' with "Hincl2 Hli Hcond") as "(Hb1 & Hcond & HL & HR)".
      simpl. iDestruct "Hc_close" as "[_ Hc_close]".
      iPoseProof ("Hc_close" with "Hb1") as "Hb".
      iFrame "HL HR".
      iDestruct "Hcond" as "(#Hcond_ty & Hcond_rfn)".
      iMod ("Hcl" with "[] [Hb]") as "Hb".
      { done. }
      { iApply "Hb". iPoseProof (typed_place_cond_ty_syn_type_eq with "Hcond_ty") as "<-". done. }
      iFrame "Hb".
      iApply (typed_place_cond_struct_lift with "[] [Hcond_rfn] []").
      + iApply (struct_lift_place_cond_ty_homo with "Houtl Hcond_ty"); [done | lia].
      + iApply (struct_lift_place_cond_rfn_homo with "Hcond_rfn"); [done | lia].
      + iPureIntro. clear. induction rts; simpl; first done.
        constructor; first apply place_access_rt_rel_refl. done.
  Qed.
  Global Instance typed_place_struct_shared_inst π E L {rts} (lts : hlist ltype rts) (r : plist place_rfn rts) sls κ bmin0 f l P :
    TypedPlace E L π l (StructLtype lts sls) #r bmin0 (Shared κ) (GetMemberPCtx sls f :: P) | 30 :=
        λ T, i2p (typed_place_struct_shared lts π E L r sls f κ bmin0 P l T).

  Definition stratify_ltype_struct_iter_cont_t := llctx → iProp Σ → ∀ rts' : list Type, hlist ltype rts' → plist place_rfn rts' → iProp Σ.
  Definition stratify_ltype_struct_iter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (i0 : nat) (sls : struct_layout_spec) {rts} (ltys : hlist ltype rts) (rfns : plist place_rfn rts) (k : bor_kind) (T : stratify_ltype_struct_iter_cont_t) : iProp Σ :=
    ∀ F sl, ⌜lftE ⊆ F⌝ -∗
    ⌜lft_userE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜struct_layout_spec_has_layout sls sl⌝ -∗
    ⌜i0 ≤ length sls.(sls_fields)⌝ -∗
    ⌜(i0 + length rts = length sls.(sls_fields))%nat⌝ -∗
    ([∗ list] i ↦ p ∈ hpzipl rts ltys rfns, let '(existT rt (lt, r)) := p in
      ∃ name st, ⌜sls.(sls_fields) !! (i + i0)%nat = Some (name, st)⌝ ∗
      (l atst{sls}ₗ name) ◁ₗ[π, k] r @ lt) ={F}=∗
    ∃ (L' : llctx) (R' : iProp Σ) (rts' : list Type) (ltys' : hlist ltype rts') (rfns' : plist place_rfn rts'),
      ⌜length rts = length rts'⌝ ∗
      ([∗ list] i ↦ p; p2 ∈ hpzipl rts ltys rfns; hpzipl rts' ltys' rfns',
          let '(existT rt (lt, r)) := p in
          let '(existT rt' (lt', r')) := p2 in
          ⌜ltype_st lt = ltype_st lt'⌝) ∗
      logical_step F (
        ([∗ list] i ↦ p ∈ hpzipl rts' ltys' rfns', let '(existT rt (lt, r)) := p in
          ∃ name st, ⌜sls.(sls_fields) !! (i + i0)%nat = Some (name, st)⌝ ∗
          (l atst{sls}ₗ name) ◁ₗ[π, k] r @ lt) ∗ R') ∗
      llctx_interp L' ∗
      T L' R' rts' ltys' rfns'.

  Lemma stratify_ltype_struct_iter_nil π E L mu md ma {M} (m : M) (l : loc) sls k i0 (T : stratify_ltype_struct_iter_cont_t) :
    T L True [] +[] -[]
    ⊢ stratify_ltype_struct_iter π E L mu md ma m l i0 sls +[] -[] k T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL ??? Hl".
    iModIntro. iExists L, True%I, [], +[], -[].
    iR. iFrame. simpl. iR. iApply logical_step_intro; eauto.
  Qed.

  Lemma stratify_ltype_struct_iter_cons π E L mu mdu ma {M} (m : M) (l : loc) sls i0 {rts rt} (ltys : hlist ltype rts) (rfns : plist place_rfn (rt :: rts)) (lty : ltype rt) k T :
    (∃ r rfns0, ⌜rfns = r -:: rfns0⌝ ∗
    stratify_ltype_struct_iter π E L mu mdu ma m l (S i0) sls ltys rfns0 k (λ L2 R2 rts2 ltys2 rs2,
      (∀ name st, ⌜sls.(sls_fields) !! i0 = Some (name, st)⌝ -∗
      stratify_ltype π E L2 mu mdu ma m (l atst{sls}ₗ name) lty r k (λ L3 R3 rt3 lty3 r3,
        T L3 (R3 ∗ R2) (rt3 :: rts2) (lty3 +:: ltys2) (r3 -:: rs2)))))
    ⊢ stratify_ltype_struct_iter π E L mu mdu ma m l i0 sls (lty +:: ltys) (rfns) k T.
  Proof.
    iIntros "(%r &  %rfns0 & -> & HT)". iIntros (????) "#CTX #HE HL %Halg %Hlen %Hleneq Hl".
    simpl. iDestruct "Hl" as "(Hl & Hl2)". simpl in *.
    iMod ("HT" with "[//] [//] CTX HE HL [//] [] [] [Hl2]") as "(%L2' & %R2' & %rts2' & %ltys2' & %rfns2' & %Hlen' & Hst & Hl2 & HL & HT)".
    { rewrite -Hleneq. iPureIntro. lia. }
    { rewrite -Hleneq. iPureIntro. lia. }
    { iApply (big_sepL_mono with "Hl2"). intros ? [? []] ?. by rewrite Nat.add_succ_r. }
    iDestruct "Hl" as "(%name & %st & %Hlook & Hl)".
    (*edestruct (lookup_lt_is_Some_2 sls.(sls_fields) i0) as ([name ?] & Hlook); first by lia.*)
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl") as "(%L3 & %R3 & %rt' & %lt' & %r' & HL & Hst1 & Hl & HT)".
    iModIntro. iExists L3, (R3 ∗ R2')%I, _, _, _. iFrame.
    iSplitR. { rewrite Hlen'. done. }
    iApply (logical_step_compose with "Hl2"). iApply (logical_step_wand with "Hl").
    iIntros "(Hl & HR1) (Hl2 & HR2)".
    simpl. iFrame.
    iSplitL "Hl". { iExists _, _. iFrame. done. }
    iApply (big_sepL_mono with "Hl2"). intros ? [? []] ?. by rewrite Nat.add_succ_r.
  Qed.

  (*
      Owned:
      - stratify all components
      - if we should refold:
          fold all of them to ofty via cast, then done.
            TODO: should i really do that? It seems like the subtyping should also be able to deal with that.
            and at other places, i anyways have cast_ltype.
            should check if I can.

     Uniq:
     - Basically, we want to stratify all the components
     - Then check if all of them obey the place cond
     - If they do not:
        + go to OpenedLtype
          Well, can this happen?
          Basically, only if we unfold an invariant etc.
          i.e. only if we use the stratification for unfolding.
          So I think this should be fine to omit, probably.
        (otherwise, if it is already unfolded before, this should already be in the Owned mode)
     - If they do:
        + if we don't need to refold, leave it
        + if we want to refold, just require that it is castable.

     Q: do we even need the Uniq case in practice?
        I guess only for unblocking. So we should have it.


     For implementation:
      basically want to be able to say
        - I get out a new hlist/plist
        - elementwise, compared to the old list, I get a place_cond (in Uniq case)
      Problem with existing stuff: I don't get an output. fold_list/relate_list are meant for proving stuff, not for computing something.

     maybe also compute a list, and each op can emit an element for the list?
     Or just have a specific stratify_ltype_list.
     e.g. what do I do with the R?
     I don't think it will be very re-usable anyways.


     How do I do it for arrays?
      Also a custom judgment?

     However, at least these won't need typeclasses I guess, just need to extend the liRJudgment tactics.

   *)
  (* TODO: stratification instance for StructLtype with optional refolding *)


  Lemma stratify_ltype_struct_owned {rts} π E L mu mdu ma {M} (m : M) l (lts : hlist ltype rts) (rs : plist place_rfn rts) sls wl T :
    stratify_ltype_struct_iter π E L mu mdu ma m l 0 sls lts rs (Owned false) (λ L2 R2 rts' lts' rs',
      T L2 R2 (plist place_rfn rts') (StructLtype lts' sls) (#rs'))
    ⊢ stratify_ltype π E L mu mdu ma m l (StructLtype lts sls) (#rs) (Owned wl) T.
  Proof.
    iIntros "HT". iIntros (???) "#CTX #HE HL Hl".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hl" as "(%sl & %Halg & %Hlen & %Hly & Hlb & Hcreds & %r' & <- & Hl)".
    iMod (maybe_use_credit with "Hcreds Hl") as "(Hcred & Hat & Hl)"; first done.
    iPoseProof (struct_ltype_focus_components with "Hl") as "(Hl & Hlcl)"; [done | done | ].
    iMod ("HT" with "[//] [//] CTX HE HL [//] [] [] [Hl]") as "(%L2 & %R2 & %rts' & %lts' & %rs' & %Hleneq & Hst & Hstep & HL & HT)".
    { iPureIntro. lia. }
    { rewrite Hlen.  done. }
    { iApply (big_sepL_mono with "Hl"). intros ? [? []] ?. rewrite Nat.add_0_r. done. }
    iModIntro. iExists L2, R2, _, _, _. iFrame. simp_ltypes. iR.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred2 !> (Ha & $)".
    iPoseProof ("Hlcl" $! rts' lts' rs' with "[//] [Hst] [Ha]") as "Hl".
    { iApply big_sepL2_Forall2.
      iApply (big_sepL2_impl with "Hst"). iModIntro. iIntros (? [? []] [? []] ? ?); done. }
    { iApply (big_sepL_mono with "Ha"). intros ? [? []] ?. rewrite Nat.add_0_r. eauto. }
    iModIntro.
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iExists _. iFrame "∗%".
    iSplitR. { by rewrite -Hleneq. }
    iExists _. iR. iNext. by iFrame.
  Qed.
  Global Instance stratify_ltype_struct_owned_inst {rts} π E L mu mdu ma {M} (m : M) l (lts : hlist ltype rts) (rs : plist place_rfn rts) sls wl :
    StratifyLtype π E L mu mdu ma m l (StructLtype lts sls) (#rs) (Owned wl) :=
    λ T, i2p (stratify_ltype_struct_owned π E L mu mdu ma m l lts rs sls wl T).

  (* TODO uniq*)

  Lemma stratify_ltype_ofty_struct {rts} π E L mu ma {M} (ml : M) l (tys : hlist type rts) (r : place_rfn (plist place_rfn rts)) sls b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (StructLtype (hmap (λ _, OfTy) tys) sls) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (struct_t sls tys)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply struct_t_unfold.
  Qed.
  Global Instance stratify_ltype_ofty_prod_inst {rts} π E L mu ma {M} (ml : M) l (tys : hlist type rts) (r : place_rfn (plist place_rfn rts)) sls b :
    StratifyLtype π E L mu StratDoUnfold ma ml l (◁ (struct_t sls tys))%I r b | 30 :=
        λ T, i2p (stratify_ltype_ofty_struct π E L mu ma ml l tys r sls b T).


  (** Subtyping *)
  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subtype_struct E L {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗
    ⌜length rts1 = length rts2⌝ ∗
    foldr (λ '(existT rt1 (ty1, r1'), existT rt2 (ty2, r2')) T,
      match r1' with
      | #r1 => ∃ r2, ⌜r2' = #r2⌝ ∗ weak_subtype E L r1 r2 ty1 ty2 T
      | _ => ∃ (Heq : rt1 = rt2), ⌜r1' = rew <-Heq in r2'⌝ ∗ mut_subtype E L ty1 (rew <- [type] Heq in ty2) T
      end) T (zip (hpzipl rts1 tys1 rs1) (hpzipl rts2 tys2 rs2))
    ⊢ weak_subtype E L rs1 rs2 (struct_t sls1 tys1) (struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & %Hlen & Hb)". iIntros (??) "#CTX #HE HL".
    match goal with |- context[foldr ?P _ _] => set (Q := P) end.
    iAssert (|={F}=> struct_t_incl_precond tys1 tys2 rs1 rs2 ∗ llctx_interp L ∗ T)%I with "[Hb HL]" as ">(Hp & $ & $)"; first last.
    { by iApply struct_t_type_incl. }
    iInduction rts1 as [ | rt1 rts1] "IH" forall (rts2 tys1 tys2 rs1 rs2 Hlen); destruct rts2 as [ | rt2 rts2]; simpl in Hlen; try done;
      inv_hlist tys2; inv_hlist tys1.
    { simpl. iFrame. by iApply big_sepL2_nil. }
    intros ty1 tys1 ty2 tys2.
    destruct rs1 as [r1 rs1]. destruct rs2 as [r2 rs2].
    simpl.
    destruct r1.
    - iDestruct "Hb" as "(%r2' & -> & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hi & HL & HT)".
      iMod ("IH" with "[] HT HL") as "(Hi2 & $ & $)"; last by iFrame.
      iPureIntro; lia.
    - iDestruct "Hb" as "(%Heq & %Heq' & %Hb & HT)". subst.
      iPoseProof (full_subtype_acc with "HE HL") as "#Hsub"; first apply Hb.
      iMod ("IH" with "[] HT HL") as "(Hi2 & $ & $)". { iPureIntro; lia. }
      rewrite {3}/struct_t_incl_precond; simpl. iFrame.
      iExists eq_refl. iR. done.
  Qed.
  Global Instance weak_subtype_struct_inst E L {rts1 rts2} (tys1 : hlist type  rts1) (tys2 : hlist type rts2) rs1 rs2 sls1 sls2 :
    Subtype E L rs1 rs2 (struct_t sls1 tys1) (struct_t sls2 tys2) | 20 :=
    λ T, i2p (weak_subtype_struct E L tys1 tys2 rs1 rs2 sls1 sls2 T).

  (* TODO replace foldr with relate_hlist *)
  Lemma mut_subtype_struct E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗ foldr (λ '(existT rt (ty1, ty2)) T, mut_subtype E L ty1 ty2 T) T (hzipl2 _ tys1 tys2)
    ⊢ mut_subtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & Hb)".
    iAssert (⌜Forall (λ '(existT x (ty1, ty2)), full_subtype E L ty1 ty2) (hzipl2 rts tys1 tys2)⌝ ∗ T)%I with "[Hb]" as "(%Hsubt & $)"; first last.
    { iPureIntro. by apply  struct_t_full_subtype. }
    iInduction rts as [ | rt rts] "IH" forall (tys1 tys2); inv_hlist tys2; inv_hlist tys1.
    { iFrame. iPureIntro. simpl. done. }
    intros ty1 tys1 ty2 tys2.
    rewrite hzipl2_cons. simpl.
    iDestruct "Hb" as "(%Hsub & Hb)".
    iPoseProof ("IH"  with "Hb") as "(%Hsubt & $)".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_subtype_struct_inst E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 :
    MutSubtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) | 20 :=
    λ T, i2p (mut_subtype_struct E L tys1 tys2 sls1 sls2 T).

  (* TODO replace foldr with relate_hlist *)
  Lemma mut_eqtype_struct E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗ foldr (λ '(existT rt (ty1, ty2)) T, mut_eqtype E L ty1 ty2 T) T (hzipl2 _ tys1 tys2)
    ⊢ mut_eqtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & Hb)".
    iAssert (⌜Forall (λ '(existT x (ty1, ty2)), full_eqtype E L ty1 ty2) (hzipl2 rts tys1 tys2)⌝ ∗ T)%I with "[Hb]" as "(%Hsubt & $)"; first last.
    { iPureIntro. apply full_subtype_eqtype; apply struct_t_full_subtype.
      - eapply Forall_impl; first done. intros [? []]. apply full_eqtype_subtype_l.
      - rewrite hzipl2_swap Forall_fmap. eapply Forall_impl; first done.
        intros [? []]. apply full_eqtype_subtype_r. }
    iInduction rts as [ | rt rts] "IH" forall (tys1 tys2); inv_hlist tys2; inv_hlist tys1.
    { iFrame. iPureIntro. simpl. done. }
    intros ty1 tys1 ty2 tys2.
    rewrite hzipl2_cons. simpl.
    iDestruct "Hb" as "(%Hsub & Hb)".
    iPoseProof ("IH"  with "Hb") as "(%Hsubt & $)".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_eqtype_struct_inst E L {rts} (tys1 tys2 : hlist type rts) sls1 sls2 :
    MutEqtype E L (struct_t sls1 tys1) (struct_t sls2 tys2) | 20 :=
    λ T, i2p (mut_eqtype_struct E L tys1 tys2 sls1 sls2 T).

  (** Subltyping *)
  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_owned_in E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 wl T  :
    ⌜sls1 = sls2⌝ ∗ ⌜length rts1 = length rts2⌝ ∗ foldr (λ '(existT rt1 (lt1, r1'), existT rt2 (lt2, r2')) T,
      weak_subltype E L (Owned false) r1' r2' lt1 lt2 T) T (zip (hpzipl rts1 lts1 rs1) (hpzipl rts2 lts2 rs2))
    ⊢ weak_subltype E L (Owned wl) (#rs1) (#rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hlen & Ha)" (??) "#CTX #HE HL".
    iAssert (|={F}=> ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2, ltype_incl (Owned false) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) ∗ llctx_interp L ∗ T)%I with "[Ha HL]" as ">(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_owned_in lts1 lts2). done. }
    iInduction rts1 as [ | rt1 rts1] "IH" forall (rts2 lts1 lts2 rs1 rs2 Hlen); destruct rts2 as [ | rt2 rts2]; try done;
      inv_hlist lts2; inv_hlist lts1.
    { simpl. by iFrame. }
    intros lt1 lts1 lt2 lts2. simpl in Hlen.
    destruct rs1 as [r1 rs1]. destruct rs2 as [r2 rs2].
    simpl. iMod ("Ha" with "[//] CTX HE HL") as "(Hincl1 & HL & HT)".
    iMod ("IH" with "[] HT HL") as "(Hincl & $ & $)"; first (iPureIntro; lia).
    by iFrame.
  Qed.
  Global Instance weak_subltype_struct_owned_in_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 wl :
    SubLtype E L (Owned wl) #rs1 #rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 10 :=
    λ T, i2p (weak_subltype_struct_owned_in E L lts1 lts2 rs1 rs2 sls1 sls2 wl T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_owned E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 wl T  :
    ⌜sls1 = sls2⌝ ∗ ⌜rs1 = rs2⌝ ∗ foldr (λ '(existT rt1 (lt1, lt2)) T,
      mut_subltype E L lt1 lt2 T) T (hzipl2 rts lts1 lts2)
    ⊢ weak_subltype E L (Owned wl) (rs1) (rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & -> & HT)" (??) "#CTX #HE HL".
    iAssert (([∗ list] ltp ∈ hzipl2 rts lts1 lts2, ∀ r, ltype_incl (Owned false) r r (projT2 ltp).1 (projT2 ltp).2) ∗ llctx_interp L ∗ T)%I with "[HT HL]" as "(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_owned lts1 lts2). done. }
    clear rs2.
    iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { simpl. iFrame. }
    intros lt1 lts1 lt2 lts2.
    simpl. iDestruct "HT" as "(%Hsubt & HT)".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl1"; first apply Hsubt.
    iPoseProof ("IH" with "HT HL")  as "(Hincl & $ & $)".
    iFrame. iIntros (?). iApply "Hincl1".
  Qed.
  Global Instance weak_subltype_struct_owned_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 wl :
    SubLtype E L (Owned wl) rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 11 :=
    λ T, i2p (weak_subltype_struct_owned E L lts1 lts2 rs1 rs2 sls1 sls2 wl T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_shared_in E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 κ T  :
    ⌜sls1 = sls2⌝ ∗ ⌜length rts1 = length rts2⌝ ∗ foldr (λ '(existT rt1 (lt1, r1'), existT rt2 (lt2, r2')) T,
      weak_subltype E L (Shared κ) r1' r2' lt1 lt2 T) T (zip (hpzipl rts1 lts1 rs1) (hpzipl rts2 lts2 rs2))
    ⊢ weak_subltype E L (Shared κ) (#rs1) (#rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hlen & Ha)" (??) "#CTX #HE HL".
    iAssert (|={F}=> ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2, ltype_incl (Shared κ) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) ∗ llctx_interp L ∗ T)%I with "[Ha HL]" as ">(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_shared_in lts1 lts2). done. }
    (* TODO duplicated *)
    iInduction rts1 as [ | rt1 rts1] "IH" forall (rts2 lts1 lts2 rs1 rs2 Hlen); destruct rts2 as [ | rt2 rts2]; try done;
      inv_hlist lts2; inv_hlist lts1.
    { simpl. by iFrame. }
    intros lt1 lts1 lt2 lts2. simpl in Hlen.
    destruct rs1 as [r1 rs1]. destruct rs2 as [r2 rs2].
    simpl. iMod ("Ha" with "[//] CTX HE HL") as "(Hincl1 & HL & HT)".
    iMod ("IH" with "[] HT HL") as "(Hincl & $ & $)"; first (iPureIntro; lia).
    by iFrame.
  Qed.
  Global Instance weak_subltype_struct_shared_in_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) rs1 rs2 sls1 sls2 κ :
    SubLtype E L (Shared κ) #rs1 #rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 10 :=
    λ T, i2p (weak_subltype_struct_shared_in E L lts1 lts2 rs1 rs2 sls1 sls2 κ T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_shared E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 κ T  :
    ⌜sls1 = sls2⌝ ∗ ⌜rs1 = rs2⌝ ∗ foldr (λ '(existT rt1 (lt1, lt2)) T,
      mut_subltype E L lt1 lt2 T) T (hzipl2 rts lts1 lts2)
    ⊢ weak_subltype E L (Shared κ) (rs1) (rs2) (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & -> & HT)" (??) "#CTX #HE HL". iModIntro.
    iAssert (([∗ list] ltp ∈ hzipl2 rts lts1 lts2, ∀ r, ltype_incl (Shared κ) r r (projT2 ltp).1 (projT2 ltp).2) ∗ llctx_interp L ∗ T)%I with "[HT HL]" as "(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl_shared lts1 lts2). done. }
    (* TODO duplicated *)
    clear rs2. iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { simpl. iFrame. }
    intros lt1 lts1 lt2 lts2.
    simpl. iDestruct "HT" as "(%Hsubt & HT)".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hincl1"; first apply Hsubt.
    iPoseProof ("IH" with "HT HL")  as "(Hincl & $ & $)".
    iFrame. iIntros (?). iApply "Hincl1".
  Qed.
  Global Instance weak_subltype_struct_shared_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 κ :
    SubLtype E L (Shared κ) rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 11 :=
    λ T, i2p (weak_subltype_struct_shared E L lts1 lts2 rs1 rs2 sls1 sls2 κ T).

  (* TODO replace foldr with relate_hlist *)
  Lemma weak_subltype_struct_base E L {rts} (lts1 lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 k T :
    ⌜sls1 = sls2⌝ ∗ ⌜rs1 = rs2⌝ ∗ foldr (λ '(existT rt1 (lt1, lt2)) T,
      mut_eqltype E L lt1 lt2 T) T (hzipl2 rts lts1 lts2)
    ⊢ weak_subltype E L k rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & -> & HT)" (??) "#CTX #HE HL". iModIntro.
    iAssert ((∀ k, [∗ list] ltp ∈ hzipl2 rts lts1 lts2, ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2) ∗ llctx_interp L ∗ T)%I with "[HT HL]" as "(Ha & $ & $)"; first last.
    { iApply (struct_ltype_incl lts1 lts2). done. }
    clear rs2. iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { simpl. by iFrame. }
    intros lt1 lts1 lt2 lts2.
    simpl. iDestruct "HT" as "(%Hsubt & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl1"; first apply Hsubt.
    iPoseProof ("IH" with "HT HL")  as "(Hincl & $ & $)".
    iFrame. iIntros (?). iSplitR.
    - iIntros (?). iApply "Hincl1".
    - iApply "Hincl".
  Qed.
  Global Instance weak_subltype_struct_base_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) rs1 rs2 sls1 sls2 k :
    SubLtype E L k rs1 rs2 (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 20 :=
    λ T, i2p (weak_subltype_struct_base E L lts1 lts2 rs1 rs2 sls1 sls2 k T).


  Program Definition MutEqltypeStructHFR (cap : nat) : HetFoldableRelation (A := Type) (G := ltype) := {|
    hfr_rel E L i rt lt1 lt2 T := mut_eqltype E L lt1 lt2 T;
    hfr_cap := cap;
    hfr_inv := True;
    hfr_core_rel E L i rt lt1 lt2 := ⌜full_eqltype E L lt1 lt2⌝%I;
    hfr_elim_mode := false
  |}.
  Next Obligation.
    iIntros (i0 E L i rt lt1 lt2 T) "(%Hsubt & HT)". by iFrame.
  Qed.
  Global Arguments MutEqltypeStructHFR : simpl never.

  Lemma mut_subltype_struct E L {rts} (lts1 lts2 : hlist ltype rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗
    relate_hlist E L [] rts lts1 lts2 0 (MutEqltypeStructHFR (length rts)) T
    ⊢ mut_subltype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    rewrite /MutEqltypeStructHFR.
    iIntros "(-> & Ha & $)".
    iPoseProof ("Ha" with "[] [//]") as "Ha".
    { simpl. iPureIntro. lia. }
    simpl.
    iAssert (⌜Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2)⌝)%I with "[Ha]" as "%Hsubt"; first last.
    { iPureIntro. by apply (struct_full_subltype _ _ lts1 lts2). }
    iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { iFrame. simpl; done. }
    intros lt1 lts1 lt2 lts2. rewrite hzipl2_cons. simpl.
    iDestruct "Ha" as "(%Hsubt & Ha)". iPoseProof ("IH" with "Ha") as "%Hsubt'".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_subltype_struct_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) sls1 sls2 :
    MutSubLtype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 20 :=
    λ T, i2p (mut_subltype_struct E L lts1 lts2 sls1 sls2 T).

  Lemma mut_eqltype_struct E L {rts} (lts1 lts2 : hlist ltype rts) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗
    relate_hlist E L [] rts lts1 lts2 0 (MutEqltypeStructHFR (length rts)) T
    ⊢ mut_eqltype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) T.
  Proof.
    rewrite /MutEqltypeStructHFR.
    iIntros "(-> & Ha & $)".
    iPoseProof ("Ha" with "[] [//]") as "Ha".
    { simpl. iPureIntro. lia. }
    simpl.
    iAssert (⌜Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2)⌝)%I with "[Ha]" as "%Hsubt"; first last.
    { iPureIntro. by apply struct_full_eqltype. }
    iInduction rts as [ | rt rts] "IH" forall (lts1 lts2); inv_hlist lts2; inv_hlist lts1.
    { iFrame. simpl; done. }
    intros lt1 lts1 lt2 lts2. rewrite hzipl2_cons. simpl.
    iDestruct "Ha" as "(%Hsubt & Ha)". iPoseProof ("IH" with "Ha") as "%Hsubt'".
    iPureIntro. constructor; done.
  Qed.
  Global Instance mut_eqltype_struct_inst E L {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) sls1 sls2 :
    MutEqLtype E L (StructLtype lts1 sls1) (StructLtype lts2 sls2) | 20 :=
    λ T, i2p (mut_eqltype_struct E L lts1 lts2 sls1 sls2 T).

  (* Ofty unfolding if necessary *)
  Lemma weak_subltype_struct_ofty_1_evar E L {rts1 rts2} (lts1 : hlist ltype rts1) (ty2 : type (plist place_rfn rts2)) sls k r1 r2 T :
    (∃ tys2, ⌜ty2 = struct_t sls tys2⌝ ∗ weak_subltype E L k r1 r2 (StructLtype lts1 sls) (StructLtype (@OfTy _ _ +<$> tys2) sls) T)
    ⊢ weak_subltype E L k r1 r2 (StructLtype lts1 sls) (◁ ty2) T.
  Proof.
    iIntros "(%tys2 & -> & Hsubt)" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply struct_t_unfold_2.
  Qed.
  Global Instance weak_subltype_struct_ofty_1_evar_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (ty2 : type (plist place_rfn rts2)) sls k rs1 rs2 `{!IsProtected ty2} :
    SubLtype E L k rs1 rs2 (StructLtype lts1 sls) (◁ ty2)%I | 30 :=
    λ T, i2p (weak_subltype_struct_ofty_1_evar E L lts1 ty2 sls k rs1 rs2 T).

  Lemma weak_subltype_struct_ofty_1 E L {rts1 rts2} (lts1 : hlist ltype rts1) (tys2 : hlist type rts2) sls1 sls2 k r1 r2 T :
    (⌜sls1 = sls2⌝ ∗ weak_subltype E L k r1 r2 (StructLtype lts1 sls1) (StructLtype (@OfTy _ _ +<$> tys2) sls2) T)
    ⊢ weak_subltype E L k r1 r2 (StructLtype lts1 sls1) (◁ struct_t sls2 tys2) T.
  Proof.
    iIntros "(-> & Hsubt)" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "Hincl").
    iApply struct_t_unfold_2.
  Qed.
  Global Instance weak_subltype_struct_ofty_1_inst E L {rts1 rts2} (lts1 : hlist ltype rts1) (tys2 : hlist type rts2) sls1 sls2 k rs1 rs2 :
    SubLtype E L k rs1 rs2 (StructLtype lts1 sls1) (◁ struct_t sls2 tys2)%I | 20 :=
    λ T, i2p (weak_subltype_struct_ofty_1 E L lts1 tys2 sls1 sls2 k rs1 rs2 T).


  Lemma weak_subltype_struct_ofty_2 E L {rts1 rts2} (tys1 : hlist type rts1) (lts2 : hlist ltype rts2) sls1 sls2 k r1 r2 T :
    (weak_subltype E L k r1 r2 (StructLtype (@OfTy _ _ +<$> tys1) sls1) (StructLtype lts2 sls2) T)
    ⊢ weak_subltype E L k r1 r2 (◁ struct_t sls1 tys1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "Hsubt" (??) "#CTX #HE HL".
    iMod ("Hsubt" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iApply (ltype_incl_trans with "[] Hincl").
    iApply struct_t_unfold_1.
  Qed.
  Definition weak_subltype_struct_ofty_2_inst := [instance weak_subltype_struct_ofty_2].
  Global Existing Instance weak_subltype_struct_ofty_2_inst | 20.

  Lemma mut_subltype_struct_ofty_1 E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfn rts)) sls T :
    (∃ tys2, ⌜ty2 = struct_t sls tys2⌝ ∗ mut_subltype E L (StructLtype lts1 sls) (StructLtype (@OfTy _ _ +<$> tys2) sls) T)
    ⊢ mut_subltype E L (StructLtype lts1 sls) (◁ ty2) T.
  Proof.
    iIntros "(%tys21 & -> & %Hsubt & $)".
    iPureIntro.
    etrans; first apply Hsubt.
    apply full_eqltype_subltype_l. apply (struct_t_unfold_full_eqltype _ _ tys21).
  Qed.
  Global Instance mut_subltype_struct_ofty_1_inst E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfn rts)) sls :
    MutSubLtype E L (StructLtype lts1 sls) (◁ ty2)%I := λ T, i2p (mut_subltype_struct_ofty_1 E L lts1 ty2 sls T).

  Lemma mut_subltype_struct_ofty_2 E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 T :
    (⌜sls1 = sls2⌝ ∗ mut_subltype E L (StructLtype (@OfTy _ _ +<$> tys1) sls1) (StructLtype lts2 sls1) T)
    ⊢ mut_subltype E L (◁ struct_t sls1 tys1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt.
    apply full_eqltype_subltype_r. apply (struct_t_unfold_full_eqltype _ _ tys1).
  Qed.
  Global Instance mut_subltype_struct_ofty_2_inst E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 :
    MutSubLtype E L (◁ struct_t sls1 tys1)%I (StructLtype lts2 sls2) := λ T, i2p (mut_subltype_struct_ofty_2 E L lts2 tys1 sls1 sls2 T).

  Lemma mut_eqltype_struct_ofty_1 E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfn rts)) sls T :
    (∃ tys2, ⌜ty2 = struct_t sls tys2⌝ ∗ mut_eqltype E L (StructLtype lts1 sls) (StructLtype (@OfTy _ _ +<$> tys2) sls) T)
    ⊢ mut_eqltype E L (StructLtype lts1 sls) (◁ ty2) T.
  Proof.
    iIntros "(%tys21 & -> & %Hsubt & $)".
    iPureIntro. etrans; first apply Hsubt. apply (struct_t_unfold_full_eqltype _ _ tys21).
  Qed.
  Global Instance mut_eqltype_struct_ofty_1_inst E L {rts} (lts1 : hlist ltype rts) (ty2 : type (plist place_rfn rts)) sls :
    MutEqLtype E L (StructLtype lts1 sls) (◁ ty2)%I := λ T, i2p (mut_eqltype_struct_ofty_1 E L lts1 ty2 sls T).

  Lemma mut_eqltype_struct_ofty_2 E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 T :
    (⌜sls1 = sls2⌝ ∗ mut_eqltype E L (StructLtype (@OfTy _ _ +<$> tys1) sls1) (StructLtype lts2 sls1) T)
    ⊢ mut_eqltype E L (◁ struct_t sls1 tys1) (StructLtype lts2 sls2) T.
  Proof.
    iIntros "(-> & %Hsubt & $)".
    iPureIntro. etrans; last apply Hsubt. symmetry. apply (struct_t_unfold_full_eqltype _ _ tys1).
  Qed.
  Global Instance mut_eqltype_struct_ofty_2_inst E L {rts} (lts2 : hlist ltype rts) (tys1 : hlist type rts) sls1 sls2 :
    MutEqLtype E L (◁ struct_t sls1 tys1)%I (StructLtype lts2 sls2) := λ T, i2p (mut_eqltype_struct_ofty_2 E L lts2 tys1 sls1 sls2 T).

  (*
  Lemma subsume_place_struct_uninit π E L wl l {rts} (lts : hlist ltype rts) (rs : plist place_rfn rts) (sls : struct_layout_spec) (st : syn_type) T :
    ⌜st = sls⌝ ∗ (* TODO: maybe make this more flexible? *)
    foldr (λ '((existT rt1 (lt1, r1)), (x, st)) T,
      λ L, subsume_full E L (l atst{sls}ₗ x ◁ₗ[π, Owned false] r1 @ lt1) (l atst{sls}ₗ x ◁ₗ[π, Owned false] .@ ◁ uninit st) T)
        T (zip (hpzipl rts lts rs) (sls_fields sls)) L -∗
    subsume_full E L (l ◁ₗ[π, Owned wl] #rs @ StructLtype lts sls) (l ◁ₗ[π, Owned wl] .@ ◁ uninit st) T.
  Proof.
    (* TODO *)
  Abort.

  Lemma subsume_place_struct π E L wl l {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) (rs1 : plist place_rfn rts1) (rs2 : plist place_rfn rts2) sls1 sls2 T :
    ⌜sls1 = sls2⌝ ∗ foldr (λ '((existT rt1 (lt1, r1), existT rt2 (lt2, r2)), (x, st)) T,
      λ L, subsume_full E L (l atst{sls1}ₗ x ◁ₗ[π, Owned false] r1 @ lt1) (l atst{sls1}ₗ x ◁ₗ[π, Owned false] r2 @ lt2) T)
        T (zip (zip (hpzipl rts1 lts1 rs1) (hpzipl rts2 lts2 rs2)) (sls_fields sls1)) L -∗
    subsume_full E L (l ◁ₗ[π, Owned wl] #rs1 @ StructLtype lts1 sls1) (l ◁ₗ[π, Owned wl] #rs2 @ StructLtype lts2 sls2) T.
  Proof.
    (* TODO *)
  Abort.
   *)
  (* TODO: owned subtype instances for deinit *)

  (** CastLtypeToType *)
  Definition hlist_list_of {A} {F : A → Type} (l : list A) (hl : hlist F l) := l.
  Fixpoint cast_ltype_to_type_iter (E : elctx) (L : llctx) {rts} (lts : hlist ltype rts) : (hlist type rts → iProp Σ) → iProp Σ :=
    match lts as rts2 return (hlist type (hlist_list_of _ rts2) → iProp Σ) → iProp Σ with
    | +[] => λ T, T +[]
    | lt +:: lts => λ T,
        cast_ltype_to_type E L lt (λ ty,
          cast_ltype_to_type_iter E L lts (λ tys, T (ty +:: tys)))
    end.

  Local Lemma cast_ltype_to_type_iter_elim E L {rts} (lts : hlist ltype rts) T :
    cast_ltype_to_type_iter E L lts T -∗
    ∃ tys : hlist type rts, T tys ∗ ⌜Forall (λ '(existT x (lt1, lt2)), full_eqltype E L lt1 lt2) (hzipl2 rts lts ((λ X : Type, OfTy) +<$> tys))⌝.
  Proof.
    iIntros "HT".
    iInduction rts as [ | rt rts] "IH"; inv_hlist lts; simpl.
    { iExists _. iFrame. iPureIntro. done. }
    intros lt lts. simpl.
    iDestruct "HT" as "(%ty & %Heqt & HT)".
    iPoseProof ("IH" with "HT") as "(%tys & HT & %Heqts)".
    iExists _. iFrame. iPureIntro. simpl. econstructor; done.
  Qed.
  Lemma cast_ltype_to_type_struct E L {rts} (lts : hlist ltype rts) sls T :
    cast_ltype_to_type_iter E L lts (λ tys, T (struct_t sls tys))
    ⊢ cast_ltype_to_type E L (StructLtype lts sls) T.
  Proof.
    iIntros "HT".
    (*Search "struct" "eq".*)
    iPoseProof (cast_ltype_to_type_iter_elim with "HT") as "(%tys & HT & %Heqts)".
    iExists _. iFrame. iPureIntro.
    etrans; last apply struct_t_unfold_full_eqltype.
    eapply (struct_full_eqltype _ _ lts).
    eapply Forall_impl; first apply Heqts. intros [? []]; done.
  Qed.
  Global Instance cast_ltype_to_type_struct_inst E L {rts} (lts : hlist ltype rts) sls  :
    CastLtypeToType E L (StructLtype lts sls) := λ T, i2p (cast_ltype_to_type_struct E L lts sls T).

  (** Struct initialization *)
  Fixpoint struct_init_fold π E L (fields : list (string * expr)) (sts : list (string * syn_type)) (T : ∀ (L : llctx) (rts : list Type), list val → hlist type rts → plist id rts → iProp Σ) : iProp Σ :=
    match sts with
    | [] =>
        T L [] [] +[] -[]
    | (name, st) :: sts =>
        (* TODO should have a faster way to do the lookup *)
        ∃ init, ⌜(list_to_map (M:=gmap _ _) fields) !! name = Some init⌝ ∗
        typed_val_expr π E L init (λ L2 v rt ty r,
        ⌜ty.(ty_syn_type) = st⌝ ∗
        struct_init_fold π E L2 fields sts (λ L3 rts vs tys rs,
            T L3 (rt :: rts) (v :: vs) (ty +:: tys) (r -:: rs)))%I
    end.

  Lemma struct_init_fold_elim π E L fields sts T Φ :
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    na_own π (↑shrN) -∗
    struct_init_fold π E L fields sts T -∗
    (∀ vs L3,
      llctx_interp L3 -∗
      na_own π (↑shrN) -∗
      (∃ (rts : list Type) (tys : hlist type rts) (rs : plist id rts),
      (* get a type assignment for the values *)
      ⌜length rts = length (sts)⌝ ∗
      ([∗ list] i ↦ v; Ty ∈ vs; hpzipl rts tys rs,
        let '(existT rt (ty, r)) := Ty in
        ∃ name st ly, ⌜sts !! i = Some (name, st)⌝ ∗ ⌜syn_type_has_layout st ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗
        v ◁ᵥ{ π} r @ ty
      ) ∗
      T L3 rts vs tys rs) -∗ Φ vs) -∗
    struct_init_components ⊤ sts fields Φ
  .
  Proof.
    iIntros "#CTX #HE HL Hna Hf Hcont".
    iInduction sts as [ | [name st] sts] "IH" forall (fields L  Φ T).
    { simpl.
      iApply ("Hcont" with "HL Hna"). iExists [], +[], -[]. simpl. eauto. }
    simpl. iDestruct "Hf" as (init Hlook) "Hf".
    (* maybe want to phrase also with custom fold instead of foldr? *)
    iIntros (ly) "%Hst". simpl.
    iPoseProof ("Hf" with "CTX HE HL") as "Ha".
    rewrite Hlook/=.
    iApply (wp_wand with "(Ha Hna [Hcont])").
    2: { eauto. }
    iIntros (L2 v rt ty r) "HL Hna Hv [<- Hr]".
    iApply ("IH" with "HL Hna Hr").
    iIntros (vs L3) "HL Hna Hc".
    iApply ("Hcont" with "HL Hna").
    iDestruct "Hc" as (rts tys rs) "(%Hlen & Ha & HT)".
    iExists (rt :: rts), (ty +:: tys), (r -:: rs).
    iFrame. iSplitR. { rewrite /=Hlen//. }
    iExists name, (ty_syn_type ty). iExists ly.
    iR. done.
  Qed.

  Lemma type_struct_init π E L (sls : struct_layout_spec) (fields : list (string * expr)) (T : typed_val_expr_cont_t) :
    ⌜struct_layout_spec_is_layoutable sls⌝ ∗
    struct_init_fold π E L fields sls.(sls_fields) (λ L2 rts vs tys rs,
      ∀ v, T L2 v _ (struct_t sls tys) (pmap (λ _ a, #a) rs))
    ⊢ typed_val_expr π E L (StructInit sls fields) T.
  Proof.
    iIntros "(%Hly & HT)". destruct Hly as (sl & Hsl).
    iIntros (?) "#CTX #HE HL Hna Hc".
    iApply wp_struct_init2; first done.
    iApply (struct_init_fold_elim with "CTX HE HL Hna HT").
    iIntros (vs L3) "HL Hna Ha".
    iDestruct "Ha" as (rts tys rs) "(%Hlen & Hv & HT)".
    iApply ("Hc" with "HL Hna [Hv] HT").
    simpl. by iApply struct_init_val.
  Qed.

  (* TODO prove_place_cond *)

  (* TODO resolve hgost *)

End rules.

Global Typeclasses Opaque MutEqltypeStructHFR.
Global Typeclasses Opaque cast_ltype_to_type_iter.
Global Typeclasses Opaque stratify_ltype_struct_iter.

Global Typeclasses Opaque unit_t.
Global Typeclasses Opaque struct_t.

(* Need this for unification to figure out how to apply typed_place lemmas -- if the plist simplifies, unification will be stuck *)
Arguments plist : simpl never.

From refinedrust Require Import int.
Section test.
  Context `{!typeGS Σ}.

  Definition test_rt : list Type := [Z: Type; Z : Type].
  Definition test_lts : hlist ltype test_rt := (◁ int i32)%I +:: (◁ int i32)%I +:: +[].
  Definition test_rfn : plist place_rfn test_rt := #32 -:: #22 -:: -[].

  Lemma bla : hnth (UninitLtype UnitSynType) test_lts 1 = (◁ int i32)%I.
  Proof. simpl. done. Abort.
  Lemma bla : pnth (#()) test_rfn 1 = #22.
  Proof. simpl. done. Abort.

  Lemma bla : hlist_insert_id (unit : Type) _ test_lts 1 (◁ int i32)%I = test_lts.
  Proof.
    simpl. rewrite /hlist_insert_id. simpl.
    (*rewrite /list_insert_lnth. *)
    (*generalize (list_insert_lnth test_rt unit 1).*)
    (*simpl. intros ?. rewrite (UIP_refl _ _ e). done.*)
  Abort.

  Lemma bla : hlist_insert _ test_lts 1 _ (◁ int i32)%I = test_lts.
  Proof.
    simpl. done.
  Abort.

  Lemma bla : plist_insert _ test_rfn 1 _ (#22) = test_rfn.
  Proof.
    simpl. done.
  Abort.

  Lemma bla : plist_insert_id (unit : Type) _ test_rfn 1 (#22) = test_rfn.
  Proof.
    simpl. cbn. done.
    (*rewrite /plist_insert_id. cbn. *)
    (*generalize (list_insert_lnth test_rt unit 1).*)
    (*simpl. intros ?. rewrite (UIP_refl _ _ e). done.*)
  Abort.

  (* Options:
     - some simplification machinery via tactic support
        li_tactic. should just rewrite a bit.
     - some simplification machinery via SimplifyHyp instances or so?
        not the right way to do it. Rather specialized SimplifyHypVal or so.
     - some simplification machinery via a new SimplifyLtype thing and have rules for judgments for that?
        How do we capture a progress condition? via .. try to simplify, then require that it is Some. This is like SimplifyHyp
       This seems unnecessarily expensive, since we usually need not be able to do it.


   *)
End test.

