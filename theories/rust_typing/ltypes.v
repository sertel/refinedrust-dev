From Equations Require Import Equations.
From iris.bi Require Export fractional.
From iris.base_logic.lib Require Export invariants na_invariants.
From caesium Require Export proofmode notation.
From caesium Require Import derived.
From lrust.lifetime Require Export frac_borrow.
From refinedrust Require Import int.
From refinedrust Require Export hlist.
From refinedrust Require Export base lft_contexts gvar_refinement type uninit_def.

From iris Require Import options.

(** * Place types *)

(** ** Basic enum infrastructure *)
Section enum.
  Context `{!typeGS Σ}.
  (*Set Universe Polymorphism.*)

  Record enum (rt : Type) : Type := mk_enum {
    enum_rt_inhabited : Inhabited rt;
    (* the layout spec *)
    enum_els : enum_layout_spec;
    (* out of the current refinement, extract the tag *)
    enum_tag : rt → var_name;
    (* out of the current refinement, extract the component type and refinement *)
    enum_ty : rt → sigT (λ rt' : Type, type rt' * rt')%type;
    (* convenience function: given the variant name, also project out the type *)
    enum_tag_ty : var_name → option (sigT type);
    (* explicitly track the lifetimes each of the variants needs -- needed for sharing *)
    enum_lfts : list lft;
    enum_wf_E : elctx;
    enum_lfts_complete : ∀ (r : rt), ty_lfts (projT2 (enum_ty r)).1 ⊆ enum_lfts;
    enum_wf_E_complete : ∀ (r : rt), ty_wf_E (projT2 (enum_ty r)).1 ⊆ enum_wf_E;
    enum_tag_compat : ∀ (r : rt) (variant : var_name),
      enum_tag r = variant →
      ∃ rte lte re,
        enum_ty r = existT rte (lte, re) ∧
        enum_tag_ty variant = Some (existT rte lte)
  }.
  Global Arguments mk_enum {_ _}.
  Global Arguments enum_rt_inhabited {_}.
  Global Arguments enum_els {_}.
  Global Arguments enum_tag {_}.
  Global Arguments enum_ty {_}.
  Global Arguments enum_tag_ty {_}.
  Global Arguments enum_lfts {_}.
  Global Arguments enum_wf_E {_}.

  (*Set Universe Polymorphism.*)
  Definition enum_tag_ty' {rt} (en : enum rt) (v : var_name) : sigT type :=
    default (existT _ $ uninit UnitSynType) (enum_tag_ty en v).
  Definition enum_tag_rt {rt} (en : enum rt) (v : var_name) : Type :=
    projT1 (enum_tag_ty' en v).
  Definition enum_tag_type {rt} (en : enum rt) (v : var_name) : type (enum_tag_rt en v) :=
    projT2 (enum_tag_ty' en v).

  Definition enum_variant_rt {rt} (en : enum rt) (r : rt) : Type :=
    projT1 (enum_ty en r).
  Definition enum_variant_rfn {rt} (en : enum rt) (r : rt) : (enum_variant_rt en r) :=
    snd (projT2 (enum_ty en r)).
  Definition enum_variant_type {rt} (en : enum rt) (r : rt) : type (enum_variant_rt en r) :=
    fst (projT2 (enum_ty en r)).

  Definition enum_lookup_tag {rt} (e : enum rt) (r : rt) :=
    els_lookup_tag e.(enum_els) (e.(enum_tag) r).

  Definition size_of_enum_data (els : enum_layout_spec) :=
    ly_size (use_union_layout_alg' (uls_of_els els)).

  Definition els_data_ly (els : enum_layout_spec) :=
    use_union_layout_alg' (uls_of_els els).

  Lemma enum_tag_rt_variant_rt_eq {rt} (en : enum rt) r tag :
    tag = enum_tag en r →
    enum_tag_rt en tag = enum_variant_rt en r.
  Proof.
    intros ->.
    edestruct (enum_tag_compat _ en r) as (rte & lte & re & Ha & Hb); first done.
    rewrite /enum_tag_rt /enum_variant_rt /enum_tag_ty'.
    rewrite Ha Hb/=//.
  Defined.

  Lemma enum_tag_ty_Some {rt} (en : enum rt) r {rte : Type} (tye : type rte) (re : rte) :
    enum_ty en r = (existT rte (tye, re)) →
    enum_tag_ty en (enum_tag en r) = Some (existT rte tye).
  Proof.
    destruct (enum_tag_compat _ en r _ eq_refl) as (rte' & lte' & re' & -> & ->).
    intros Ha. injection Ha. intros _ _ ->.
    apply existT_inj in Ha. injection Ha as -> ->.
    done.
  Qed.
  Lemma enum_tag_ty_Some' {rt} (en : enum rt) r :
    enum_tag_ty en (enum_tag en r) = Some (existT (projT1 (enum_ty en r)) (fst $ projT2 (enum_ty en r))).
  Proof.
    eapply (enum_tag_ty_Some _ _ _ (snd $ projT2 (enum_ty en r))).
    destruct (enum_ty en r) as [? [??]]; done.
  Qed.

  Import EqNotations.
  Lemma enum_tag_type_variant_type_eq {rt} (en : enum rt) r:
    enum_tag_type en (enum_tag en r) = rew <-[type] (enum_tag_rt_variant_rt_eq en r _ eq_refl) in enum_variant_type en r.
  Proof.
    (*destruct (enum_ty en r) as [rte [lte re]] eqn:Heq.*)
    destruct (enum_tag_compat _ en r (enum_tag en r)) as (rte & lte & re & Ha & Hb); first done.
    rewrite /enum_tag_type/enum_variant_type/enum_tag_ty'.
    generalize (enum_tag_rt_variant_rt_eq en r (enum_tag en r) eq_refl) as Heq.
    rewrite /enum_tag_rt /enum_tag_ty' /enum_variant_rt.
    rewrite Ha Hb. simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq); done.
  Qed.
End enum.

Section array.
  Context `{!typeGS Σ}.
  Section list_map.
    Context {K : Type} `{!EqDecision K}.
    Fixpoint lookup_iml {X} (iml : list (K * X)) (i : K) : option X :=
      match iml with
      | [] => None
      | (j, x) :: iml => if decide (i = j) then Some x else lookup_iml iml i
      end.

    Lemma lookup_iml_Some_iff {X} (iml : list (K * X)) i x :
      (∃ a, iml !! a = Some (i, x) ∧ (∀ b j y, b < a → iml !! b = Some (j, y) → j ≠ i)) ↔ lookup_iml iml i = Some x.
    Proof.
      induction iml as [ | [j y] iml IH] in i |-*; simpl.
      - split.
        + intros (? & Ha & _). rewrite lookup_nil in Ha. done.
        + intros [=].
      - split.
        + intros (a & Hlook & Hle). destruct a as [ | a].
          * simpl in *. injection Hlook as -> ->. rewrite decide_True; done.
          * simpl in *. destruct (decide (i = j)) as [<- | Hneq].
            { by efeed pose proof (Hle 0); [lia | done | done | ]. }
            eapply IH. eexists. split; first done. intros. eapply (Hle (S b)); last done. lia.
        + destruct (decide (i = j)) as [<- | Hneq].
          * intros [= ->]. exists 0. simpl. split; first done. intros. lia.
          * intros (a & Ha & Hleq)%IH. exists (S a).
            split; first done. intros ???? Hlook.
            destruct b; simpl in *. { congruence. }
            eapply Hleq; last done. lia.
    Qed.
    Lemma lookup_iml_None {X} (iml : list (K * X)) i :
      (∀ b j y, iml !! b = Some (j, y) → j ≠ i) ↔ lookup_iml iml i = None.
    Proof.
      induction iml as [ | [j y] iml IH] in i |-*; simpl.
      { split; first done. naive_solver. }
      split.
      - intros Ha. destruct (decide (i = j)) as [<- | ]; first last.
        { eapply IH. intros. eapply (Ha (S b)); done. }
        by efeed pose proof (Ha 0); [done | done | ].
      - destruct (decide (i = j)) as [<- | ]; first done.
        intros Ha b ??. destruct b as [ | b]; first (simpl; congruence).
        simpl. intros Hlook. eapply IH; done.
    Qed.
  End list_map.

  (* Interpretation of an insertion list: from front to back. The same index may appear multiple times,
      then the first occurrence is what is relevant. *)
  Definition interpret_inserts {X} (iml : list (nat * X)) (ls : list X) : list X :=
    foldr (λ '(i, x) acc, <[i := x]> acc) ls iml.
  Definition interpret_iml {X} (def : X) (len : nat) (iml : list (nat * X)) : list X :=
    interpret_inserts iml (replicate len def).

  Lemma interpret_inserts_length {X} (iml : list (nat * X)) (ls : list X) :
    length (interpret_inserts iml ls) = length ls.
  Proof.
    induction iml as [ | [i x] iml IH]; simpl; first done.
    rewrite insert_length //.
  Qed.
  Lemma interpret_iml_length {X} (def : X) (len : nat) (iml : list (nat * X)) :
    length (interpret_iml def len iml) = len.
  Proof.
    rewrite /interpret_iml interpret_inserts_length replicate_length //.
  Qed.

  Lemma lookup_interpret_inserts_Some_inv {X} (iml : list (nat * X)) (ls : list X) i x :
    interpret_inserts iml ls !! i = Some x →
    ((i, x) ∈ iml) ∨ ls !! i = Some x.
  Proof.
    intros Ha. specialize (lookup_lt_Some _ _ _ Ha) as Hlen.
    induction iml as [ | [j y] iml IH] in i, Hlen, Ha |-*; simpl; first by eauto.
    move: Ha. simpl in *.
    rewrite insert_length in Hlen.
    destruct (decide (i = j)) as [ <- | Hneq].
    - rewrite list_lookup_insert; last done.
      intros [= ->]. left. apply elem_of_cons. by left.
    - rewrite list_lookup_insert_ne; last done.
      intros Ha%IH; last done.
      destruct Ha as [ Ha| Ha].
      + left. rewrite elem_of_cons. by right.
      + right. done.
  Qed.
  Lemma lookup_interpret_iml_Some_inv {X} (iml : list (nat * X)) def len i x :
    interpret_iml def len iml !! i = Some x →
    i < len ∧ (x = def ∨ (i, x) ∈ iml).
  Proof.
    rewrite /interpret_iml. intros Ha.
    specialize (lookup_lt_Some _ _ _ Ha) as Hlen.
    rewrite interpret_inserts_length replicate_length in Hlen.
    split; first done.
    apply lookup_interpret_inserts_Some_inv in Ha as [ | Ha]; first by eauto.
    apply lookup_replicate_1 in Ha as [ ]. by left.
  Qed.

  Lemma lookup_interpret_inserts_1 {X} (iml : list (nat * X)) (ls : list X) i :
    lookup_iml iml i = None →
    interpret_inserts iml ls !! i = ls !! i.
  Proof.
    intros Ha. induction iml as [ | [j x] iml IH]; simpl in *; first done.
    destruct (decide (i = j)) as [<- | Hneq]; first done.
    rewrite list_lookup_insert_ne; last done. by eapply IH.
  Qed.
  Lemma lookup_interpret_inserts_Some_2 {X} (iml : list (nat * X)) (ls : list X) i x :
    i < length ls →
    lookup_iml iml i = Some x →
    interpret_inserts iml ls !! i = Some x.
  Proof.
    induction iml as [ | [j y] iml IH]; simpl; first done.
    intros Hlen Ha. destruct (decide (i = j)) as [<- | Hneq].
    - injection Ha as ->. rewrite list_lookup_insert; first done.
      rewrite interpret_inserts_length //.
    - rewrite list_lookup_insert_ne; last done. by eapply IH.
  Qed.

  Lemma lookup_interpret_iml_Some_1 {X} (iml : list (nat * X)) (def : X) len i :
    lookup_iml iml i = None →
    i < len →
    interpret_iml def len iml !! i = Some def.
  Proof.
    intros Ha Hlen. rewrite lookup_interpret_inserts_1; last done.
    rewrite lookup_replicate; done.
  Qed.
  Lemma lookup_interpret_iml_None_1 {X} (iml : list (nat * X)) (def : X) len i :
    lookup_iml iml i = None →
    len ≤ i →
    interpret_iml def len iml !! i = None.
  Proof.
    intros Ha Hlen. rewrite lookup_interpret_inserts_1; last done.
    apply lookup_replicate_None; done.
  Qed.
  Lemma lookup_interpret_iml_Some_2 {X} (iml : list (nat * X)) (def : X) len i x :
    lookup_iml iml i = Some x →
    i < len →
    interpret_iml def len iml !! i = Some x.
  Proof.
    intros Ha Hlen. induction iml as [ | [j y] iml IH]; simpl; first done.
    simpl in *. destruct (decide (i = j)) as [<- | Hneq].
    - injection Ha as ->. rewrite list_lookup_insert; first done.
      rewrite interpret_iml_length//.
    - rewrite list_lookup_insert_ne; last done. by apply IH.
  Qed.

  Lemma elem_of_interpret_iml_inv {X} (def : X) iml len x :
    x ∈ interpret_iml def len iml → x = def ∨ ∃ i, (i, x) ∈ iml.
  Proof.
    intros (i & Hel)%elem_of_list_lookup_1.
    apply lookup_interpret_iml_Some_inv in Hel as (? & [? | ?]); eauto.
  Qed.


  Lemma interpret_inserts_fmap {X Y} (f : X → Y) iml ls :
    interpret_inserts ((λ '(a, b), (a, f b)) <$> iml) (f <$> ls) =
    f <$> interpret_inserts iml ls.
  Proof.
    induction iml as [ | [i x] iml IH]; simpl; first done.
    rewrite list_fmap_insert. f_equiv. by apply IH.
  Qed.
  Lemma interpret_iml_fmap {X Y} (f : X → Y) (def : X) len iml :
    interpret_iml (f def) len ((λ '(a, b), (a, f b)) <$> iml) =
    f <$> interpret_iml def len iml.
  Proof.
    rewrite /interpret_iml -interpret_inserts_fmap.
    rewrite fmap_replicate. done.
  Qed.

  Lemma interpret_inserts_nil {X} (iml : list (nat * X)) :
    interpret_inserts iml [] = [].
  Proof.
    induction iml as [ | [] iml IH]; simpl; first done.
    rewrite IH. done.
  Qed.
  Lemma interpret_iml_0 {X} (def : X) (iml : list (nat * X)) :
    interpret_iml def 0 iml = [].
  Proof.
    rewrite /interpret_iml. rewrite interpret_inserts_nil//.
  Qed.

  Fixpoint cut_iml {X} (iml : list (nat * X)) : list (nat * X) :=
    match iml  with
    | [] => []
    | (0, x) :: iml => cut_iml iml
    | (S i, x) :: iml => (i, x) :: cut_iml iml
    end.

  Lemma interpret_inserts_cons {X} (iml : list (nat * X)) h (l : list _) :
    interpret_inserts iml (h :: l) =
    (match lookup_iml iml 0 with | Some a => a | _ => h end) :: interpret_inserts (cut_iml iml) l.
  Proof.
    induction iml as [ | [i x] iml IH] in h, l |-*; simpl; first done.
    rewrite IH. destruct i as [ | i]; simpl; done.
  Qed.
  Lemma interpret_iml_succ {X} len (def : X) (iml : list (nat * X)) :
    interpret_iml def (S len) iml =
    (match lookup_iml iml 0 with | Some a => a | _ => def end) :: interpret_iml def len (cut_iml iml).
  Proof.
    rewrite /interpret_iml/=. rewrite interpret_inserts_cons//.
  Qed.

  Lemma insert_interpret_iml {X} (def : X) (len : nat) (iml : list (nat * X)) i x :
    <[i := x]> (interpret_iml def len iml) = interpret_iml def len ((i, x) :: iml).
  Proof. done. Qed.
End array.

(** ** Place types *)

(** bor_kind *)
Section ltype.
Context `{typeGS Σ}.

(**
  A [bor_kind] determines which ownership we have of an ltype.
  [Owned with_later] says that we fully own it, where inner ownership is optionally guarded by a later.
    + the [with_later = true] case is needed for Box types, which need to guard their inner type to enable recursive types.
    + the [with_later = false] case is needed for top-level ownership of places in the typing context (for modelling stack places).
  [Shared κ] says that we have shared ownership at lifetime κ.
  [Uniq κ γ] says that we own it under a mutable borrow at lifetime κ, where γ is the ghost variable for the mutable reference. This is needed for properly nesting the refinements of mutable references.
 *)
Inductive bor_kind :=
 | Owned (with_later : bool) | Shared (κ : lft) | Uniq (κ : lft) (γ : gname).
Global Instance bor_kind_inhabited : Inhabited bor_kind := populate (Owned false).

Definition lctx_bor_kind_alive (E : elctx) (L : llctx) (b : bor_kind) :=
  match b with
  | Owned _ => True
  | Shared κ | Uniq κ _ => lctx_lft_alive E L κ
  end.

(** ** Inclusion of bor_kinds *)
(* we ignore the ghost variable names *)
Definition bor_kind_min (b1 b2 : bor_kind) : bor_kind :=
  match b1, b2 with
  | Owned wl, _ => b2
  | _, Owned wl => b1
  | Uniq κ1 γ1, Uniq κ2 γ2 => Uniq (κ1 ⊓ κ2) γ1
  | Shared κ1, Uniq κ2 γ2 => Uniq (κ1 ⊓ κ2) γ2
  | Uniq κ1 γ1, Shared κ2 => Uniq (κ1 ⊓ κ2) γ1
  | Shared κ1, Shared κ2 => Shared (κ1 ⊓ κ2)
  end.
Arguments bor_kind_min : simpl nomatch.

Definition bor_kind_incl (b1 b2 : bor_kind) : iProp Σ :=
  match b1, b2 with
  | _, Owned _ => True
  | Uniq κ1 γ1, Uniq κ2 γ2 => κ1 ⊑ κ2
  | Uniq κ1 γ1, Shared κ2 => κ1 ⊑ κ2
  | Shared κ1, Shared κ2 => κ1 ⊑ κ2
  | _, _ => False
  end%I.
Arguments bor_kind_incl : simpl nomatch.

Definition bor_kind_direct_incl (b1 b2 : bor_kind) : iProp Σ :=
  match b1, b2 with
  | Owned wl1, Owned wl2 => ⌜wl1 = wl2⌝
  | Uniq κ1 γ1, Uniq κ2 γ2 => κ1 ⊑ κ2 ∗ ⌜γ1 = γ2⌝
  | Shared κ1, Shared κ2 => κ1 ⊑ κ2
  | _, _ => False
  end.
Arguments bor_kind_direct_incl : simpl nomatch.


Infix "⊑ₖ" := bor_kind_incl (at level 70) : bi_scope.
Infix "⊓ₖ" := bor_kind_min (at level 40) : stdpp_scope.
Infix "⊑ₛₖ" := bor_kind_direct_incl (at level 70) : bi_scope.

Global Instance bor_kind_incl_pers b1 b2 : Persistent (b1 ⊑ₖ b2).
Proof. destruct b1, b2; apply _. Qed.

Lemma bor_kind_incl_refl b:
  ⊢ (b ⊑ₖ b)%I.
Proof. destruct b; first done; iApply lft_incl_refl. Qed.
Lemma bor_kind_min_incl_l b1 b2 :
  ⊢ (b1 ⊓ₖ b2 ⊑ₖ b1)%I.
Proof. destruct b1, b2; simpl; eauto using lft_incl_refl, lft_intersect_incl_l. Qed.
Lemma bor_kind_min_incl_r b1 b2 :
  ⊢ (b1 ⊓ₖ b2 ⊑ₖ b2)%I.
Proof. destruct b1, b2; simpl; eauto using lft_incl_refl, lft_intersect_incl_r. Qed.
Lemma bor_kind_incl_trans b1 b2 b3 :
  ⊢ (b1 ⊑ₖ b2 -∗ b2 ⊑ₖ b3 -∗ b1 ⊑ₖ b3)%I.
Proof. destruct b1, b2, b3; simpl; iIntros "#?? //"; by iApply lft_incl_trans. Qed.
Lemma bor_kind_incl_glb b1 b2 b3 :
  b1 ⊑ₖ b2 -∗
  b1 ⊑ₖ b3 -∗
  b1 ⊑ₖ b2 ⊓ₖ b3.
Proof.
  iIntros "Hincl1 Hincl2".
  destruct b1, b2, b3; unfold bor_kind_min, bor_kind_incl; simpl; try done; try iApply lft_incl_refl.
  all: iApply (lft_incl_glb with "Hincl1 Hincl2").
Qed.

Definition lctx_bor_kind_incl (E : elctx) (L : llctx) b b' : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ b ⊑ₖ b').

Lemma lctx_bor_kind_incl_acc E L k1 k2 :
  lctx_bor_kind_incl E L k1 k2 →
  elctx_interp E -∗ llctx_interp L -∗ k1 ⊑ₖ k2.
Proof.
  intros Hincl. iIntros "HE HL".
  iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
  iApply (Hincl with "HL HE").
Qed.

Lemma lctx_bor_kind_incl_use E L b1 b2 :
  lctx_bor_kind_incl E L b1 b2 →
  elctx_interp E -∗
  llctx_interp L -∗
  b1 ⊑ₖ b2.
Proof.
  iIntros (Hincl) "HE HL".
  iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
  by iPoseProof (Hincl with "HL HE") as "Ha".
Qed.


(** Outliving *)
Definition bor_kind_outlives (b : bor_kind) (κ : lft) : iProp Σ :=
  match b with
  | Owned _ => True
  | Uniq κ' _ => κ ⊑ κ'
  | Shared κ' => κ ⊑ κ'
  end.
Global Instance bor_kind_outlives_persistent b κ : Persistent (bor_kind_outlives b κ).
Proof. destruct b; apply _. Qed.
Lemma bor_kind_outlives_mono b b' κ :
  b ⊑ₖ b' -∗ bor_kind_outlives b κ -∗ bor_kind_outlives b' κ.
Proof.
  iIntros "#Hincl1 #Hincl2". destruct b, b'; unfold bor_kind_incl; simpl; first [done | iApply lft_incl_trans; done ].
Qed.

Definition lctx_bor_kind_outlives (E : elctx) (L : llctx) (b : bor_kind) (κ : lft) :=
  ∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ bor_kind_outlives b κ.
Arguments lctx_bor_kind_outlives : simpl nomatch.

Lemma lctx_bor_kind_outlives_all_use (E : elctx) (L : llctx) k κs :
  ⌜Forall (lctx_bor_kind_outlives E L k) κs⌝ -∗
  elctx_interp E -∗
  llctx_interp L -∗
  [∗ list] κ ∈ κs, bor_kind_outlives k κ.
Proof.
  iIntros (Hf) "#HE HL".
  iPoseProof (Forall_big_sepL _ (bor_kind_outlives k) with "HL []") as "(Houtl & HL)"; first apply Hf.
  { iModIntro. iIntros (?) "HL %Hout". iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (Hout with "HL HE") as "#Hout". iPoseProof ("HL_cl"  with "HL") as "?". by iFrame. }
  done.
Qed.

(** Direct inclusion *)
Global Instance bor_kind_direct_incl_pers b1 b2 : Persistent (b1 ⊑ₛₖ b2).
Proof. destruct b1, b2; apply _. Qed.

Lemma bor_kind_direct_incl_refl b:
  ⊢ (b ⊑ₛₖ b)%I.
Proof.
  destruct b; simpl.
  - eauto.
  - iApply lft_incl_refl.
  - iSplit; last done. iApply lft_incl_refl.
Qed.
Lemma bor_kind_direct_incl_trans b1 b2 b3 :
  ⊢ (b1 ⊑ₛₖ b2 -∗ b2 ⊑ₛₖ b3 -∗ b1 ⊑ₛₖ b3)%I.
Proof.
  destruct b1, b2, b3; simpl; first [iIntros "-> ->" | iIntros "[#? ->] [#? ->]" | iIntros "#?? //"].
  - done.
  - by iApply lft_incl_trans.
  - iSplit; last done. by iApply lft_incl_trans.
Qed.
Lemma bor_kind_direct_incl_glb b1 b2 b3 :
  b1 ⊑ₛₖ b2 -∗
  b1 ⊑ₛₖ b3 -∗
  b1 ⊑ₛₖ b2 ⊓ₖ b3.
Proof.
  iIntros "Hincl1 Hincl2".
  destruct b1, b2, b3; unfold bor_kind_min, bor_kind_incl; simpl; try done; try iApply lft_incl_refl.
  - iApply (lft_incl_glb with "Hincl1 Hincl2").
  - iDestruct "Hincl1" as "(Hincl1 & ->)". iDestruct "Hincl2" as "(Hincl2 & ->)".
    iSplit; last done. iApply (lft_incl_glb with "Hincl1 Hincl2").
Qed.
Lemma bor_kind_direct_incl_bor_kind_incl b1 b2 :
  b1 ⊑ₛₖ b2 -∗ b1 ⊑ₖ b2.
Proof.
  iIntros "Hincl".
  destruct b1, b2; unfold bor_kind_incl, bor_kind_direct_incl; simpl; try done.
  iDestruct "Hincl" as "($ & _)".
Qed.

Definition lctx_bor_kind_direct_incl (E : elctx) (L : llctx) b b' : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ b ⊑ₛₖ b').

Lemma lctx_bor_kind_direct_incl_use E L b1 b2 :
  lctx_bor_kind_direct_incl E L b1 b2 →
  elctx_interp E -∗
  llctx_interp L -∗
  b1 ⊑ₛₖ b2.
Proof.
  iIntros (Hincl) "HE HL".
  iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
  by iPoseProof (Hincl with "HL HE") as "Ha".
Qed.

End ltype.

Infix "⊑ₖ" := bor_kind_incl (at level 70) : bi_scope.
Infix "⊑ₛₖ" := bor_kind_direct_incl (at level 70) : bi_scope.
Infix "⊓ₖ" := bor_kind_min (at level 40) : stdpp_scope.

Global Arguments bor_kind_min : simpl never.
Global Arguments bor_kind_incl : simpl never.
Global Arguments bor_kind_direct_incl : simpl never.

(*Global Hint Extern 4 (Inhabited _) => refine (populate _); assumption : typeclass_instances.*)

Section ltype_def.
  Context `{typeGS Σ}.

  (**
    [PlaceIn]: the current inner refinement is accurate (no blocking of the inner refinement).
    [PlaceGhost]: the current inner refinement is determined by a ghost variable, either because it is currently blocked or was implicitly unblocked.
  *)
  Inductive place_rfn_mode := PlaceModeIn | PlaceModeGhost.
  (* concrete refinements *)
  Inductive place_rfn (rt : Type) :=
    | PlaceIn (r : rt)
    | PlaceGhost (γ : gname).
  Global Arguments PlaceIn {_}.
  Global Arguments PlaceGhost {_}.

  Global Instance place_rfn_inh rt : Inhabited (place_rfn rt).
  Proof. refine (populate (PlaceGhost inhabitant )). Qed.
  Global Instance place_rfn_mode_inh : Inhabited (place_rfn_mode).
  Proof. refine (populate (PlaceModeGhost)). Qed.

  (* interpretation of place_rfn under owned *)
  Definition place_rfn_interp_owned {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ' => gvar_pobs γ' r'
    end.

  Definition place_rfn_interp_owned_blocked {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ' => gvar_auth γ' r'
    end.

  (* interpretation of place_rfn under mut *)
  Definition place_rfn_interp_mut {rt} (r : place_rfn rt) γ : iProp Σ :=
    match r with
    | PlaceIn r' => gvar_obs γ r'
    | PlaceGhost γ' => Rel2 γ' γ (@eq rt)
    end.
  Definition place_rfn_interp_mut_blocked {rt} (r : place_rfn rt) γ : iProp Σ :=
    match r with
    | PlaceIn r' => gvar_obs γ r'
    | PlaceGhost γ' => Rel2 γ' γ (@eq rt)
    end.

  (* interpretation of place_rfn under shared *)
  (* we don't get any knowledge for PlaceGhost: we should really unblock before initiating sharing *)
  Definition place_rfn_interp_shared {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ => gvar_pobs γ r'
    end.
  Global Instance place_rfn_interp_shared_pers {rt} (r : place_rfn rt) r' : Persistent (place_rfn_interp_shared r r').
  Proof. destruct r; apply _. Qed.
  (* NOTE: It's a bit unlucky that we have to rely on timelessness of this in some cases, in particular for some of the unfolding lemmas. *)
  Global Instance place_rfn_interp_shared_timeless {rt} (r : place_rfn rt) r' : Timeless (place_rfn_interp_shared r r').
  Proof. destruct r; apply _. Qed.
  Global Instance place_rfn_interp_owned_timeless {rt} (r : place_rfn rt) r' : Timeless (place_rfn_interp_owned r r').
  Proof. destruct r; apply _. Qed.
  Global Instance place_rfn_interp_mut_timeless {rt} (r : place_rfn rt) γ : Timeless (place_rfn_interp_mut r γ).
  Proof. destruct r; apply _. Qed.

  Lemma place_rfn_interp_mut_iff {rt} (r : place_rfn rt) γ :
    place_rfn_interp_mut r γ ⊣⊢ ∃ r' : rt, gvar_obs γ r' ∗ match r with | PlaceGhost γ' => gvar_pobs γ' r' | PlaceIn r => ⌜r = r'⌝ end.
  Proof.
    destruct r as [ r | γ']; simpl.
    - iSplit.
      + iIntros "?"; eauto with iFrame.
      + iIntros "(%r' & ? & ->)"; iFrame.
    - iSplit.
      + iIntros "(%r1 & %r2 & ? & ? & ->)". iExists _. iFrame.
      + iIntros "(%r' & ? & ?)". iExists _, _. iFrame. done.
  Qed.

  Lemma place_rfn_interp_mut_owned {rt} (r : place_rfn rt) (r' : rt) γ :
    place_rfn_interp_mut r γ -∗
    gvar_auth γ r' ==∗
    place_rfn_interp_owned r r' ∗
    gvar_obs γ r' ∗ gvar_auth γ r'.
  Proof.
    iIntros "Hrfn Hauth".
    destruct r as [r'' | γ']; simpl.
    - iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
      iSplitR; first done. by iFrame.
    - iDestruct "Hrfn" as "(%r1 & %r2 & Hauth' & Hobs & ->)".
      iPoseProof (gvar_agree with "Hauth Hobs") as "#->". iFrame. done.
  Qed.
  Lemma place_rfn_interp_owned_mut {rt} (r : place_rfn rt) r' γ :
    place_rfn_interp_owned r r' -∗
    gvar_obs γ r' -∗
    place_rfn_interp_mut r γ.
  Proof.
    iIntros "Hrfn Hobs".
    destruct r as [r'' | γ'].
    - iDestruct "Hrfn" as "<-". iFrame.
    - iDestruct "Hrfn" as "Hauth'". simpl.
      rewrite /Rel2. iExists _, _. by iFrame.
  Qed.

  (** lemmas for unblocking *)
  Lemma place_rfn_interp_owned_blocked_unblock {rt} (r : place_rfn rt) (r' : rt) :
    place_rfn_interp_owned_blocked r r' ==∗ place_rfn_interp_owned r r'.
  Proof.
    destruct r as [ r'' | γ]; simpl; first by eauto.
    iApply gvar_auth_persist.
  Qed.
  Lemma place_rfn_interp_mut_blocked_unblock {rt} (r : place_rfn rt) (γ : gname) :
    place_rfn_interp_mut_blocked r γ ==∗ place_rfn_interp_mut r γ.
  Proof.
    destruct r as [ r' | γ']; simpl; first by eauto.
    eauto.
  Qed.

  (** lemmas for sharing *)
  Lemma place_rfn_interp_owned_share' {rt} (r : place_rfn rt) (r' : rt) :
    place_rfn_interp_owned r r' -∗
    place_rfn_interp_shared r r'.
  Proof.
    iIntros "Hrfn".
    destruct r.
    - iDestruct "Hrfn" as "->". eauto.
    - iDestruct "Hrfn" as "#Hrfn". eauto.
  Qed.
  Lemma place_rfn_interp_owned_share F {rt} (r : place_rfn rt) (r' : rt) q κ :
    lftE ⊆ F →
    lft_ctx -∗
    &{κ} (place_rfn_interp_owned r r') -∗
    q.[κ] ={F}=∗
    place_rfn_interp_shared r r' ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT Hb Htok".
    iMod (bor_acc with "LFT Hb Htok") as "(>Hrfn & Hcl)"; first solve_ndisj.
    iPoseProof (place_rfn_interp_owned_share' with "Hrfn") as "#Hrfn'".
    iMod ("Hcl" with "[//]") as "(? & $)". eauto.
  Qed.
  Lemma place_rfn_interp_mut_share' (F : coPset) {rt} `{!Inhabited rt} (r : place_rfn rt) (r' : rt) γ (q : Qp) κ :
    lftE ⊆ F →
    lft_ctx -∗
    place_rfn_interp_mut r γ -∗
    &{κ} (gvar_auth γ r') -∗
    q.[κ] ={F}=∗
    place_rfn_interp_shared r r' ∗ (▷ place_rfn_interp_mut r γ) ∗ &{κ} (gvar_auth γ r') ∗ q.[κ].
  Proof.
    iIntros (?) "#CTX Hobs Hauth Htok".
    iMod (bor_acc with "CTX Hauth Htok") as "(>Hauth & Hcl_auth)"; first solve_ndisj.
    iAssert (|={F}=> place_rfn_interp_shared r r' ∗ gvar_auth γ r' ∗ ▷ place_rfn_interp_mut r γ)%I with "[Hauth Hobs]" as ">(Hrfn & Hauth & Hobs)".
    { destruct r.
      - iDestruct "Hobs" as "Hobs". iPoseProof (gvar_agree with "Hauth Hobs") as "#->". eauto with iFrame.
      - simpl. rewrite /Rel2. iDestruct "Hobs" as "(%v1 & %v2 & #Hpobs & Hobs & %Heq')". rewrite Heq'.
        iPoseProof (gvar_agree with "Hauth Hobs") as "%Heq". rewrite Heq.
        iFrame. iR. iModIntro. iModIntro. iExists _, _. iFrame. iR. done.
    }
    iMod ("Hcl_auth" with "[$Hauth]") as "($ & Htoka2)".
    by iFrame.
  Qed.
  Lemma place_rfn_interp_mut_share (F : coPset) {rt} `{!Inhabited rt} (r : place_rfn rt) (r' : rt) γ (q : Qp) κ :
    lftE ⊆ F →
    lft_ctx -∗
    &{κ} (place_rfn_interp_mut r γ) -∗
    &{κ} (gvar_auth γ r') -∗
    q.[κ] ={F}=∗
    place_rfn_interp_shared r r' ∗ &{κ} (place_rfn_interp_mut r γ) ∗ &{κ} (gvar_auth γ r') ∗ q.[κ].
  Proof.
    iIntros (?) "#CTX Hobs Hauth (Htok1 & Htok2)".
    iMod (bor_acc with "CTX Hobs Htok1") as "(>Hobs & Hcl_obs)"; first solve_ndisj.
    iMod (place_rfn_interp_mut_share' with "CTX Hobs Hauth Htok2") as "($ & Hmut & $ & $)"; first done.
    iMod ("Hcl_obs" with "[$Hmut]") as "($ & Htok_κ')".
    by iFrame.
  Qed.

  Lemma place_rfn_interp_shared_mut {rt} (r : place_rfn rt) r' γ :
    place_rfn_interp_shared r r' -∗
    gvar_obs γ r' -∗
    place_rfn_interp_mut r γ.
  Proof.
    iIntros "Hrfn Hobs".
    destruct r as [ r | γ']; simpl.
    - iDestruct "Hrfn" as "<-"; eauto with iFrame.
    - iExists _, _. eauto with iFrame.
  Qed.
  Lemma place_rfn_interp_shared_owned {rt} (r : place_rfn rt) r' :
    place_rfn_interp_shared r r' -∗
    place_rfn_interp_owned r r'.
  Proof. destruct r; eauto with iFrame. Qed.


  (** For adding information to the context *)
  Definition place_rfn_interp_mut_extracted {rt} (r : place_rfn rt) (γ : gname) : iProp Σ :=
    match r with
    | PlaceIn r' => gvar_pobs γ r'
    | PlaceGhost γ' => Rel2 (T:=rt) γ' γ eq
    end.
  Definition place_rfn_interp_owned_extracted {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ' => gvar_pobs γ' r'
    end.

  Lemma place_rfn_interp_mut_extract {rt} (r : place_rfn rt) (γ : gname) :
    place_rfn_interp_mut r γ ==∗ place_rfn_interp_mut_extracted r γ.
  Proof.
    destruct r; simpl.
    - iIntros "Hobs". iApply (gvar_obs_persist with "Hobs").
    - eauto.
  Qed.
  Lemma place_rfn_interp_owned_extract {rt} (r : place_rfn rt) (r' : rt) :
    place_rfn_interp_owned r r' ==∗ place_rfn_interp_owned_extracted r r'.
  Proof.
    destruct r; simpl.
    - eauto.
    - eauto.
  Qed.

  Implicit Types
    (κ : lft)
    (k : bor_kind)
    (l : loc)
    (π : thread_id)
  .

  (** ** Definition *)
  (** ltypes are Type-indexed by their refinement type.
    However, defining this directly makes it hard to define an induction principle on them,
    so we first define a separate version [lty] that is not indexed, but rather Type-equalities when using them,
     and later on define [ltype], which exposes [lty_rt] as in index, on top. *)
  Inductive lty : Type :=
    | BlockedLty {rt} (t : type rt) (κ : lft)
    | ShrBlockedLty {rt} (t : type rt) (κ : lft)
    | OfTyLty {rt} (t : type rt)
    (* AliasLty is polymorphic in the refinement type -- it accepts any refinement *)
    | AliasLty (rt : Type) (st : syn_type) (l : loc)
    | MutLty (lt : lty) (κ : lft)
    | ShrLty (lt : lty) (κ : lft)
    | BoxLty (lt : lty)
    (* [ls = true] iff this should put a later *)
    | OwnedPtrLty (lt : lty) (ls : bool)
    | StructLty (lts : list lty) (sls : struct_layout_spec)
    (* [def] is the default element type; [lts] masks this for certain indices *)
    | ArrayLty {rt} (def : type rt) (len : nat) (lts : list (nat * lty))
    (* [en] is the enum spec. [variant] is the current unfolded variant. [lte] is the current type of the variant. *)
    | EnumLty {rt} (en : enum rt) (variant : string) (lte : lty)
    | OpenedLty
        (* NOTE: we parameterize over the refinement types here,
           as we don't have support for induction-recursion in Coq to define [lty_rfn] mutually.
           The ownership predicate will require that they are equal to the actual refinement types. *)
        (** [lt_cur] is the currently owned ltype here.
            [lt_inner] is the condition on when we can fold again: the core of [lt_cur] needs to be equivalent to [lt_inner].
            [ty_full] is the type describing the original ownership. It needs to be a type to formulate the Uniq case.
           (we might be able to lift this restriction by having equations that unfold applicable ltypes from Uniq to Owned, exposing the borrow in the process) *)
        {rt_inner rt_full : Type}
        (lt_cur : lty) (lt_inner : lty) (lt_full : lty)
        (Cpre : rt_inner → rt_full → iProp Σ)
        (Cpost : rt_inner → rt_full → iProp Σ)
    | CoreableLty
        (** gives us [lt_full] after all [κs] are dead; with no currently accessible ownership *)
        (* TODO think about how we can unify this with BlockedLtype *)
        (κs : list lft)
        (lt_full : lty)
    | ShadowedLty {rt : Type} (lt_cur : lty) (r_cur : place_rfn rt) (lt_full : lty)
  .

  (*
  Basic setup for augmenting these with place_rfns:
      - since we move down the interpretation of ownership by one level anyways,
        we also handle the interpretation of place_rfn for a particular place there,
        one level down (for the respective place)
      - this enables us to state ownership of the gvar_obs of the outer mut ref (one above) depending on the state of the place owned by the reference.
        i.e.:
          - for blocked this is quite clear, we want to link up the outer reference with the inner reference.
          - for other places, this controls the presence of the gvar_obs fragment/what we know about the inner refinement
   *)
  Fixpoint lty_rt (lt : lty) : Type :=
    match lt with
    | @BlockedLty rt _ _ => rt
    | @ShrBlockedLty rt _ _ => rt
    | @OfTyLty rt _ => rt
    | AliasLty rt st l => rt
    | MutLty lt _ => (place_rfn (lty_rt lt) * gname)%type
    | BoxLty lt => place_rfn (lty_rt lt)
    | OwnedPtrLty lt ls => (place_rfn (lty_rt lt) * loc)
    | ShrLty lt _ => place_rfn (lty_rt lt)
    | StructLty lts _ =>
        (*unit*)
        plist (λ lt, place_rfn (lty_rt lt)) lts
    | @ArrayLty rt def len lts => list (place_rfn rt)
    | @EnumLty rt en variant lte => rt
    | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
        lty_rt lt_cur
    | CoreableLty κ lt_full =>
        lty_rt lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        lty_rt lt_full
    end.

  Fixpoint lty_st (lt : lty) : syn_type :=
    match lt with
    | BlockedLty ty _ => ty.(ty_syn_type)
    | ShrBlockedLty ty _ => ty.(ty_syn_type)
    | OfTyLty ty => ty.(ty_syn_type)
    | AliasLty _ st l => st
    | MutLty _ _ => PtrSynType
    | BoxLty _ => PtrSynType
    | OwnedPtrLty _ _ => PtrSynType
    | ShrLty _ _ => PtrSynType
    | StructLty _ sls => sls
    | ArrayLty def len lts => ArraySynType (ty_syn_type def) len
    | EnumLty en variant lte => en.(enum_els)
    | OpenedLty lt_cur _ _ _ _ => lty_st lt_cur
    | CoreableLty _ lt_full =>
        lty_st lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        lty_st lt_full
    end.

  Fixpoint lty_wf (lt : lty) : Prop :=
    match lt with
    | BlockedLty _ _ => True
    | ShrBlockedLty _ _ => True
    | OfTyLty _ => True
    | AliasLty _ st l => True
    | MutLty lt κ => lty_wf lt
    | ShrLty lt _ => lty_wf lt
    | BoxLty lt => lty_wf lt
    | OwnedPtrLty lt _ => lty_wf lt
    | StructLty lts _ => Forall_cb lty_wf lts
    | @ArrayLty rt def len lts =>
        Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt(*∧ i < len *)) lts
    | EnumLty en variant lte =>
        lty_wf lte ∧ lty_rt lte = (enum_tag_rt en variant)
    | @OpenedLty rt_inner rt_full lt_cur lt_inner lt_full _ _ =>
        (* require that the refinements actually match *)
        rt_inner = lty_rt lt_inner ∧ rt_full = lty_rt lt_full ∧ lty_wf lt_cur ∧ lty_wf lt_inner ∧ lty_wf lt_full
        (*∧ lty_st lt_inner = lty_st lt_full ∧ lty_st lt_cur = lty_st lt_full*)
    | CoreableLty _ lt =>
        lty_wf lt
    | @ShadowedLty rt_cur lt_cur r_cur lt_full =>
        lty_wf lt_cur ∧ lty_wf lt_full ∧ lty_rt lt_cur = rt_cur
    end.


  (* induction principle loosely based on unary parametricity *)
  Lemma lty_recursor :
    ∀ P : lty → Type,
      (∀ (rt : Type) (t : type rt), ∀ κ : lft, P (BlockedLty t κ)) →
      (∀ (rt : Type) (t : type rt), ∀ κ : lft, P (ShrBlockedLty t κ)) →
      (∀ (rt : Type) (t : type rt), P (OfTyLty t)) →
      (∀ (rt : Type) (st : syn_type) (l : loc), P (AliasLty rt st l)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (MutLty lt κ)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (ShrLty lt κ)) →
      (∀ lt : lty, P lt → P (BoxLty lt)) →
      (∀ (lt : lty) (ls : bool), P lt → P (OwnedPtrLty lt ls)) →
      (∀ lts : list lty, list_is_list lty P lts → ∀ sls : struct_layout_spec, P (StructLty lts sls)) →
      (∀ (rt : Type) (def : type rt) (len : nat) (lts : list (nat * lty)),
        list_is_list _ (λ '(_, lt), P lt) lts → P (ArrayLty def len lts)) →
      (∀ (rt : Type) (en : enum rt) (variant : string) (lte : lty),
        P lte → P (EnumLty en variant lte)) →
      (∀ (rt_inner rt_full : Type) (lt_cur lt_inner lt_full : lty)
        (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ),
          P lt_cur → P lt_inner → P lt_full → P (OpenedLty lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ κs (lt_full : lty), P lt_full → P (CoreableLty κs lt_full)) →
      (∀ (rt_cur : Type) (lt_cur : lty) (r_cur : place_rfn rt_cur) (lt_full : lty), P lt_cur → P lt_full → P (ShadowedLty lt_cur r_cur lt_full)) →
      ∀ lt : lty, P lt.
  Proof.
    intros P Hblocked Hshrblocked Hofty Halias Hmut Hshr Hbox Hptr Hstruct Harr Henum Hopened Hcoreable Hshadow.
    (* doing induction does not give us the IH *)
    refine (fix IH (lt : lty) {struct lt} : P lt :=
      match lt return (P lt) with
      | BlockedLty t κ => Hblocked _ t κ
      | ShrBlockedLty t κ => Hshrblocked _ t κ
      | OfTyLty t => Hofty _ t
      | AliasLty rt st l => Halias rt st l
      | MutLty lt κ => Hmut lt _ κ
      | ShrLty lt κ => Hshr lt _ κ
      | BoxLty lt => Hbox lt _
      | OwnedPtrLty lt ls => Hptr lt ls _
      | StructLty lts sls =>
          _
      | @ArrayLty rt def len lts =>
          _
      | EnumLty en variant lte =>
          _
      | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
          _
      | CoreableLty κ lt_full =>
          _
      | ShadowedLty lt_cur r_cur lt_full =>
          _
      end); [apply IH.. | | | | | | ].
      - apply Hstruct.
        apply list_is_list_full.
        apply IH.
      - apply Harr. apply list_is_list_full. intros []. apply IH.
      - apply Henum. apply IH.
      - apply Hopened; apply IH.
      - apply Hcoreable; apply IH.
      - apply Hshadow; apply IH.
  Defined.

  Lemma lty_induction :
    ∀ P : lty → Prop,
      (∀ (rt : Type) (t : type rt), ∀ κ : lft, P (BlockedLty t κ)) →
      (∀ (rt : Type) (t : type rt), ∀ κ : lft, P (ShrBlockedLty t κ)) →
      (∀ (rt : Type) (t : type rt), P (OfTyLty t)) →
      (∀ (rt : Type) (st : syn_type) (l : loc), P (AliasLty rt st l)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (MutLty lt κ)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (ShrLty lt κ)) →
      (∀ lt : lty, P lt → P (BoxLty lt)) →
      (∀ (lt : lty) (ls : bool), P lt → P (OwnedPtrLty lt ls)) →
      (∀ lts : list lty, (∀ lt, lt ∈ lts → P lt) → ∀ sls : struct_layout_spec, P (StructLty lts sls)) →
      (∀ (rt : Type) (def : type rt) (len : nat) (lts : list (nat * lty)), (∀ i lt, (i, lt) ∈ lts → P lt) → P (ArrayLty def len lts)) →
      (∀ (rt : Type) (en : enum rt) (variant : var_name) (lte : lty), P lte → P (EnumLty en variant lte)) →
      (∀ (rt_inner rt_full : Type) (lt_cur lt_inner lt_full : lty)
        (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ),
          P lt_cur → P lt_inner → P lt_full → P (OpenedLty lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ κs (lt_full : lty), P lt_full → P (CoreableLty κs lt_full)) →
      (∀ (rt_cur : Type) (lt_cur : lty) (r_cur : place_rfn rt_cur) (lt_full : lty), P lt_cur → P lt_full → P (ShadowedLty lt_cur r_cur lt_full)) →
      ∀ lt : lty, P lt.
  Proof.
    intros P ? ? ? ? ? ? ? ? Hstruct Harr Henum Hopened Hcoreable Hshadow lt.
    induction lt as [ | | | | | | | | lts IH sls | rt def len lts IH | | | | ] using lty_recursor; [by eauto.. | | | | | | ].
    - eapply Hstruct. intros lt Hin. induction lts as [ | lt' lts IH'].
      + apply elem_of_nil in Hin. done.
      + inversion IH; subst. apply elem_of_cons in Hin as [<- | Hin]; first done.
        by apply IH'.
    - eapply Harr.
      intros i lt Hin. induction lts as [ | [j lt'] lts IH'].
      + apply elem_of_nil in Hin. done.
      + inversion IH; subst. apply elem_of_cons in Hin as [ [= <- <-] | Hin]; first done.
        by apply IH'.
    - eapply Henum. done.
    - eapply Hopened; eauto.
    - eapply Hcoreable; eauto.
    - eapply Hshadow; eauto.
  Qed.

  (** Stronger induction principle for the OpenedLtype case, but requires well-formedness. *)
  Lemma lty_induction_wf :
    ∀ P : lty → Prop,
      (∀ (rt : Type) (t : type rt), ∀ κ : lft, P (BlockedLty t κ)) →
      (∀ (rt : Type) (t : type rt), ∀ κ : lft, P (ShrBlockedLty t κ)) →
      (∀ (rt : Type) (t : type rt), P (OfTyLty t)) →
      (∀ (rt : Type) (st : syn_type) (l : loc), P (AliasLty rt st l)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (MutLty lt κ)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (ShrLty lt κ)) →
      (∀ lt : lty, P lt → P (BoxLty lt)) →
      (∀ (lt : lty) (ls : bool), P lt → P (OwnedPtrLty lt ls)) →
      (∀ lts : list lty, (∀ lt, lt ∈ lts → P lt) → ∀ sls : struct_layout_spec, P (StructLty lts sls)) →
      (∀ (rt : Type) (def : type rt) (len : nat) (lts : list (nat * lty)),
        (∀ i lt, (i, lt) ∈ lts → P lt ∧ lty_rt lt = rt) → P (ArrayLty def len lts)) →
      (∀ (rt : Type) (en : enum rt) (variant : var_name) (lte : lty),
        (P lte ∧ lty_rt lte = (enum_tag_rt en variant)) → P (EnumLty en variant lte)) →
      (∀ (lt_cur lt_inner lt_full : lty) (Cpre : (lty_rt lt_inner) → lty_rt lt_full → iProp Σ)
        (Cpost : (lty_rt lt_inner) → (lty_rt lt_full) → iProp Σ),
          P lt_cur → P lt_inner → P lt_full → P (OpenedLty lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ κs (lt_full : lty), P lt_full → P (CoreableLty κs lt_full)) →
      (∀ (lt_cur : lty) (r_cur : place_rfn (lty_rt lt_cur)) (lt_full : lty),
        P lt_cur → P lt_full → P (ShadowedLty lt_cur r_cur lt_full)) →
      ∀ lt : lty, lty_wf lt → P lt.
  Proof.
    intros P ???????? Hstruct Harr Henum Hopened Hcoreable Hshadow lt Hwf.
    induction lt as [ | | | | | | | | lts IH sls | rt def len lts IH | rt en variant lte IH | rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost IH1 IH2 IH3 | κ lt_full IH | ] using lty_induction; [by eauto.. | | | | | | ].
    - eapply Hstruct. intros lt Hlt. eapply IH; first done.
      simpl in Hwf. apply Forall_Forall_cb in Hwf.
      eapply Forall_forall; done.
    - simpl in Hwf. eapply Harr.
      intros i lt Hin.
      simpl in Hwf. apply Forall_Forall_cb in Hwf.
      eapply Forall_forall in Hwf; last apply Hin.
      destruct Hwf as (? & ?). split_and!; [ | done..].
      eapply IH; done.
    - simpl in Hwf. destruct Hwf as (Hwf & Hrt).
      eapply Henum. split. { apply IH. apply Hwf. }
      done.
    - destruct Hwf as (Heq1 & Heq2 & Hcur & Hinner & Hfull ). subst.
      eapply Hopened; eauto.
    - eapply Hcoreable; eauto.
    - destruct Hwf as (? & ? & <-).
      eapply Hshadow; eauto.
  Qed.

  Fixpoint lty_size (lt : lty) : nat :=
    match lt with
    | OfTyLty _ => 0
    | AliasLty rt st l => 0
    | BlockedLty _ _ => 0
    | ShrBlockedLty _ _ => 0
    | BoxLty lt => 1 + lty_size lt
    | OwnedPtrLty lt _ => 1 + lty_size lt
    | MutLty lt _ => 1 + lty_size lt
    | ShrLty lt _ => 1 + lty_size lt
    | StructLty lts _ => 1 + list_max (fmap lty_size lts)
    | ArrayLty def len lts => 1 + (list_max (fmap (λ '(_, lt), lty_size lt) lts))
    | EnumLty en variant lte => 1 + lty_size lte
    | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
        (* we will be using both [lt_cur] and [lt_inner] and [lt_full] recursively *)
        1 + max (lty_size lt_cur) (max (lty_size lt_inner) (lty_size lt_full))
    | CoreableLty _ lt_full =>
        1 + lty_size lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        1 + lty_size lt_cur + lty_size lt_full
    end.
  Definition lty_size_rel : lty → lty → Prop :=
    ltof _ lty_size.
  Global Instance lty_size_rel_wf : WellFounded lty_size_rel.
  Proof. apply well_founded_ltof. Qed.

  (** Derived, stronger well-founded induction principle *)
  Lemma lty_size_recursor (P : lty → Type) :
    (∀ lt, (∀ lt', lty_size lt' < lty_size lt → P lt') → P lt) →
    ∀ lt, P lt.
  Proof.
    apply induction_ltof1.
  Defined.
  Lemma lty_size_induction (P : lty → Prop) :
    (∀ lt, (∀ lt', lty_size lt' < lty_size lt → P lt') → P lt) →
    ∀ lt, P lt.
  Proof.
    apply lty_size_recursor.
  Qed.


  (** The "core" of an ltype that we need to fold it to a type *)
  Fixpoint lty_core (lt : lty) : lty :=
    match lt with
    | BlockedLty t _ => OfTyLty t
    | ShrBlockedLty t _ => OfTyLty t
    | OfTyLty t => OfTyLty t
    | AliasLty rt st l => AliasLty rt st l
    | MutLty lt κ => MutLty (lty_core lt) κ
    | ShrLty lt κ => ShrLty (lty_core lt) κ
    | BoxLty lt => BoxLty (lty_core lt)
    | OwnedPtrLty lt ls => OwnedPtrLty (lty_core lt) ls
    | StructLty lts sls => StructLty (fmap lty_core lts) sls
    | ArrayLty def len lts => ArrayLty def len (fmap (λ '(i, lt), (i, lty_core lt)) lts)
    | EnumLty en variant lte => EnumLty en variant (lty_core lte)
    | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
        (** Rationale: below unfolded stuff, the core just doesn't matter, because we have currently
           anyways broken all contracts and invariants.
            This is also important to get the [lty_core_rt_eq] law, which we use heavily (and is intrinsic to the definition of ltype ownership!).
           Otherwise, we would like to define it as [lt_full], but that breaks this law. *)
        OpenedLty lt_cur lt_inner lt_full Cpre Cpost
    | CoreableLty κ lt_full =>
        lty_core lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        lty_core lt_full
    end.

  Lemma lty_core_syn_type_eq (lt : lty) :
    lty_st (lty_core lt) = lty_st lt.
  Proof.
    induction lt as [ | | | | | | | | | ? IH | | | | ]; by eauto.
  Qed.

  Lemma lty_core_rt_eq lt :
    lty_rt (lty_core lt) = lty_rt lt.
  Proof.
    induction lt as [ | | | | ? IH ? | ? IH ? | ? IH | ? ? IH | ? IH ? | ???? IH | | | | ] using lty_induction; simpl; [done.. | | | | | | | | done | done | done].
    - by rewrite IH.
    - by rewrite IH.
    - by rewrite IH.
    - by rewrite IH.
    - rewrite !(plist_fmap_shift _ lty_rt). f_equiv.
      induction lts as [ | lt lts IH']; first done.
      simpl. rewrite IH; first last. { apply elem_of_cons; eauto. }
      f_equiv. apply IH'. intros. apply IH. apply elem_of_cons; eauto.
    - done.
    - done.
  Qed.

  (* We cannot get the other direction because of CoreableLty *)
  Lemma lty_core_wf lt :
    lty_wf lt → lty_wf (lty_core lt).
  Proof.
    induction lt as [ | | | | | | | | lts IH sls | rt def len lts IH | rt en variant lte IH | | rt lt IH | ] using lty_induction; simpl; [done.. | | | | done | | ].
    - rewrite -!Forall_Forall_cb.
      rewrite Forall_fmap.
      apply Forall_impl_strong.
      intros; by apply IH.
    - rewrite -!Forall_Forall_cb.
      rewrite Forall_fmap.
      intros Hwf.
      eapply Forall_impl_strong; last done.
      intros [i lt] Hlt (? & Hrt). simpl.
      rewrite lty_core_rt_eq.
      split; last done. eapply IH; done.
    - intros [Hwf Hrt]. split; first by apply IH.
      rewrite lty_core_rt_eq. done.
    - done.
    - intros (? & ? & <-). eauto.
  Qed.

  Lemma lty_size_core (lt : lty) :
    lty_size (lty_core lt) ≤ lty_size lt.
  Proof.
    induction lt as [ | | | | | | | |lts IH sls | rt def len lts IH | | | | ] using lty_induction; simpl; [lia.. | | | lia | lia| lia | lia].
    - induction lts as [ | lt lts IH']; simpl; first done.
      efeed pose proof (IH lt) as IH0. { apply elem_of_cons. by left. }
      feed specialize IH'. { intros. apply IH. apply elem_of_cons. by right. }
      unfold fmap in IH'. lia.
    - induction lts as [ | [i lt] lts IH2]; simpl; first lia.
      efeed pose proof (IH i lt) as IH0. { apply elem_of_cons. by left. }
      feed specialize IH2. { intros. eapply IH. apply elem_of_cons. by right. }
      unfold fmap in IH2. lia.
  Qed.

  (*
    Notes on the placement of laters and fancy updates in the interpretations:

    For sharing:
      What are the constraints here/design space?
       - we are forced to have a later over recursive calls to the sharing predicate, due to contractiveness
       - we should not put laters over the fractured borrow (that would require us to take two steps when reading/unable to use timelessness over pointsto)

      So: need to put a later in each of the sharing cases, directly over the recursive call.

      Q: should we also put a later in the ofty case?
        Pro: makes the equation _1 for mut ref unfolding go through easily
        Con: Now I need to put a later above the fractional borrow in MutLty to get the equation _2, which I don't want to do.
      So: just put an update there for timeless stripping

      Approach: put an update in ltype_eq also for the shared borrow case. Does this have drawbacks?
        => Problem: this kills the compatibility with e.g. mut_lty, due to later fupd commuting problems. So this does not seem like the right approach.

      Approach: I need to put an update over the whole MutLty (because all interesting stuff is under the update)
        What is the downside? we anyways need to be able to eliminate an update when accessing the fractional borrow.
        the same trick also seems to work just fine for mutable borrows, where we have an update over the full borrow.
        => This seems to work fine.

      Approach: try to modify the definition of the sharing case of ofty in order to get more useful stuff directly.
        (fundamental problem in this equation here: MutLty has a lot of info upfront, while the def of ofty can't really provide a lot directly) one idea for that: give sharing a "with_later" parameter that allows pushing laters down a bit. still doesn't answer how to get the fractured borrow here without a later though.
   *)


  Definition lty_own_type (lt : lty) := bor_kind → thread_id → place_rfn (lty_rt lt) → loc → iProp Σ.

  Definition lty_own_type_rec (lt0 : lty) := ∀ lt : lty, bor_kind → thread_id → place_rfn (lty_rt lt) → loc → lty_size_rel lt lt0 → iProp Σ.

  Definition UninitLty st := OfTyLty (uninit st).

  Definition maybe_creds (wl : bool) := (if wl then £ num_cred ∗ atime 1 else True)%I.
  Definition have_creds : iProp Σ := £ num_cred ∗ atime 1.

  Definition lty_of_ty_own {rt} (ty : type rt) k π (r : place_rfn rt) l :=
    (∃ ly : layout, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      ty.(ty_sidecond) ∗ loc_in_bounds l 0 (ly.(ly_size)) ∗
    match k with
    | Owned wl =>
        maybe_creds wl ∗
        ∃ r' : rt,
        place_rfn_interp_owned r r' ∗
        (* Have a later here according to wl, which is imposed by e.g. a Box directly above it.
          As such, this is really needed for contractiveness/making working with rec types possible. *)
        ▷?(wl)|={lftE}=>  ∃ v, l ↦ v ∗ ty.(ty_own_val) π r' v
    | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        (* Note: need an update inside the borrow over the recursive thing to get the unfolding equation for products
          (as products need an update there)
          This is really annoying, as this propagates to the other ltypes as well.
          And there, it means that we actually have an update over the pointsto (e.g. in Box and Mutref) in the Uniq case,
            which breaks timelessness after opening the borrow..
         *)
        |={lftE}=> &pin{κ} (∃ r', gvar_auth γ r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r')
    | Shared κ =>
        (* we need an update for timelessness in the unfolding equations (eg for mut_ref) *)
        ∃ r' : rt, place_rfn_interp_shared r r' ∗ □ |={lftE}=> ty.(ty_shr) κ π r' l
    end)%I.

  Definition alias_lty_own (rt : Type) (st : syn_type) (p : loc) k π (r : place_rfn rt) l :=
    match k with
    | Owned wl =>
      ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜p = l⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗ loc_in_bounds l 0 (ly_size ly) ∗ maybe_creds wl
    | _ => False
    end%I.

  Definition blocked_lty_own {rt} (ty : type rt) κ k π (r : place_rfn rt) l :=
    (∃ ly, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      ty.(ty_sidecond) ∗ loc_in_bounds l 0 ly.(ly_size) ∗
    match k with
    | Owned wl =>
        ([† κ] ={lftE}=∗
          ∃ (r' : rt), place_rfn_interp_owned_blocked r r' ∗ |={lftE}=> l ↦: (ty.(ty_own_val) π r')) ∗
        (* and the original credits *)
        maybe_creds wl
    | Shared κ' =>
        (* sharing of inheritances is weird, they are of no use like that,
          and there's no reason to create inheritances directly below
          shared borrows in the first place *)
        False
    | Uniq κ' γ' =>
        (* borrow needs to be synced up with OfTy *)
        ([† κ] ={lftE}=∗
          place_rfn_interp_mut_blocked r γ' ∗
          &pin{κ'} (∃ r' : rt, gvar_auth γ' r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r')) ∗
        (* and the original credits *)
        £ num_cred ∗ atime 1
    end)%I.

  Definition shr_blocked_lty_own {rt} (ty : type rt) κ k π (r : place_rfn rt) l :=
    (∃ ly : layout, ⌜syn_type_has_layout ty.(ty_syn_type) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗ ty.(ty_sidecond) ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
    ∃ r': rt, place_rfn_interp_shared r r' ∗
    match k with
    | Owned wl =>
        (* also have the sharing predicate *)
        ty.(ty_shr) κ π r' l ∗
        ([† κ] ={lftE}=∗ l ↦: ty.(ty_own_val) π r') ∗
        maybe_creds wl
    | Shared κ' =>
        (* already shared -- no need to do something special *)
        (*ty.(ty_shr) κ' π r' l*)
        False
    | Uniq κ' γ' =>
        place_rfn_interp_mut r γ' ∗
        ty.(ty_shr) κ π r' l ∗
        ([† κ] ={lftE}=∗
          (* this needs to be synced up with [OfTy] *)
          &pin{κ'} (∃ r'': rt, gvar_auth γ' r'' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r'')) ∗
        (* original credits *)
        £ num_cred ∗ atime 1
    end)%I.

  (** Shows that the recursive struct case is well-formed. Crucially uses the information we obtain from [big_sepL_P]. *)
  Lemma struct_lts_size_decreasing sl sls (lts : list lty) (r' : plist (λ lt, place_rfn (lty_rt lt)) lts) ty :
    ty ∈  pad_struct (sl_members sl) (pzipl lts r') (λ ly : layout, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())) →
    lty_size_rel (projT1 ty) (StructLty lts sls).
  Proof.
    intros HP.
    destruct ty as (lt & rlt).
    apply elem_of_list_lookup_1 in HP as (j & HP).
    apply pad_struct_lookup_Some_1 in HP as (n & ly & Hlook1 & Hlook2).
    destruct Hlook2 as [ Hlook2 | [_ [= -> ->]]]; first last.
    { unfold lty_size_rel, ltof. simpl. lia. }
    move: Hlook2. generalize (field_idx_of_idx (sl_members sl) j) as m. clear.
    unfold lty_size_rel, ltof; simpl. intros m.
    induction lts as [ | lt0 lts IH] in m, r' |-*; intros [ ? Heq ]; simpl; first done.
    destruct m as [ | m]; simpl.
    - injection Heq as [= <- Heq]. apply existT_inj in Heq. subst rlt. lia.
    - eapply Nat.lt_le_trans; first eapply IH. { split; first done. apply Heq. }
      unfold fmap. lia.
  Qed.

  Lemma array_lts_size_decreasing {rt} (def : type rt) len (lts : list (nat * lty)) {A} (r : list A) (lt : lty * A)  :
    lt ∈ (zip (interpret_iml (OfTyLty def) len lts) r) → lty_size_rel (lt.1) (ArrayLty def len lts).
  Proof.
    intros HP.
    apply elem_of_list_lookup_1 in HP as (j & HP).
    unfold lty_size_rel, ltof; simpl.
    apply lookup_zip in HP as [Hlook1 Hlook2].
    apply lookup_interpret_iml_Some_inv in Hlook1 as (Hlen & Hlook1).
    destruct lt as [lt a].
    destruct Hlook1 as [-> | Hlook1]; simpl; first lia.
    assert (lty_size lt ≤ list_max ((λ '(_, lt), lty_size lt) <$> lts)) as ?; last lia.
    apply elem_of_list_lookup_1 in Hlook1 as (k & Hlook).
    eapply (list_max_le_lookup _ k).
    { rewrite list_lookup_fmap. rewrite Hlook. done. }
    done.
  Qed.

  Import EqNotations.
  (*Set Printing All.*)
  Equations lty_own_pre (core : bool) (ltp : lty) (k : bor_kind) (π : thread_id) (r : place_rfn (lty_rt ltp)) (l : loc) : iProp Σ by wf ltp lty_size_rel :=
    lty_own_pre core (OfTyLty ty) k π r l :=
      (* OfTy *)
      lty_of_ty_own ty k π r l;
    lty_own_pre core (AliasLty rt st p) k π r l :=
      alias_lty_own rt st p k π r l;
    lty_own_pre core (BlockedLty ty κ) k π r l :=
      (** Blocked *)
      if core then lty_of_ty_own ty k π r l else blocked_lty_own ty κ k π r l ;
    lty_own_pre core (ShrBlockedLty ty κ) k π r l :=
      (** ShrBlocked *)
      if core then lty_of_ty_own ty k π r l else shr_blocked_lty_own ty κ k π r l;

    lty_own_pre core (BoxLty lt) k π r l :=
      (** Box *)
      (* TODO: eventually remove this when we model Box as a struct *)
      (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          (* the placement of the pointsto below the later let's us get the unfoldings equation without timelessness *)
          ∃ r' : place_rfn (lty_rt lt), place_rfn_interp_owned r r' ∗ ▷?wl |={lftE}=>
          ∃ (l' : loc) (ly' : layout), l ↦ l' ∗
          ⌜syn_type_has_layout (lty_st lt) ly'⌝ ∗
          ⌜l' `has_layout_loc` ly'⌝ ∗
          freeable_nz l' ly'.(ly_size) 1 HeapAlloc ∗
          lty_own_pre core lt (Owned true) π r' l'
      | Uniq κ γ =>
          have_creds ∗
          place_rfn_interp_mut r γ ∗
          |={lftE}=> &pin{κ}
              [∃ (r' : place_rfn (lty_rt lt)),
                gvar_auth γ r' ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (l' : loc) (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (lty_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                (freeable_nz l' ly'.(ly_size) 1 HeapAlloc) ∗
                lty_own_pre true lt (Owned true) π r' l'
              ]
              (∃ (r' : place_rfn (lty_rt lt)),
                gvar_auth γ r' ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (l' : loc) (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (lty_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                (freeable_nz l' ly'.(ly_size) 1 HeapAlloc) ∗
                lty_own_pre core lt (Owned true) π r' l')
      | Shared κ =>
        (∃ r', place_rfn_interp_shared r r' ∗
          □ |={lftE}=> ∃ li : loc,
            &frac{κ}(λ q', l ↦{q'} li) ∗
            ▷ lty_own_pre core lt (Shared κ) π r' li)%I
      end)%I;

    lty_own_pre core (OwnedPtrLty lt ls) k π r l :=
      (** OwnedPtr *)
      (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          (* the placement of the pointsto below the later let's us get the unfoldings equation without timelessness *)
          ∃ (r' : place_rfn (lty_rt lt)) (l' : loc), place_rfn_interp_owned r (r', l') ∗ ▷?wl |={lftE}=>
          ∃ (ly' : layout), l ↦ l' ∗
          ⌜syn_type_has_layout (lty_st lt) ly'⌝ ∗
          ⌜l' `has_layout_loc` ly'⌝ ∗
          lty_own_pre core lt (Owned ls) π r' l'
      | Uniq κ γ =>
          have_creds ∗
          place_rfn_interp_mut r γ ∗
          |={lftE}=> &pin{κ}
              [∃ (r' : place_rfn (lty_rt lt)) (l' : loc),
                gvar_auth γ (r', l') ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (lty_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                lty_own_pre true lt (Owned ls) π r' l'
              ]
              (∃ (r' : place_rfn (lty_rt lt)) (l' : loc),
                gvar_auth γ (r', l') ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (lty_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                lty_own_pre core lt (Owned ls) π r' l')
      | Shared κ =>
        (∃ r' li, place_rfn_interp_shared r (r', li) ∗
          □ |={lftE}=>
            &frac{κ}(λ q', l ↦{q'} li) ∗
            ▷ lty_own_pre core lt (Shared κ) π r' li)%I
      end)%I;

    lty_own_pre core (MutLty lt κ) k π r l :=
      (** Mut *)
      (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
       loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          (* it's fine to existentially quantify here over the gvar_obs, since
            the outer can actually tell us about it. Keep in mind that the gvar here can actually
            change if we write under nested places. *)
          ∃ (γ : gname) (r' : place_rfn (lty_rt lt)) ,
          place_rfn_interp_owned r (r', γ) ∗
          (* TODO layout requirements on l' here? *)
          ▷?wl |={lftE}=> ∃ l' : loc , l ↦ l' ∗ (lty_own_pre core lt (Uniq κ γ) π r' l')
      | Uniq κ' γ' =>
            have_creds ∗
            place_rfn_interp_mut r γ' ∗
            |={lftE}=> &pin{κ'}
              [∃ (r' : (place_rfn (lty_rt lt)) * gname),
                gvar_auth γ' r' ∗
                (* update here to be compatible with ofty *)
                |={lftE}=>
                ∃ (l' : loc), l ↦ l' ∗
                lty_own_pre true lt (Uniq κ r'.2) π r'.1 l'
              ]
              (∃ (r' : (place_rfn (lty_rt lt)) * gname),
                gvar_auth γ' r' ∗
                (* update here to be compatible with ofty *)
                |={lftE}=>
                ∃ (l' : loc), l ↦ l' ∗
                lty_own_pre core lt (Uniq κ r'.2) π r'.1 l')
      | Shared κ' =>
        (∃ r' γ, place_rfn_interp_shared r (r', γ) ∗
        (* the update is also over the fractional borrow to deal with timelessness *)
        □ |={lftE}=> ∃ (li : loc),
          &frac{κ'}(λ q', l ↦{q'} li) ∗
          (* later is for contractiveness, the update for timelessness *)
          ▷ lty_own_pre core lt (Shared (κ⊓κ')) π r' li)%I
      end)%I;

    lty_own_pre core (ShrLty lt κ) k π r l :=
      (** Shr *)
      (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
         loc_in_bounds l 0 ly.(ly_size) ∗
        match k with
        | Owned wl =>
            maybe_creds wl ∗
            ∃ (r' : place_rfn (lty_rt lt)), place_rfn_interp_owned r r' ∗
            ▷?wl |={lftE}=> ∃ (l' : loc), l ↦ l' ∗
            lty_own_pre core lt (Shared κ) π r' l'
        | Uniq κ' γ' =>
            have_creds ∗
            place_rfn_interp_mut r γ' ∗
            |={lftE}=> &pin{κ'}
              [∃ (r' : place_rfn (lty_rt lt)), gvar_auth γ' r' ∗
                |={lftE}=> ∃ (l' : loc), l ↦ l' ∗ lty_own_pre true lt (Shared κ) π r' l']
              (∃ (r' : place_rfn (lty_rt lt)), gvar_auth γ' r' ∗
                |={lftE}=> ∃ (l' : loc), l ↦ l' ∗ lty_own_pre core lt (Shared κ) π r' l')
        | Shared κ' =>
            ∃ (r' : place_rfn (lty_rt lt)),
            place_rfn_interp_shared r r' ∗
            (* the update is also over the fractional borrow to deal with timelessness *)
            □ |={lftE}=> ∃ (l' : loc),
            &frac{κ'} (λ q, l ↦{q} l') ∗
            (* no intersection here, as we also don't do that for the type interpretation *)
            ▷ lty_own_pre core lt (Shared κ) π r' l'
        end)%I;

    lty_own_pre core (StructLty lts sls) k π r l :=
      (** Struct *)
      ∃ sl : struct_layout,
      ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜length (sls_fields sls) = length lts⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗
      match k with
      | Owned wl =>
          (* We change the interpretation to Owned false and interpret the later here, because we cannot push down/split up the credits for each of the components *)
          maybe_creds wl ∗
          ∃ r' : plist (λ lt, place_rfn (lty_rt lt)) lts, place_rfn_interp_owned r r' ∗
          ▷?wl |={lftE}=>
          big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))
            (λ i ty HP,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
              lty_own_pre core (projT1 ty) (Owned false) π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))
      | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        (* We change the ownership to Owned false, because we can't push the borrow down in this formulation of products.
          The cost of this is that we need an update here (to get congruence rules for ltype_eq),
          which propagates to all the other Uniq cases of other ltypes. *)
        |={lftE}=> &pin{κ}
          [∃ (r' : plist (λ lt, place_rfn (lty_rt lt)) lts),
            gvar_auth γ r' ∗ |={lftE}=>
            big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))
              (λ i ty HP,
                  ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
                  lty_own_pre true (projT1 ty) (Owned false) π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))
          ]
          (∃ (r' : plist (λ lt, place_rfn (lty_rt lt)) lts),
            gvar_auth γ r' ∗ |={lftE}=>
            big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))
              (λ i ty HP,
                ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
                lty_own_pre core (projT1 ty) (Owned false) π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))
          )
      | Shared κ =>
          (∃ r', place_rfn_interp_shared r r' ∗
            (* update needed to make the unfolding equation work *)
            □ |={lftE}=>
              big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))
                (λ i ty HP,
                  ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
                  lty_own_pre core (projT1 ty) (Shared κ) π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))))
      end;

    lty_own_pre core (@ArrayLty rt def len lts) k π r l :=
      (** ArrayLty *)
      ∃ ly,
        ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt isize_t)%Z⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly.(ly_size) * len) ∗
        (*⌜Forall (λ '(i, lts), i < len) lts⌝ ∗*)
      match k with
      | Owned wl =>
        maybe_creds wl ∗
        ∃ r' : list (place_rfn rt), place_rfn_interp_owned r r' ∗
        ▷?wl |={lftE}=>
        (⌜length r' = len⌝ ∗
        big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
          (λ i ty HP,
            ∃ (Heq : lty_rt ty.1 = rt),
              ⌜lty_st ty.1 = ty_syn_type def⌝ ∗
              lty_own_pre core ty.1 (Owned false) π (rew <-Heq in ty.2) (offset_loc l ly i)))
      | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        |={lftE}=> &pin{κ}
          [∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
              (λ i ty HP,
                ∃ (Heq : lty_rt ty.1 = rt),
                  ⌜lty_st ty.1 = ty_syn_type def⌝ ∗
                  lty_own_pre true ty.1 (Owned false) π (rew <-Heq in ty.2) (offset_loc l ly i)))]
          (∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
              (λ i ty HP,
                ∃ (Heq : lty_rt ty.1 = rt),
                  ⌜lty_st ty.1 = ty_syn_type def⌝ ∗
                  lty_own_pre core ty.1 (Owned false) π (rew <-Heq in ty.2) (offset_loc l ly i))))

      | Shared κ =>
          ∃ r', place_rfn_interp_shared r r' ∗
            □ |={lftE}=> ⌜length r' = len⌝ ∗
            big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
              (λ i ty HP,
                ∃ (Heq : lty_rt ty.1 = rt),
                  ⌜lty_st ty.1 = ty_syn_type def⌝ ∗
                  lty_own_pre core ty.1 (Shared κ) π (rew <-Heq in ty.2) (offset_loc l ly i))
      end;

    lty_own_pre core (@EnumLty rt en variant lte) k π r l :=
    (** EnumLty *)
      ∃ el rty,
      ⌜enum_layout_spec_has_layout en.(enum_els) el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(ly_size) ∗
      (* require all the tag info to be coherent -- in particular the refinement type *)
      ⌜enum_tag_ty en variant = Some rty⌝ ∗
      ⌜lty_rt lte = projT1 rty⌝ ∗
      match k with
      | Owned wl =>
        maybe_creds wl ∗
        ∃ r' : rt, place_rfn_interp_owned r r' ∗
        ▷?wl |={lftE}=>(
        ⌜enum_tag en r' = variant⌝ ∗
        ∃ (Heq : lty_rt lte = enum_variant_rt en r'),
        (* ownership of the discriminant *)
        lty_of_ty_own (int en.(enum_els).(els_tag_it)) (Owned false) π (PlaceIn (enum_lookup_tag en r')) (l atst{sls_of_els en.(enum_els)}ₗ "discriminant") ∗
        (* ownership of the data *)
        lty_own_pre core lte (Owned false) π (rew <-[place_rfn]Heq in (PlaceIn (enum_variant_rfn en r'))) (l atst{sls_of_els en.(enum_els)}ₗ "data") ∗
        (* ownership of the remaining padding after the data *)
        (∃ v, ((l atst{sls_of_els en.(enum_els)}ₗ "data") +ₗ (size_of_st (lty_st lte))) ↦ v ∗ ⌜v `has_layout_val` ly_offset (els_data_ly en.(enum_els)) (size_of_st (lty_st lte))⌝) ∗
        (* ownership of the padding fields of the sl *)
        ([∗ list] i ↦ mly ∈ pad_struct el.(sl_members) [None; None] (λ ly, Some ly),
          from_option (λ ly, lty_of_ty_own (uninit (UntypedSynType ly)) (Owned false) π (PlaceIn ()) (l +ₗ Z.of_nat (offset_of_idx el.(sl_members) i))) True mly)
        )
      | _ =>
          (* TODO *)
          False
      end;
    lty_own_pre core (@OpenedLty rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost) k π r l :=
      (** OpenedLty *)
      ∃ ly, ⌜use_layout_alg (lty_st lt_cur) = Some ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly_size ly) ∗
        ⌜lty_st lt_cur = lty_st lt_inner⌝ ∗
        ⌜lty_st lt_inner = lty_st lt_full⌝ ∗

      match k with
      | Owned wl =>
          lty_own_pre false lt_cur (Owned false) π r l ∗
          logical_step lftE
          (∃ (Heq_inner : rt_inner = lty_rt lt_inner) (Heq_full : rt_full = lty_rt lt_full),
            (* once we have restored to [lt_inner], we can fold to [lt_full] again *)
            ∀ (r : rt_inner) (r' : rt_full) (κs : list lft),
              (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
              (* directly hand out Cpost. We don't need to wait to get tokens from closing borrows etc. *)
              Cpost r r' ∗
              (lft_dead_list κs -∗
               lty_own_pre false lt_inner (Owned false) π (PlaceIn (rew [id] Heq_inner in r)) l ={lftE}=∗
               lty_own_pre true lt_full (Owned wl) π (PlaceIn (rew [id] Heq_full in r')) l
              ))
      | Uniq κ γ =>
        lty_own_pre false lt_cur (Owned false) π r l ∗
        (* Note: we are not interpreting γ here - it is currently completely unconstrained, and the
           ownership of the ghost variable fragments lies with the closing viewshift *)

        (* Main points important for this VS:
            - we close the pinned borrow again, so that we can get lifetime tokens back in Cpost
            - we cannot restore lt_full directly, because we want to be able to execute this while subplaces are still borrowed;
              instead we require that we can shift to lt_inner once [κ] is dead (has a flavor of [imp_unblockable]). *)
        (* to prove when unfolding in the first place:
            if I assume Cpre r r' and lty_own_pre true lt_inner(Owned false) π r l, then I can restore lt_full again and produce Cpost r r' *)
        logical_step lftE
        (∃ (Heq : rt_inner = lty_rt lt_inner) (Heq_full : rt_full = lty_rt lt_full),
          (* we will execute this VS when closing the invariant, after having already stratified [lt_cur].
             At that point, we will know [lt_cur] is unblockable to [lt_inner] after some set of lifetimes [κs] is dead *)
          ∀ (own_lt_cur' : thread_id → rt_inner → loc → iProp Σ) (κs : list lft)
            (r : rt_inner) (r' : rt_full),
            (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
            ([∗ list] κ' ∈ κs, κ' ⊑ κ) -∗
            own_lt_cur' π r l -∗

            (* the ownership of [lt_cur'] needs to be shiftable to the _core_ of [lt_inner];
              this is required for closing the borrow and for proving that it can be unblocked to lt_full
                (which is needed for showing the shift to Coreable) *)
            (□ (lft_dead_list κs -∗ own_lt_cur' π r l ={lftE}=∗
              lty_own_pre true lt_inner (Owned false) π (rew Heq in PlaceIn r) l)) ={lftE}=∗

            Cpost r r' ∗
            gvar_obs γ (rew [id] Heq_full in r') ∗
            (lft_dead_list κs -∗ gvar_obs γ (rew [id] Heq_full in r') ={lftE}=∗
              lty_own_pre true lt_full (Uniq κ γ) π (rew Heq_full in PlaceIn r') l)
        )

      | Shared κ =>
        (* TODO: how do we deal with fractional ownership of the pointsto we get from ofty?
           And how does it interact with the types we want to unfold in practice?
        *)
        (*lty_own_pre false lt_cur (Shared κ) π r l*)
        False
      end;
    lty_own_pre core (@CoreableLty κs lt_full) k π r l :=
      (if core then
        lty_own_pre true lt_full k π r l
      else
        ∃ ly, ⌜syn_type_has_layout (lty_st lt_full) ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly_size ly) ∗
        match k with
        | Owned wl =>
            lft_dead_list κs ={lftE}=∗ lty_own_pre true lt_full (Owned wl) π r l
        | Uniq κ' γ =>
            place_rfn_interp_mut r γ ∗
            (lft_dead_list κs -∗ place_rfn_interp_mut r γ ={lftE}=∗ lty_own_pre true lt_full (Uniq κ' γ) π r l)
        | Shared κ =>
            (*False*)
            lty_own_pre true lt_full (Shared κ) π r l
        end)%I;
    lty_own_pre core (@ShadowedLty rt_cur lt_cur r_cur lt_full) k π r l :=
      (if core then lty_own_pre true lt_full k π r l
       else
        ∃ (Heq_cur : rt_cur = lty_rt lt_cur),
        ⌜lty_st lt_cur = lty_st lt_full⌝ ∗
        lty_own_pre core lt_cur k π ((rew Heq_cur in r_cur)) l ∗
        lty_own_pre core lt_full k π r l)%I
  .
  Solve Obligations with first [unfold lty_size_rel, ltof; simpl; lia | intros; eauto using struct_lts_size_decreasing, array_lts_size_decreasing].
  Definition lty_own := @lty_own_pre false.
  Definition lty_own_core := @lty_own_pre true.

  (** Basic laws of ltypes *)

  Lemma lty_own_pre_shr_pers core (lt : lty) κ π r l :
    Persistent (lty_own_pre core lt (Shared κ) π r l).
  Proof.
    induction lt using lty_induction in κ, π, r, l, core |-*; simp lty_own_pre;
    destruct core; simpl; try done; apply _.
  Qed.
  Global Instance lty_own_shr_pers (lt : lty) κ π r l :
    (*TCDone (match lt with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (lty_own lt (Shared κ) π r l).
  Proof. apply lty_own_pre_shr_pers. Qed.
  Global Instance lty_own_core_shr_pers (lt : lty) κ π r l :
    (*TCDone (match lt with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (lty_own_core lt (Shared κ) π r l).
  Proof. apply lty_own_pre_shr_pers. Qed.

  Lemma lty_core_idemp (lt : lty) :
    lty_core (lty_core lt) = lty_core lt.
  Proof.
    induction lt as [ | | | | | | | | lts IH ? | rt def len lts IH | | | | ] using lty_induction;
    [simpl; f_equiv.. | | ]; [solve[eauto].. | | | | | | ].
    - done.
    - induction lts as [ | lt lts IH']; first done.
      simpl. rewrite IH; first last. { apply elem_of_cons; eauto. }
      f_equiv. apply IH'.
      intros. apply IH. apply elem_of_cons; eauto.
    - induction lts as [ | [j lt] lts IH2]; first done.
      simpl. erewrite IH; first last. { apply elem_of_cons; eauto. }
      f_equiv. apply IH2.
      intros. eapply (IH (i)). apply elem_of_cons; eauto.
    - done.
    - done.
    - done.
  Qed.

  Lemma lty_own_has_layout (lt : lty) k π r l :
    lty_own lt k π r l -∗ ∃ ly : layout, ⌜syn_type_has_layout (lty_st lt) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝.
  Proof.
    iIntros "Hown". rewrite /lty_own.
    iInduction lt as [ | | | | | | | | | rt def len lts IH | | ?? lt_cur lt_inner lt_full Cpre Cpost | | ] "IH" using lty_induction forall (k); simp lty_own_pre.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - destruct k; [ | done..].
      iDestruct "Hown" as "(%ly & ? & ? & ? & ? & ?)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%sl & % & % & % & _)".
      iExists sl. simpl. iPureIntro. split; last done. by apply use_struct_layout_alg_Some_inv.
    - iDestruct "Hown" as "(%ly & % & %Hsz & % & _)".
      iExists (mk_array_layout ly len). iSplitR; last done.
      iPureIntro. simpl.
      eapply syn_type_has_layout_array; done.
    - iDestruct "Hown" as (el [rte tye]) "(%Hen & %Hly & Hown)".
      iExists _. iL.
      iPureIntro. by eapply use_enum_layout_alg_Some_inv in Hen.
    - simpl. iDestruct "Hown" as "(%ly & ? & ? & ? & ? & _)".
      eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)". eauto.
    - iDestruct ("Hown") as (->) "(%Hst & Ha & Hb)".
      simpl. rewrite -Hst. iApply ("IH" with "Ha").
  Qed.

  Lemma lty_own_loc_in_bounds (lt : lty) k π r l ly :
    syn_type_has_layout (lty_st lt) ly →
    lty_own lt k π r l -∗ loc_in_bounds l 0 ly.(ly_size).
  Proof.
    iIntros (Ha) "Hown". rewrite /lty_own.
    iInduction lt as [ | | | | | | | | | | | ? ??? | | ] "IH" using lty_induction forall (k); simp lty_own_pre.
    - iDestruct "Hown" as "(%ly' & %Halg' & ? & ? & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - destruct k; [ | done..]. iDestruct "Hown" as "(%ly' & % & ? & ? & ? & ?)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%sl & %Hsl & _ & _ & ? & _)".
      apply use_struct_layout_alg_Some_inv in Hsl.
      have ?: layout_of sl = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & %Halg & _ & _ & ? & _)".
      apply syn_type_has_layout_array_inv in Ha as (ly0 & Halg' & -> & ?).
      assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
      done.
    - (* enum *)
      iDestruct "Hown" as (el [rte tye]) "(%Hen & %Hly & Hlb & _)".
      eapply use_enum_layout_alg_Some_inv in Hen.
      have ?: layout_of el = ly by eapply syn_type_has_layout_inj.
      subst. done.
    - iDestruct "Hown" as "(%ly' & %Halg & ? & ? & ? & ? & _)".
      simpl in *. assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      iFrame.
    - iDestruct "Hown" as "(%ly' & %Halg & ? & ? & _)".
      simpl in *. assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      iFrame.
    - iDestruct "Hown" as (->) "(%Hst & Ha & Hb)".
      simpl in Ha. rewrite -Hst in Ha.
      iApply "IH"; done.
  Qed.

  Lemma lty_own_Owned_true_false (lt : lty) π r l :
    (match lt with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end) →
    lty_own lt (Owned true) π r l -∗
    have_creds ∗ ▷ lty_own lt (Owned false) π r l.
  Proof.
    iIntros (?) "Hown". rewrite /lty_own.
    destruct lt as [ | | | | | | | | | | | ? ??? | | ]; simp lty_own_pre.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & ? & Hcred)". eauto with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & % & ? & ? & ? & Hcred)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & Hcred & % & ? & Hl)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & Hcred)". eauto with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & Hcred & % & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? &? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & ? & ? & ? & ? & % & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & ? & ? & ? & ? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & ? & ? & ? & ? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & % & ? & ? & ? & ? & ? & ? & % & ? & ?)". eauto 8 with iFrame.
    - done.
    - done.
    - (* this will definitely be a problem also for the other property, because we need two sets of credits
        Maybe change the interpretation to have Owned false for the shadow, always? *)
      done.
  Qed.
  Lemma lty_own_Owned_false_true (lt : lty) π r l :
    (match lt with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end) →
    (lty_own lt (Owned false) π r l) -∗
    have_creds -∗
    lty_own lt (Owned true) π r l.
  Proof.
    iIntros (?) "Hown Hcred". rewrite /lty_own.
    destruct lt as [ | | | | | | | | | | | ? ??? | | ]; simp lty_own_pre.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & ? & _)". iExists _. eauto with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & % & ? & ? & ? & _)". iExists _. eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & _ & % & ? & Hl)". iExists _. eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & _)". iExists _. eauto with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & _ & % & % & ? & ?)". iExists _. eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? & ? & ? & % & ? & ?)". iExists _. eauto 8 with iFrame.
    - iDestruct "Hown" as "(%ly & ? & ? &? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & ? & ? & ? & ? & % & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & ? & ? & ? & ? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & ? & ? & ? & ? & ? & % & ? & ?)". eauto 8 with iFrame.
    - iDestruct "Hown" as "(% & % & h1 & h2 & h3 & h4 & h5 & _ & % & Hrfn & ?)". eauto 8 with iFrame.
    - done.
    - done.
    - (* this will definitely be a problem also for the other property, because we need two sets of credits
        Maybe change the interpretation to have Owned false for the shadow, always? *)
      done.
  Qed.

  Import EqNotations.
  Definition transport_rfn {rt1 rt2} (Heq : rt1 = rt2) (r1 : place_rfn rt1) : place_rfn rt2 :=
    rew [place_rfn] Heq in r1.
  Arguments transport_rfn : simpl never.

  Lemma lty_own_pre_rfn_eq (lt : lty) π (r1 r2 : place_rfn (lty_rt lt)) core (b : bor_kind) (l : loc) :
    r1 = r2 → lty_own_pre core lt b π r1 l -∗ lty_own_pre core lt b π r2 l.
  Proof.
    intros ->. auto.
  Qed.
  Lemma lty_own_pre_rfn_eq' (lt : lty) π (r1 r2 : place_rfn (lty_rt lt)) core (b : bor_kind) (l : loc) :
    r1 = r2 → lty_own_pre core lt b π r1 l ⊣⊢ lty_own_pre core lt b π r2 l.
  Proof.
    intros ->. auto.
  Qed.

  Lemma lty_core_plist_rt_eq lts :
    plist (λ lt, place_rfn (lty_rt lt)) (fmap lty_core lts) = plist (λ lt, place_rfn (lty_rt lt)) lts.
  Proof.
    induction lts as [ | lt lts IH]; simpl; first done.
    rewrite /plist. rewrite lty_core_rt_eq. f_equiv. apply IH.
  Qed.

  Local Definition pzipl_core_map_fun := λ (p : sigT (λ lt, place_rfn (lty_rt lt))),
    (existT (lty_core (projT1 p)) (rew <-[place_rfn] (lty_core_rt_eq (projT1 p)) in (projT2 p)) :
    sigT (λ lt, place_rfn (lty_rt lt))).
  Local Lemma pzipl_core_map_eq (lts : list lty) (r : plist (λ lt, place_rfn (lty_rt lt)) (map lty_core lts)) (Heq : plist (λ lt : lty, place_rfn (lty_rt lt)) (map lty_core lts) =
      plist (λ lt : lty, place_rfn (lty_rt lt)) lts) :
    pzipl (fmap lty_core lts) r = fmap pzipl_core_map_fun (pzipl lts (rew [id] Heq in r)).
  Proof.
    rewrite (pzipl_fmap_eqcast lty_core pzipl_core_map_fun _ _ lty_core_plist_rt_eq).
    - rewrite (UIP_t _ _ _ (lty_core_plist_rt_eq lts) Heq). done.
    - intros. rewrite lty_core_rt_eq. done.
    - intros lt ? Heq1. unfold pzipl_core_map_fun. f_equiv; simpl.
      generalize (lty_core_rt_eq lt) as Heq'.
      move : Heq1.
      generalize (lty_rt lt) => T.
      intros Heq1 <-. rewrite (UIP_refl _ _ Heq1). done.
  Qed.
  (* Follows the same structure as the proof for the struct ltype unfolding.
     Essentially the relevant part of the proof of [lty_own_core_core] below. *)
  Local Lemma StructLty_own_core_core_lift (sl : struct_layout) (lts : list lty) (r' : plist (λ lt, place_rfn (lty_rt lt)) (map lty_core lts)) (Heq : plist (λ lt : lty, place_rfn (lty_rt lt)) (map lty_core lts) = plist (λ lt : lty, place_rfn (lty_rt lt)) lts) π l k :
    (∀ lt : lty, lt ∈ lts → ∀ k π r (Heq : lty_rt (lty_core lt) = lty_rt lt) l, lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π (transport_rfn Heq r) l) →
    ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl (map lty_core lts) r') (λ ly : layout, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre true (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i)) ⊣⊢
    [∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl lts (rew [id] Heq in r')) (λ ly : layout, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre true (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i).
  Proof.
    intros IH.
    rewrite pzipl_core_map_eq.
    set (ps' := (λ ly : layout, pzipl_core_map_fun (existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))).
    rewrite (pad_struct_ext _ _ _ ps'); first last.
    { intros. unfold ps', pzipl_core_map_fun. simpl. f_equiv.
      generalize (lty_core_rt_eq (UninitLty (UntypedSynType ly))) => Heq2.
      rewrite (UIP_refl _ _ Heq2). done. }
    rewrite pad_struct_fmap.
    rewrite big_sepL_fmap.
    iApply big_sepL_proper.
    iIntros (? [lt r0] Hlook).
    specialize (lty_core_rt_eq lt) as Heq2.
    apply pad_struct_lookup_Some_1 in Hlook as (n & ly & ? & [[_ Hlook] | [_ Huninit]]).
    + eapply pzipl_lookup_inv in Hlook.
      f_equiv => Hly. f_equiv. f_equiv.
      { simpl. f_equiv. f_equiv. rewrite lty_core_syn_type_eq. done. }
      unshelve rewrite IH; first last. { by eapply elem_of_list_lookup_2. }
      2: apply Heq2.
      iApply lty_own_pre_rfn_eq'.
      clear. simpl.
      generalize (lty_core_rt_eq lt) as Heq3.
      move : Heq2 r0. generalize (lty_rt lt) => T.
      intros <- ? Heq3. rewrite (UIP_refl _ _ Heq3) //.
    + injection Huninit as -> ->.
      simpl. clear. f_equiv => Hly. f_equiv. f_equiv.
      iApply lty_own_pre_rfn_eq'.
      generalize (lty_core_rt_eq (UninitLty (UntypedSynType ly))) => Heq.
      rewrite (UIP_refl _ _ Heq). done.
  Qed.


  Local Lemma ArrayLty_own_core_core_lift {rt} st ly (lts : list lty) (r' : list (place_rfn rt)) π l k :
    (∀ lt : lty, lt ∈ lts → ∀ k π r (Heq : lty_rt (lty_core lt) = lty_rt lt) l, lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π (transport_rfn Heq r) l) →
    ([∗ list] i ↦ ty ∈ zip (fmap lty_core lts) r', ∃ Heq : lty_rt ty.1 = rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre true ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)) ⊣⊢
    ([∗ list] i ↦ ty ∈ zip lts r', ∃ Heq : lty_rt ty.1 = rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre true ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)).
  Proof.
    intros IH.
    rewrite zip_fmap_l big_sepL_fmap.
    apply big_sepL_proper.
    intros ? [lt r] Hlook.
    apply lookup_zip in Hlook as [Hlook1 Hlook2].
    assert (lty_rt (lty_core lt) = lty_rt lt) as Heq3. { rewrite lty_core_rt_eq. done. }
    simpl in *. iSplit.
    - iIntros "(%Heq & %Hst & Hb)". assert (Heq2 : lty_rt lt = rt). { rewrite -lty_core_rt_eq. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq in Hst. iSplitR; first done.
      apply elem_of_list_lookup_2 in Hlook1.
      unshelve rewrite IH; [done | | done].
      clear. subst rt. cbn.
      move: Heq2 Heq3 r. intros <-. intros Heq. rewrite (UIP_refl _ _ Heq). eauto.
    - iIntros "(%Heq & %Hst & Hb)". assert (Heq2 : lty_rt (lty_core lt) = rt).
      { rewrite lty_core_rt_eq. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq. iSplitR; first done.
      apply elem_of_list_lookup_2 in Hlook1. unshelve rewrite IH; [done | | done].
      clear. subst rt. cbn.
      move: Heq2 Heq3 r. intros ->. intros Heq. rewrite (UIP_refl _ _ Heq). eauto.
  Qed.

  Lemma OfTyLty_core_id {rt} (ty : type rt) :
    lty_core (OfTyLty ty) = OfTyLty ty.
  Proof. done. Qed.

  Lemma lty_own_core_core (lt : lty) k π r r' Heq l :
    r' = (transport_rfn Heq r) →
    lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π r' l.
  Proof.
    intros ->. rewrite /lty_own_core.
    induction lt as [ | | | | lt IH κ | lt IH κ | lt IH | lt ls IH | lts IH sls | rt def len lts IH | rt en variant lt IH | | | ] using lty_induction in k, π, r, l, Heq |-*; simpl in *.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - rewrite (UIP_refl _ _ Heq). done.
    - rewrite (UIP_refl _ _ Heq). done.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      move: r Heq Heq2 IH.
      generalize (lty_core lt) as lt' => lt'.
      intros r Heq Heq2 IH.
      f_equiv.
      all: unshelve setoid_rewrite IH; [done.. | ].
      all: revert r Heq Heq2.
      all: generalize (lty_rt lt') => ?.
      all: intros r ? ->.
      all: solve [ done | rewrite (UIP_refl _ _ Heq) //].
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      move: r Heq Heq2 IH.
      generalize (lty_core lt) as lt' => lt'.
      intros r Heq Heq2 IH.
      f_equiv.
      all: unshelve setoid_rewrite IH; [done.. | ].
      all: revert r Heq Heq2.
      all: generalize (lty_rt lt') => ?.
      all: intros r ? ->.
      all: solve [ done | rewrite (UIP_refl _ _ Heq) //].
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_syn_type_eq lt) as Hst.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2 Hst.
      move: r Heq Heq2 IH Hst.
      generalize (lty_core lt) as lt' => lt'.
      intros r Heq Heq2 IH Hst.
      f_equiv.
      all: unshelve setoid_rewrite IH; [done.. | ].
      all: revert r Heq Heq2.
      all: generalize (lty_rt lt') => ?.
      all: intros r ? ->.
      all: try rewrite Hst.
      all: first [ done | rewrite (UIP_refl _ _ Heq) // | idtac].

    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_syn_type_eq lt) as Hst.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2 Hst.
      move: r Heq Heq2 IH Hst.
      generalize (lty_core lt) as lt' => lt'.
      intros r Heq Heq2 IH Hst.
      f_equiv.
      all: unshelve setoid_rewrite IH; [done.. | ].
      all: revert r Heq Heq2.
      all: generalize (lty_rt lt') => ?.
      all: intros r ? ->.
      all: try rewrite Hst.
      all: first [ done | rewrite (UIP_refl _ _ Heq) // | idtac].
    - simp lty_own_pre. fold lty_rt.
      do 5 f_equiv.
      { rewrite map_length. done. }
      do 2 f_equiv.
      all: setoid_rewrite big_sepL_P_eq.
      all: simpl.
      3: do 2 f_equiv;
        [move : r; simpl; rewrite <-Heq; done | do 2 f_equiv].
      1: f_equiv.
      all: iSplit.
      all: iIntros "(%r' & Hrfn & Hb)".
      all: first [iExists (rew [id] Heq in r') | iExists (rew <-[id] Heq in r')].
      all: iSplitL "Hrfn";
        [ clear; try move: r'; try move: r; rewrite <-Heq; done| ].
      all: unshelve rewrite StructLty_own_core_core_lift;
        [ apply Heq| | done].
      all: rewrite ?rew_invert'; done.
    - simp lty_own_pre.
      do 6 f_equiv.
      (*{ rewrite Forall_fmap. simpl.*)
        (*iPureIntro. eapply Forall_iff. intros []; done. }*)
      fold lty_rt. simpl.
      rewrite (UIP_refl _ _ Heq). clear Heq.
      f_equiv.
      all: repeat f_equiv; try done.
      all: rewrite !big_sepL_P_eq.
      all: rewrite -OfTyLty_core_id.
      all: rewrite interpret_iml_fmap.
      all: eapply ArrayLty_own_core_core_lift.
      all: intros ? [-> | []]%elem_of_interpret_iml_inv; simpl.
      all: intros ??? Heq; try rewrite (UIP_refl _ _ Heq); eauto.
    - (* enum *)
      simp lty_own_pre.
      do 6 f_equiv.
      f_equiv. f_equiv. f_equiv.
      { rewrite lty_core_rt_eq. done. }
      fold lty_rt. simpl.
      rewrite (UIP_refl _ _ Heq). clear Heq.
      f_equiv.
      all: repeat f_equiv; try done.
      rewrite lty_core_syn_type_eq.
      iSplit.
      + iIntros "(%Heq & Ha & Hb & ?)".
        match goal with a : rt |- _ => rename a into r1 end.
        assert (Heq' : lty_rt lt = enum_variant_rt en r1).
        { rewrite -Heq -lty_core_rt_eq. done. }
        iExists Heq'. iFrame.
        unshelve rewrite IH. { apply lty_core_rt_eq. }
        iApply (lty_own_pre_rfn_eq with "Hb").
        (* TODO: I think we could develop a general tactic for these kinds of things by principled application of these lemmas *)
        rewrite /transport_rfn.
        rewrite rew_compose.
        apply rew_swap.
        rewrite rew_compose.
        apply elim_id_cast_l.
      + iIntros "(%Heq & Ha & Hb & ?)".
        match goal with a : rt |- _ => rename a into r1 end.
        assert (Heq' : lty_rt (lty_core lt) = enum_variant_rt en r1).
        { rewrite -Heq. apply lty_core_rt_eq. }
        iExists Heq'. iFrame.
        unshelve rewrite IH. { apply lty_core_rt_eq. }
        iApply (lty_own_pre_rfn_eq with "Hb").
        rewrite /transport_rfn.
        rewrite rew_compose.
        apply rew_swap'.
        rewrite rew_compose.
        apply elim_id_cast_r.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - simp lty_own_pre.
    - simp lty_own_pre.
  Qed.
  Lemma lty_own_core_core' (lt : lty) k π r Heq l :
    lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π (transport_rfn Heq r) l.
  Proof.
    rewrite lty_own_core_core; first done. done.
  Qed.

  Local Lemma StructLty_own_core_equiv_lift (sl : struct_layout) (lts : list lty) r (r' : plist (λ lt, place_rfn (lty_rt lt)) (fmap lty_core lts)) (Heq : plist (λ lt : lty, place_rfn (lty_rt lt)) (fmap lty_core lts) = plist (λ lt : lty, place_rfn (lty_rt lt)) lts) π l k (core : bool) :
    (∀ (lt : lty), lt ∈ lts → ∀ k π r (Heq :  lty_rt lt = lty_rt (lty_core lt)) l, lty_own_pre true lt k π r l ≡ lty_own_pre core (lty_core lt) k π (transport_rfn Heq r) l) →
    r = rew [id] Heq in r' →
    ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl lts r) (λ ly : layout, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre true (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i)) ⊣⊢
    [∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl (fmap lty_core lts) r') (λ ly : layout, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre core (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i).
  Proof.
    intros IH.
    rewrite pzipl_core_map_eq.
    set (ps' := (λ ly : layout, pzipl_core_map_fun (existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))).
    rewrite (pad_struct_ext _ (pzipl_core_map_fun <$> _) _ ps'); first last.
    { intros. unfold ps', pzipl_core_map_fun. simpl. f_equiv.
      generalize (lty_core_rt_eq (UninitLty (UntypedSynType ly))) => Heq2.
      rewrite (UIP_refl _ _ Heq2). done. }
    intros ->.
    rewrite pad_struct_fmap.
    rewrite big_sepL_fmap.
    iApply big_sepL_proper.
    iIntros (? [lt r0] Hlook).
    specialize (lty_core_rt_eq lt) as Heq2.
    apply pad_struct_lookup_Some_1 in Hlook as (n & ly & ? & [[_ Hlook] | [_ Huninit]]).
    + eapply pzipl_lookup_inv in Hlook.
      f_equiv => ly'. f_equiv. f_equiv. { simpl. f_equiv. f_equiv. rewrite lty_core_syn_type_eq //. }
      unshelve rewrite IH; first last. { by eapply elem_of_list_lookup_2. }
      2: { simpl. apply (eq_sym Heq2). }
      simpl.
      apply elem_of_list_lookup_2 in Hlook.
      rewrite -!IH; done.
    + injection Huninit as -> ->.
      simpl. clear.
      generalize (lty_core_rt_eq (UninitLty (UntypedSynType ly))) => Heq.
      rewrite (UIP_refl _ _ Heq).
      do 4 f_equiv.
      destruct core.
      * by iApply lty_own_pre_rfn_eq'.
      * simp lty_own_pre; done.
  Qed.

  Local Lemma ArrayLty_own_core_equiv_lift {rt} core st ly (lts : list lty) (r' : list (place_rfn rt)) π l k :
    (∀ lt : lty, lt ∈ lts → ∀ k π r (Heq : lty_rt lt = lty_rt (lty_core lt)) l, lty_own_pre true lt k π (r) l ≡ lty_own_pre core (lty_core lt) k π (transport_rfn Heq r) l) →
    ([∗ list] i ↦ ty ∈ zip (fmap lty_core lts) r', ∃ Heq : lty_rt ty.1 = rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre core ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)) ⊣⊢
    ([∗ list] i ↦ ty ∈ zip lts r', ∃ Heq : lty_rt ty.1 = rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre true ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)).
  Proof.
    intros IH.
    rewrite zip_fmap_l big_sepL_fmap.
    apply big_sepL_proper.
    intros ? [lt r] Hlook.
    apply lookup_zip in Hlook as [Hlook1 Hlook2].
    assert (lty_rt (lty_core lt) = lty_rt lt) as Heq3. { rewrite lty_core_rt_eq. done. }
    simpl in *. iSplit.
    - iIntros "(%Heq & %Hst & Hb)". assert (Heq2 : lty_rt lt = rt). { rewrite -lty_core_rt_eq. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq in Hst. iSplitR; first done.
      apply elem_of_list_lookup_2 in Hlook1.
      unshelve rewrite IH; [ done | | done].
      clear. subst rt. cbn.
      move: Heq2 Heq3 r. intros ->. intros Heq. rewrite (UIP_refl _ _ Heq). eauto.
    - iIntros "(%Heq & %Hst & Hb)". assert (Heq2 : lty_rt (lty_core lt) = rt).
      { rewrite lty_core_rt_eq. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq. iSplitR; first done.
      apply elem_of_list_lookup_2 in Hlook1. unshelve rewrite IH; [done | | done].
      clear. subst rt. cbn.
      move: Heq2 Heq3 r. intros <-. intros Heq. rewrite (UIP_refl _ _ Heq). eauto.
  Qed.

 Lemma lty_own_core_equiv (lt : lty) core k π r l Heq :
    lty_own_pre true lt k π r l ≡ lty_own_pre core (lty_core lt) k π (transport_rfn Heq r) l.
  Proof.
    rewrite /lty_own_core /lty_own.
    induction lt as [ | | | | lt IH κ | lt IH κ | lt IH | lt ls IH | lts IH sls | def len lts IH IH' | rt en variant lt  IH | | | ] using lty_induction in k, π, r, l, Heq, core |-*; simpl in *.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      f_equiv.
      3: unshelve setoid_rewrite (lty_own_core_core' lt); [ done | ].
      all: unshelve setoid_rewrite (IH core); [done.. | ].
      all: clear.
      all: move: r Heq Heq2.
      all: generalize (lty_rt lt) => ?.
      all: intros r ? <-.
      all: rewrite (UIP_refl _ _ Heq); simpl.
      all: repeat f_equiv; done.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      f_equiv.
      3: unshelve setoid_rewrite (lty_own_core_core' lt); [ done | ].
      all: unshelve setoid_rewrite (IH core); [done.. | ].
      all: clear.
      all: move: r Heq Heq2.
      all: generalize (lty_rt lt) => ?.
      all: intros r ? <-.
      all: rewrite (UIP_refl _ _ Heq); simpl.
      all: by repeat f_equiv.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_syn_type_eq lt) as Hst.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2 Hst.
      f_equiv.
      3: unshelve setoid_rewrite (lty_own_core_core' lt); [ done | ].
      all: unshelve setoid_rewrite (IH core); [done.. | ].
      all: clear -Hst.
      all: move: r Heq Heq2.
      all: generalize (lty_rt lt) => ?.
      all: intros r ? <-.
      all: rewrite (UIP_refl _ _ Heq); simpl.
      all: try rewrite Hst.
      all: by repeat f_equiv.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_syn_type_eq lt) as Hst.
      specialize (lty_core_rt_eq lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2 Hst.
      f_equiv.
      3: unshelve setoid_rewrite (lty_own_core_core' lt); [ done | ].
      all: unshelve setoid_rewrite (IH core); [done.. | ].
      all: clear -Hst.
      all: move: r Heq Heq2.
      all: generalize (lty_rt lt) => ?.
      all: intros r ? <-.
      all: rewrite (UIP_refl _ _ Heq); simpl.
      all: try rewrite Hst.
      all: by repeat f_equiv.
    - simp lty_own_pre. fold lty_rt.
      do 5 f_equiv.
      { rewrite map_length. done. }
      do 2 f_equiv.
      all: simpl.
      all: setoid_rewrite big_sepL_P_eq.
      3: do 2 f_equiv;
        [move : r; rewrite <-Heq; done | do 2 f_equiv].
      1: f_equiv.
      all: iSplit.
      all: iIntros "(%r' & Hrfn & Hb)".
      all: first [iExists (rew [id] Heq in r') | iExists (rew <-[id] Heq in r')].
      all: iSplitL "Hrfn";
        [ clear; try move: r'; try move: r; rewrite <-Heq; done| ].
      all: rewrite -(StructLty_own_core_equiv_lift _ _ _ _ (eq_sym Heq)); [done | intros; apply IH; done | ].
      all: clear; move: r'; generalize (eq_sym Heq); move : Heq.
      all: intros -> Heq; rewrite (UIP_refl _ _ Heq) //.
    - simp lty_own_pre. fold lty_rt.
      do 6 f_equiv.
      (*{ iPureIntro. rewrite Forall_fmap. eapply Forall_iff. intros []; done. }*)
      simpl.
      rewrite (UIP_refl _ _ Heq). clear Heq. simpl.
      f_equiv.
      all: repeat f_equiv; try done.
      all: rewrite !big_sepL_P_eq.
      all: rewrite -OfTyLty_core_id.
      all: rewrite interpret_iml_fmap ArrayLty_own_core_equiv_lift; first done.
      all: intros ? [-> | []]%elem_of_interpret_iml_inv; simpl; intros ??? Heq ?.
      all: try rewrite (UIP_refl _ _ Heq); simpl.
      all: try by (eapply IH').
      all: simp lty_own_pre; done.
    - (* enum *)
      simp lty_own_pre. fold lty_rt.
      do 6 f_equiv. do 3 f_equiv.
      { rewrite lty_core_rt_eq. done. }
      (*{ iPureIntro. rewrite Forall_fmap. eapply Forall_iff. intros []; done. }*)
      simpl.
      rewrite (UIP_refl _ _ Heq). clear Heq. simpl.
      f_equiv.
      all: repeat f_equiv; try done.
      rewrite lty_core_syn_type_eq.
      iSplit.
      + iIntros "(%Heq & Ha & Hb & ?)".
        match goal with a : rt |- _ => rename a into r1 end.
        assert (Heq' : lty_rt (lty_core lt) = enum_variant_rt en r1).
        { rewrite -Heq. apply lty_core_rt_eq. }
        iExists Heq'. iFrame.
        unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq. }
        iApply (lty_own_pre_rfn_eq with "Hb").
        rewrite /transport_rfn.
        rewrite rew_compose.
        apply rew_swap.
        rewrite rew_compose.
        apply elim_id_cast_l.
      + iIntros "(%Heq & Ha & Hb & ?)".
        match goal with a : rt |- _ => rename a into r1 end.
        assert (Heq' : lty_rt lt = enum_variant_rt en r1).
        { rewrite -Heq -lty_core_rt_eq. done. }
        iExists Heq'. iFrame.
        unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq. }
        iApply (lty_own_pre_rfn_eq with "Hb").
        rewrite /transport_rfn.
        rewrite rew_compose.
        apply rew_swap'.
        rewrite rew_compose.
        apply elim_id_cast_r.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
    - simp lty_own_pre.
    - simp lty_own_pre.
  Qed.

  Local Lemma place_rfn_interp_shared_transport_eq {rt rt'} (r : place_rfn rt) (r' : rt) (Heq : rt = rt') :
    place_rfn_interp_shared r r' -∗
    place_rfn_interp_shared (transport_rfn Heq r) (rew [id] Heq in r').
  Proof.
    subst. auto.
  Qed.

  Local Lemma lty_own_to_core_ofty {rt} (def : type rt) (r1 : place_rfn rt) (lt1 : lty) k π Heq l (Heq2 : lty_rt lt1 = rt) :
    lt1 = OfTyLty def →
    lty_own_pre false lt1 k π (rew <-Heq2 in r1) l -∗
    lty_own_pre false (lty_core lt1) k π (rew <-[place_rfn] Heq in r1) l.
  Proof.
    intros Ha. subst lt1. simpl.
    iApply lty_own_pre_rfn_eq. apply rew_swap.
    rewrite rew_compose rew_UIP//.
  Qed.

  Lemma lty_own_shared_to_core lt κ0 π r l Heq :
    lty_own lt (Shared κ0) π r l -∗ lty_own (lty_core lt) (Shared κ0) π (transport_rfn Heq r) l.
  Proof.
    rewrite /lty_own_core /lty_own.
    induction lt as [ | | | | lt IH κ | lt IH κ | lt IH | lt ls IH | lts IH sls | rt def len lts IH  | rt en variant lt IH | | | ???? IH1 IH2] using lty_induction in κ0, π, r, l, Heq |-*; simpl in *.
    - simp lty_own_pre. iIntros "(% & _ & _ & _ & _ & [])".
    - simp lty_own_pre. iIntros "(% & _ & _ & _ & _ & % & _ & [])".
    - rewrite (UIP_refl _ _ Heq). auto.
    - rewrite (UIP_refl _ _ Heq). auto.
    - simp lty_own_pre. fold lty_rt.
      iIntros "(%ly & %Halg & %Hly & Hlb & %r' & %γ & Ha & #Hl)".
      iExists ly. iR. iR. iFrame.
      set (Heq' := lty_core_rt_eq lt).
      iExists (rew <-[place_rfn] Heq' in r'), γ.
      iSplitL "Ha".
      { iClear "Hl". clear -Heq'.
        move: Heq' Heq r r'.
        simpl. generalize (lty_rt lt) => ?? Heq *. subst.
        rewrite (UIP_refl _ _ Heq). done. }
      iModIntro. iMod "Hl" as "(%li & Hf & Hl)". iModIntro. iExists li. iFrame.
      iApply IH. done.
    - simp lty_own_pre. fold lty_rt.
      iIntros "(%ly & %Halg & %Hly & Hlb & %r' & Ha & #Hl)".
      iExists ly. iR. iR. iFrame.
      set (Heq' := lty_core_rt_eq lt).
      iExists (rew <-[place_rfn] Heq' in r').
      iSplitL "Ha".
      { iClear "Hl". clear -Heq'.
        move: Heq' Heq r r'.
        simpl. generalize (lty_rt lt) => ?? Heq *. subst.
        rewrite (UIP_refl _ _ Heq). done. }
      iModIntro. iMod "Hl" as "(%li & Hf & Hl)". iModIntro. iExists li. iFrame.
      iApply IH. done.
    - simp lty_own_pre. fold lty_rt.
      iIntros "(%ly & %Halg & %Hly & Hlb & %r' & Ha & #Hl)".
      iExists ly. iR. iR. iFrame.
      set (Heq' := lty_core_rt_eq lt).
      iExists (rew <-[place_rfn] Heq' in r').
      iSplitL "Ha".
      { iClear "Hl". clear -Heq'.
        move: Heq' Heq r r'.
        simpl. fold lty_rt.
        generalize (lty_rt lt) => ?? Heq *. subst.
        rewrite (UIP_refl _ _ Heq). done. }
      iModIntro. iMod "Hl" as "(%li & Hf & Hl)". iModIntro. iExists li. iFrame.
      iApply IH. done.
    - simp lty_own_pre. fold lty_rt.
      iIntros "(%ly & %Halg & %Hly & Hlb & %r' & %li & Ha & #Hl)".
      iExists ly. iR. iR. iFrame.
      set (Heq' := lty_core_rt_eq lt).
      iExists (rew <-[place_rfn] Heq' in r'), li.
      iSplitL "Ha".
      { iClear "Hl". clear -Heq'.
        move: Heq' Heq r r'.
        simpl. fold lty_rt.
        generalize (lty_rt lt) => ?? Heq *. subst.
        rewrite (UIP_refl _ _ Heq). done. }
      iModIntro. iMod "Hl" as "(Hf & Hl)". iModIntro. iFrame.
      iApply IH. done.
    - (* struct *)
      simp lty_own_pre. fold lty_rt.
      iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & %r' & Ha & #Hl)".
      rewrite big_sepL_P_eq.
      iExists sl. iR.
      rewrite fmap_length. iR. iR. iFrame.
      (*set (Heq' := lty_core_rt_eq ).*)
      simpl in r'.
      simpl.
      iExists (rew [id]Heq in r').
      iSplitL "Ha".
      { by iApply place_rfn_interp_shared_transport_eq. }
      iModIntro. iMod "Hl". iModIntro.
      rewrite big_sepL_P_eq.
      rewrite pzipl_core_map_eq; first done; intros ?.
      rewrite rew_compose rew_UIP.
      rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, pzipl_core_map_fun (existT (UninitLty (UntypedSynType ly)) (PlaceIn ())))); first last.
      { intros ly; rewrite /pzipl_core_map_fun. f_equiv. rewrite rew_UIP'//. }
      rewrite pad_struct_fmap big_sepL_fmap.
      iApply (big_sepL_wand with "Hl").
      iApply big_sepL_intro. iModIntro.
      iIntros (? [? ] Hlook) "(%ly & % & % & Ha)".
      iExists ly. iR. simpl. rewrite lty_core_syn_type_eq. iR.
      apply pad_struct_lookup_Some in Hlook; first last.
      { rewrite pzipl_length. rewrite -Hlen.
        erewrite struct_layout_spec_has_layout_fields_length; done. }
      destruct Hlook as (n & ly' & Hlook & [(? & Hlook2) | (-> & Hlook2)]).
      + apply pzipl_lookup_inv in Hlook2.
        iApply (IH with "Ha"). by eapply elem_of_list_lookup_2.
      + injection Hlook2. intros _ ->.
        apply existT_inj in Hlook2 as ->.
        simpl. rewrite rew_UIP'. done.
    - (* array *)
      simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & Ha & #Hl)".
      rewrite big_sepL_P_eq.
      iExists ly. iR. iR. iR. iFrame.
      (*set (Heq' := lty_core_rt_eq ).*)
      iExists (rew [id]Heq in r').
      iSplitL "Ha". { by iApply place_rfn_interp_shared_transport_eq. }
      iModIntro. iMod "Hl" as "(%Hlen & Hl)". iModIntro.
      iSplitR. { rewrite -Hlen. iPureIntro. clear. rewrite (UIP_refl _ _ Heq). done. }
      rewrite big_sepL_P_eq.
      assert (OfTyLty def = lty_core $ OfTyLty def) as Hcore_eq. { done. }
      iEval (rewrite Hcore_eq).
      rewrite interpret_iml_fmap.
      rewrite rew_UIP zip_fmap_l big_sepL_fmap.
      iApply (big_sepL_wand with "Hl"). iApply big_sepL_intro.
      iModIntro. iIntros (k [lt1 r1] Hlook) "(%Heq1 & %Hst & Hl)".
      simpl in Heq1, Hst. subst rt. cbn.
      unshelve iExists _. { apply lty_core_rt_eq. }
      rewrite lty_core_syn_type_eq. iR.
      apply lookup_zip in Hlook as (Hlook & _). apply lookup_interpret_iml_Some_inv in Hlook as [? [Ha | Ha]].
      + unshelve iApply lty_own_to_core_ofty; [ | done | done | ]. done.
      + unshelve iPoseProof (IH with "Hl") as "Hl"; [ | | done | ].
        { by rewrite lty_core_rt_eq. }
        iApply (lty_own_pre_rfn_eq with "Hl"). apply rew_swap. rewrite rew_compose rew_UIP//.
    - (* enum *)
      simp lty_own_pre.
      iIntros "(%el & %rt' & %Hel & %Hly & Hlb & %Htag & %Hrt & Hf)".
      done.
    - simp lty_own_pre.
      iIntros "(%ly & % & % & ? & % & % & [])".
    - simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & Hlb & Hown)".
      clear. rewrite -lty_own_core_equiv. done.
    - simp lty_own_pre.
      iIntros "(%Heq_cur & %Hst & Ha & Hb)".
      iApply (IH2 with "Hb").
  Qed.
  (* NOTE: The reverse does not hold because the core of [BlockedLty] is [OfTy], which has a sharing predicate, but [BlockedLty] doesn't *)

  (** ** We define derived versions on top that expose the refinement type as an index.
     This is the variant that will be actually used by the type system. *)
  Record ltype (rt : Type) := mk_ltype {
    ltype_lty : lty;
    ltype_rt_agree : lty_rt ltype_lty = rt;
    ltype_lty_wf : lty_wf ltype_lty;
  }.
  Arguments ltype_lty {_}.
  Arguments ltype_rt_agree {_}.
  Arguments ltype_rt_agree : simpl never.

  (* uses PI *)
  Lemma mk_ltype_irrel {rt} lt Heq1 Heq2 Hwf1 Hwf2 :
    mk_ltype rt lt Heq1 Hwf1 = mk_ltype rt lt Heq2 Hwf2.
  Proof.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.

  Program Definition OfTy {rt} (ty : type rt) : ltype rt := {|
    ltype_lty := OfTyLty ty;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Arguments OfTy : simpl never.
  Global Typeclasses Opaque OfTy.

  Program Definition AliasLtype (rt : Type) (st : syn_type) (l : loc) : ltype rt := {|
    ltype_lty := AliasLty rt st l;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Global Typeclasses Opaque AliasLtype.

  Program Definition BlockedLtype {rt} (ty : type rt) (κ : lft) : ltype rt := {|
    ltype_lty := BlockedLty ty κ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Global Typeclasses Opaque BlockedLtype.

  Program Definition ShrBlockedLtype {rt} (ty : type rt) (κ : lft) : ltype rt := {|
    ltype_lty := ShrBlockedLty ty κ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Global Typeclasses Opaque ShrBlockedLtype.


  Program Definition BoxLtype {rt} (lt : ltype rt) : ltype (place_rfn rt) := {|
    ltype_lty := BoxLty (lt.(ltype_lty));
  |}.
  Next Obligation.
    by intros rt [lty <-].
  Qed.
  Next Obligation.
    by intros rt [lty <- Hwf].
  Qed.
  Arguments BoxLtype : simpl never.
  Global Typeclasses Opaque BoxLtype.

  Program Definition OwnedPtrLtype {rt} (lt : ltype rt) (ls : bool) : ltype (place_rfn rt * loc) := {|
    ltype_lty := OwnedPtrLty (lt.(ltype_lty)) ls;
  |}.
  Next Obligation.
    by intros rt [lty <-].
  Qed.
  Next Obligation.
    by intros rt [lty <- Hwf].
  Qed.
  Arguments OwnedPtrLtype : simpl never.
  Global Typeclasses Opaque OwnedPtrLtype.

  Program Definition MutLtype {rt} (lt : ltype rt) (κ : lft) : ltype (place_rfn rt * gname) := {|
    ltype_lty := MutLty (lt.(ltype_lty)) κ;
  |}.
  Next Obligation.
    by intros rt [lty <-].
  Qed.
  Next Obligation.
    by intros rt [lty <- Hwf].
  Qed.
  Arguments MutLtype : simpl never.
  Global Typeclasses Opaque MutLtype.

  Program Definition ShrLtype {rt} (lt : ltype rt) (κ : lft) : ltype (place_rfn rt) := {|
    ltype_lty := ShrLty (lt.(ltype_lty)) κ;
  |}.
  Next Obligation.
    by intros rt [lty <-].
  Qed.
  Next Obligation.
    by intros rt [lty <- Hwf].
  Qed.
  Arguments ShrLtype : simpl never.
  Global Typeclasses Opaque ShrLtype.

  #[universes(polymorphic)]
  Program Definition StructLtype {rts : list Type} (lts : hlist ltype rts) (sls : struct_layout_spec) : ltype (plist place_rfn rts) := {|
    ltype_lty := StructLty (hcmap (@ltype_lty) lts) sls;
  |}.
  Next Obligation.
    intros rts lts sls.
    induction rts as [ | rt rts IH]; simpl.
    - inv_hlist lts. done.
    - inv_hlist lts. intros [lt <-] lts'.
      simpl. f_equiv. apply IH.
  Qed.
  Next Obligation.
    intros rts lts sls. simpl.
    induction rts as [ | rt rts IH]; inv_hlist lts; simpl; first done.
    intros [lt <- Hwf] lts. split; first done. apply IH.
  Qed.
  Arguments StructLtype : simpl never.
  Global Typeclasses Opaque StructLtype.

  Program Definition ArrayLtype {rt : Type} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) : ltype (list (place_rfn rt)) := {|
    ltype_lty := @ArrayLty rt def len (map (λ '(i, lt), (i, lt.(ltype_lty))) lts);
  |}.
  Next Obligation.
    intros rt def len lts. simpl. done.
  Qed.
  Next Obligation.
    intros rt def len lts. simpl.
    induction lts as [ | [i lt] lts IH]; simpl; first done.
    split; last done. split_and!; [ apply ltype_lty_wf | rewrite !ltype_rt_agree// ].
  Qed.
  Global Arguments ArrayLtype : simpl never.
  Global Typeclasses Opaque ArrayLtype.

  Program Definition EnumLtype {rt : Type} (en : enum rt) (variant : string) (lte : ltype ((enum_tag_rt en variant))) : ltype rt := {|
    ltype_lty := @EnumLty rt en variant lte.(ltype_lty);
  |}.
  Next Obligation.
    intros rt en variant lte. simpl. done.
  Qed.
  Next Obligation.
    intros rt en variant lte. simpl. split_and!.
    - apply ltype_lty_wf.
    - rewrite ltype_rt_agree. done.
  Qed.
  Global Typeclasses Opaque EnumLtype.
  Global Arguments ArrayLtype : simpl never.

  Program Definition OpenedLtype {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ) : ltype rt_cur := {|
    ltype_lty := OpenedLty (ltype_lty lt_cur) (ltype_lty lt_inner) (ltype_lty lt_full) Cpre Cpost;
  |}.
  Next Obligation.
    intros rt_cur rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost. simpl.
    rewrite ltype_rt_agree; done.
  Qed.
  Next Obligation.
    intros rt_cur rt_inner rt_full [lt_cur <- Hcur] [lt_inner <- Hinner] [lt_full <- Hfull] Cpre Cpost; simpl.
    eauto.
  Qed.
  Global Typeclasses Opaque OpenedLtype.
  Global Arguments OpenedLtype : simpl never.

  Program Definition CoreableLtype {rt_full} (κs : list lft) (lt_full : ltype rt_full) : ltype rt_full := {|
    ltype_lty := CoreableLty κs (ltype_lty lt_full);
  |}.
  Next Obligation.
    intros rt_full κ lt_full. simpl. apply ltype_rt_agree.
  Qed.
  Next Obligation.
    intros rt_full κ [lt_full <- ?]. simpl. eauto.
  Qed.
  Global Arguments CoreableLtype : simpl never.
  Global Typeclasses Opaque CoreableLtype.

  Program Definition ShadowedLtype {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) : ltype rt_full := {|
    ltype_lty := ShadowedLty (ltype_lty lt_cur) r_cur (ltype_lty lt_full);
  |}.
  Next Obligation.
    intros rt_cur rt_full lt_cur r_cur lt_full. simpl. apply ltype_rt_agree.
  Qed.
  Next Obligation.
    intros rt_cur rt_full lt_cur r_cur lt_full. split_and!; [apply ltype_lty_wf.. | ].
    apply ltype_rt_agree.
  Qed.
  Global Arguments ShadowedLtype : simpl never.
  Global Typeclasses Opaque ShadowedLtype.

  Import EqNotations.
  Definition ltype_own_pre (core : bool) {rt} (lt : ltype rt) : bor_kind → thread_id → place_rfn rt → loc → iProp Σ :=
    λ k π r l, lty_own_pre core lt.(ltype_lty) k π (rew <- lt.(ltype_rt_agree) in r) l.

  Local Definition ltype_own_core_def := @ltype_own_pre true.
  Local Definition ltype_own_core_aux : seal (@ltype_own_core_def). Proof. by eexists. Qed.
  Definition ltype_own_core := ltype_own_core_aux.(unseal).
  Lemma ltype_own_core_unseal : @ltype_own_core = ltype_own_core_def.
  Proof. rewrite -ltype_own_core_aux.(seal_eq) //. Qed.
  Global Arguments ltype_own_core {_}.
  Global Typeclasses Opaque ltype_own_core.

  Local Definition ltype_own_def := @ltype_own_pre false.
  Local Definition ltype_own_aux : seal (@ltype_own_def). Proof. by eexists. Qed.
  Definition ltype_own := ltype_own_aux.(unseal).
  Lemma ltype_own_unseal : @ltype_own = ltype_own_def.
  Proof. rewrite -ltype_own_aux.(seal_eq) //. Qed.
  Global Arguments ltype_own {_}.
  Global Typeclasses Opaque ltype_own.

  Definition ltype_st {rt} (lt : ltype rt) : syn_type := lty_st lt.(ltype_lty).
  Global Arguments ltype_st : simpl never.

  Program Definition ltype_core {rt} (lt : ltype rt) : ltype rt := {|
    ltype_lty := lty_core lt.(ltype_lty);
  |}.
  Next Obligation.
    intros rt lt. rewrite lty_core_rt_eq. apply ltype_rt_agree.
  Qed.
  Next Obligation.
    intros rt [lt <- Hwf]; simpl. by apply lty_core_wf.
  Qed.
  Global Arguments ltype_core : simpl never.
  Global Typeclasses Opaque ltype_core.


  Section induction.
    Local Fixpoint make_ltype_hlist (lts : list lty) : Forall_cb lty_wf lts → hlist ltype (fmap lty_rt lts) :=
      match lts as lts' return Forall_cb lty_wf lts' → hlist ltype (fmap lty_rt lts') with
      | [] => λ _, +[]
      | lt :: lts => λ Hwf,
          (mk_ltype _ lt eq_refl (proj1 Hwf)) +:: make_ltype_hlist lts (proj2 Hwf)
      end.
    Local Lemma make_ltype_hlist_lift lts (Hwf : Forall_cb lty_wf lts) (P : ∀ rt, ltype rt → Prop) :
      (∀ (lt : lty) (Helt : lt ∈ lts) (Hwf : lty_wf lt), P (lty_rt lt) (mk_ltype _ lt eq_refl Hwf)) →
      (∀ lt0, lt0 ∈ hzipl _ (make_ltype_hlist lts Hwf) → P (projT1 lt0) (projT2 lt0)).
    Proof.
      induction lts as [ | lt lts IH]; simpl; intros Ha.
      - intros ? []%elem_of_nil.
      - intros [rt lt0]. rewrite elem_of_cons.
        intros [[= -> ->] | Hel].
        { apply Ha. apply elem_of_cons; eauto. }
        eapply IH; last done.
        intros. eapply Ha. apply elem_of_cons; eauto.
    Qed.
    Local Lemma make_ltype_hlist_map_proj_eq lts Hwf :
      (@ltype_lty +c<$> make_ltype_hlist lts Hwf) = lts.
    Proof.
      induction lts as [ | lt lts IH]; first done.
      simpl. by rewrite IH.
    Qed.

    Local Fixpoint make_ltype_list {rt} (lts : list (nat * lty)) : Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt) lts → list (nat * ltype rt) :=
      match lts as lts' return Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt) lts' → list (nat * ltype rt) with
      | [] => λ _, []
      | (i, lt) :: lts => λ Hwf,
          (i, mk_ltype _ lt (proj2 (proj1 Hwf)) (proj1 (proj1 Hwf))) :: make_ltype_list lts (proj2 Hwf)
      end.
    Local Lemma make_ltype_list_lift {rt} lts (Hwf : Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt) lts) (P : ∀ rt, ltype rt → Prop) :
      (∀ rt (lt : lty) Heq1 Heq2 Hwf1 Hwf2, P rt (mk_ltype rt lt Heq1 Hwf1) → P rt (mk_ltype rt lt Heq2 Hwf2)) →
      (∀ (i : nat) (lt : lty) (Helt : (i, lt) ∈ lts) (Hwf : lty_wf lt), P (lty_rt lt) (mk_ltype _ lt eq_refl Hwf)) →
      (∀ i lt0, (i, lt0) ∈ make_ltype_list lts Hwf → P _ lt0).
    Proof.
      intros P_irrel Ha. induction lts as [ | [i lt] lts IH]; simpl.
      - intros ? ? []%elem_of_nil.
      - intros i0 lt0. rewrite elem_of_cons. intros [[= -> ->] | Hel]; first last.
        { eapply IH; last done. intros. eapply Ha. apply elem_of_cons; by right. }
        destruct Hwf as [[Hwf Heq] ?].
        clear IH.
        unshelve efeed pose proof (Ha i lt) as Ha.
        { done. } { apply elem_of_cons; by left. }
        subst rt. eapply P_irrel; done.
    Qed.
    Local Lemma make_ltype_list_map_proj_eq {rt} lts Hwf :
      (map (λ '(i, lt), (i, ltype_lty lt)) (make_ltype_list (rt:=rt) lts Hwf)) = lts.
    Proof.
      induction lts as [ | [i lt] lts IH]; simpl; first done.
      f_equiv. apply IH.
    Qed.

    Lemma ltype_induction (P : ∀ rt, ltype rt → Prop) :
      (∀ (rt : Type) (t : type rt) κ, P _ (BlockedLtype t κ)) →
      (∀ (rt : Type) (t : type rt) κ, P _ (ShrBlockedLtype t κ)) →
      (∀ (rt : Type) (t : type rt), P _ (OfTy t)) →
      (∀ (rt : Type) (st : syn_type) (l : loc), P _ (AliasLtype rt st l)) →
      (∀ (rt : Type) (lt : ltype rt), P _ lt → ∀ κ, P _ (MutLtype lt κ)) →
      (∀ (rt : Type) (lt : ltype rt), P _ lt → ∀ κ, P _ (ShrLtype lt κ)) →
      (∀ (rt : Type) (lt : ltype rt), P _ lt → P _ (BoxLtype lt)) →
      (∀ (rt : Type) (lt : ltype rt) (ls : bool), P _ lt → P _ (OwnedPtrLtype lt ls)) →
      (∀ (rts : list Type) (lts : hlist ltype rts),
        (∀ lt, lt ∈ hzipl rts lts → P _ (projT2 lt)) →
        ∀ sls : struct_layout_spec, P _ (StructLtype lts sls)) →
      (∀ (rt : Type) (def : type rt) (len : nat) (lts : list (nat * ltype rt)),
        (∀ i lt, (i, lt) ∈ lts → P _ lt) →
        P _ (ArrayLtype def len lts)) →
      (∀ (rt : Type) (en : enum rt) (variant : var_name) (lte : ltype (enum_tag_rt en variant)),
        P _ lte → P _ (EnumLtype en variant lte)) →
      (∀ (rt_cur rt_inner rt_full : Type) (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
        (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ),
        P _ lt_cur → P _ lt_inner → P _ lt_full →
        P _ (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ (rt_full : Type) κs (lt_full : ltype rt_full), P _ lt_full → P _ (CoreableLtype κs lt_full)) →
      (∀ (rt_cur rt_full : Type) (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full),
        P _ lt_cur → P _ lt_full → P _ (ShadowedLtype lt_cur r_cur lt_full)) →
      ∀ (rt : Type) (lt : ltype rt), P _ lt.
    Proof.
      intros Hblocked Hshrblocked Hofty Halias Hmut Hshr Hbox Hptr Hstruct Harr Hen Hopened Hcoreable Hshadow.

      assert (P_irrel:
        ∀ rt (lt : lty) Heq1 Heq2 Hwf1 Hwf2, P rt (mk_ltype rt lt Heq1 Hwf1) → P rt (mk_ltype rt lt Heq2 Hwf2)).
      { intros rt lt <- Heq2. rewrite (UIP_refl _ _ Heq2).
        intros Hwf1 Hwf2. rewrite (proof_irrelevance _ Hwf1 Hwf2). done. }

      intros rt [lt <- Hwf].
      induction lt as [ | | | | lt IH κ | lt IH κ | lt IH | lt ls IH | lts IH sls | rt def len lts IH | rt en variant lte IH | rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost IH_cur IH_inner IH_full | κ lt_full IH | rt_cur lt_cur r_cur lt_full IH_cur IH_full] using lty_induction; simpl.
      - eapply P_irrel. apply Hblocked.
      - eapply P_irrel. apply Hshrblocked.
      - eapply P_irrel. apply Hofty.
      - eapply P_irrel. apply Halias.
      - specialize (Hmut _ _ (IH Hwf)). eapply P_irrel. apply Hmut.
      - specialize (Hshr _ _ (IH Hwf)). eapply P_irrel. apply Hshr.
      - specialize (Hbox _ _ (IH Hwf)). eapply P_irrel. apply Hbox.
      - specialize (Hptr _ _ ls (IH Hwf)). eapply P_irrel. apply Hptr.
      - specialize (make_ltype_hlist_lift lts Hwf P IH) as IH'.
        specialize (Hstruct _ _ IH' sls). clear -Hstruct P_irrel.
        move: Hstruct. unfold StructLtype.
        generalize (StructLtype_obligation_2 (lty_rt <$> lts) (make_ltype_hlist lts Hwf) sls) as Hwf'.
        generalize (StructLtype_obligation_1 (lty_rt <$> lts) (make_ltype_hlist lts Hwf) sls) as Heq.
        rewrite make_ltype_hlist_map_proj_eq.
        simpl. intros <- Hwf'.
        eapply P_irrel.
      - simpl in Hwf.
        specialize (make_ltype_list_lift lts Hwf P P_irrel IH) as IH2.
        specialize (Harr _ def len _ IH2).
        move: Harr. rewrite /ArrayLtype.
        generalize (ArrayLtype_obligation_2 _ def len (make_ltype_list lts Hwf)).
        generalize (ArrayLtype_obligation_1 _ def len (make_ltype_list lts Hwf)).
        rewrite make_ltype_list_map_proj_eq.
        simpl. intros <- Hwf'. eapply P_irrel.
      - (* enum *)
        simpl in Hwf. destruct Hwf as (Hwf & Hrt).
        specialize (IH Hwf).
        set (ltypee := mk_ltype _ _ Hrt Hwf).
        specialize (Hen rt en variant ltypee).
        eapply P_irrel.
        apply Hen.
        subst ltypee.
        move: IH.
        clear.
        move: Hrt. generalize (enum_tag_rt en variant). intros ??. subst.
        done.
      - destruct Hwf as (Heq1 & Heq2 & Hwf_cur & Hwf_inner & Hwf_full); subst.
        specialize (Hopened _ _ _ _ _ _ Cpre Cpost (IH_cur Hwf_cur) (IH_inner Hwf_inner) (IH_full Hwf_full)).
        eapply P_irrel. eapply Hopened.
      - specialize (Hcoreable _ κ _ (IH Hwf)).
        eapply P_irrel. eapply Hcoreable.
      - destruct Hwf as (Hwf_cur & Hwf_full & <-).
        specialize (Hshadow _ _ _ r_cur _ (IH_cur Hwf_cur) (IH_full Hwf_full)).
        eapply P_irrel. eapply Hshadow.
    Qed.
  End induction.

  (** Unfolding equations for [ltype] *)
  Definition ltype_own_type := ∀ rt, ltype rt → bor_kind → thread_id → place_rfn rt → loc → iProp Σ.

  Definition UninitLtype st := OfTy (uninit st).

  (** Note: Parameterized over [rec] and [rec_core] instead of using [ltype_own] and [ltype_own_core] because [rec] might be [ltype_own_core] if we go into the core *)
  Definition box_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rt} (lt : ltype rt) (k : bor_kind) (π : thread_id) (r : place_rfn (place_rfn rt)) (l : loc) : iProp Σ :=
    (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          (* the placement of the pointsto below the later let's us get the unfoldings equation without timelessness *)
          ∃ r' : place_rfn rt, place_rfn_interp_owned r r' ∗ ▷?wl|={lftE}=>
          ∃ (l' : loc) (ly' : layout), l ↦ l' ∗
          ⌜syn_type_has_layout (ltype_st lt) ly'⌝ ∗
          ⌜l' `has_layout_loc` ly'⌝ ∗
          freeable_nz l' ly'.(ly_size) 1 HeapAlloc ∗
          rec _ lt (Owned true) π r' l'
      | Uniq κ γ =>
          have_creds ∗
          place_rfn_interp_mut r γ ∗
          (* TODO can we remove the update here? *)
          |={lftE}=> &pin{κ}
              [∃ (r' : place_rfn rt),
                gvar_auth γ r' ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (l' : loc) (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (ltype_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                (freeable_nz l' ly'.(ly_size) 1 HeapAlloc) ∗
                rec_core _ lt (Owned true) π r' l'
              ]
              (∃ (r' : place_rfn rt),
                gvar_auth γ r' ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (l' : loc) (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (ltype_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                (freeable_nz l' ly'.(ly_size) 1 HeapAlloc) ∗
                rec _ lt (Owned true) π r' l')
      | Shared κ =>
        (∃ r', place_rfn_interp_shared r r' ∗
          □ |={lftE}=> ∃ li : loc,
            &frac{κ}(λ q', l ↦{q'} li) ∗
            ▷ rec _ lt (Shared κ) π r' li)%I
      end)%I.

  Definition owned_ptr_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rt} (lt : ltype rt) (ls : bool) (k : bor_kind) (π : thread_id) (r : place_rfn (place_rfn rt * loc)) (l : loc) : iProp Σ :=
    (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          (* the placement of the pointsto below the later let's us get the unfoldings equation without timelessness *)
          ∃ (r' : place_rfn rt) (l' : loc), place_rfn_interp_owned r (r', l') ∗ ▷?wl|={lftE}=>
          ∃ (ly' : layout), l ↦ l' ∗
          ⌜syn_type_has_layout (ltype_st lt) ly'⌝ ∗
          ⌜l' `has_layout_loc` ly'⌝ ∗
          rec _ lt (Owned ls) π r' l'
      | Uniq κ γ =>
          have_creds ∗
          place_rfn_interp_mut r γ ∗
          |={lftE}=> &pin{κ}
              [∃ (r' : place_rfn rt) (l' : loc),
                gvar_auth γ (r', l') ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (ltype_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                rec_core _ lt (Owned ls) π r' l'
              ]
              (∃ (r' : place_rfn rt) (l' : loc),
                gvar_auth γ (r', l') ∗
                (* the update here is needed to eliminate ltype_eq, which has an update/except0 in the Owned case *)
                |={lftE}=>
                ∃ (ly' : layout),
                l ↦ l' ∗
                ⌜syn_type_has_layout (ltype_st lt) ly'⌝ ∗
                ⌜l' `has_layout_loc` ly'⌝ ∗
                rec _ lt (Owned ls) π r' l')
      | Shared κ =>
        (∃ r' li, place_rfn_interp_shared r (r', li) ∗
          □ |={lftE}=>
            &frac{κ}(λ q', l ↦{q'} li) ∗
            ▷ rec _ lt (Shared κ) π r' li)%I
      end)%I.

  Definition shr_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rt} (lt : ltype rt) κ k π (r : place_rfn (place_rfn rt)) l :=
        (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
         loc_in_bounds l 0 ly.(ly_size) ∗
        match k with
        | Owned wl =>
            maybe_creds wl ∗
            ∃ (r' : place_rfn rt), place_rfn_interp_owned r r' ∗
            ▷?wl|={lftE}=>  ∃ (l' : loc), l ↦ l' ∗
            rec _ lt (Shared κ) π r' l'
        | Uniq κ' γ' =>
            have_creds ∗
            place_rfn_interp_mut r γ' ∗
            |={lftE}=> &pin{κ'}
              [∃ (r' : place_rfn rt), gvar_auth γ' r' ∗ |={lftE}=>  ∃ (l' : loc), l ↦ l' ∗ rec_core _ lt (Shared κ) π r' l']
              (∃ (r' : place_rfn rt), gvar_auth γ' r' ∗ |={lftE}=>  ∃ (l' : loc), l ↦ l' ∗ rec _ lt (Shared κ) π r' l')
        | Shared κ' =>
            ∃ (r' : place_rfn rt),
            place_rfn_interp_shared r r' ∗
            (* the update is also over the fractional borrow to deal with timelessness *)
            □ |={lftE}=> ∃ (l' : loc),
            &frac{κ'} (λ q, l ↦{q} l') ∗
            (* no intersection here, as we also don't do that for the type interpretation *)
            ▷ rec _ lt (Shared κ) π r' l'
        end)%I.

  Definition mut_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rt} (lt : ltype rt) (κ : lft) (k : bor_kind) (π : thread_id) (r : place_rfn (place_rfn rt * gname)) (l : loc) : iProp Σ :=
    (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
       loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          (* it's fine to existentially quantify here over the gvar_obs, since
            the outer can actually tell us about it. Keep in mind that the gvar here can actually
            change if we write under nested places. *)
          ∃ (γ : gname) (r' : place_rfn rt) ,
          place_rfn_interp_owned r (r', γ) ∗
          (* TODO layout requirements on l' here? *)
          ▷?wl|={lftE}=>  ∃ l' : loc , l ↦ l' ∗ (rec _ lt (Uniq κ γ) π r' l')
      | Uniq κ' γ' =>
          have_creds ∗
          place_rfn_interp_mut r γ' ∗
          |={lftE}=> &pin{κ'}
            [∃ (r' : (place_rfn rt) * gname),
              gvar_auth γ' r' ∗
              (* update here to be compatible with ofty *)
              |={lftE}=>
              ∃ (l' : loc), l ↦ l' ∗
              rec_core _ lt (Uniq κ r'.2) π r'.1 l'
            ]
            (∃ (r' : (place_rfn rt) * gname),
              gvar_auth γ' r' ∗
              (* update here to be compatible with ofty *)
              |={lftE}=>
              ∃ (l' : loc), l ↦ l' ∗
              rec _ lt (Uniq κ r'.2) π r'.1 l')
      | Shared κ' =>
        (∃ r' γ, place_rfn_interp_shared r (r', γ) ∗
        (* the update is also over the fractional borrow to deal with timelessness *)
        □ |={lftE}=> ∃ (li : loc),
          &frac{κ'}(λ q', l ↦{q'} li) ∗
          (* later is for contractiveness, the update for timelessness *)
          ▷ rec _ lt (Shared (κ⊓κ')) π r' li)%I
      end)%I.

  Definition struct_make_uninit_ltype (ly : layout) : sigT (λ rt : Type, (ltype rt * place_rfn rt)%type) :=
    existT (unit : Type) (UninitLtype (UntypedSynType ly), PlaceIn ()).

  Definition struct_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rts : list Type}
    (lts : hlist ltype rts) (sls : struct_layout_spec)
    (k : bor_kind) (π : thread_id) (r : place_rfn (plist place_rfn rts)) (l : loc) : iProp Σ :=
    ∃ sl : struct_layout,
    ⌜use_struct_layout_alg sls = Some sl⌝ ∗
    ⌜length (sls_fields sls) = length rts⌝ ∗
    ⌜l `has_layout_loc` sl⌝ ∗
    loc_in_bounds l 0 (sl.(ly_size)) ∗
    match k with
    | Owned wl =>
        maybe_creds wl ∗
        ∃ r' : plist place_rfn rts, place_rfn_interp_owned r r' ∗ ▷?wl |={lftE}=>
          [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
            ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            rec _ (projT2 ty).1 (Owned false) π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))
    | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        (* We change the ownership to Owned false, because we can't push the borrow down in this formulation of products.
          The cost of this is that we need an update here (to get congruence rules for ltype_eq),
          which propagates to all the other Uniq cases of other ltypes. *)
        |={lftE}=> &pin{κ}
          [∃ (r' : plist place_rfn rts),
            gvar_auth γ r' ∗ |={lftE}=>
            [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
              rec_core _ (projT2 ty).1 (Owned false) π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))
          ]
          (∃ (r' : plist place_rfn rts),
            gvar_auth γ r' ∗ |={lftE}=>
            [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
              rec _ (projT2 ty).1 (Owned false) π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))
          )
    | Shared κ =>
        (∃ r', place_rfn_interp_shared r r' ∗
          (* update needed to make the unfolding equation work *)
          □ |={lftE}=>
            [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
              rec _ (projT2 ty).1 (Shared κ) π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))%I
    end.

  Definition array_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    (rt : Type) (def : type rt) (len : nat) (lts : list (nat * ltype rt))
    (k : bor_kind) (π : thread_id) (r : place_rfn (list (place_rfn rt))) (l : loc) : iProp Σ :=
    ∃ ly,
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      ⌜(ly_size ly * len ≤ MaxInt isize_t)%Z⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗
      (*⌜Forall (λ '(i, _), i < len) lts⌝ ∗*)
      match k with
      | Owned wl =>
          maybe_creds wl ∗
          ∃ r' : list (place_rfn rt), place_rfn_interp_owned r r' ∗
          ▷?wl |={lftE}=>
          (⌜length r' = len⌝ ∗
          [∗ list] i ↦ lt; r0 ∈ (interpret_iml (OfTy def) len lts); r',
              ⌜ltype_st lt = ty_syn_type def⌝ ∗ rec _ lt (Owned false) π r0 (offset_loc l ly i))
      | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        |={lftE}=> &pin{κ}
          [∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              [∗ list] i ↦ lt; r0 ∈ interpret_iml (OfTy def) len lts; r',
                ⌜ltype_st lt = ty_syn_type def⌝ ∗ rec_core _ lt (Owned false) π r0 (offset_loc l ly i))]
          (∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              [∗ list] i ↦ lt; r0 ∈ interpret_iml (OfTy def) len lts; r',
                ⌜ltype_st lt = ty_syn_type def⌝ ∗ rec _ lt (Owned false) π r0 (offset_loc l ly i)))
      | Shared κ =>
          ∃ r', place_rfn_interp_shared r r' ∗
            □ |={lftE}=> (⌜length r' = len⌝ ∗ [∗ list] i ↦ lt; r0 ∈ interpret_iml (OfTy def) len lts; r',
                  ⌜ltype_st lt = ty_syn_type def⌝ ∗ rec _ lt (Shared κ) π r0 (offset_loc l ly i))
      end.


  Definition enum_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    (rt : Type) (en : enum rt)
    (tag : var_name) (lte : ltype (enum_tag_rt en tag))
    (k : bor_kind) (π : thread_id) (r : place_rfn rt) (l : loc) : iProp Σ :=
      ∃ el,
      ⌜enum_layout_spec_has_layout en.(enum_els) el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(ly_size) ∗
      ⌜is_Some (enum_tag_ty en tag)⌝ ∗
      match k with
      | Owned wl =>
        maybe_creds wl ∗
        ∃ r' : rt, place_rfn_interp_owned r r' ∗
        ▷?wl |={lftE}=>(
        ∃ (Heq : enum_variant_rt en r' = enum_tag_rt en tag),
        ⌜enum_tag en r' = tag⌝ ∗
        (* ownership of the discriminant *)
        lty_of_ty_own (int en.(enum_els).(els_tag_it)) (Owned false) π (PlaceIn (enum_lookup_tag en r')) (l atst{sls_of_els en.(enum_els)}ₗ "discriminant") ∗
        (* ownership of the data *)
        rec _ lte (Owned false) π (rew [place_rfn] Heq in (PlaceIn (enum_variant_rfn en r'))) (l atst{sls_of_els en.(enum_els)}ₗ "data") ∗
        (* ownership of the remaining padding after the data *)
        (∃ v, ((l atst{sls_of_els en.(enum_els)}ₗ "data") +ₗ (size_of_st (ltype_st lte))) ↦ v ∗ ⌜v `has_layout_val` ly_offset (els_data_ly en.(enum_els)) (size_of_st (ltype_st lte))⌝) ∗
        (* ownership of the padding fields of the sl *)
        ([∗ list] i ↦ mly ∈ pad_struct el.(sl_members) [None; None] (λ ly, Some ly),
        if mly is Some ly then lty_of_ty_own (uninit (UntypedSynType ly)) (Owned false) π (PlaceIn ()) (l +ₗ Z.of_nat (offset_of_idx el.(sl_members) i)) else True))
      | _ =>
          (* TODO *)
          False
      end.

  Definition opened_ltype_own
      (rec : ltype_own_type) (rec_core : ltype_own_type)
      {rt_cur rt_inner rt_full : Type}
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ)
      (k : bor_kind) (π : thread_id) (r : place_rfn rt_cur) (l : loc) : iProp Σ :=
    ∃ ly, ⌜use_layout_alg (ltype_st lt_cur) = Some ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 (ly_size ly) ∗
      ⌜ltype_st lt_cur = ltype_st lt_inner⌝ ∗
      ⌜ltype_st lt_inner = ltype_st lt_full⌝ ∗

      match k with
      | Owned wl =>
          ltype_own lt_cur (Owned false) π r l ∗
          (* once we have restored to [lt_inner], we can fold to [lt_full] again *)
          logical_step lftE
          (∀ (r : rt_inner) (r' : rt_full) (κs : list lft),
            (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
            (* directly hand out Cpost. We don't need to wait to get tokens from closing borrows etc. *)
            Cpost r r' ∗
            (lft_dead_list κs -∗
             ltype_own lt_inner (Owned false) π (PlaceIn r) l ={lftE}=∗
             ltype_own_core lt_full (Owned wl) π (PlaceIn r') l))
      | Uniq κ γ =>
        ltype_own lt_cur (Owned false) π r l ∗
          (* we will execute this VS when closing the invariant, after having already stratified [lt_cur].
             At that point, we will know [lt_cur] is unblockable to [lt_inner] after the set of lifetimes [κs] is dead *)
        logical_step lftE
          (∀ (own_lt_cur' : thread_id → rt_inner → loc → iProp Σ) (κs : list lft) (r : rt_inner) (r' : rt_full),
            (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
            ([∗ list] κ' ∈ κs, κ' ⊑ κ) -∗
            own_lt_cur' π r l -∗

            (* the ownership of [lt_cur'] needs to be shiftable to the _core_ of [lt_inner];
              this is required for closing the borrow and for proving that it can be unblocked to lt_full
                (which is needed for showing the shift to Coreable) *)
            (□ (lft_dead_list κs -∗ own_lt_cur' π r l ={lftE}=∗
              ltype_own_core lt_inner (Owned false) π (PlaceIn r) l)) ={lftE}=∗

            Cpost r r' ∗
            gvar_obs γ r' ∗
            (lft_dead_list κs -∗ gvar_obs γ r' ={lftE}=∗
              ltype_own_core lt_full (Uniq κ γ) π (PlaceIn r') l))
      | Shared κ =>
          False
        (*ltype_own lt_cur (Shared κ) π r l*)
      end.

  Definition coreable_ltype_own (rec : ltype_own_type) (rec_core : ltype_own_type)
      {rt_full} (κs : list lft) (lt_full : ltype rt_full)
      (k : bor_kind) (π : thread_id) (r : place_rfn rt_full) (l : loc) : iProp Σ :=
    ∃ ly, ⌜syn_type_has_layout (ltype_st lt_full) ly⌝ ∗
    ⌜l `has_layout_loc` ly⌝ ∗
    loc_in_bounds l 0 (ly_size ly) ∗
    match k with
    | Owned wl =>
        lft_dead_list κs ={lftE}=∗ rec_core _ lt_full (Owned wl) π r l
    | Uniq κ' γ =>
        place_rfn_interp_mut r γ ∗
        (lft_dead_list κs -∗ place_rfn_interp_mut r γ ={lftE}=∗ rec_core _ lt_full (Uniq κ' γ) π r l)
    | Shared κ =>
        rec_core _ lt_full (Shared κ) π r l
    end.

  Definition shadowed_ltype_own (rec : ltype_own_type) (rec_core : ltype_own_type)
    {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full)
    (k : bor_kind) (π : thread_id) (r : place_rfn rt_full) (l : loc) : iProp Σ :=
    ⌜ltype_st lt_cur = ltype_st lt_full⌝ ∗
    rec _ lt_cur k π (r_cur) l ∗
    rec _ lt_full k π r l.

  Lemma ltype_own_pre_ofty_unfold {rt} (ty : type rt) (core : bool) k π r l :
    ltype_own_pre core (OfTy ty) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof.
    rewrite /ltype_own_pre. simp lty_own_pre. rewrite /lty_of_ty_own.
    move: r.
    generalize (ltype_rt_agree (OfTy ty)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.
  Lemma ltype_own_ofty_unfold {rt} (ty : type rt) k π r l :
    ltype_own (OfTy ty) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof. rewrite ltype_own_unseal. apply ltype_own_pre_ofty_unfold. Qed.
  Lemma ltype_own_core_ofty_unfold {rt} (ty : type rt) k π r l :
    ltype_own_core (OfTy ty) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof. rewrite ltype_own_core_unseal. apply ltype_own_pre_ofty_unfold. Qed.

  Lemma ltype_own_pre_alias_unfold (rt : Type) (st : syn_type) (p : loc) (core : bool) k π r l :
    ltype_own_pre core (AliasLtype rt st p) k π r l ≡ alias_lty_own rt st p k π r l.
  Proof.
    rewrite /ltype_own_pre. simp lty_own_pre. rewrite /alias_lty_own.
    destruct k; [ | done..].
    done.
  Qed.
  Lemma ltype_own_alias_unfold (rt : Type) (st : syn_type) (p : loc) k π r l :
    ltype_own (AliasLtype rt st p) k π r l ≡ alias_lty_own rt st p k π r l.
  Proof. rewrite ltype_own_unseal. apply ltype_own_pre_alias_unfold. Qed.
  Lemma ltype_own_core_alias_unfold (rt : Type) (st : syn_type) (p : loc) k π r l :
    ltype_own_core (AliasLtype rt st p) k π r l ≡ alias_lty_own rt st p k π r l.
  Proof. rewrite ltype_own_core_unseal. apply ltype_own_pre_alias_unfold. Qed.

  Lemma ltype_own_blocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own (BlockedLtype ty κ) k π r l ≡ blocked_lty_own ty κ k π r l.
  Proof.
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre. simp lty_own_pre.
    rewrite /blocked_lty_own.
    move: r.
    generalize (ltype_rt_agree (BlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.
  Lemma ltype_own_core_blocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own_core (BlockedLtype ty κ) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof.
    rewrite ltype_own_core_unseal /ltype_own_core_def /ltype_own_pre. simp lty_own_pre.
    rewrite /lty_of_ty_own.
    move: r.
    generalize (ltype_rt_agree (BlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.

  Lemma ltype_own_shrblocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own (ShrBlockedLtype ty κ) k π r l ≡ shr_blocked_lty_own ty κ k π r l.
  Proof.
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre. simp lty_own_pre.
    rewrite /shr_blocked_lty_own.
    move: r.
    generalize (ltype_rt_agree (ShrBlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.
  Lemma ltype_own_core_shrblocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own_core (ShrBlockedLtype ty κ) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof.
    rewrite ltype_own_core_unseal /ltype_own_core_def /ltype_own_pre. simp lty_own_pre.
    rewrite /shr_blocked_lty_own.
    move: r.
    generalize (ltype_rt_agree (ShrBlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.

  Lemma ltype_own_pre_box_unfold {rt} (lt : ltype rt) (core : bool) k π r l :
    ltype_own_pre core (BoxLtype lt) k π r l ≡ box_ltype_own (@ltype_own_pre core) (@ltype_own_core) lt k π r l.
  Proof.
    (* NOTE: pay attention to unfold also the core, otherwise we get into trouble with generalizing below *)
    rewrite /box_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    move: r.
    generalize (ltype_rt_agree (BoxLtype lt)).
    generalize (ltype_rt_agree lt). simpl.
    intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros r. repeat f_equiv; done.
  Qed.
  Lemma ltype_own_box_unfold {rt} (lt : ltype rt) k π r l :
    ltype_own (BoxLtype lt) k π r l ≡ box_ltype_own (@ltype_own) (@ltype_own_core) lt k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_box_unfold. Qed.
  Lemma ltype_own_core_box_unfold {rt} (lt : ltype rt) k π r l :
    ltype_own_core (BoxLtype lt) k π r l ≡ box_ltype_own (@ltype_own_core) (@ltype_own_core) lt k π r l.
  Proof. rewrite {1 2}ltype_own_core_unseal. apply ltype_own_pre_box_unfold. Qed.

  Lemma ltype_own_pre_owned_ptr_unfold {rt} (lt : ltype rt) (ls : bool) (core : bool) k π r l :
    ltype_own_pre core (OwnedPtrLtype lt ls) k π r l ≡ owned_ptr_ltype_own (@ltype_own_pre core) (@ltype_own_core) lt ls k π r l.
  Proof.
    (* NOTE: pay attention to unfold also the core, otherwise we get into trouble with generalizing below *)
    rewrite /owned_ptr_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    move: r.
    generalize (ltype_rt_agree (OwnedPtrLtype lt ls)).
    generalize (ltype_rt_agree lt). simpl.
    intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros r. repeat f_equiv; done.
  Qed.
  Lemma ltype_own_owned_ptr_unfold {rt} (lt : ltype rt) (ls : bool) k π r l :
    ltype_own (OwnedPtrLtype lt ls) k π r l ≡ owned_ptr_ltype_own (@ltype_own) (@ltype_own_core) lt ls k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_owned_ptr_unfold. Qed.
  Lemma ltype_own_core_owned_ptr_unfold {rt} (lt : ltype rt) (ls : bool) k π r l :
    ltype_own_core (OwnedPtrLtype lt ls) k π r l ≡ owned_ptr_ltype_own (@ltype_own_core) (@ltype_own_core) lt ls k π r l.
  Proof. rewrite {1 2}ltype_own_core_unseal. apply ltype_own_pre_owned_ptr_unfold. Qed.

  Lemma ltype_own_pre_shr_ref_unfold {rt} (lt : ltype rt) (core : bool) κ k π r l :
    ltype_own_pre core (ShrLtype lt κ) k π r l ≡ shr_ltype_own (@ltype_own_pre core) (@ltype_own_core) lt κ k π r l.
  Proof.
    (* NOTE: pay attention to unfold also the core, otherwise we get into trouble with generalizing below *)
    rewrite /shr_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    move: r.
    generalize (ltype_rt_agree (ShrLtype lt κ)).
    generalize (ltype_rt_agree lt). simpl.
    intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros r. repeat f_equiv; done.
  Qed.
  Lemma ltype_own_shr_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own (ShrLtype lt κ) k π r l ≡ shr_ltype_own (@ltype_own) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_shr_ref_unfold. Qed.
  Lemma ltype_own_core_shr_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own_core (ShrLtype lt κ) k π r l ≡ shr_ltype_own (@ltype_own_core) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite {1 2}ltype_own_core_unseal. apply ltype_own_pre_shr_ref_unfold. Qed.

  Lemma ltype_own_pre_mut_ref_unfold {rt} (lt : ltype rt) (core : bool) κ k π r l :
    ltype_own_pre core (MutLtype lt κ) k π r l ≡ mut_ltype_own (@ltype_own_pre core) (@ltype_own_core) lt κ k π r l.
  Proof.
    (* NOTE: pay attention to unfold also the core, otherwise we get into trouble with generalizing below *)
    rewrite /mut_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    move: r.
    generalize (ltype_rt_agree (MutLtype lt κ)).
    generalize (ltype_rt_agree lt). simpl.
    intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros r. repeat (first [fast_done | f_equiv]).
  Qed.
  Lemma ltype_own_mut_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own (MutLtype lt κ) k π r l ≡ mut_ltype_own (@ltype_own) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_mut_ref_unfold. Qed.
  Lemma ltype_own_core_mut_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own_core (MutLtype lt κ) k π r l ≡ mut_ltype_own (@ltype_own_core) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite {1 2}ltype_own_core_unseal. apply ltype_own_pre_mut_ref_unfold. Qed.

  Lemma StructLtype_StructLty_rfn_eq (rts : list Type) (lts : hlist ltype rts) :
    plist place_rfn rts = plist (λ lt : lty, place_rfn (lty_rt lt)) (@ltype_lty +c<$> lts).
  Proof.
    induction rts as [ | ?? IH]; inv_hlist lts; simpl; first done.
    intros x xl'. f_equiv.
    - rewrite (ltype_rt_agree x); done.
    - apply IH.
  Qed.
  Section structlty.
    (** The unfolding for StructLtype requires a bit of work. We first bring the big_sepL into a shape where we can use [big_sepL_fmap]. *)

    Local Definition lty_own_pre_sig (core : bool) (lt : sigT (λ lt : lty, place_rfn (lty_rt lt))) (k : bor_kind) (π : thread_id) (l : loc) : iProp Σ :=
      lty_own_pre core (projT1 lt) k π (projT2 lt) l.

    Local Definition map_fun : sigT (λ rt : Type, (ltype rt * place_rfn rt)%type) → sigT (λ lt : lty, place_rfn (lty_rt lt)) :=
      (λ x, existT (ltype_lty (projT2 x).1) (rew <- [place_rfn] ltype_rt_agree (projT2 x).1 in (projT2 x).2)).


    Local Lemma StructLtype_fmap_eq {rts : list Type} (lts : hlist ltype rts) (r : plist place_rfn rts) (Heq: plist (λ lt : lty, place_rfn (lty_rt lt)) (@ltype_lty +c<$> lts) = plist place_rfn rts):
      (pzipl (hcmap (@ltype_lty) lts) (rew <-[id] Heq in r)) = fmap map_fun (hpzipl rts lts r).
    Proof.
      induction rts as [ | rt rts IH] in lts, r, Heq |-*.
      { inv_hlist lts. done. }
      inv_hlist lts. intros lt lts Heq2.
      simpl.
      f_equiv.
      - simpl. unfold map_fun. f_equiv.
        simpl. generalize (ltype_rt_agree lt) as Heq3.
        clear.
        intros.
        rewrite phd_rew_commute.
        { rewrite Heq3 //. }
        2: { apply StructLtype_StructLty_rfn_eq. }
        intros Heq4.
        clear. move: Heq4 Heq3.
        generalize (ltype_lty lt) as lt' => lt'.
        intros ? <-. rewrite (UIP_refl _ _ Heq4) //.
      - specialize (IH lts (ptl r)). unfold fmap in IH. rewrite -IH.
        { rewrite -StructLtype_StructLty_rfn_eq. done. }
        intros Heq3.
        f_equiv.
        destruct r as [r tl]. simpl.
        rewrite ptl_rew_commute.
        { rewrite -StructLtype_StructLty_rfn_eq. done. }
        2: { rewrite ltype_rt_agree. done. }
        intros Heq4.
        simpl. clear. move: tl Heq4 Heq3.
        generalize (@ltype_lty +c<$> lts) as l => l.
        intros tl. destruct Heq4.
        intros Heq3. rewrite (UIP_refl _ _ Heq3). done.
    Qed.

    Local Lemma StructLtype_big_sepL_fmap' {rts : list Type} (sl : struct_layout) (lts : hlist ltype rts) (r : plist place_rfn rts) r'
      (Heq2: plist (λ lt : lty, place_rfn (lty_rt lt)) (@ltype_lty +c<$> lts) = plist place_rfn rts)
      (l : loc) (π : thread_id) k core :
      r' = rew <-[id] Heq2 in r →
      ([∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (pzipl (hcmap (@ltype_lty) lts) r')
          (λ ly : layout, existT (UninitLty (UntypedSynType ly)) (PlaceIn ())),
        (∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
        lty_own_pre core (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx sl.(sl_members) i))) ⊣⊢

      ([∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r)
          (λ ly : layout, existT (unit : Type) (UninitLtype (UntypedSynType ly), PlaceIn tt)),
        ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
       lty_own_pre core (ltype_lty (projT2 ty).1) k π (rew <-[place_rfn] ltype_rt_agree (projT2 ty).1 in (projT2 ty).2) (l +ₗ offset_of_idx sl.(sl_members) i)).
    Proof.
      intros ->.
      rewrite StructLtype_fmap_eq.
      rewrite (pad_struct_ext _ _ _ (λ ly : layout, map_fun (existT (unit : Type) (UninitLtype (UntypedSynType ly), PlaceIn ())))).
      2: { intros. unfold map_fun. simpl. f_equiv.
        generalize (ltype_rt_agree (UninitLtype (UntypedSynType ly))).
        simpl. intros Heq3. rewrite (UIP_refl _ _ Heq3). done. }
      rewrite (pad_struct_fmap _ _ _ (λ _, _)).
      simpl. fold map_fun.
      rewrite big_sepL_fmap. done.
    Qed.
  End structlty.

  Lemma ltype_own_pre_struct_unfold {rts : list Type} (lts : hlist ltype rts) (sls : struct_layout_spec) (core : bool) k π r l :
    ltype_own_pre core (StructLtype lts sls) k π r l ≡ struct_ltype_own (@ltype_own_pre core) (@ltype_own_core) lts sls k π r l.
  Proof.
    rewrite /struct_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre. fold (lty_rt).
    generalize (ltype_rt_agree (StructLtype lts sls)) as Heq => Heq.
    assert (Heq2 : plist (λ lt, place_rfn (lty_rt lt)) (hcmap (@ltype_lty) lts) = plist place_rfn rts).
    { rewrite -Heq. done. }
    repeat f_equiv.
    { rewrite hcmap_length. done. }
    (*{ rewrite fmap_hcmap. done. }*)
    (* TODO deduplicate all this stuff *)
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew [id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2.
          intros r'. rewrite (UIP_refl _ _ Heq). done. }
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew <-[id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2.
          intros r'. rewrite (UIP_refl _ _ Heq). done. }
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done.
    }
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & #Hb)".
        iExists (rew [id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2.
          intros r'. rewrite (UIP_refl _ _ Heq). done. }
        iModIntro. iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done.
      - iIntros "(%r' & Hrfn & #Hb)".
        iExists (rew <-[id]Heq2 in r').
        iSplitL "Hrfn".
        { iClear "Hb". move: r'. destruct Heq2.
          intros r'. rewrite (UIP_refl _ _ Heq). done. }
        iModIntro. iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done.
    }
    { move: r. destruct Heq. done. }
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew [id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2. done. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew <-[id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2. done. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done. }
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew [id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2. done. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew <-[id]Heq2 in r').
        iSplitL "Hrfn".
        { move: r'. destruct Heq2. done. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        clear. destruct Heq2. done. }
  Qed.

  Lemma ltype_own_struct_unfold {rts : list Type} (lts : hlist ltype rts) (sls : struct_layout_spec) k π r l :
    ltype_own (StructLtype lts sls) k π r l ≡ struct_ltype_own (@ltype_own) (@ltype_own_core) lts sls k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_struct_unfold. Qed.
  Lemma ltype_own_core_struct_unfold {rts : list Type} (lts : hlist ltype rts) (sls : struct_layout_spec) k π r l :
    ltype_own_core (StructLtype lts sls) k π r l ≡ struct_ltype_own (@ltype_own_core) (@ltype_own_core) lts sls k π r l.
  Proof. rewrite {1 2} ltype_own_core_unseal. apply ltype_own_pre_struct_unfold. Qed.

  Local Lemma ArrayLtype_big_sepL_fmap {rt} (lts : list (ltype rt)) (r : list (place_rfn rt)) core π k ly st l :
    length lts = length r →
    ([∗ list] i↦ ty ∈ zip (map ltype_lty lts) r,
      ∃ Heq : lty_rt ty.1 = rt, ⌜lty_st ty.1 = st⌝ ∗
        lty_own_pre core ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)) ⊣⊢
    ([∗ list] i↦ lt;r' ∈ lts;r, ⌜ltype_st lt = st⌝ ∗
        lty_own_pre core (ltype_lty lt) k π (rew <- [place_rfn] ltype_rt_agree lt in r') (l offset{ly}ₗ i)).
  Proof.
    intros Hlen.
    assert (⌜length lts = length lts⌝ ⊣⊢ (True : iProp Σ))%I as Heq.
    { iSplit; eauto. }
    rewrite big_sepL2_alt.
    rewrite -Hlen. rewrite Heq. rewrite left_id.
    rewrite zip_fmap_l big_sepL_fmap.
    f_equiv. intros ? [lt r']. simpl.
    iSplit.
    { iIntros "(%Heq2 & $ & Hb)". generalize (ltype_rt_agree lt) => Heq3.
      rewrite (UIP_t _ _ _ Heq2 Heq3). done.
    }
    { iIntros "($ & Hb)". iExists _. iFrame. }
  Qed.
  Local Lemma OfTy_ltype_lty {rt} (ty : type rt) :
    ltype_lty (OfTy ty) = OfTyLty ty.
  Proof. done. Qed.
  Lemma ltype_own_pre_array_unfold {rt : Type} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (core : bool) k π r l :
    ltype_own_pre core (ArrayLtype def len lts) k π r l ≡ array_ltype_own (@ltype_own_pre core) (@ltype_own_core) rt def len lts k π r l.
  Proof.
    rewrite /array_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree (ArrayLtype def len lts)).
    fold lty_rt. simpl.
    intros Heq1. rewrite (UIP_refl _ _ Heq1). cbn.
    do 6 f_equiv.
    (*f_equiv.*)
    (*{ rewrite Forall_fmap. iPureIntro. apply Forall_iff. intros []; done. }*)
    f_equiv.
    - do 4 f_equiv.
      f_equiv. f_equiv.
      apply sep_equiv_proper => Hlen.
      rewrite big_sepL_P_eq.
      rewrite -OfTy_ltype_lty.
      rewrite interpret_iml_fmap ArrayLtype_big_sepL_fmap //.
      rewrite interpret_iml_length //.
    - do 3 f_equiv.
      do 2 f_equiv.
      apply sep_equiv_proper => Hlen.
      rewrite big_sepL_P_eq.
      rewrite -OfTy_ltype_lty interpret_iml_fmap ArrayLtype_big_sepL_fmap //.
      rewrite interpret_iml_length//.
    - do 6 f_equiv. all: f_equiv.
      all: f_equiv.
      all: apply sep_equiv_proper => Hlen.
      all: repeat f_equiv; rewrite big_sepL_P_eq.
      all: rewrite -OfTy_ltype_lty interpret_iml_fmap ArrayLtype_big_sepL_fmap//.
      all: rewrite interpret_iml_length//.
  Qed.

  Lemma ltype_own_array_unfold {rt : Type} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) k π r l :
    ltype_own (ArrayLtype def len lts) k π r l ≡ array_ltype_own (@ltype_own) (@ltype_own_core) rt def len lts k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_array_unfold. Qed.
  Lemma ltype_own_core_array_unfold {rt : Type} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) k π r l :
    ltype_own_core (ArrayLtype def len lts) k π r l ≡ array_ltype_own (@ltype_own_core) (@ltype_own_core) rt def len lts k π r l.
  Proof. rewrite {1 2} ltype_own_core_unseal. apply ltype_own_pre_array_unfold. Qed.

  Lemma ltype_own_pre_enum_unfold {rt : Type} (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) (core : bool) k π r l :
    ltype_own_pre core (EnumLtype en tag lte) k π r l ≡ enum_ltype_own (@ltype_own_pre core) (@ltype_own_core) rt en tag lte k π r l.
  Proof.
    rewrite /enum_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree (EnumLtype en tag lte)).
    fold lty_rt. simpl.
    intros Heq1. rewrite (UIP_refl _ _ Heq1). cbn.
    do 1 f_equiv.
    f_equiv.
    iSplit.
    - iIntros "(%rty & %Hels & %Hly & Hlb & %Htag & %Hrt & Hl)".
      destruct rty as (rte & tye).
      iR. iR. iFrame.
      destruct k as [ wl | | ]; [ | done.. ].
      iDestruct "Hl" as "(Hcred & %r' & Hrfn & Ha)".
      iFrame. rewrite Htag. iR. iExists r'. iFrame. iNext.
      iMod ("Ha") as "(<- & %Heq & Ha)".
      iModIntro.
      assert (Heq' : enum_variant_rt en r' = enum_tag_rt en (enum_tag en r')).
      { rewrite -Heq. rewrite ltype_rt_agree. done. }
      iExists Heq'. iR.
      iDestruct "Ha" as "($ & Ha & $)".
      iApply (lty_own_pre_rfn_eq with "Ha").
      apply rew_swap'. rewrite !rew_compose rew_UIP//.
    - iIntros "(%Hels & %Hly & Hlb & %Htag & Hl)".
      destruct Htag as ([rte tye] & Htag).
      iExists (existT rte tye). iR. iR. iFrame. iR.
      specialize (ltype_lty_wf _ (EnumLtype en tag lte)); simpl; intros [_ Hrt].
      iSplitR. { rewrite {1}Hrt /enum_tag_rt/enum_tag_ty' Htag//. }
      destruct k as [ wl | | ]; [ | done.. ].
      iDestruct "Hl" as "(Hcreds & %r' & Hrfn & Hl)".
      iFrame. iExists r'. iFrame.
      iNext. iMod "Hl" as "(%Heq & <- & ? & Hl & ?)".
      iModIntro. iR.
      assert (Heq' : lty_rt (ltype_lty lte) = enum_variant_rt en r').
      { rewrite Hrt. by apply enum_tag_rt_variant_rt_eq. }
      iExists Heq'. iFrame.
      iApply (lty_own_pre_rfn_eq with "Hl").
      apply rew_swap. rewrite !rew_compose rew_UIP//.
  Qed.

  Lemma ltype_own_enum_unfold {rt : Type} (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) k π r l :
    ltype_own (EnumLtype en tag lte) k π r l ≡ enum_ltype_own (@ltype_own) (@ltype_own_core) rt en tag lte k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_enum_unfold. Qed.
  Lemma ltype_own_core_enum_unfold {rt : Type} (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) k π r l :
    ltype_own_core (EnumLtype en tag lte) k π r l ≡ enum_ltype_own (@ltype_own_core) (@ltype_own_core) rt en tag lte k π r l.
  Proof. rewrite {1 2} ltype_own_core_unseal. apply ltype_own_pre_enum_unfold. Qed.

  Lemma ltype_own_opened_unfold {rt_cur rt_inner rt_full : Type} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ) k π r l :
    ltype_own (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) k π r l ≡ opened_ltype_own (@ltype_own) (@ltype_own_core) lt_cur lt_inner lt_full Cpre Cpost k π r l.
  Proof.
    rewrite /opened_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_cur).
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree lt_inner).
    generalize (ltype_rt_agree (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost)).
    simpl.
    intros Heq1 Heq2 Heq3 Heq4. move : Cpre Cpost r.
    move: Heq1 Heq2 Heq3 Heq4.
    intros <- <- <-.
    intros Heq Cpre Cpost r. specialize (UIP_refl _ _ Heq) => ->. clear Heq.
    repeat f_equiv.
    - done.
    - done.
    - iSplit.
      + iIntros "(%Heq1 & %Heq2 & Ha)".
        rewrite (UIP_refl _ _ Heq1) (UIP_refl _ _ Heq2). done.
      + iIntros "Ha". iExists eq_refl, eq_refl. done.
    - iSplit.
      + iIntros "(%Heq1 & %Heq2 & Ha)".
        rewrite (UIP_refl _ _ Heq1) (UIP_refl _ _ Heq2). done.
      + iIntros "Ha". iExists eq_refl, eq_refl. done.
  Qed.
  Lemma ltype_own_core_opened_unfold {rt_cur rt_inner rt_full : Type} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ) k π r l :
    ltype_own_core (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) k π r l ≡ opened_ltype_own (@ltype_own) (@ltype_own_core) lt_cur lt_inner lt_full Cpre Cpost k π r l.
  Proof.
    rewrite -ltype_own_opened_unfold.
    rewrite ltype_own_core_unseal ltype_own_unseal /ltype_own_core_def /ltype_own_def /ltype_own_pre.
    simp lty_own_pre. done.
  Qed.

  Lemma ltype_own_coreable_unfold {rt_full} (κs : list lft) (lt_full : ltype rt_full) k π r l :
    ltype_own (CoreableLtype κs lt_full) k π r l ≡ coreable_ltype_own (@ltype_own) (@ltype_own_core) κs lt_full k π r l.
  Proof.
    rewrite /coreable_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (CoreableLtype κs lt_full)).
    simpl. intros Heq1 Heq2. move: Heq1 Heq2 r.
    intros <- Heq r. rewrite (UIP_refl _ _ Heq). clear Heq.
    done.
  Qed.
  Lemma ltype_own_core_coreable_unfold {rt_full} (κs : list lft) (lt_full : ltype rt_full) k π r l :
    ltype_own_core (CoreableLtype κs lt_full) k π r l ≡ ltype_own_core lt_full k π r l.
  Proof.
    rewrite /coreable_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (CoreableLtype κs lt_full)).
    simpl. intros Heq1 Heq2. move : Heq1 Heq2 r. intros <- Heq r.
    rewrite (UIP_refl _ _ Heq). done.
  Qed.

  Lemma ltype_own_shadowed_unfold {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) k π r l :
    ltype_own (ShadowedLtype lt_cur r_cur lt_full) k π r l ≡ shadowed_ltype_own (@ltype_own) (@ltype_own_core) lt_cur r_cur lt_full k π r l.
  Proof.
    rewrite /shadowed_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_cur).
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (ShadowedLtype lt_cur r_cur lt_full)).
    simpl. intros Heq1 Heq2 Heq3. move: Heq1 Heq2 Heq3 r r_cur. intros <- Heq <-.
    rewrite (UIP_refl _ _ Heq). cbn. intros ??.
    iSplit.
    - iIntros "(%Heq' & ?)". rewrite (UIP_refl _ _ Heq'). iFrame.
    - iIntros "?". iExists eq_refl. done.
  Qed.
  Lemma ltype_own_core_shadowed_unfold {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) k π r l :
    ltype_own_core (ShadowedLtype lt_cur r_cur lt_full) k π r l ≡ ltype_own_core lt_full k π r l.
  Proof.
    rewrite /shadowed_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (ShadowedLtype lt_cur r_cur lt_full)).
    intros Heq1 Heq2. move: Heq1 Heq2 r. intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros ?. done.
  Qed.

  (** Lifting basic lemmas to [ltype] *)

  (* NOTE: This does not hold true for [OpenedLtype]! *)
  Lemma ltype_own_pre_shr_pers core {rt} (lt : ltype rt) κ π r l :
    (*match lt.(ltype_lty) with OpenedLty _ _ _ _ _ => False | _ => True end →*)
    Persistent (ltype_own_pre core lt (Shared κ) π r l).
  Proof. rewrite /ltype_own_pre. apply lty_own_pre_shr_pers. Qed.
  Global Instance ltype_own_shr_pers {rt} (lt : ltype rt) κ π r l :
    (*TCDone (match lt.(ltype_lty) with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (ltype_own lt (Shared κ) π r l).
  Proof. rewrite ltype_own_unseal. apply ltype_own_pre_shr_pers. Qed.
  Global Instance ltype_own_core_shr_pers {rt} (lt : ltype rt) κ π r l :
    (*TCDone (match lt.(ltype_lty) with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (ltype_own_core lt (Shared κ) π r l).
  Proof. rewrite ltype_own_core_unseal. apply ltype_own_pre_shr_pers. Qed.

  Lemma ltype_core_idemp {rt} (lt : ltype rt) :
    ltype_core (ltype_core lt) = ltype_core lt.
  Proof.
    destruct lt as [lt Heq Hwf].
    rewrite /ltype_core /=.
    specialize (lty_core_idemp lt) as Heq2.
    match goal with
    | |- context[ltype_core_obligation_1 ?H1 ?H2] => generalize (ltype_core_obligation_1 H1 H2) as Heq3
    end.
    simpl. intros Heq3.
    match goal with
    | |- context[ltype_core_obligation_1 ?H1 ?H2] => generalize (ltype_core_obligation_1 H1 H2) as Heq4
    end. intros Heq4.
    match goal with
    | |- context[ltype_core_obligation_2 ?H1 ?H2] => generalize (ltype_core_obligation_2 H1 H2) as Hwf1
    end; simpl.
    intros Hwf1.
    match goal with
    | |- context[ltype_core_obligation_2 ?H1 ?H2] => generalize (ltype_core_obligation_2 H1 H2) as Hwf2
    end; simpl.
    intros Hwf2.
    move: Hwf Heq2 Heq3 Heq4 Hwf1 Hwf2.
    subst. simpl.
    generalize (lty_core lt) as l => lt'.
    intros _ -> Heq3 Heq4 Hwf1 Hwf2.
    rewrite (UIP_t _ _ _ Heq3 Heq4).
    (* TODO uses proof irrelevance, can we avoid that? *)
    rewrite (proof_irrelevance _ Hwf1 Hwf2). done.
  Qed.

  Lemma ltype_own_has_layout {rt} (lt : ltype rt) k π r l :
    ltype_own lt k π r l -∗ ∃ ly : layout, ⌜syn_type_has_layout (ltype_st lt) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝.
  Proof.
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre.
    iIntros "Hown". iPoseProof lty_own_has_layout as "Ha".
    by iApply "Ha".
  Qed.
  Lemma ltype_own_has_layout' {rt} (lt : ltype rt) k π r l ly :
    syn_type_has_layout (ltype_st lt) ly →
    ltype_own lt k π r l -∗ ⌜l `has_layout_loc` ly⌝.
  Proof.
    iIntros (Hst) "Hown". iPoseProof (ltype_own_has_layout with "Hown") as "(%ly' & % & %)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj. done.
  Qed.

  Lemma ltype_own_loc_in_bounds {rt} (lt : ltype rt) k π r l ly :
    syn_type_has_layout (ltype_st lt) ly →
    ltype_own lt k π r l -∗ loc_in_bounds l 0 ly.(ly_size).
  Proof.
    iIntros (?) "Hown".
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre.
    iPoseProof lty_own_loc_in_bounds as "Ha"; first done.
    by iApply "Ha".
  Qed.

  Lemma ltype_core_syn_type_eq {rt} (lt : ltype rt) :
    ltype_st (ltype_core lt) = ltype_st lt.
  Proof.
    rewrite /ltype_st /ltype_core /= lty_core_syn_type_eq //.
  Qed.

  Lemma ltype_own_shared_to_core {rt} (lt : ltype rt) κ0 π r l :
    ltype_own lt (Shared κ0) π r l -∗ ltype_own (ltype_core lt) (Shared κ0) π (r) l.
  Proof.
    iIntros "Ha".
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre.
    assert (Heq2 : lty_rt (ltype_lty lt) = lty_rt (lty_core (ltype_lty lt))).
    { (rewrite lty_core_rt_eq//). }
    unshelve iPoseProof (lty_own_shared_to_core _ _ _ _ _  with "Ha") as "Ha"; first done.
    revert r Heq2.
    generalize (lty_core_rt_eq (ltype_lty lt)).
    generalize (ltype_rt_agree (ltype_core lt)).
    generalize (ltype_rt_agree lt).
    destruct lt; simpl.
    intros Heq0. subst.
    intros Heq _. destruct Heq. intros ? Heq2.
    rewrite (UIP_refl _ _ Heq2).
    rewrite (UIP_refl _ _ Heq0).
    done.
  Qed.

  Lemma ltype_own_Owned_true_false {rt} (lt : ltype rt) π r l :
    match ltype_lty lt with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end →
    ltype_own lt (Owned true) π r l -∗
    have_creds ∗ ▷ ltype_own lt (Owned false) π r l.
  Proof.
    rewrite ltype_own_unseal/ltype_own_def/=.
    rewrite /ltype_own_pre.
    apply lty_own_Owned_true_false.
  Qed.
  Lemma ltype_own_Owned_false_true {rt} (lt : ltype rt) π r l :
    match ltype_lty lt with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | _ => True end →
    ltype_own lt (Owned false) π r l -∗
    have_creds -∗
    ltype_own lt (Owned true) π r l.
  Proof.
    rewrite ltype_own_unseal/ltype_own_def/=.
    rewrite /ltype_own_pre.
    apply lty_own_Owned_false_true.
  Qed.

  (** Rules for ltype_core *)
  (** Since [ltype]s bundle equality proofs, [ltype_core] does not compute well, and we need equational lemmas instead. *)
  Lemma ltype_core_ofty {rt} (ty : type rt) :
    ltype_core (OfTy ty) = OfTy ty.
  Proof.
    rewrite /ltype_core /OfTy. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_alias (rt : Type) (st : syn_type) (p : loc) :
    ltype_core (AliasLtype rt st p) = AliasLtype rt st p.
  Proof.
    rewrite /ltype_core /AliasLtype. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_blocked {rt} (ty : type rt) (κ : lft) :
    ltype_core (BlockedLtype ty κ) = OfTy ty.
  Proof.
    rewrite /ltype_core /BlockedLtype /OfTy. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_shrblocked {rt} (ty : type rt) (κ : lft) :
    ltype_core (ShrBlockedLtype ty κ) = OfTy ty.
  Proof.
    rewrite /ltype_core /ShrBlockedLtype /OfTy. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_box {rt} (lt : ltype rt) :
    ltype_core (BoxLtype lt) = BoxLtype (ltype_core lt).
  Proof.
    rewrite /ltype_core /BoxLtype /=. f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_owned_ptr {rt} (lt : ltype rt) (ls : bool) :
    ltype_core (OwnedPtrLtype lt ls) = OwnedPtrLtype (ltype_core lt) ls.
  Proof.
    rewrite /ltype_core /OwnedPtrLtype /=. f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_mut_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_core (MutLtype lt κ) = MutLtype (ltype_core lt) κ.
  Proof.
    rewrite /ltype_core /MutLtype /=. f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_shr_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_core (ShrLtype lt κ) = ShrLtype (ltype_core lt) κ.
  Proof.
    rewrite /ltype_core /ShrLtype /=. f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_struct {rts} (lts : hlist ltype rts) (sls : struct_layout_spec) :
    ltype_core (StructLtype lts sls) = StructLtype (hmap (@ltype_core) lts) sls.
  Proof.
    rewrite /ltype_core /StructLtype /=.
    match goal with
    | |- mk_ltype _ ?lt1 ?H1 ?H3 = mk_ltype _ ?lt2 ?H2 ?H4 =>
        generalize H1 as Heq1; generalize H2 as Heq2;
        generalize H3 as Hwf1; generalize H4 as Hwf2
    end; simpl.
    intros Hwf1 Hwf2 <-. simpl.
    move: Hwf1 Hwf2.
    rewrite hcmap_hmap fmap_hcmap. simpl.
    intros Hwf1 Hwf2 Heq. rewrite (UIP_refl _ _ Heq).
    f_equiv. apply proof_irrelevance.
  Qed.

  Lemma ltype_lty_core {rt} (lt : ltype rt) :
    ltype_lty (ltype_core lt) = lty_core (ltype_lty lt).
  Proof. done. Qed.

  Lemma ltype_core_array {rt} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) :
    ltype_core (ArrayLtype def len lts) = ArrayLtype def len ((λ '(i, lt), (i, ltype_core lt)) <$> lts).
  Proof.
    rewrite /ltype_core /ArrayLtype /=.
    match goal with
    | |- mk_ltype _ ?lt1 ?H1 ?H3 = mk_ltype _ ?lt2 ?H2 ?H4 =>
        generalize H1 as Heq1; generalize H2 as Heq2;
        generalize H3 as Hwf1; generalize H4 as Hwf2
    end; simpl.
    intros Hwf1 Hwf2 <-. simpl.
    move: Hwf1 Hwf2.
    rewrite !map_fmap !map_map.

    rewrite (map_ext _  ((λ x : nat * ltype rt, let '(i, lt) := let '(i, lt) := x in (i, ltype_lty lt) in (i, lty_core lt)))); first last.
    { intros []. done. }
    intros Hwf1 Hwf2 Heq1.
    rewrite (UIP_refl _ _ Heq1).
    specialize (proof_irrelevance _  Hwf1 Hwf2) as ?. subst.
    done.
  Qed.
  Lemma ltype_core_enum {rt} (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) :
    ltype_core (EnumLtype en tag lte) = EnumLtype en tag (ltype_core lte).
  Proof.
    rewrite /ltype_core /EnumLtype /=.
    match goal with
    | |- mk_ltype _ ?lt1 ?H1 ?H3 = mk_ltype _ ?lt2 ?H2 ?H4 =>
        generalize H1 as Heq1; generalize H2 as Heq2;
        generalize H3 as Hwf1; generalize H4 as Hwf2
    end; simpl.
    intros [Hwf1 Hrt1] [Hwf2 Hrt2] Heq1 Heq2.
    rewrite (UIP_refl _ _ Heq1).
    rewrite (UIP_refl _ _ Heq2).
    f_equiv. apply proof_irrelevance.
  Qed.
  Lemma ltype_core_opened {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost :
    ltype_core (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) = OpenedLtype lt_cur lt_inner lt_full Cpre Cpost.
  Proof.
    rewrite /ltype_core /OpenedLtype /=.
    f_equiv; simpl.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_coreable {rt_full} (κs : list lft) (lt_full : ltype rt_full) :
    ltype_core (CoreableLtype κs lt_full) = ltype_core lt_full.
  Proof.
    rewrite /ltype_core /CoreableLtype /=.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_shadowed {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) :
    ltype_core (ShadowedLtype lt_cur r_cur lt_full) = ltype_core lt_full.
  Proof.
    rewrite /ltype_core /ShadowedLtype /=.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_uninit st :
    ltype_core (UninitLtype st) = UninitLtype st.
  Proof.
    rewrite /ltype_core. simpl. apply mk_ltype_irrel.
  Qed.

  (** Rules for ltype_st *)
  Lemma ltype_st_ofty {rt} (ty : type rt) :
    ltype_st (OfTy ty) = ty.(ty_syn_type).
  Proof. done. Qed.
  Lemma ltype_st_alias rt st p :
    ltype_st (AliasLtype rt st p) = st.
  Proof. done. Qed.
  Lemma ltype_st_blocked {rt} (ty : type rt) (κ : lft) :
    ltype_st (BlockedLtype ty κ) = ty.(ty_syn_type).
  Proof. done. Qed.
  Lemma ltype_st_shrblocked {rt} (ty : type rt) (κ : lft) :
    ltype_st (ShrBlockedLtype ty κ) = ty.(ty_syn_type).
  Proof. done. Qed.
  Lemma ltype_st_box {rt} (lt : ltype rt) :
    ltype_st (BoxLtype lt) = PtrSynType.
  Proof. done. Qed.
  Lemma ltype_st_owned_ptr {rt} (lt : ltype rt) (ls : bool) :
    ltype_st (OwnedPtrLtype lt ls) = PtrSynType.
  Proof. done. Qed.
  Lemma ltype_st_mut_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_st (MutLtype lt κ) = PtrSynType.
  Proof. done. Qed.
  Lemma ltype_st_shr_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_st (ShrLtype lt κ) = PtrSynType.
  Proof. done. Qed.
  Lemma ltype_st_struct {rts} (lts : hlist ltype rts) (sls : struct_layout_spec) :
    ltype_st (StructLtype lts sls) = sls.
  Proof. done. Qed.
  Lemma ltype_st_array {rt} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) :
    ltype_st (ArrayLtype def len lts) = ArraySynType (ty_syn_type def) len.
  Proof. rewrite /ltype_st /= //. Qed.
  Lemma ltype_st_enum {rt} (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) :
    ltype_st (EnumLtype en tag lte) = en.(enum_els).
  Proof. rewrite /ltype_st /= //. Qed.
  Lemma ltype_st_opened {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost :
    ltype_st (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) = ltype_st lt_cur.
  Proof. done. Qed.
  Lemma ltype_st_coreable {rt_full} κs (lt_full : ltype rt_full) :
    ltype_st (CoreableLtype κs lt_full) = ltype_st lt_full.
  Proof. done. Qed.
  Lemma ltype_st_shadowed {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) :
    ltype_st (ShadowedLtype lt_cur r_cur lt_full) = ltype_st lt_full.
  Proof. done. Qed.

  (** Lifting the core equations to ltypes *)
  Lemma ltype_own_core_equiv {rt} (lt : ltype rt) k π r l :
    ltype_own_core lt k π r l ≡ ltype_own (ltype_core lt) k π r l.
  Proof.
    rewrite ltype_own_unseal ltype_own_core_unseal /ltype_own_core_def /ltype_own_def.
    assert (Heq : lty_rt (ltype_lty lt) = lty_rt (lty_core (ltype_lty lt))).
    { rewrite lty_core_rt_eq. done. }
    unshelve rewrite /ltype_own_pre (lty_own_core_equiv _ false); first apply Heq.
    simpl. iApply lty_own_pre_rfn_eq'.
    move: Heq.
    generalize (ltype_rt_agree lt) as Heq2.
    generalize (ltype_rt_agree (ltype_core lt)) as Heq2.
    simpl. rewrite lty_core_rt_eq.
    intros Heq1 Heq2 Heq3. rewrite (UIP_t _ _ _  Heq1 Heq2).
    rewrite (UIP_refl _ _ Heq3). done.
  Qed.
  Lemma ltype_own_core_core {rt} (lt : ltype rt) k π r l :
    ltype_own_core (ltype_core lt) k π r l ≡ ltype_own_core lt k π r l.
  Proof.
    rewrite ltype_own_core_unseal /ltype_own_core_def.
    assert (Heq : lty_rt (lty_core (ltype_lty lt)) = lty_rt (ltype_lty lt)).
    { rewrite lty_core_rt_eq. done. }
    unshelve rewrite /ltype_own_pre lty_own_core_core'; first apply Heq.
    simpl. iApply lty_own_pre_rfn_eq'.
    move: Heq.
    generalize (ltype_rt_agree lt) as Heq2.
    generalize (ltype_rt_agree (ltype_core lt)) as Heq2.
    simpl. rewrite lty_core_rt_eq.
    intros Heq1 Heq2 Heq3. rewrite (UIP_t _ _ _  Heq1 Heq2).
    rewrite (UIP_refl _ _ Heq3). done.
  Qed.


  (** Compute the lifetimes at which there are blocked components of an lty. *)
  Fixpoint lty_blocked_lfts (lt : lty) : list lft :=
    match lt with
    | OfTyLty ty => []
    | AliasLty _ _ _ => []
    | BlockedLty ty κ => [κ]
    | ShrBlockedLty ty κ => [κ]
    | BoxLty lt => lty_blocked_lfts lt
    | OwnedPtrLty lt ls => lty_blocked_lfts lt
    | MutLty lt κ => lty_blocked_lfts lt
    | ShrLty lt κ => lty_blocked_lfts lt
    | StructLty lts sls => concat (map lty_blocked_lfts lts)
    | ArrayLty def len lts => concat (map (λ '(_, lt), lty_blocked_lfts lt) lts)
    | EnumLty en tag lte => lty_blocked_lfts lte
    | OpenedLty _ _ _ _ _  => []
    | CoreableLty κs _ => κs
    | ShadowedLty lt_cur r_cur lt_full => lty_blocked_lfts lt_full
    end.

  Definition ltype_blocked_lfts {rt} (lt : ltype rt) : list lft :=
    lty_blocked_lfts (lt.(ltype_lty)).

  (** ** Deinitialization of ltypes *)
  Definition lty_uniq_deinitializable (lt : lty) : Prop :=
    match lt with
    | BlockedLty _ _  => False
    | ShrBlockedLty _ _ => False
    | OfTyLty _ => True
    | AliasLty _ _ _ => False
    | MutLty _ _ => True
    | ShrLty _ _ => True
    | BoxLty _  =>
        (* honestly, it is a bug to get into this case. We should not just drop a box, but the drop glue should be called. *)
        False
    | OwnedPtrLty _ _ => True
    | StructLty lts sls =>
        True
    | ArrayLty def len lts =>
        True
    | EnumLty en tag lte =>
        True
    | OpenedLty _ _ _ _ _ => False
    | CoreableLty _ _ => True
    | ShadowedLty lt _ _ =>
        False
    end.
  Definition ltype_uniq_deinitializable {rt} (lt : ltype rt) :=
    lty_uniq_deinitializable lt.(ltype_lty).

  Lemma lty_own_deinit_ghost_drop_uniq π F (lt : lty) κ γ r l :
    lftE ⊆ F →
    lty_uniq_deinitializable lt →
    lty_own lt (Uniq κ γ) π r l ={F}=∗
    place_rfn_interp_mut r γ.
  Proof.
    intros ? Hdeinit.
    induction lt using lty_induction; simpl; try done.
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & ? & Hcred & $ & Hl)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & Hlb & Hcred & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      iDestruct 1 as "(%el & %rty & ? & ? & ? & ? & ? & [])".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & ? & ? & $ & _)".
  Qed.
  Lemma ltype_own_deinit_ghost_drop_uniq π F {rt} (lt : ltype rt) κ γ r l :
    lftE ⊆ F →
    ltype_uniq_deinitializable lt →
    ltype_own lt (Uniq κ γ) π r l ={F}=∗
    place_rfn_interp_mut r γ.
  Proof.
    iIntros (??) "Hown".
    iPoseProof (lty_own_deinit_ghost_drop_uniq _ _ (lt.(ltype_lty)) with "[Hown]") as "Ha";
      [done | done | ..].
    { rewrite ltype_own_unseal. done. }
    destruct lt; subst; eauto.
  Qed.

  Definition lty_uniq_extractable (lt : lty) : option (option lft) :=
    match lt with
    | BlockedLty _ κ  => Some (Some κ)
    | ShrBlockedLty _ _ => Some None
    | OfTyLty _ => Some (None)
    | AliasLty _ _ _ => None
    | MutLty _ _ => Some None
    | ShrLty _ _ => Some None
    | BoxLty _  =>
        (* TODO honestly, it is a bug to get into this case. We should not just drop a box, but the drop glue should be called. *)
        Some None
    | OwnedPtrLty _ _ => Some None
    | StructLty lts sls =>
        Some None
    | ArrayLty def len lts =>
        Some None
    | EnumLty en tag lte =>
        Some None
    | OpenedLty _ _ _ _ _ => None
    | CoreableLty _ _ => Some None
    | ShadowedLty lt _ _ =>
        None
    end.
  Definition ltype_uniq_extractable {rt} (lt : ltype rt) : option (option lft) :=
    lty_uniq_extractable lt.(ltype_lty).


  Inductive inherit_ghost := InheritGhost.
  Lemma lty_own_extract_ghost_drop_uniq π F (lt : lty) κ κm γ r l :
    lftE ⊆ F →
    lty_uniq_extractable lt = Some κm →
    lty_own lt (Uniq κ γ) π r l ={F}=∗
    (MaybeInherit (κm) InheritGhost (place_rfn_interp_mut r γ)).
  Proof.
    intros ? Hdeinit.
    rewrite /MaybeInherit/Inherit.
    induction lt using lty_induction; simpl; simpl in Hdeinit; try done.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-. simpl.
      iIntros "(%ly & %Halg & %Hly & ? & ? & Hinh & Hcred & Hl)".
      iModIntro. iIntros (??) "Ha".
      iMod (fupd_mask_mono with "(Hinh Ha)") as "($ & _)"; first done.
      done.
    - rewrite /lty_own. simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & ? & Hlb & (%r' & Hrfn & Hobs & Hb))". injection Hdeinit as <-.
      iModIntro. iIntros (??). simpl.
      done.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hr & Hb)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hb)". injection Hdeinit as <-.
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hb)". injection Hdeinit as <-.
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hb)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%el & %rty & ? & ? & ? & ? & ? & [])".
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
  Qed.
  Lemma ltype_own_extract_ghost_drop_uniq π F {rt} (lt : ltype rt) κ κm γ r l :
    lftE ⊆ F →
    ltype_uniq_extractable lt = Some κm →
    ltype_own lt (Uniq κ γ) π r l ={F}=∗
    MaybeInherit κm InheritGhost (place_rfn_interp_mut r γ).
  Proof.
    iIntros (??) "Hown".
    iPoseProof (lty_own_extract_ghost_drop_uniq _ _ (lt.(ltype_lty)) with "[Hown]") as "Ha";
      [done | done | ..].
    { rewrite ltype_own_unseal. done. }
    destruct lt; subst; eauto.
  Qed.
End ltype_def.

Notation "# x" := (PlaceIn x) (at level 9) : stdpp_scope.
Notation "'<#>' x" := (fmap (M := list) PlaceIn x) (at level 30).
Notation "'<#>@{' A '}' x" := (fmap (M := A) PlaceIn x) (at level 30).
Notation "👻 γ" := (PlaceGhost γ) (at level 9) : stdpp_scope.
Notation "◁ ty" := (OfTy ty) (at level 15) : bi_scope.

Notation "l ◁ₗ[ π , k ]  r  @  ty" := (ltype_own ty k π r l) (at level 15) : bi_scope.
Notation "l ◁ₗ[ π , k ]  .@  ty" := (ltype_own ty k π (PlaceIn ()) l) (at level 15) : bi_scope.

(** Ltac for simplifying some of the Ltac functions that don't compute *)
Ltac simp_ltype_core Heq :=
  cbn in Heq;
  repeat lazymatch type of Heq with
  | _ = ltype_core (ltype_core _) =>
      rewrite ltype_core_idemp in Heq
  | _ = ltype_core (OfTy _) =>
      rewrite ltype_core_ofty in Heq
  | _ = ltype_core (AliasLtype _ _ _) =>
      rewrite ltype_core_alias in Heq
  | _ = ltype_core (BlockedLtype _ _) =>
      rewrite ltype_core_blocked in Heq
  | _ = ltype_core (ShrBlockedLtype _ _) =>
      rewrite (ltype_core_shrblocked) in Heq
  | _ = ltype_core (BoxLtype _) =>
      rewrite (ltype_core_box) in Heq
  | _ = ltype_core (OwnedPtrLtype _ _) =>
      rewrite (ltype_core_owned_ptr) in Heq
  | _ = ltype_core (MutLtype _ _) =>
      rewrite (ltype_core_mut_ref) in Heq
  | _ = ltype_core (ShrLtype _ _) =>
      rewrite (ltype_core_shr_ref) in Heq
  | _ = ltype_core (StructLtype _ _) =>
      rewrite (ltype_core_struct) in Heq
  | _ = ltype_core (ArrayLtype _ _ _) =>
      rewrite (ltype_core_array) in Heq
  | _ = ltype_core (EnumLtype _ _ _) =>
      rewrite ltype_core_enum in Heq
  | _ = ltype_core (OpenedLtype _ _ _ _ _) =>
      rewrite (ltype_core_opened) in Heq
  | _ = ltype_core (CoreableLtype _ _) =>
      rewrite (ltype_core_coreable) in Heq
  | _ = ltype_core (ShadowedLtype _ _ _) =>
      rewrite (ltype_core_shadowed _ _ _) in Heq
  end.
Ltac simp_ltype_st Heq :=
  cbn in Heq;
  repeat lazymatch type of Heq with
  | _ = ltype_st (ltype_core _) =>
      rewrite ltype_core_syn_type_eq in Heq
  | _ = ltype_st (OfTy _) =>
      rewrite ltype_st_ofty in Heq
  | _ = ltype_st (AliasLtype _ _ _) =>
      rewrite ltype_st_alias in Heq
  | _ = ltype_st (BlockedLtype _ _) =>
      rewrite ltype_st_blocked in Heq
  | _ = ltype_st (ShrBlockedLtype _ _) =>
      rewrite (ltype_st_shrblocked) in Heq
  | _ = ltype_st (OwnedPtrLtype _ _) =>
      rewrite (ltype_st_owned_ptr) in Heq
  | _ = ltype_st (MutLtype _ _) =>
      rewrite (ltype_st_mut_ref) in Heq
  | _ = ltype_st (ShrLtype _ _) =>
      rewrite (ltype_st_shr_ref) in Heq
  | _ = ltype_st (StructLtype _ _) =>
      rewrite (ltype_st_struct) in Heq; simpl in Heq
  | _ = ltype_st (ArrayLtype _ _ _) =>
      rewrite (ltype_st_array) in Heq; simpl in Heq
  | _ = ltype_st (EnumLtype _ _ _) =>
      rewrite (ltype_st_enum) in Heq; simpl in Heq
  | _ = ltype_st (OpenedLtype _ _ _ _ _) =>
      rewrite (ltype_st_opened) in Heq
  | _ = ltype_st (CoreableLtype _ _) =>
      rewrite (ltype_st_coreable) in Heq
  | _ = ltype_st (ShadowedLtype _ _ _) =>
      rewrite (ltype_st_shadowed _ _ _) in Heq
  end.

Ltac simp_ltype :=
  match goal with
  | |- context[ltype_core ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_core lt) as ltc eqn:Heq;
      simp_ltype_core Heq;
      subst ltc
  | |- context[ltype_st ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_st lt) as ltc eqn:Heq;
      simp_ltype_st Heq;
      subst ltc
  end.
Ltac simp_ltypes := repeat simp_ltype.

Tactic Notation "simp_ltype" "in" hyp(H) :=
  match type of H with
  | context[ltype_core ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_core lt) as ltc eqn:Heq in H;
      simp_ltype_core Heq;
      subst ltc
  | context[ltype_st ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_st lt) as ltc eqn:Heq in H;
      simp_ltype_st Heq;
      subst ltc
  end.
Tactic Notation "simp_ltypes" "in" hyp(H) := repeat simp_ltype in H.

(** ** Ltype subtyping *)
Definition ltype_incl' `{!typeGS Σ} {rt1 rt2 : Type} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : iProp Σ :=
  (□
    match b with
    | Owned wl =>
      ∀ π l, ltype_own lt1 (Owned wl) π r1 l ={lftE}=∗ ltype_own lt2 (Owned wl) π r2 l
    | Uniq κ γ =>
      ∀ π l, ltype_own lt1 (Uniq κ γ) π r1 l -∗ ltype_own lt2 (Uniq κ γ) π r2 l
    | Shared κ =>
      ∀ π l, ltype_own lt1 (Shared κ) π r1 l -∗ ltype_own lt2 (Shared κ) π r2 l
    end).

Definition ltype_incl `{!typeGS Σ} {rt1 rt2 : Type} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : iProp Σ :=
  (□ (* same layout *)
  (⌜ltype_st lt1 = ltype_st lt2⌝ ∗
   ltype_incl' b r1 r2 lt1 lt2 ∗
   ltype_incl' b r1 r2 (ltype_core lt1) (ltype_core lt2)
  )).
Global Instance ltype_incl_persistent `{!typeGS Σ} {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Persistent (ltype_incl b r1 r2 lt1 lt2) := _.

Definition ltype_eq `{!typeGS Σ} {rt1 rt2 : Type} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : iProp Σ :=
  ltype_incl b r1 r2 lt1 lt2 ∗ ltype_incl b r2 r1 lt2 lt1.
Global Instance ltype_eq_persistent `{!typeGS Σ} {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Persistent (ltype_eq b r1 r2 lt1 lt2) := _.

(** Heterogeneous ltype equality *)
Definition eqltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ (rrust_ctx -∗ elctx_interp E -∗ ltype_eq b r1 r2 lt1 lt2).
#[export]
Instance: Params (@eqltype) 6 := {}.

(** Homogeneous ltype equality, disregarding the refinement and borkind *)
Definition full_eqltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ∀ b r, ltype_eq b r r lt1 lt2.
#[export]
Instance: Params (@full_eqltype) 5 := {}.

(** Heterogeneous ltype subtyping *)
Definition subltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ (elctx_interp E -∗ ltype_incl b r1 r2 lt1 lt2).
#[export]
Instance: Params (@subltype) 6 := {}.

(** Homogeneous ltype subtyping, disregarding the refinement and borkind *)
Definition full_subltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ∀ b r, ltype_incl b r r lt1 lt2.
#[export]
Instance: Params (@full_subltype) 5 := {}.

Lemma ltype_incl'_use `{!typeGS Σ} {rt1 rt2} F (lt1 : ltype rt1) (lt2 : ltype rt2) l π b r1 r2 :
  lftE ⊆ F →
  ltype_incl' b r1 r2 lt1 lt2 -∗
  l ◁ₗ[π, b] r1 @ lt1 ={F}=∗
  l ◁ₗ[π, b] r2 @ lt2.
Proof.
  iIntros (?) "#Hincl Hl".
  iMod (fupd_mask_subseteq lftE) as "Hcl"; first done.
  destruct b.
  - iMod ("Hincl" with "Hl") as "$". by iMod "Hcl".
  - iMod "Hcl". iModIntro. by iApply "Hincl".
  - iMod "Hcl". iModIntro. by iApply "Hincl".
Qed.
Lemma ltype_incl_use `{!typeGS Σ} {rt1 rt2} π F b r1 r2 l (lt1 : ltype rt1) (lt2 : ltype rt2) :
  lftE ⊆ F →
  ltype_incl b r1 r2 lt1 lt2 -∗
  l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2.
Proof.
  iIntros (?) "Hincl Ha".
  iDestruct "Hincl" as "(_ & #Hincl & _)".
  destruct b.
  - iApply (fupd_mask_mono with "(Hincl Ha)"); done.
  - by iApply "Hincl".
  - by iApply "Hincl".
Qed.
Lemma ltype_incl_use_core `{!typeGS Σ} {rt1 rt2} π F b r1 r2 l (lt1 : ltype rt1) (lt2 : ltype rt2) :
  lftE ⊆ F →
  ltype_incl b r1 r2 lt1 lt2 -∗
  l ◁ₗ[π, b] r1 @ ltype_core lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ ltype_core lt2.
Proof.
  iIntros (?) "Hincl Ha".
  iDestruct "Hincl" as "(_ & _ & #Hincl)".
  destruct b.
  - iApply (fupd_mask_mono with "(Hincl Ha)"); done.
  - by iApply "Hincl".
  - by iApply "Hincl".
Qed.


Section accessors.
  Context `{!typeGS Σ}.
  Lemma subltype_use {rt1 rt2} F E L b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    lftE ⊆ F →
    subltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    □ ∀ π l, l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2.
  Proof.
    iIntros (? Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "#Hincl".
    iModIntro. iIntros (π l). iApply ltype_incl_use; done.
  Qed.
  Lemma subltype_use_core {rt1 rt2} F E L b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    lftE ⊆ F →
    subltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    □ ∀ π l, l ◁ₗ[π, b] r1 @ ltype_core lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ ltype_core lt2.
  Proof.
    iIntros (? Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "#Hincl".
    iModIntro. iIntros (π l). iApply ltype_incl_use_core; done.
  Qed.

  Lemma subltype_acc {rt1 rt2} E L b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    subltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ltype_incl b r1 r2 lt1 lt2.
  Proof.
    iIntros (Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "#Hincl". done.
  Qed.
  Lemma full_subltype_acc E L {rt} (lt1 lt2 : ltype rt) :
    full_subltype E L lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ∀ b r, ltype_incl b r r lt1 lt2.
  Proof.
    iIntros (Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "#Hincl".
    iIntros (b r). iApply "Hincl".
  Qed.

  Lemma eqltype_use_noend F E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) qL l π :
    lftE ⊆ F →
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    (l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2) ∗
    llctx_interp_noend L qL.
  Proof.
    iIntros (? Hunfold) "#CTX #HE HL".
    iPoseProof (Hunfold with "HL CTX HE") as "#Hll". iFrame.
    iIntros "Hl".
    iDestruct "Hll" as "((_ & #Ha & _) & _)".
    destruct b.
    - iMod (fupd_mask_subseteq lftE) as "Hcl"; first solve_ndisj.
      iMod ("Ha" with "Hl") as "$". by iMod "Hcl" as "_".
    - by iApply "Ha".
    - by iApply "Ha".
  Qed.
  Lemma eqltype_use F E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) l π :
    lftE ⊆ F →
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    (l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2) ∗
    llctx_interp L.
  Proof.
    iIntros (? Hunfold) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (eqltype_use_noend with "CTX HE HL") as "($ & HL)"; [done.. | ].
    by iApply "HL_cl".
  Qed.
  Lemma eqltype_acc E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ltype_eq b r1 r2 lt1 lt2.
  Proof.
    iIntros (Heq) "CTX HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iApply (Heq with "HL CTX HE").
  Qed.
  Lemma full_eqltype_acc E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ∀ b r, ltype_eq b r r lt1 lt2.
  Proof.
    iIntros (Heq) "CTX HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iApply (Heq with "HL CTX HE").
  Qed.

  Lemma all_ltype_eq_alt {rt} b (lt1 lt2 : ltype rt) :
    (∀ r, ltype_eq b r r lt1 lt2) ⊣⊢ (∀ r, ltype_incl b r r lt1 lt2) ∧ (∀ r, ltype_incl b r r lt2 lt1).
  Proof.
    iSplit.
    - iIntros "#Ha". iSplit; iIntros (r); iSpecialize ("Ha" $! r); iDestruct "Ha" as "[Ha Hb]"; done.
    - iIntros "#[Ha Hb]". iIntros (r). iSplit; done.
  Qed.
  Lemma full_eqltype_use F π E L {rt} b r (lt1 lt2 : ltype rt) l :
    lftE ⊆ F →
    full_eqltype E L lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    (l ◁ₗ[ π, b] r @ lt1 ={F}=∗ l ◁ₗ[ π, b] r @ lt2) ∗
    llctx_interp L.
  Proof.
    iIntros (? Heq) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [done | ].
    iFrame. iIntros "Hl". iDestruct ("Heq" $! _ _) as "[Hincl _]".
    by iApply (ltype_incl_use with "Hincl Hl").
  Qed.

  Lemma eqltype_syn_type_eq_noend E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) qL :
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros (Hunfold) "#CTX #HE HL".
    iPoseProof (Hunfold with "HL CTX HE") as "#Hll".
    iDestruct "Hll" as "((#$ & _) & _)".
  Qed.
  Lemma eqltype_syn_type_eq E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros (Hunfold) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (eqltype_syn_type_eq_noend with "CTX HE HL") as "#$".
    done.
  Qed.
End accessors.

Section eqltype.
  Context `{!typeGS Σ}.

  (** *** [ltype_incl]/[ltype_eq] *)
  Lemma ltype_incl_eq {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_incl b r1 r2 lt1 lt2 -∗ ltype_incl b r2 r1 lt2 lt1 -∗ ltype_eq b r1 r2 lt1 lt2.
  Proof.
    iIntros "H1 H2". iSplit; done.
  Qed.

  Lemma ltype_incl'_refl {rt} b r (lt : ltype rt) : ⊢ ltype_incl' b r r lt lt.
  Proof.
    iModIntro. destruct b; iIntros; try destruct wl; eauto.
  Qed.
  Lemma ltype_incl_refl {rt} b r (lt : ltype rt) : ⊢ ltype_incl b r r lt lt.
  Proof.
    iIntros "!>". iSplit; first done. iSplit; iApply ltype_incl'_refl.
  Qed.
  Lemma ltype_incl_trans {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    ltype_incl b r1 r2 lt1 lt2 -∗ ltype_incl b r2 r3 lt2 lt3 -∗ ltype_incl b r1 r3 lt1 lt3.
  Proof.
    iIntros "(%Hly1 & #Hi1 & #Hc1) (%Hly2 & #Hi2 & #Hc2)".
    iModIntro.
    iSplit. { rewrite Hly1 Hly2. done. }
    iSplit.
    - iModIntro. destruct b.
      + iIntros (??) "Ha". iMod ("Hi1" with "Ha") as "Ha". by iApply "Hi2".
      + iIntros (??) "Ha". iPoseProof ("Hi1" with "Ha") as "Ha". by iApply "Hi2".
      + iIntros (??) "Ha". iApply "Hi2". iApply "Hi1". done.
    - iModIntro. destruct b.
      + iIntros (??) "Ha". iMod ("Hc1" with "Ha") as "Ha". iApply ("Hc2" with "Ha").
      + iIntros (??) "Ha". iApply "Hc2". iApply "Hc1". done.
      + iIntros (??) "Ha". iApply "Hc2". iApply "Hc1". done.
  Qed.

  Lemma ltype_eq_ltype_incl_l {rt1 rt2} k r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq k r1 r2 lt1 lt2 -∗ ltype_incl k r1 r2 lt1 lt2.
  Proof. iIntros "($ & _)". Qed.
  Lemma ltype_eq_ltype_incl_r {rt1 rt2} k r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq k r1 r2 lt1 lt2 -∗ ltype_incl k r2 r1 lt2 lt1.
  Proof. iIntros "(_ & $)". Qed.

  Lemma ltype_eq_refl {rt} b r (lt : ltype rt) : ⊢ ltype_eq b r r lt lt.
  Proof.
    iSplit; iApply ltype_incl_refl.
  Qed.
  Lemma ltype_eq_sym {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : ltype_eq b r1 r2 lt1 lt2 -∗ ltype_eq b r2 r1 lt2 lt1.
  Proof.
    iIntros "[H1 H2]". iSplit; done.
  Qed.
  Lemma ltype_eq_trans {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    ltype_eq b r1 r2 lt1 lt2 -∗ ltype_eq b r2 r3 lt2 lt3 -∗ ltype_eq b r1 r3 lt1 lt3.
  Proof.
    iIntros "(Hi1 & Hi2) (Hj1 & Hj2)". iSplit.
    - iApply (ltype_incl_trans with "Hi1 Hj1").
    - iApply (ltype_incl_trans with "Hj2 Hi2").
  Qed.

  Lemma ltype_eq_syn_type {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq b r1 r2 lt1 lt2 -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros "((#$ & _) & _)".
  Qed.
  Lemma ltype_eq_core {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq b r1 r2 lt1 lt2 -∗ ltype_eq b r1 r2 (ltype_core lt1) (ltype_core lt2).
  Proof.
    iIntros "((%Hly_eq & #Hi & #Hc) & (_ & #Hi2 & #Hc2))".
    iSplit; iModIntro.
    - iSplit. { by rewrite !ltype_core_syn_type_eq. }
      rewrite !ltype_core_idemp. iSplit; done.
    - iSplit. { by rewrite !ltype_core_syn_type_eq. }
      rewrite !ltype_core_idemp. iSplit; done.
  Qed.

  (** *** [eqltype] / [subltype] / [full_eqltype] / [full_subltype] *)
  Lemma full_eqltype_alt E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 ↔ (∀ b r, eqltype E L b r r lt1 lt2).
  Proof.
    split.
    - iIntros (Heq b r qL) "HL CTX HE". iApply (Heq with "HL CTX HE").
    - iIntros (Heq qL) "HL CTX HE". iIntros (b r). iApply (Heq with "HL CTX HE").
  Qed.
  Lemma full_subltype_alt E L {rt} (lt1 lt2 : ltype rt) :
    full_subltype E L lt1 lt2 ↔ (∀ b r, subltype E L b r r lt1 lt2).
  Proof.
    split.
    - iIntros (Hsub b r qL) "HL CTX HE". iApply (Hsub with "HL CTX HE").
    - iIntros (Hsub qL) "HL CTX HE". iIntros (b r). iApply (Hsub with "HL CTX HE").
  Qed.

  Global Instance eqltype_refl E L {rt} b r : Reflexive (eqltype E L b (rt1:=rt) (rt2:=rt) r r).
  Proof. iIntros (??) "? ? ?". iApply ltype_eq_refl. Qed.
  Lemma eqltype_symm E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    eqltype E L b r1 r2 lt1 lt2 → eqltype E L b r2 r1 lt2 lt1.
  Proof.
    intros Heq.
    iIntros (?) "HL CTX HE". iDestruct (Heq with "HL CTX HE") as "#Heq".
    by iApply ltype_eq_sym.
  Qed.
  Lemma eqltype_trans E L {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    eqltype E L b r1 r2 lt1 lt2 → eqltype E L b r2 r3 lt2 lt3 → eqltype E L b r1 r3 lt1 lt3.
  Proof.
    intros H1 H2.
    iIntros (?) "HL #CTX #HE". iDestruct (H1 with "HL CTX HE") as "#Heq1".
    iDestruct (H2 with "HL CTX HE") as "#Heq2".
    iApply ltype_eq_trans; done.
  Qed.

  Global Instance full_eqltype_equivalence E L {rt}:
    Equivalence (full_eqltype E L (rt:=rt)).
  Proof.
    split.
    - intros ?. apply full_eqltype_alt => ??. apply eqltype_refl.
    - intros ??. rewrite !full_eqltype_alt => ? ??. by apply eqltype_symm.
    - intros ???. rewrite !full_eqltype_alt => H1 H2 ??. eapply eqltype_trans; [apply H1 | apply H2].
  Qed.

  Global Instance subltype_refl E L {rt} b r : Reflexive (subltype E L (rt1:=rt) (rt2:=rt) b r r).
  Proof.
    iIntros (lt ?) "HL CTX HE !>".
    iSplitR; first done.
    iSplit; iApply ltype_incl'_refl.
  Qed.
  Lemma subltype_trans E L {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    subltype E L b r1 r2 lt1 lt2 → subltype E L b r2 r3 lt2 lt3 → subltype E L b r1 r3 lt1 lt3.
  Proof.
    iIntros (Hsub12 Hsub23). iIntros (?) "HL #CTX #HE".
    iPoseProof (Hsub12 with "HL CTX HE") as "#Hsub12".
    iPoseProof (Hsub23 with "HL CTX HE") as "#Hsub23".
    iApply (ltype_incl_trans with "Hsub12 Hsub23").
  Qed.
  Global Instance full_subltype_preorder E L {rt} : PreOrder (full_subltype E L (rt := rt)).
  Proof.
    split.
    - intros ?. apply full_subltype_alt. intros ??. apply subltype_refl.
    - intros ???. rewrite !full_subltype_alt. intros H1 H2 ??. eapply subltype_trans; [apply H1 | apply H2].
  Qed.

  Lemma all_subltype_alt E L {rt} b (lt1 lt2 : ltype rt) :
    (∀ r, subltype E L b r r lt1 lt2) ↔
    (∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ∀ r, ltype_incl b r r lt1 lt2).
  Proof.
    split.
    - intros Ha qL. iIntros "HL CTX HE" (r).
      by iPoseProof (Ha r with "HL CTX HE") as "Ha".
    - intros Ha r. iIntros (qL) "HL CTX HE".
      iApply (Ha with "HL CTX HE").
  Qed.
  Lemma all_eqltype_alt E L {rt} b (lt1 lt2 : ltype rt) :
    (∀ r, eqltype E L b r r lt1 lt2) ↔
    (∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ∀ r, ltype_eq b r r lt1 lt2).
  Proof.
    split.
    - intros Ha qL. iIntros "HL CTX HE" (r).
      by iPoseProof (Ha r with "HL CTX HE") as "Ha".
    - intros Ha r. iIntros (qL) "HL CTX HE".
      iApply (Ha with "HL CTX HE").
  Qed.

  Lemma subltype_eqltype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b r1 r2 :
    subltype E L b r1 r2 lt1 lt2 → subltype E L b r2 r1 lt2 lt1 → eqltype E L b r1 r2 lt1 lt2.
  Proof.
    intros Ha Hb. iIntros (?) "HL #CTX #HE".
    iPoseProof (Ha with "HL CTX HE") as "#Ha". iPoseProof (Hb with "HL CTX HE") as "#Hb".
    iSplit; done.
  Qed.
  Lemma full_subltype_eqltype E L {rt} (lt1 lt2 : ltype rt) :
    full_subltype E L lt1 lt2 → full_subltype E L lt2 lt1 → full_eqltype E L lt1 lt2.
  Proof.
    rewrite !full_subltype_alt !full_eqltype_alt.
    intros Ha Hb b r. eapply subltype_eqltype; done.
  Qed.

  (** ** Compatibilty of [OfTy] with subtyping *)
  Lemma type_ltype_incl_shared_in {rt1 rt2} r1 r2 κ (ty1 : type rt1) (ty2 : type rt2) :
    type_incl r1 r2 ty1 ty2 -∗
    ltype_incl (Shared κ) #r1 #r2 (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "Hsub".
    iDestruct ("Hsub") as "(%Hst & #Hsceq & #Hown & #Hshr)".
    iSplitR; first done; iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb". rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & Hst & ? & Hsc & ? & %r' & -> & #Hb)".
    iExists ly. rewrite Hst. iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".
    iExists r2. iSplitR; first done. iModIntro. iMod "Hb". iModIntro. by iApply "Hshr".
  Qed.
  Lemma subtype_subltype_shared_in E L {rt1 rt2} r1 r2 κ (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 →
    subltype E L (Shared κ) (PlaceIn r1) (PlaceIn r2) (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub qL) "HL #CTX #HE". iPoseProof (Hsub with "HL HE") as "#Hsub".
    by iApply (type_ltype_incl_shared_in).
  Qed.

  Lemma type_ltype_incl_shared {rt} `{!Inhabited rt} κ (ty1 : type rt) (ty2 : type rt) :
    (∀ r, type_incl r r ty1 ty2) -∗
    ∀ r, ltype_incl (Shared κ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "#Hsub". iIntros (r).
    iPoseProof ("Hsub" $! inhabitant) as "(%Hst & #Hsceq & _)".
    iSplitR; first done. iModIntro.
    simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb". rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & Hst & ? & Hsc & ? & %r' & Hrfn & #Hb)".
    iExists ly. rewrite Hst. iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".
    iExists r'. iFrame. iModIntro. iMod "Hb". iModIntro.
    iDestruct ("Hsub" $! r') as "(_ & _ & _ & Hshr)".
    by iApply "Hshr".
  Qed.
  Lemma subtype_subltype_shared E L {rt} `{!Inhabited rt} κ (ty1 : type rt) (ty2 : type rt) :
    (∀ r, subtype E L r r ty1 ty2) →
    ∀ r, subltype E L (Shared κ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub r qL) "HL #CTX #HE".
    rewrite all_subtype_alt in Hsub.
    iPoseProof (Hsub with "HL HE") as "#Hsub".
    iApply (type_ltype_incl_shared with "Hsub").
  Qed.

  Lemma type_ltype_incl_owned_in_strong {rt1 rt2} π r1 r2 wl (ty1 : type rt1) (ty2 : type rt2) :
    ty1.(ty_syn_type) = ty2.(ty_syn_type) →
    (∀ v, v ◁ᵥ{π} r1 @ ty1 -∗ v ◁ᵥ{π} r2 @ ty2) -∗
    (ty1.(ty_sidecond) -∗ ty2.(ty_sidecond)) -∗
    ∀ l, l ◁ₗ[π, Owned wl] #r1 @ (◁ ty1) -∗ l ◁ₗ[π, Owned wl] #r2 @ (◁ ty2)%I.
  Proof.
    iIntros (Hst) "Hsub Hsceq".
    iIntros (l) "Hb".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & Hst & ? & Hsc & ? & ? & %r' & Hrfn & Hb)".
    iExists ly. rewrite Hst. iFrame.
    iSplitL "Hsceq Hsc". { by iApply "Hsceq". }
    iExists r2. iSplitR; first done. iNext. iMod "Hb" as "(% & ? & Hv)". iExists _. iFrame.
    iModIntro. iDestruct "Hrfn" as "->". by iApply "Hsub".
  Qed.
  Lemma type_ltype_incl_owned_in {rt1 rt2} r1 r2 wl (ty1 : type rt1) (ty2 : type rt2) :
    type_incl r1 r2 ty1 ty2 -∗ ltype_incl (Owned wl) #r1 #r2 (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "Hsub".
    iDestruct ("Hsub") as "(%Hst & #Hsceq & #Hown & #Hshr)".
    iSplitR; first done; iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb".
    iApply (type_ltype_incl_owned_in_strong with "Hown"); [done.. | ].
    done.
  Qed.
  Lemma subtype_subltype_owned_in E L {rt1 rt2} r1 r2 wl (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 → subltype E L (Owned wl) #r1 #r2 (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub qL) "HL #CTX #HE". iPoseProof (Hsub with "HL HE") as "#Hsub".
    by iApply (type_ltype_incl_owned_in).
  Qed.

  Lemma type_ltype_incl_owned {rt} `{!Inhabited rt} wl (ty1 : type rt) (ty2 : type rt) :
    (∀ r, type_incl r r ty1 ty2) -∗ ∀ r, ltype_incl (Owned wl) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "#Hsub" (r).
    iPoseProof ("Hsub" $! inhabitant) as "(%Hst & #Hsceq & _)".
    iSplitR; first done; iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb".
    iModIntro.
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & Hst & ? & Hsc & ? & ? & %r' & Hrfn & Hb)".
    iDestruct ("Hsub" $! r') as "(_ & _ & #Hown & #Hshr)".
    iExists ly. rewrite Hst. iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".
    iExists r'. iFrame. iNext. iMod "Hb" as "(% & ? & Hv)". iExists _. iFrame.
    iModIntro. by iApply "Hown".
  Qed.
  Lemma subtype_subltype_owned E L {rt} `{!Inhabited rt} wl (ty1 : type rt) (ty2 : type rt) :
    (∀ r, subtype E L r r ty1 ty2) → ∀ r, subltype E L (Owned wl) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub r qL) "HL #CTX #HE". rewrite all_subtype_alt in Hsub.
    iPoseProof (Hsub with "HL HE") as "#Hsub".
    iApply (type_ltype_incl_owned with "Hsub").
  Qed.

  (* NOTE: We do not get a direct heterogeneous subtyping lemma in the Uniq, because we cannot update the ghost variables in general.
     (I think we could get a lemma looking roughly like what we want, but it would work by reborrowing and  thus require later credits, and might also need a proof of liveness depending on how the atomic accessor works.) *)
  Lemma eqtype_subltype_homo_uniq_strong E L {rt} κ γ r1 r2 (ty1 : type rt) (ty2 : type rt) :
    eqtype E L r1 r2 ty1 ty2 → subltype E L (Uniq κ γ) (PlaceIn r1) (PlaceIn r2) (◁ ty1)%I (◁ ty2)%I.
  Proof.
    (* even this does not work, because we'd either:
       - need to update the ghost variable (TODO maybe this works with an atomic accessor)
       - or need to reborrow the whole thing, which would need a credit, see the comment above
     *)
  Abort.

  Lemma type_eq_ltype_incl_uniq {rt} `{!Inhabited rt} κ γ (ty1 : type rt) (ty2 : type rt) :
    (∀ r, type_incl r r ty1 ty2) -∗ (∀ r, type_incl r r ty2 ty1) -∗ ∀ r, ltype_incl (Uniq κ γ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "#Hsub1 #Hsub2" (r).
    iPoseProof ("Hsub1" $! inhabitant) as "(%Hst & #Hsceq & _)".
    iSplitR; first done; iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & Hst & ? & Hsc & Hlb & ? & Hrfn & Hb)".
    iExists ly. iFrame. rewrite Hst. iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".

    iMod "Hb". iModIntro.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hrfn & Hb)". iExists _. iFrame.
      iMod "Hb". iModIntro.
      iDestruct "Hb" as "(%v & Hl & Hv)". iExists _. iFrame.
      iDestruct ("Hsub1" $! r') as "(_ & _ & Hown & _)".
      by iApply "Hown".
    * iIntros "(%r' & Hrfn & Hb)". iExists _. iFrame.
      iMod "Hb". iModIntro.
      iDestruct "Hb" as "(%v & Hl & Hv)". iExists _. iFrame.
      iDestruct ("Hsub2" $! r') as "(_ & _ & Hown & _)".
      by iApply "Hown".
  Qed.
  Lemma eqtype_subltype_uniq E L {rt} `{!Inhabited rt} κ γ (ty1 : type rt) (ty2 : type rt) :
    (∀ r, eqtype E L r r ty1 ty2) → ∀ r, subltype E L (Uniq κ γ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub r qL) "HL #CTX #HE". apply all_eqtype_alt in Hsub as [Hsub1 Hsub2].
    iPoseProof (Hsub1 with "HL HE") as "#Hsub1".
    iPoseProof (Hsub2 with "HL HE") as "#Hsub2".
    iApply (type_eq_ltype_incl_uniq with "Hsub1 Hsub2").
  Qed.

  Lemma full_eqtype_subltype E L {rt} `{!Inhabited rt} (ty1 : type rt) (ty2 : type rt) :
    (full_eqtype E L ty1 ty2) → full_subltype E L (◁ ty1)%I (◁ ty2)%I.
  Proof.
    intros Heq. apply full_subltype_alt => b r.
    destruct b.
    - eapply subtype_subltype_owned; [done | ].
      intros. eapply Heq.
    - eapply subtype_subltype_shared; [done | ].
      intros. eapply Heq.
    - eapply eqtype_subltype_uniq; [done | ]. done.
  Qed.

  Lemma full_eqtype_eqltype E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt):
    (full_eqtype E L ty1 ty2) → full_eqltype E L (◁ ty1)%I (◁ ty2)%I.
  Proof.
    intros Ha. apply full_subltype_eqltype; apply full_eqtype_subltype; last symmetry; done.
  Qed.

  Lemma full_eqltype_subltype_l E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 → full_subltype E L lt1 lt2.
  Proof.
    iIntros (Heq ?) "HL #CTX #HE". iIntros (??).
    iDestruct (Heq with "HL CTX HE") as "Ha".
    iDestruct ("Ha" $! _ _) as "($ & _)".
  Qed.
  Lemma full_eqltype_subltype_r E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 → full_subltype E L lt2 lt1.
  Proof.
    iIntros (Heq ?) "HL #CTX #HE". iIntros (??).
    iDestruct (Heq with "HL CTX HE") as "Ha".
    iDestruct ("Ha" $! _ _) as "(_ & $)".
  Qed.
End eqltype.

Section ghost_variables.
  Context `{typeGS Σ}.
  Context {T : Type}.
  Implicit Types (γ : gname) (t : T).

  Definition GRel2 κ (γ1 γ2 : gname) (R : T → T → Prop) : iProp Σ :=
    [† κ] ={lftE}=∗ Rel2 γ1 γ2 R.

  Lemma GRel2_use_pobs κ γ1 γ2 R v1 :
    [†κ] -∗ gvar_pobs γ1 v1 -∗ GRel2 κ γ1 γ2 R ={lftE}=∗ ∃ v2, gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hdead Hobs Hr". iMod ("Hr" with "Hdead") as "Hr".
    iModIntro. iApply (Rel2_use_pobs with "Hobs Hr").
  Qed.

  Lemma GRel2_use_obs κ γ1 γ2 R v1 :
    [† κ] -∗ gvar_obs γ1 v1 -∗ GRel2 κ γ1 γ2 R ={lftE}=∗ ∃ v2, gvar_obs γ2 v2 ∗ gvar_obs γ1 v1 ∗ gvar_pobs γ1 v1 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hdead Hobs Hr". iMod ("Hr" with "Hdead") as "Hr".
    iModIntro. iApply (Rel2_use_obs with "Hobs Hr").
  Qed.

  Lemma GRel2_use_trivial κ γ1 γ2 R :
    [† κ] -∗ GRel2 κ γ1 γ2 R ={lftE}=∗ ∃ v2 : T, gvar_obs γ2 v2.
  Proof.
    iIntros "Hdead Hr". iMod ("Hr" with "Hdead") as "Hr".
    iModIntro. iApply (Rel2_use_trivial with "Hr").
  Qed.
End ghost_variables.

Section blocked.
  Context `{typeGS Σ}.

  Section unblockable.
    Context {rt rti : Type}.

    (** Implicit unblocking by the lifetime logic, saying that we can go back to the core of an ltype [lt] after [κs] has ended.
      Crucially, these shifts need to work without assuming anything about liveness of lifetimes and
      without updating any refinements.
      Moreover, we rely on later credits here in order to do this without laters by prepaying inheritance viewshifts (in particular to get the congruence lemma for products).
     *)
    Definition imp_unblockable (κs : list lft) (lt : ltype rt) : iProp Σ :=
      □
      (** Uniq *)
      ((∀ κ' γ' π r l,
        lft_dead_list κs -∗
        (ltype_own lt (Uniq κ' γ') π r l ={lftE}=∗ ltype_own_core lt (Uniq κ' γ') π r l)) ∗
      (** Owned. *)
      (∀ π r l wl,
        lft_dead_list κs -∗ ltype_own lt (Owned wl) π r l ={lftE}=∗ ltype_own_core lt (Owned wl) π r l)
      (** We don't have a requirement on Shared, as we should not have blocked things below shared ownership anyways. *)
      ).

    Global Instance imp_unblockable_persistent κ lt : Persistent (imp_unblockable κ lt).
    Proof. apply _. Qed.

    Lemma imp_unblockable_shorten κs κs' lt :
      □ (lft_dead_list κs ={lftE}=∗ lft_dead_list κs') -∗
      imp_unblockable κs' lt -∗ imp_unblockable κs lt.
    Proof.
      iIntros "#Hincl #(Ha1 & Ha2) !>".
      iSplitL.
      - iIntros (?????) "#Hdead Hb".
        iMod ("Hincl" with "Hdead") as "Hdead'".
        iApply ("Ha1" with "Hdead' Hb").
      - iIntros (????) "Hdead Hb".
        iMod ("Hincl" with "Hdead") as "Hdead'".
        iApply ("Ha2" with "Hdead' Hb").
    Qed.

    Lemma imp_unblockable_shorten' κ κ' lt :
      κ' ⊑ κ -∗ imp_unblockable [κ'] lt -∗ imp_unblockable [κ] lt.
    Proof.
      iIntros "#Hincl". iApply imp_unblockable_shorten.
      iIntros "!> (Hdead & _)".
      iMod (lft_incl_dead with "Hincl Hdead") as "Hdead'"; first done.
      iApply big_sepL_singleton. done.
    Qed.
  End unblockable.

  (** Ofty is trivially unblockable *)
  Lemma ofty_imp_unblockable {rt} (ty : type rt) κs :
    ⊢ imp_unblockable κs (◁ ty).
  Proof.
    iModIntro. iSplitR.
    - iIntros "*". rewrite ltype_own_core_equiv. simp_ltypes. eauto.
    - iIntros "*". rewrite ltype_own_core_equiv. simp_ltypes. eauto.
  Qed.

  (** Blocked is unblockable *)
  Lemma blocked_imp_unblockable {rt} (ty : type rt) κ :
    ⊢ imp_unblockable [κ] (BlockedLtype ty κ).
  Proof.
    iModIntro. iSplitR.
    - iIntros (κ' γ' π r l) "(#Hdead & _) Hb/=".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_blocked_unfold ltype_own_ofty_unfold.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & Hsc & Hlb & Hb & Hcred & Hat)".
      iExists ly. iSplitR; first done. iSplitR; first done. iFrame "Hsc Hlb Hcred Hat".
      iMod ("Hb" with "Hdead") as "($ & Hb)". iApply "Hb".
    - iIntros (π r l wl) "(#Hdead & _)".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_blocked_unfold ltype_own_ofty_unfold.
      iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & Hinh & Hcred)".
      iMod ("Hinh" with "Hdead") as "Hv".
      iDestruct "Hv" as "(%r' & Hrfn & >(%v & Hl & Hv))".
      iMod (place_rfn_interp_owned_blocked_unblock with "Hrfn") as "Hrfn".
      iModIntro. iExists ly. iSplitR; first done. iSplitR; first done. iFrame "Hsc Hlb Hcred".
      iExists r'. iFrame "Hrfn". iModIntro. iExists v. iFrame. done.
  Qed.

  (** Shr Blocked is unblockable *)
  Lemma shr_blocked_imp_unblockable {rt} (ty : type rt) κ :
    ⊢ imp_unblockable [κ] (ShrBlockedLtype ty κ).
  Proof.
    iModIntro. iSplitR.
    - iIntros (κ' γ' π r l) "(#Hdead & _) Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_shrblocked_unfold ltype_own_ofty_unfold.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hobs & Hshr & Hinh & Hcred & Hat)".
      iExists ly. iFrame.
      iMod ("Hinh" with "Hdead") as "$". done.
    - iIntros (π r l wl) "(#Hdead & _) Hblocked".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_shrblocked_unfold ltype_own_ofty_unfold.
      iDestruct "Hblocked" as "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hshr & Hunblock & Hcred)".
      iMod ("Hunblock" with "Hdead") as "Hl".
      iDestruct "Hl" as "(%v & Hl & Hv)".
      iModIntro. iExists ly. iFrame. iExists r'.
      iPoseProof (place_rfn_interp_shared_owned with "Hrfn") as "$".
      iNext. eauto with iFrame.
  Qed.

  Lemma mut_ltype_imp_unblockable {rt} κs κ' (lt : ltype rt) :
    imp_unblockable κs lt -∗
    imp_unblockable κs (MutLtype lt κ').
  Proof.
    iIntros "#(Hub_mut & Hub_own)". iModIntro. iSplitL.
    - iIntros (κ0 γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & ? & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro. iModIntro.
      (*rewrite ltype_core_syn_type_eq.*)
      setoid_rewrite ltype_own_core_core.
      iApply (pinned_bor_impl with "[] Hb").
      iNext. iModIntro. iSplit; first last.
      { setoid_rewrite ltype_own_core_equiv. eauto. }
      iIntros "(%r' & Hauth & Hb)". iExists _. iFrame "Hauth".
      iMod "Hb". iDestruct "Hb" as "(%l' & Hl & Hb)".
      iMod ("Hub_mut" with "Hdead Hb") as "Hb"; first last.
      { iModIntro. rewrite ltype_own_core_equiv. eauto with iFrame. }
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & %γ & %r' & Hrfn & Hb)".
      iExists ly. iFrame.
      iModIntro. iExists _, _. iFrame "Hrfn". iNext.
      iMod "Hb" as "(%l' & Hl & Hb)".
      iExists _. iFrame. rewrite -ltype_own_core_equiv.
      iApply ("Hub_mut" with "Hdead Hb").
  Qed.

  Lemma shr_ltype_imp_unblockable {rt} κs κ' (lt : ltype rt) :
    imp_unblockable κs lt -∗
    imp_unblockable κs (ShrLtype lt κ').
  Proof.
    iIntros "#(Hub_mut & Hub_own)". iModIntro. iSplitL.
    - iIntros (κ0 γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & ? & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro. iModIntro.
      setoid_rewrite ltype_own_core_core.
      iApply (pinned_bor_impl with "[] Hb").
      iNext. iModIntro. iSplit; first last.
      { setoid_rewrite ltype_own_core_equiv. eauto. }
      iIntros "(%r' & Hauth & Hb)". iExists _. iFrame "Hauth".
      iMod "Hb". iDestruct "Hb" as "(%l' & Hl & Hb)".
      iExists _. iFrame.
      iApply (ltype_own_shared_to_core with "Hb").
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hb)".
      iExists ly. iFrame.
      iModIntro. iExists _. iFrame "Hrfn". iNext.
      iMod "Hb" as "(%l' & Hl & Hb)".
      iExists _. iFrame.
      by iApply ltype_own_shared_to_core.
  Qed.

  Lemma box_ltype_imp_unblockable {rt} κs (lt : ltype rt) :
    imp_unblockable κs lt -∗
    imp_unblockable κs (BoxLtype lt).
  Proof.
    iIntros "#(Hub_mut & Hub_own)". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_box_unfold /box_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & ? & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro. rewrite ltype_core_syn_type_eq.
      setoid_rewrite ltype_own_core_core.
      iApply (pinned_bor_impl with "[] Hb").
      iNext. iModIntro. iSplit; first last.
      { setoid_rewrite ltype_own_core_equiv. eauto. }
      iIntros "(%r' & Hauth & Hb)". iExists _. iFrame "Hauth".
      iMod "Hb". iDestruct "Hb" as "(%l' & %ly' & Hl & ? & ? & Hf & Hb)".
      iMod ("Hub_own" with "Hdead Hb") as "Hb".
      iModIntro. rewrite ltype_own_core_equiv. eauto with iFrame.
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_box_unfold /box_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hb)".
      iExists ly. iFrame.
      iModIntro. iExists _. iFrame "Hrfn". iNext.
      iMod "Hb" as "(%l' & %ly' & Hl & ? & ? & ? & Hb)".
      iExists _, _. iFrame. rewrite ltype_core_syn_type_eq. iFrame.
      rewrite -ltype_own_core_equiv. iApply "Hub_own"; done.
  Qed.

  Lemma owned_ptr_ltype_imp_unblockable {rt} κs (lt : ltype rt) ls :
    imp_unblockable κs lt -∗
    imp_unblockable κs (OwnedPtrLtype lt ls).
  Proof.
    iIntros "#(Hub_mut & Hub_own)". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_owned_ptr_unfold /box_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & ? & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro. rewrite ltype_core_syn_type_eq.
      setoid_rewrite ltype_own_core_core.
      iApply (pinned_bor_impl with "[] Hb").
      iNext. iModIntro. iSplit; first last.
      { setoid_rewrite ltype_own_core_equiv. eauto. }
      iIntros "(%r' & %l' & Hauth & Hb)". iExists _, _. iFrame "Hauth".
      iMod "Hb". iDestruct "Hb" as "(%ly' & Hl & ? & Hf & Hb)".
      iMod ("Hub_own" with "Hdead Hb") as "Hb".
      iModIntro. rewrite ltype_own_core_equiv. eauto with iFrame.
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_owned_ptr_unfold /owned_ptr_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & %r' & %l' & Hrfn & Hb)".
      iExists ly. iFrame.
      iModIntro. iExists _, _. iFrame "Hrfn". iNext.
      iMod "Hb" as "(%ly' & Hl & ? & ? & Hb)".
      iExists _. iFrame. rewrite ltype_core_syn_type_eq. iFrame.
      rewrite -ltype_own_core_equiv. iApply "Hub_own"; done.
  Qed.

  Lemma struct_ltype_imp_unblockable {rts} κ (lts : hlist ltype rts) sls :
    ([∗ list] lt ∈ hzipl rts lts, imp_unblockable κ (projT2 lt)) ⊢
    imp_unblockable κ (StructLtype lts sls).
  Proof.
    set (map_core := (λ '(existT x (a, b)), existT x (ltype_core a, b) : sigT (λ rt, ltype rt * place_rfn rt)%type)).
    iIntros "#Hub". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hb" as "(%sl & %Halg & %Hlen & ? & ? & ? & ? & Hb)".
      iExists sl. iFrame. iR. iR.
      iMod "Hb". iModIntro.
      iApply (pinned_bor_impl' with "[] [] Hb").
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          iMod ("Ha").
          iApply big_sepL_fupd.
          iApply (big_sepL_impl with "Ha").
          iModIntro. iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          apply pad_struct_lookup_Some in Hlook; first last.
          { rewrite hpzipl_length -Hlen. erewrite struct_layout_spec_has_layout_fields_length;done. }
          destruct Hlook as (n & ly' & Hlook & [(? & Hlook1) | (-> & Hlook1)]).
          { apply hpzipl_lookup_inv_hzipl_pzipl in Hlook1 as (Hlook1 & _).
            iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
            iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
            rewrite ltype_own_core_equiv. rewrite ltype_core_syn_type_eq. eauto 8 with iFrame. }
          { (* uninit *)
            injection Hlook1 => _ _ ?. subst.
            apply existT_inj in Hlook1. injection Hlook1 as -> ->.
            rewrite ltype_core_uninit. eauto 8. }
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          setoid_rewrite ltype_own_core_equiv.
          iMod ("Ha").
          iApply (big_sepL_impl with "Ha").
          iModIntro. iModIntro.
          iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          simp_ltypes. eauto 8 with iFrame.
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          setoid_rewrite ltype_own_core_equiv.
          iMod ("Ha").
          iApply (big_sepL_impl with "Ha").
          iModIntro. iModIntro.
          iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          simp_ltypes. eauto 8 with iFrame.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          setoid_rewrite ltype_own_core_equiv.
          iMod ("Ha").
          iApply (big_sepL_impl with "Ha").
          iModIntro. iModIntro.
          iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          simp_ltypes. eauto 8 with iFrame.
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hb" as "(%sl & %Halg & %Hlen & ? & ? & ? & %r' & ? & Hb)".
      iExists sl. iFrame. iR. iR. iExists _. iFrame.
      iModIntro. iNext. iMod "Hb".
      rewrite hpzipl_hmap.
      rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
      { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
      rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
      iApply big_sepL_fupd.
      iApply (big_sepL_impl with "Hb").
      iModIntro. iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
      apply pad_struct_lookup_Some in Hlook; first last.
      { rewrite hpzipl_length -Hlen. erewrite struct_layout_spec_has_layout_fields_length;done. }
      destruct Hlook as (n & ly' & Hlook & [(? & Hlook1) | (-> & Hlook1)]).
      { apply hpzipl_lookup_inv_hzipl_pzipl in Hlook1 as (Hlook1 & _).
        iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
        iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
        rewrite ltype_own_core_equiv. rewrite ltype_core_syn_type_eq. eauto 8 with iFrame. }
      { (* uninit *)
        injection Hlook1 => _ _ ?. subst.
        apply existT_inj in Hlook1. injection Hlook1 as -> ->.
        rewrite ltype_core_uninit. eauto 8. }
  Qed.

  Lemma array_ltype_imp_unblockable {rt} κs (def : type rt) len (lts : list (nat * ltype rt)) :
    ([∗ list] lt ∈ (interpret_iml (◁ def) len lts), imp_unblockable κs lt) -∗
    imp_unblockable κs (ArrayLtype def len lts).
  Proof.
    iIntros "#Hub". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_array_unfold /array_ltype_own.
      iDestruct "Hb" as "(%sl & %Halg & % & % & ? & ? & ? & Hb)".
      iExists sl. iFrame. iR. iR. iR.
      iMod "Hb". iModIntro.
      iApply (pinned_bor_impl' with "[] [] Hb").
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)).
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          iMod ("Ha") as "(%Hlen & Ha)". iR.
          iApply big_sepL2_fupd.
          iApply (big_sepL2_impl with "Ha").
          iModIntro. iIntros (k lt r'' Hlook1 Hlook2) "(%Hst & Hl)".
          simp_ltypes. iR.
          iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
          iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
          rewrite ltype_own_core_equiv. done.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)) in "Ha".
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          setoid_rewrite ltype_core_syn_type_eq.
          setoid_rewrite ltype_own_core_equiv. done.
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)).
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          setoid_rewrite ltype_core_syn_type_eq.
          setoid_rewrite ltype_own_core_equiv.
          setoid_rewrite ltype_core_idemp. done.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)) in "Ha".
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          setoid_rewrite ltype_core_syn_type_eq.
          setoid_rewrite ltype_own_core_equiv.
          setoid_rewrite ltype_core_idemp. done.
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_array_unfold /array_ltype_own.
      iDestruct "Hb" as "(%ly & %Halg & % & % & ? & ? & %r' & ? & Hb)".
      iExists ly. iFrame. iR. iR. iR.
      iModIntro. iExists r'. iFrame.
      iEval (rewrite -(ltype_core_ofty def)).
      rewrite interpret_iml_fmap big_sepL2_fmap_l.
      iNext. iMod ("Hb") as "(%Hlen & Ha)". iR.
      iApply big_sepL2_fupd.
      iApply (big_sepL2_impl with "Ha").
      iModIntro. iIntros (k lt r'' Hlook1 Hlook2) "(%Hst & Hl)".
      simp_ltypes. iR.
      iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
      iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
      rewrite ltype_own_core_equiv. done.
  Qed.

  Lemma enum_ltype_imp_unblockable {rt} κs (en : enum rt) (tag : string) (lte : ltype (enum_tag_rt en tag)) :
    imp_unblockable κs lte -∗
    imp_unblockable κs (EnumLtype en tag lte).
  Proof.
    iIntros "#Hub". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_enum_unfold /enum_ltype_own.
      iDestruct "Hb" as "(%el & %Halg & % & ? & % & Hb)".
      done.
    - iIntros (π r l wl) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_enum_unfold /enum_ltype_own.
      iDestruct "Hb" as "(%el & %Halg & % & ? & %Htag & ? & %r' & ? & Hb)".
      iExists el. iFrame. iR. iR. iR.
      iModIntro. iExists r'. iFrame.
      iNext. iMod "Hb" as "(%Heq & %Htag' & ? & Hb & ? & ?)".
      iExists Heq. iR. rewrite ltype_core_syn_type_eq. iFrame.
      iDestruct "Hub" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hb") as "Hl".
      rewrite ltype_own_core_equiv. done.
  Qed.


  (* Unblocking is trivial for OpenedLtype, since the core is trivial.
     However, that also doesn't buy us much, since we will anyways never have OpenedLtype below an intact mutable reference.
  *)
  Lemma opened_ltype_imp_unblockable {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost κs :
    ⊢ imp_unblockable κs (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost).
  Proof.
    iModIntro. iSplitL.
    - iIntros (κ' ????). rewrite ltype_own_core_equiv ltype_core_opened. eauto.
    - iIntros (????). rewrite ltype_own_core_equiv ltype_core_opened. eauto.
  Qed.

  Lemma coreable_ltype_imp_unblockable {rt_full} (lt_full : ltype rt_full) κs :
    ⊢ imp_unblockable κs (CoreableLtype κs lt_full).
  Proof.
    iModIntro. iSplitL.
    - iIntros (κ' γ π r l) "#Hdead Hb".
      rewrite ltype_own_core_coreable_unfold ltype_own_coreable_unfold /coreable_ltype_own.
      iDestruct "Hb" as "(%ly & _ & _ & _ & Hrfn & Hvs)".
      iApply ("Hvs" with "Hdead Hrfn").
    - iIntros (π r l wl) "Hdead Ha".
      rewrite ltype_own_core_coreable_unfold ltype_own_coreable_unfold /coreable_ltype_own.
      iDestruct "Ha" as "(%ly & _ & _ & _ & Ha)".
      iApply ("Ha" with "Hdead").
  Qed.

  Lemma alias_ltype_imp_unblockable rt st l κs :
    ⊢ imp_unblockable κs (AliasLtype rt st l).
  Proof.
    iModIntro. iSplitL.
    - iIntros (?????). rewrite ltype_own_core_equiv ltype_core_alias. eauto.
    - iIntros (????). rewrite ltype_own_core_equiv ltype_core_alias. eauto.
  Qed.

  Lemma shadowed_ltype_imp_unblockable {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) κs :
    imp_unblockable κs lt_full -∗ imp_unblockable κs (ShadowedLtype lt_cur r_cur lt_full).
  Proof.
    iIntros "#(Ha1 & Ha2)".
    iModIntro. iSplitL.
    - iIntros (?????). rewrite ltype_own_core_equiv ltype_own_shadowed_unfold. simp_ltypes.
      iIntros "Hdead (_ & _ & Hb)".
      rewrite -ltype_own_core_equiv. iApply ("Ha1" with "Hdead Hb").
    - iIntros (????). rewrite ltype_own_core_equiv ltype_own_shadowed_unfold. simp_ltypes.
      iIntros "Hdead (_ & _ & Hb)".
      rewrite -ltype_own_core_equiv. iApply ("Ha2" with "Hdead Hb").
  Qed.

  (** Once all the blocked lifetimes are dead, every ltype is unblockable to its core. *)
  Lemma imp_unblockable_blocked_dead {rt} (lt : ltype rt) :
    ⊢ imp_unblockable (ltype_blocked_lfts lt) lt.
  Proof.
    (* TODO is there a way to use this dependent induction principle directly with iInduction or induction? *)
    move: rt lt. eapply ltype_induction.
    - iIntros (rt ty κ). cbn. iApply blocked_imp_unblockable.
    - iIntros (rt ty κ). iApply shr_blocked_imp_unblockable.
    - iIntros (rt ty). iApply ofty_imp_unblockable.
    - iIntros (rt st l). iApply alias_ltype_imp_unblockable.
    - iIntros (rt lt IH κ). iApply mut_ltype_imp_unblockable. by iApply IH.
    - iIntros (rt lt IH κ). iApply shr_ltype_imp_unblockable. by iApply IH.
    - iIntros (rt lt IH). iApply box_ltype_imp_unblockable. by iApply IH.
    - iIntros (rt lt ls IH). iApply owned_ptr_ltype_imp_unblockable. by iApply IH.
    - iIntros (rts lts IH sls).
      iApply (struct_ltype_imp_unblockable _ lts sls).
      iApply big_sepL_intro. iModIntro. iIntros (k [rt lt] Hlook).
      iApply imp_unblockable_shorten; first last.
      { iApply IH. by eapply elem_of_list_lookup_2. }
      simpl. clear -Hlook.
      unfold ltype_blocked_lfts. simpl.
      iModIntro. rewrite /lft_dead_list.
      iInduction lts as [ | X Xl lt' lts ] "IH" forall (k Hlook); simpl; first done.
      destruct k as [ | k]; simpl in Hlook.
      + injection Hlook as Heq Heq2; subst. apply existT_inj in Heq2 as ->.
        rewrite big_sepL_app. by iIntros "($ & _)".
      + iIntros "Ha". iApply "IH"; first done.
        rewrite big_sepL_app. iDestruct "Ha" as "(_ & $)".
    - iIntros (rt def len lts IH ).
      iApply array_ltype_imp_unblockable.
      iApply big_sepL_intro. iModIntro. iIntros (k lt Hlook).
      apply lookup_interpret_iml_Some_inv in Hlook as (? & [-> | Hel]).
      + iApply ofty_imp_unblockable.
      + iApply imp_unblockable_shorten; first last.
        { iApply IH. done. }
        simpl. rewrite /ltype_blocked_lfts /=. iModIntro.
        iIntros "Hdead". clear -Hel.
        iInduction lts as [ | lt' lts ] "IH" forall (k Hel).
        { by apply elem_of_nil in Hel. }
        apply elem_of_cons in Hel as [<- | Hel].
        * simpl. rewrite lft_dead_list_app. by iDestruct "Hdead" as "($ & _)".
        * simpl. rewrite lft_dead_list_app. iDestruct "Hdead" as "(_ & Hdead)".
          by iApply "IH".
    - iIntros (rt en tag lte Hub).
      by iApply enum_ltype_imp_unblockable.
    - iIntros (rt_cur rt_inner rt_full lt_cur lt_inner ty_full Cpre R Cpost IH1 IH2).
      iApply opened_ltype_imp_unblockable.
    - iIntros (rt_full κ' lt_full Hdead). iApply coreable_ltype_imp_unblockable.
    - iIntros (rt_cur rt_full lt_cur r_cur lt_full _ Hub).
      iApply shadowed_ltype_imp_unblockable. done.
  Qed.

  (** We can essentiallly rewrite with [ltype_eq] when proving [imp_unblockable]. *)
  Lemma ltype_eq_imp_unblockable {rt} κs (lt1 lt2 : ltype rt) :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    imp_unblockable κs lt1 -∗
    imp_unblockable κs lt2.
  Proof.
    (*iIntros "((% & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2)) (#Hub1 & #Hub2)". *)
    iIntros "#Heq (#Hub1 & #Hub2)".
    iSplitL; iModIntro.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      iDestruct ("Heq" $! (Uniq κ' γ') r) as "((% & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
      iDestruct ("Hub1" with "Hdead") as "#Hub1'".
      iApply ltype_own_core_equiv. iApply "Hc1". iApply ltype_own_core_equiv.
      iApply "Hub1'". by iApply "Hi2".
    - iIntros (π r l wl) "#Hdead Hb".
      iDestruct ("Heq" $! (Owned wl) r) as "((% & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
      iMod ("Hi2" with "Hb") as "Hb".
      iMod ("Hub2" with "Hdead Hb") as "Hb".
      rewrite !ltype_own_core_equiv. by iApply "Hc1".
  Qed.
  (** A particular instance: when we unfold a type to an ltype, this should always be unblockable. *)
  Lemma ltype_eq_imp_unblockable_ofty {rt} κs ty (lt : ltype rt) :
    (∀ b r, ltype_eq b r r (◁ ty)%I lt) -∗
    imp_unblockable κs lt.
  Proof.
    iIntros "Heq". iApply (ltype_eq_imp_unblockable with "Heq").
    iApply ofty_imp_unblockable.
  Qed.

  Lemma imp_unblockable_use π F κs {rt} (lt : ltype rt) (r : place_rfn rt) l bk :
    lftE ⊆ F →
    imp_unblockable κs lt -∗
    lft_dead_list κs -∗
    l ◁ₗ[π, bk] r @ lt ={F}=∗ l ◁ₗ[π, bk] r @ ltype_core lt.
  Proof.
    iIntros (?) "(#Hub_uniq & #Hub_owned) Hdead Hl".
    destruct bk.
    - iMod (fupd_mask_mono with "(Hub_owned Hdead Hl)") as "Hl"; first done.
      rewrite ltype_own_core_equiv. done.
    - iApply (ltype_own_shared_to_core with "Hl").
    - iMod (fupd_mask_mono with "(Hub_uniq Hdead Hl)") as "Hl"; first done.
      rewrite ltype_own_core_equiv. done.
  Qed.

  Lemma unblock_blocked {rt} E κ π l b (ty : type rt) r :
    lftE ⊆ E →
    [† κ] -∗
    l ◁ₗ[π, b] r @ (BlockedLtype ty κ) ={E}=∗ l ◁ₗ[π, b] r @ (◁ ty)%I.
  Proof.
    iIntros (?) "Hdead Hl".
    iPoseProof (blocked_imp_unblockable ty κ) as "Ha".
    iMod (imp_unblockable_use with "Ha [$Hdead//] Hl") as "Hb"; first done.
    simp_ltypes. done.
  Qed.
  Lemma unblock_shrblocked {rt} E κ π l b (ty : type rt) r :
    lftE ⊆ E →
    [† κ] -∗
    l ◁ₗ[π, b] r @ (ShrBlockedLtype ty κ) ={E}=∗ l ◁ₗ[π, b] r @ (◁ ty)%I.
  Proof.
    iIntros (?) "Hdead Hl".
    iPoseProof (shr_blocked_imp_unblockable ty κ) as "Ha".
    iMod (imp_unblockable_use with "Ha [$Hdead//] Hl") as "Hb"; first done.
    simp_ltypes. done.
  Qed.
  Lemma unblock_coreable {rt} F π (lt_full : ltype rt) r κs l b :
    lftE ⊆ F →
    lft_dead_list κs -∗
    l ◁ₗ[π, b] r @ CoreableLtype κs lt_full ={F}=∗
    l ◁ₗ[π, b] r @ ltype_core lt_full.
  Proof.
    iIntros (?) "Hdead Hl".
    iPoseProof (coreable_ltype_imp_unblockable lt_full κs) as "Ha".
    iMod (imp_unblockable_use with "Ha [$Hdead//] Hl") as "Hb"; first done.
    simp_ltypes. done.
  Qed.
End blocked.
