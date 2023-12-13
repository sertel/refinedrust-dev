From stdpp Require Export strings.
From stdpp Require Import gmap list.
From caesium Require Export base layout int_type loc char.
Set Default Proof Using "Type".

Notation var_name := string (only parsing).

Definition field_list := list (option var_name * layout).

Definition field_members (s : field_list) : list (var_name * layout) :=
  (omap (λ '(n, ly), (λ n', (n', ly)) <$> n) s).
Definition field_names (s : field_list) : list var_name := omap fst s.
Definition offset_of_idx (s : field_list) (i : nat) : nat :=
  sum_list (take i (ly_size <$> s.*2)).
Definition index_of (s : field_list) (n : var_name) : option nat :=
  fst <$> list_find (λ x, x.1 = Some n) s.
Definition offset_of (s : field_list) (n : var_name) : option nat :=
  (λ idx, offset_of_idx s idx) <$> index_of s n.
Definition field_idx_of_idx (s : field_list) (i : nat) : nat :=
  length (field_names (take i s)).
Fixpoint field_index_of (s : field_list) (n : var_name) : option nat :=
  match s with
  | [] => None
  | (n', ly)::s' => if bool_decide (n' = Some n) then Some 0%nat else
                    (if n' is Some _ then S else id) <$> field_index_of s' n
  end.
Fixpoint pad_struct {A} (s : field_list) (l : list A) (f : layout → A) : list A :=
  match s with
  | [] => []
  | (n, ly)::s' => (if n is Some _ then default (f ly) (head l) else f ly)::pad_struct s' (if n is Some _ then tail l else l) f
  end.
Fixpoint check_fields_aligned (s : field_list) (pos : nat) : bool :=
  match s with
  | [] => true
  | (_,ly)::s' => bool_decide (pos `mod` ly_align ly = 0) && check_fields_aligned s' (pos + ly.(ly_size))
  end.

(* TODO: potentially, this should require that [length sl_members ≤ max_int i32], since
  this is a restriction placed by LLVM's GEP instruction for indexing into structs *)
Record struct_layout := {
   sl_members : field_list;
   sl_nodup : bool_decide (NoDup (field_names sl_members));
   (* Note: difference to RefinedC: using isize_t instead of usize_t *)
   sl_size : sum_list (ly_size <$> sl_members.*2) < max_int isize_t + 1;
   sl_fields_aligned : check_fields_aligned sl_members 0 = true;
}.

Definition layout_of (s : struct_layout) : layout := {|
  ly_size := sum_list (ly_size <$> s.(sl_members).*2);
  ly_align_log := max_list (ly_align_log <$> s.(sl_members).*2)
|}.

Coercion layout_of : struct_layout >-> layout.

Lemma struct_layout_eq sl1 sl2 :
  sl1.(sl_members) = sl2.(sl_members) →
  sl1 = sl2.
Proof. destruct sl1, sl2 => /= ?. subst. f_equal; apply: proof_irrel. Qed.

Lemma field_members_length s:
  length (field_members s) = length (field_names s).
Proof. apply: omap_length_eq => [?[[?|]?]] ?//. Qed.
Lemma field_members_idx_lookup s i n ly:
  s !! i = Some (Some n, ly) →
  field_members s !! field_idx_of_idx s i = Some (n, ly).
Proof. elim: s i => //= -[[?|] ?] s IH [|i] //= ?; simplify_eq => //; by apply: IH. Qed.
Lemma field_idx_of_idx_bound sl i n ly:
  sl_members sl !! i = Some (Some n, ly) →
  (field_idx_of_idx (sl_members sl) i < length (field_names (sl_members sl)))%nat.
Proof. move => /field_members_idx_lookup => /(lookup_lt_Some _ _ _). by rewrite field_members_length. Qed.

Lemma index_of_cons n n' ly s:
  index_of ((n',ly)::s) n = (if decide (n' = Some n) then Some 0%nat else S <$> index_of s n).
Proof. cbn. case_decide => //. rewrite /index_of -!option_fmap_compose. apply option_fmap_ext. by case. Qed.
Lemma index_of_lookup s n i :
  index_of s n = Some i ↔ ∃ ly, s !! i = Some (Some n, ly) ∧ (∀ j y, s !! j = Some y → (j < i)%nat → y.1 ≠ Some n).
Proof.
  rewrite /index_of fmap_Some.
  split.
  - intros ([j [n' ly]] & Ha%list_find_Some & ->).
    simpl in Ha. destruct Ha as (? & -> & ?). eauto.
  - intros (ly & Hlook & ?).
    exists (i, (Some n, ly)). rewrite list_find_Some. done.
Qed.

Lemma field_index_of_leq s n i:
  field_index_of s n = Some i →
  (i < length (field_names s))%nat.
Proof.
  elim: s i => //= -[??]? IH i /= Hf. case_bool_decide; simplify_eq => //=; first lia.
  move: Hf => /fmap_Some[?[Hf ?]]; subst. case_match => /=; naive_solver lia.
Qed.

Lemma field_index_of_to_index_of n s i:
  field_index_of s n = Some i →
  is_Some (index_of s n).
Proof.
  rewrite /index_of.
  elim: s i => // -[n' ly] s IH i/=. case_decide; case_bool_decide => //=; eauto.
  destruct n' => /fmap_Some[x [? _]]; have [|? /fmap_Some[?[->?]]] := IH x; eauto.
Qed.

Lemma field_idx_of_idx_cons_Some x f s k :
  field_idx_of_idx ((Some x, f) :: s) (S k) = S (field_idx_of_idx s k).
Proof.
  done.
Qed.
Lemma field_idx_of_idx_cons_None f s k :
  field_idx_of_idx ((None, f) :: s) (S k) = (field_idx_of_idx s k).
Proof.
  done.
Qed.

Lemma sl_elem_of_field_index_of fields x ly :
  (Some x, ly) ∈ fields → ∃ i, field_index_of fields x = Some i.
Proof.
  induction fields as [ | [[y|] ly'] fields IH].
  - rewrite elem_of_nil. done.
  - rewrite elem_of_cons. intros [[= <- <-] | Hel].
    + exists 0%nat. simpl. by rewrite bool_decide_eq_x_x_true.
    + apply IH in Hel as (i & Hi). destruct (decide (x = y)) as [<- | Hneq].
      { exists 0%nat. simpl. by rewrite bool_decide_eq_x_x_true. }
      exists (S i). simpl.
      rewrite bool_decide_false; last congruence.
      rewrite Hi => //.
  - rewrite elem_of_cons. intros [[= [=] ?] | ?] => /=.
    rewrite option_fmap_id. by apply IH.
Qed.

Lemma sl_index_of_lookup sl n i :
  index_of (sl_members sl) n = Some i ↔ (∃ ly : layout, sl.(sl_members) !! i = Some (Some n, ly)).
Proof.
  rewrite index_of_lookup.
  split; first naive_solver.
  intros (ly & Hsl). exists ly. split; first done.
  intros j (n' & ly') Hlook Hlt.
  simpl. destruct n' as [ n' | ]; last naive_solver.
  intros [= ->].
  move: Hsl Hlook.
  assert (NoDup (field_names (sl_members sl))) as Hnd.
  { specialize (sl_nodup sl). case_bool_decide; naive_solver. }
  move: Hnd. generalize (sl_members sl) as fields. clear sl.
  induction fields as [ | [n1 ly1] fields IH] in i, j, Hlt |-*; simpl.
  { naive_solver. }
  destruct n1 as [ n1 | ].
  - (* named head *)
    rewrite NoDup_cons. intros [Hnel Hnd].
    destruct i as [ | i].
    { simpl. intros [= [= ->] ->]. destruct j; lia. }
    simpl. destruct j as [ | j]; simpl.
    { intros Ha [= [= ->] ->].
      apply Hnel. apply elem_of_list_omap.
      eexists (_, _); split; last done.
      by eapply elem_of_list_lookup_2. }
    { eapply IH; last done. lia. }
  - intros Hnd.
    destruct i as [ | i]; first done.
    simpl. destruct j as [ | j]; simpl; first done.
    eapply IH; last done. lia.
Qed.
Lemma sl_index_of_lookup_1 sl i n :
  index_of sl.(sl_members) n = Some i →
  ∃ ly, sl.(sl_members) !! i = Some (Some n, ly).
Proof.
  intros Ha. apply sl_index_of_lookup. eauto.
Qed.
Lemma sl_index_of_lookup_2 sl i n ly :
  sl.(sl_members) !! i = Some (Some n, ly) →
  index_of sl.(sl_members) n = Some i.
Proof.
  intros Ha. apply sl_index_of_lookup. eauto.
Qed.

Lemma pad_struct_length {A} s (l : list A) f:
  length (pad_struct s l f) = length s.
Proof. elim: s l => //= -[[?|]?] s IH l/=; f_equal; done. Qed.
Lemma pad_struct_lookup_Some {A} s (l : list A) f k x:
  length l = length (field_names s) →
  pad_struct s l f !! k = Some x ↔
    ∃ n ly, s !! k = Some (n, ly) ∧ ((n ≠ None ∧ l !! field_idx_of_idx s k = Some x) ∨ (n = None ∧ x = f ly)).
Proof.
  elim: s k l. { move => ???/=. naive_solver. }
  move => [n ly] s IH k l/= Hl. destruct n => /=.
  - destruct l; simplify_eq/=. destruct k => /=; naive_solver.
  - destruct k => /=; naive_solver.
Qed.
(** the first direction can be slightly strengthened *)
Lemma pad_struct_lookup_Some_1 {A} s (l : list A) f k x:
  pad_struct s l f !! k = Some x →
    ∃ n ly, s !! k = Some (n, ly) ∧
      ((n ≠ None ∧ l !! field_idx_of_idx s k = Some x) ∨
      ((n = None ∨ length l ≤ field_idx_of_idx s k) ∧ x = f ly)).
Proof.
  elim: s k l. { move => ??/=. naive_solver. }
  move => [n ly] s IH k l/=. destruct n => /=.
  - destruct l; simplify_eq/=.
    + intros Hlook. destruct k => /=; simpl in Hlook; naive_solver lia.
    + destruct k => /=.
      * intros [= ->]. naive_solver lia.
      * rewrite field_idx_of_idx_cons_Some. naive_solver lia.
  - destruct k => /=; naive_solver.
Qed.
Lemma pad_struct_lookup_Some_1' {A} (s : field_list) (l : list A) (f : layout → A) (k : nat) (x : A) n ly :
  pad_struct s l f !! k = Some x →
  length l = length (field_names s) →
  s !! k = Some (n, ly) →
  (n ≠ None ∧ l !! field_idx_of_idx s k = Some x) ∨ (n = None ∧ x = f ly).
Proof.
  intros Hlook ? Hlook2.
  apply pad_struct_lookup_Some in Hlook as (? & ? & Hlook2' & ?); last done.
  congruence.
Qed.

Lemma pad_struct_lookup_field_Some_2 {A} s (l : list A) f i j n ly x :
  (* j-th field is named *)
  s !! j = Some (Some n, ly) →
  (* i-th named field *)
  field_idx_of_idx s j = i →
  l !! i = Some x →
  pad_struct s l f !! j = Some x.
Proof.
  elim: s l i j x => // -[n' ly'] s IH l i j x/= Hin Hf Ha.
  destruct j as [ | j]; simpl in Hin; simplify_eq; first by destruct l.
  move: Hin Ha => /=; subst.
  destruct n'.
  - rewrite field_idx_of_idx_cons_Some -lookup_tail. intros; eapply IH; done.
  - intros. eapply IH; done.
Qed.
Lemma pad_struct_lookup_field_Some_2' {A} s (l : list A) f i j n x :
  index_of s n = Some j →
  field_index_of s n = Some i →
  l !! i = Some x →
  pad_struct s l f !! j = Some x.
Proof.
  elim: s l i j => // -[n' ly] s IH l i j/= Hin Hf ?. rewrite index_of_cons in Hin.
  case_bool_decide; case_decide => //; simplify_eq; first by destruct l.
  move: Hin Hf => /fmap_Some[j'[??]] /fmap_Some[?[??]]; subst.
  by case_match; destruct l => //=; apply: IH.
Qed.
Lemma pad_struct_lookup_field_Some_2'' {A} s (l : list A) f i j n x :
  (* j-th field *)
  index_of s n = Some j →
  (* i-th named field *)
  field_idx_of_idx s j = i →
  l !! i = Some x →
  pad_struct s l f !! j = Some x.
Proof.
  intros (? & ? & _)%index_of_lookup ? ?. eapply pad_struct_lookup_field_Some_2; done.
Qed.

Lemma pad_struct_lookup_field_None_2 {A} s (l : list A) f i j n ly :
  s !! j = Some (n, ly) →
  field_idx_of_idx s j = i →
  (n = None ∨ length l ≤ i) →
  pad_struct s l f !! j = Some (f ly).
Proof.
  elim: s l i j => // -[n' ly'] s IH l i j /= Hin Hf Ha.
  destruct j; simpl in *.
  - destruct n', l; simplify_eq; destruct Ha; done.
  - destruct n'; simplify_eq; simpl.
    + eapply IH; [done.. | ].
      destruct Ha; first by left.
      right. rewrite field_idx_of_idx_cons_Some in H.
      destruct l; simpl in *; lia.
    + rewrite field_idx_of_idx_cons_None in Ha.
      eapply IH; done.
Qed.

Lemma pad_struct_lookup_Some_Some {A} s l f k (x : A) n ly :
  length l = length (field_names s) →
  pad_struct s l f !! k = Some x →
  s !! k = Some (Some n, ly) →
  l !! field_idx_of_idx s k = Some x.
Proof.
  intros Hlen Hlook1 Hlook2.
  apply pad_struct_lookup_Some in Hlook1; last done.
  destruct Hlook1 as (n' & ly' & Hlooka & Hlook1).
  rewrite Hlook2 in Hlooka. injection Hlooka as [= <- <-].
  destruct Hlook1 as [(_ & ?) | (? & _)]; naive_solver.
Qed.
Lemma pad_struct_lookup_Some_None {A} s l f k (x : A) ly :
  length l = length (field_names s) →
  pad_struct s l f !! k = Some x →
  s !! k = Some (None, ly) →
  x = f ly.
Proof.
  intros Hlen Hlook1 Hlook2.
  apply pad_struct_lookup_Some in Hlook1; last done.
  destruct Hlook1 as (n' & ly' & Hlooka & Hlook1).
  rewrite Hlook2 in Hlooka. injection Hlooka as [= <- <-].
  destruct Hlook1 as [(? & ?) | (? & ?)]; naive_solver.
Qed.

Lemma pad_struct_insert_field {A} s (l : list A) f i j n x :
  index_of s n = Some j →
  field_index_of s n = Some i →
  (i < length l)%nat →
  <[j:=x]> (pad_struct s l f) = pad_struct s (<[i:=x]> l) f.
Proof.
  elim: s l i j => // -[n' ly] s IH l i j /= Hin Hf ?. rewrite index_of_cons in Hin.
  case_bool_decide; case_decide => //; simplify_eq; first by destruct l; naive_solver lia.
  move: Hin Hf => /fmap_Some[j'[??]] /fmap_Some[?[??]]; subst. destruct l; first by naive_solver lia.
  case_match => /=; f_equal; apply IH; naive_solver lia.
Qed.

Lemma pad_struct_snoc_Some {A} s n ly ls (l : A) f :
  length (field_names s) = length ls →
  pad_struct (s ++ [(Some n, ly)]) (ls ++ [l]) f = pad_struct s ls f ++ [l].
Proof.
  elim: s ls => /=. 1: by destruct ls.
  move => -[n' ly'] s IH ls /=. case_match.
  - destruct ls => //= -[?]. f_equal. by apply IH.
  - move => ?. f_equal. by apply IH.
Qed.

Lemma pad_struct_snoc_None {A} s ly (ls : list A) f :
  pad_struct (s ++ [(None, ly)]) ls f = pad_struct s ls f ++ [f ly].
Proof. elim: s ls => //=. move => -[n' ly'] s IH ls /=. f_equal. by apply IH. Qed.

Lemma pad_struct_fmap {A B} (fields : field_list) (l : list A) (g : layout → A) (f : A → B) :
  pad_struct fields (fmap f l) (λ ly : layout, f (g ly)) =
  fmap f (pad_struct fields l g).
Proof.
  induction fields as [ | [n ly] fields IH] in l |-*; simpl; first done.
  destruct n as [ n | ].
  - rewrite (apply_default f). f_equiv.
    { f_equiv. induction l; eauto. }
    rewrite -fmap_tail IH //.
  - f_equiv. apply IH.
Qed.
Lemma pad_struct_ext {A} (fields : field_list) (l : list A) (f g : layout → A) :
  (∀ ly : layout, f ly = g ly) →
  pad_struct fields l f = pad_struct fields l g.
Proof.
  intros Heq. induction fields as [ | [n ly] fields IH] in l |-*; simpl; first done.
  destruct n as [n | ].
  - rewrite Heq. f_equiv. apply IH.
  - rewrite Heq. f_equiv. apply IH.
Qed.

Lemma offset_of_cons' n n' ly s:
  offset_of ((n', ly)::s) n = (if decide (n' = Some n) then Some 0 else (λ m, ly_size ly + m) <$> (offset_of s n))%nat.
Proof. rewrite /offset_of/= index_of_cons. case_decide => //=. destruct (index_of s n) eqn: Hfind => //=. Qed.

Lemma offset_of_cons n n' ly s:
  n' = Some n ∨ n ∈ field_names s →
  default 0%nat (offset_of ((n', ly)::s) n) = (if decide (n' = Some n) then 0 else ly_size ly + (default 0%nat (offset_of s n)))%nat.
Proof.
  rewrite /offset_of/= index_of_cons. case_decide => //= -[|/elem_of_list_omap[x Hin]]//.
  destruct (index_of s n) eqn: Hfind => //=.
  move: Hfind => /fmap_None/list_find_None /Forall_forall Hfind. set_solver.
Qed.

Lemma offset_of_from_in m s:
  Some m ∈ s.*1 → ∃ n, offset_of s m = Some n.
Proof.
  elim: s. 1: set_solver.
  move => [??]? IH. rewrite offset_of_cons'. csimpl => ?.
  case_decide => //; [ naive_solver |].
  have [|? ->] := IH. 1: by set_solver.
  naive_solver.
Qed.

Lemma offset_of_idx_le_size sl i:
  (offset_of_idx (sl_members sl) i ≤ ly_size sl)%nat.
Proof. apply: sum_list_with_take. Qed.
Lemma offset_of_idx_with_mem_le_size sl i ly:
  snd <$> sl_members sl !! i = Some ly →
  (offset_of_idx (sl_members sl) i + ly_size ly ≤ ly_size sl)%nat.
Proof.
  intros Hlook.
  rewrite {2}/ly_size/=.
  rewrite /offset_of_idx.
  rewrite -{2}(take_drop i (ly_size <$> (sl_members sl).*2)).
  rewrite sum_list_with_app.
  enough (ly_size ly ≤ sum_list (drop i (ly_size <$> (sl_members sl).*2))) by lia.
  erewrite drop_S; first last.
  { rewrite !list_lookup_fmap Hlook//. }
  simpl. lia.
Qed.

Lemma offset_of_bound i sl:
  offset_of_idx sl.(sl_members) i ≤ max_int isize_t.
Proof.
  have ?:= sl_size sl.
  enough (offset_of_idx (sl_members sl) i ≤ sum_list (ly_size <$> (sl_members sl).*2)) by lia.
  by apply Nat2Z.inj_le, sum_list_with_take.
Qed.

Fixpoint check_fields_aligned_alt (s : field_list) (l : loc) : Prop :=
  match s with
  | [] => True
  | (_,ly)::s' => l `has_layout_loc` ly ∧ check_fields_aligned_alt s' (l +ₗ ly.(ly_size))
  end.

Lemma check_fields_aligned_alt_correct sl l:
  l `has_layout_loc` layout_of sl →
  check_fields_aligned_alt sl.(sl_members) l.
Proof.
  rewrite /layout_of.
  have := sl_fields_aligned sl. rewrite -{2}[l]shift_loc_0_nat. move: O => off.
  elim: (sl_members sl) off => // -[n ly] s IH; csimpl => off /andb_true_iff[/bool_decide_eq_true/Z.mod_divide Hdiv ?]?.
  split.
  - apply aligned_to_offset.
    + apply: has_layout_loc_trans => //. rewrite /ly_align_log. lia.
    + apply Hdiv. have ->: 0 = O by []. move => /Nat2Z.inj/Nat.pow_nonzero. lia.
  - rewrite shift_loc_assoc_nat. apply IH => //. apply: has_layout_loc_trans => //. rewrite /ly_align_log. lia.
Qed.

Lemma struct_layout_member_size_bound sl n :
  ∀ on ly, (on, ly) ∈ sl_members sl → ly_size sl ≤ n → ly_size ly ≤ n.
Proof.
  intros on ly.
  rewrite /layout_of{1}/ly_size/=.
  generalize (sl_members sl) as mems.
  induction mems as [ | [n2 ly2] mem IH].
  { intros []%elem_of_nil. }
  intros Ha%elem_of_cons. destruct Ha as [[= <- <-] | Hel].
  - simpl. lia.
  - simpl. intros Ha. apply IH; first done.
    unfold fmap. lia.
Qed.

Lemma struct_layout_field_aligned (sl : struct_layout) l :
  l `has_layout_loc` sl →
  ∀ k ly,
  snd <$> sl_members sl !! k = Some ly →
  l +ₗ offset_of_idx (sl_members sl) k `has_layout_loc` ly.
Proof.
  intros Hl%check_fields_aligned_alt_correct k ly Hlook.
  elim: (sl_members sl) l Hl k Hlook => //.
  intros [n ly0] s IH l [Hl0 Hl] k Hlook.
  rewrite /offset_of_idx.
  destruct k as [ | k]; simpl in *.
  { injection Hlook as [= ->]. rewrite shift_loc_0_nat. done. }
  rewrite -(shift_loc_assoc_nat l).
  eapply IH; done.
Qed.

(** get the named fields of a struct field list *)
Definition named_fields (sl_fields : field_list) : list (var_name * layout) :=
  foldr (λ '(n, ly) acc, match n with Some n => (n, ly) :: acc | _ => acc end) [] sl_fields.
Lemma elem_of_named_fields x ly members :
  (x, ly) ∈ named_fields members ↔ (Some x, ly) ∈ members.
Proof.
  induction members as [ | [[y|] ly'] members IH].
  - simpl. split; rewrite !elem_of_nil; done.
  - simpl. rewrite !elem_of_cons IH. naive_solver.
  - simpl. rewrite elem_of_cons. naive_solver.
Qed.
Lemma elem_of_named_fields_field_names fields v ly :
  (v, ly) ∈ named_fields fields → v ∈ field_names fields.
Proof.
  induction fields as [ | [[]] fields IH]; simpl.
  - rewrite elem_of_nil. done.
  - rewrite elem_of_cons. intros [[= <- <-] | ? ]; apply elem_of_cons.
    + eauto.
    + right. by apply IH.
  - done.
Qed.
Lemma named_fields_lookup_1 fields v ly i :
  named_fields fields !! i = Some (v, ly) → ∃ j, fields !! j = Some (Some v, ly).
Proof.
  induction fields as [ | [[]] fields IH] in i |-*; simpl; first done.
  - destruct i as [ | i]; simpl.
    + intros [= -> ->]. exists 0%nat. done.
    + intros (j & ?)%IH. exists (S j). done.
  - intros (j & ?)%IH. exists (S j). done.
Qed.
Lemma named_fields_lookup_2 fields v ly i :
  fields !! i = Some (Some v, ly) → ∃ j, named_fields fields !! j = Some (v, ly).
Proof.
  induction fields as [ | [[]] fields IH] in i |-*; simpl; first done.
  - destruct i as [ | i]; simpl.
    + intros [= -> ->]. exists 0%nat. done.
    + intros (j & ?)%IH. exists (S j). done.
  - destruct i as [ | i].
    + intros [=].
    + intros (j & ?)%IH. exists j. done.
Qed.
(** A stronger version that gives us the concrete index, if there are no duplicate field names *)
Lemma named_fields_lookup_field_index_of fields i x ly :
  NoDup (field_names fields) →
  named_fields fields !! i = Some (x, ly) →
  field_index_of fields x = Some i.
Proof.
  intros Hnd.
  induction fields  as [ | [[]] fields IH] in i, Hnd |-*; simpl; first done.
  - case_bool_decide as Heq.
    + injection Heq as [= <-].
      inversion Hnd; subst.
      destruct i as [ | i]; first done.
      simpl. intros Hel%elem_of_list_lookup_2.
      exfalso.
      apply elem_of_named_fields_field_names in Hel. done.
    + destruct i as [ | i]. { intros [= <- <-]. done. }
      simpl. inversion Hnd; subst. intros Hlook. erewrite IH; done.
  - rewrite option_fmap_id. simpl in Hnd. apply IH. done.
Qed.
Lemma named_fields_eq fields :
  named_fields fields = omap (λ '(name, ly), name ← name; Some(name, ly)) fields.
Proof.
  induction fields as [ | [[name | ] ly] fields IH]; simpl; first done.
  - rewrite IH. done.
  - done.
Qed.
Lemma named_fields_field_names_length fields :
  length (named_fields fields) = length (field_names fields).
Proof.
  rewrite named_fields_eq /field_names.
  apply omap_length_eq. intros ? [[] ] ? => //.
Qed.


Definition GetMemberLoc (l : loc) (s : struct_layout) (m : var_name) : loc :=
  (l +ₗ Z.of_nat (default 0%nat (offset_of s.(sl_members) m))).
Notation "l 'at{' s '}ₗ' m" := (GetMemberLoc l s m) (at level 10, format "l  'at{' s '}ₗ'  m") : stdpp_scope.
Global Typeclasses Opaque GetMemberLoc.
Arguments GetMemberLoc : simpl never.

(** ** Unions *)
Record union_layout := {
   ul_members : list (var_name * layout);
   ul_nodup : bool_decide (NoDup ul_members.*1);
   (* Note: difference to RefinedC: we require isize_t as the bound, not usize_t *)
   ul_size : max_list (ly_size <$> ul_members.*2) < max_int isize_t + 1;
}.

Definition ul_layout (ul : union_layout) : layout := {|
  ly_size := max_list (ly_size <$> ul.(ul_members).*2);
  ly_align_log := max_list (ly_align_log <$> ul.(ul_members).*2)
|}.
Coercion ul_layout : union_layout >-> layout.

Definition index_of_union (n : var_name) (ul : union_layout) : option nat :=
  fst <$> list_find (λ x, x.1 = n) ul.(ul_members).

Definition layout_of_union_member (n : var_name) (ul : union_layout) : option layout :=
  i ← index_of_union n ul; (snd <$> ul.(ul_members) !! i).

Lemma union_layout_eq ul1 ul2 :
  ul1.(ul_members) = ul2.(ul_members) →
  ul1 = ul2.
Proof. destruct ul1, ul2 => /= ?. subst. f_equal; apply: proof_irrel. Qed.

Lemma layout_of_union_member_in_ul n ul ly:
  layout_of_union_member n ul = Some ly →
  ly ∈ ul.(ul_members).*2.
Proof.
  rewrite /layout_of_union_member. destruct (index_of_union n ul) => //= Hin.
  apply: elem_of_list_lookup_2. by rewrite list_lookup_fmap.
Qed.

Lemma index_of_union_lookup ul i n ly:
  ul.(ul_members) !! i = Some (n, ly) →
  index_of_union n ul = Some i.
Proof.
  move => H1. apply fmap_Some. exists (i, (n, ly)). split => //.
  apply list_find_Some. split_and! => // j[??]H2? /=?. subst.
  suff : (i = j) by lia. apply: NoDup_lookup.
  { eapply bool_decide_spec. apply (ul_nodup ul). }
  all: rewrite list_lookup_fmap; apply fmap_Some; naive_solver.
Qed.

Definition GetMemberUnionLoc (l : loc) (ul : union_layout) (m : var_name) : loc := (l).
Notation "l 'at_union{' ul '}ₗ' m" := (GetMemberUnionLoc l ul m) (at level 10, format "l  'at_union{' ul '}ₗ'  m") : stdpp_scope.
Global Typeclasses Opaque GetMemberUnionLoc.
Arguments GetMemberUnionLoc : simpl never.

(** ** op_type *)
Inductive op_type : Set :=
| BoolOp
| IntOp (i : int_type)
| PtrOp
| StructOp (sl : struct_layout) (ots : list op_type)
| UntypedOp (ly : layout)
| CharOp.

Definition ot_layout (ot : op_type) : layout :=
  match ot with
  | BoolOp => bool_layout
  | PtrOp => void*
  | IntOp it => it_layout it
  | StructOp sl ots => sl
  | UntypedOp ly => ly
  | CharOp => char_layout
  end.

Lemma op_type_recursor (P : op_type → Type) :
  P BoolOp →
  (∀ it, P (IntOp it)) →
  P PtrOp →
  (∀ sl ots, list_is_list _ P ots → P (StructOp sl ots)) →
  (∀ ly, P (UntypedOp ly)) →
  P CharOp →
  ∀ ot, P ot.
Proof.
  intros Hbool Hint Hptr Hstruct Huntyped Hchar.
  refine (fix IH ot {struct ot} := _ ).
  destruct ot.
  - apply Hbool.
  - apply Hint.
  - apply Hptr.
  - apply Hstruct.
    by apply list_is_list_full.
  - apply Huntyped.
  - apply Hchar.
Qed.

(* Well-formedness of op_types requires that [StructOp] has coherent op_types for every struct component *)
Fixpoint op_type_wf (ot : op_type) :=
  match ot with
  | StructOp sl ots =>
      Forall2_cb (λ ot '(n, ly), op_type_wf ot ∧ ot_layout ot = ly) ots (named_fields sl.(sl_members))
  | _ => True
  end.
