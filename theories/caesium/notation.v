From caesium Require Export lang syntypes.
Set Default Proof Using "Type".

Coercion val_of_loc : loc >-> val.
Coercion Val : val >-> expr.
Coercion Var : var_name >-> expr.
Definition string_to_varname (s : string) : var_name := s.
Coercion string_to_varname : string >-> var_name.
Coercion it_layout : int_type >-> layout.
Notation "☠" := MPoison : val_scope.
Notation "!{ ot , o , mc } e" := (Deref o ot mc e%E) (at level 9, format "!{ ot ,  o ,  mc } e") : expr_scope.
Notation "!{ ot , o } e" := (Deref o ot true e%E) (at level 9, format "!{ ot ,  o } e") : expr_scope.
Notation "!{ ot } e" := (Deref Na1Ord ot true e%E) (at level 9, format "!{ ot } e") : expr_scope.
(* − is a unicode minus, not the normal minus to prevent parsing conflicts *)
Notation "'−' '{' ot } e" := (UnOp NegOp ot e%E)
  (at level 40, format "'−' '{' ot }  e") : expr_scope.
Notation "e1 '+' '{' ot1 , ot2 } e2" := (BinOp AddOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '+' '{' ot1 ,  ot2 }  e2") : expr_scope.
(* This conflicts with rewrite -{2}(app_nil_r vs). *)
Notation "e1 '-' '{' ot1 , ot2 } e2" := (BinOp SubOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '-' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 '=' '{' ot1 , ot2 , rit } e2" := (BinOp (EqOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  '=' '{' ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 '!=' '{' ot1 , ot2 , rit } e2" := (BinOp (NeOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  '!=' '{' ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 ≤{ ot1 , ot2 , rit } e2" := (BinOp (LeOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ≤{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 <{ ot1 , ot2 , rit } e2" := (BinOp (LtOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  <{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 ≥{ ot1 , ot2 , rit } e2" := (BinOp (GeOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ≥{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 >{ ot1 , ot2 , rit } e2" := (BinOp (GtOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  >{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 ×{ ot1 , ot2 } e2" := (BinOp MulOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ×{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 /{ ot1 , ot2 } e2" := (BinOp DivOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  /{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 %{ ot1 , ot2 } e2" := (BinOp ModOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  %{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 <<{ ot1 , ot2 } e2" := (BinOp ShlOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  <<{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 >>{ ot1 , ot2 } e2" := (BinOp ShrOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  >>{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 &b{ ot1 , ot2 } e2" := (BinOp AndOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  &b{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 |{ ot1 , ot2 } e2" := (BinOp OrOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  |{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 ^{ ot1 , ot2 } e2" := (BinOp XorOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ^{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 ,{ ot1 , ot2 } e2" := (BinOp Comma ot1 ot2 e1%E e2%E)
  (at level 30, format "e1  ,{ ot1 ,  ot2 }  e2") : expr_scope.

Notation "e1 '+c' '{' ot1 , ot2 } e2" := (BinOp CheckedAddOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '+c' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 '-c' '{' ot1 , ot2 } e2" := (BinOp CheckedSubOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '-c' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 '×c{' ot1 , ot2 } e2" := (BinOp CheckedMulOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '×c{' ot1 ,  ot2 }  e2") : expr_scope.

(* The offset must be evaluated first for the type system to work, thus the order is switched here. *)
Notation "e1 'at_offset{' ly , ot1 , ot2 } e2" := (BinOp (PtrOffsetOp ly) ot2 ot1 e2%E e1%E)
  (at level 70, format "e1  at_offset{ ly ,  ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 'at_neg_offset{' ly , ot1 , ot2 } e2" := (BinOp (PtrNegOffsetOp ly) ot2 ot1 e2%E e1%E)
  (at level 70, format "e1  at_neg_offset{ ly ,  ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 'sub_ptr{' ly , ot1 , ot2 } e2" := (BinOp (PtrDiffOp ly) ot2 ot1 e1%E e2%E)
  (at level 70, format "e1  sub_ptr{ ly ,  ot1 ,  ot2 }  e2") : expr_scope.
Notation "'if{' ot ',' join '}' ':' e1 'then' s1 'else' s2" := (IfS ot join e1%E s1%E s2%E)
  (at level 102, e1, s1, s2 at level 150, format "'[v' 'if{' ot ','  join '}' ':'  e1  'then' '/  ' s1 '/' 'else' '/  ' s2 ']'") : expr_scope.
Notation "'if{' ot '}' ':' e1 'then' s1 'else' s2" := (IfS ot None e1%E s1%E s2%E)
  (at level 102, e1, s1, s2 at level 150, format "'[v' 'if{' ot '}' ':'  e1  'then' '/  ' s1 '/' 'else' '/  ' s2 ']'") : expr_scope.
Notation "'expr:' e ; s" := (ExprS e%E s%E)
  (at level 80, s at level 200, format "'[v' 'expr:'  e ';' '/' s ']'") : expr_scope.

Definition LogicalAnd (ot1 ot2 : op_type) rit (e1 e2 : expr) : expr :=
  (IfE ot1 e1 (IfE ot2 e2 (i2v 1 rit) (i2v 0 rit)) (i2v 0 rit)).
Notation "e1 &&{ ot1 , ot2 , rit } e2" := (LogicalAnd ot1 ot2 rit e1 e2)
  (at level 70, format "e1  &&{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Arguments LogicalAnd : simpl never.
Global Typeclasses Opaque LogicalAnd.

Definition LogicalOr (ot1 ot2 : op_type) rit (e1 e2 : expr) : expr :=
  (IfE ot1 e1 (i2v 1 rit) (IfE ot2 e2 (i2v 1 rit) (i2v 0 rit))).
Notation "e1 ||{ ot1 , ot2 , rit } e2" := (LogicalOr ot1 ot2 rit e1 e2)
  (at level 70, format "e1  ||{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Arguments LogicalOr : simpl never.
Global Typeclasses Opaque LogicalOr.

Definition Assert (ot : op_type) (e : expr) (s : stmt) : stmt := (if{ ot, None }: e then s else StuckS)%E.
Notation "'assert{' ot '}' ':' e ; s" := (Assert ot e%E s%E)
  (at level 80, s at level 200, format "'[v' 'assert{' ot '}' ':'  e ';' '/' s ']'") : expr_scope.
Arguments Assert : simpl never.
Global Typeclasses Opaque Assert.

Notation "'free{' e_size ',' e_align '}' e_ptr ; s" := (Free e_size%E e_align%E e_ptr%E s%E)
  (at level 80, s at level 200, format "'[v' 'free{' e_size ','  e_align '}'  e_ptr ';' '/' s ']'") : expr_scope.


(** This has a skip in order to facilitate unblocking. *)
Definition Use (o : order) (ot : op_type) (memcast : bool) (e : expr) := Deref o ot memcast (SkipE e).
Notation "'use{' ot , o , mc } e" := (Use o ot mc e%E) (at level 9, format "'use{' ot ,  o ,  mc }  e") : expr_scope.
Notation "'use{' ot , o } e" := (Use o ot true e%E) (at level 9, format "'use{' ot ,  o }  e") : expr_scope.
Notation "'use{' ot } e" := (Use Na1Ord ot true e%E) (at level 9, format "'use{' ot }  e") : expr_scope.
Arguments Use : simpl never.
Global Typeclasses Opaque Use.

(* This has a skip in order to facilitate unblocking. *)
Definition AssignSE o ot e1 e2 s := Assign o ot (SkipE e1) e2 s.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <-{ ot , o } e2 ; s" := (AssignSE o ot e1%E e2%E s%E)
  (at level 80, s at level 200, format "'[v' e1  '<-{' ot ',' o '}'  e2 ';' '/' s ']'") : expr_scope.
Notation "e1 <-{ ot } e2 ; s" := (AssignSE Na1Ord ot e1%E e2%E s%E)
  (at level 80, s at level 200, format "'[v' e1  '<-{' ot '}'  e2 ';' '/' s ']'") : expr_scope.
Arguments AssignSE : simpl never.
Global Typeclasses Opaque AssignSE.

Definition AddrOf (e : expr) := e.
(* TODO: this breaks the sigT notation { A : Type & (A -> nat) }. See if we can do something about it. *)
Notation "& e" := (AddrOf e%E) (at level 9, format "& e") : expr_scope.
Arguments AddrOf : simpl never.
Global Typeclasses Opaque AddrOf.

Inductive mutability := | Mut | Shr.
Inductive ptr_kind := | PRaw | PRef.

(** A syntactic representation of Rust types we support in type annotations. *)
Inductive rust_type : Type :=
  | RSTTyVar (name : string)
  | RSTLitType (ty : list string) (app : list rust_type)
  | RSTInt (it : IntType)
  | RSTBool
  | RSTUnit
  | RSTStruct (sls : struct_layout_spec) (components : list rust_type)
  | RSTArray (len : nat) (el : rust_type)
  | RSTRef (m : mutability) (lft : string) (ty : rust_type)
.

(* We need two skips:
   - one for stratifying,
   - and one for initiating sharing (in the case of shared references) or for the prepaying of mutable references (in the mutable case)
  There's no inherent other step we could use, except for possibly the step for the assignment to the LHS
    (but that would kill modularity). *)
Definition Ref (m : mutability) (κ : string) (ty : option rust_type) (e : expr) := SkipE (SkipE e).
Definition Raw (m : mutability) (e : expr) := SkipE e.
Notation "'&ref{' mut , ty , κ '}' e" := (Ref mut κ ty e) (at level 9, format "&ref{ mut , ty , κ }  e") : expr_scope.
Notation "'&raw{' mut '}' e" := (Raw mut e) (at level 9, format "&raw{ mut }  e") : expr_scope.
Arguments Ref : simpl never.
Global Typeclasses Opaque Ref.
Arguments Raw : simpl never.
Global Typeclasses Opaque Raw.

Definition LValue (e : expr) := e.
Arguments LValue : simpl never.
Global Typeclasses Opaque LValue.

Definition AnnotExpr (n : nat) {A} (a : A) (e : expr) := Nat.iter n SkipE e.
Arguments AnnotExpr : simpl never.
Global Typeclasses Opaque AnnotExpr.

Notation "'return' e" := (Return (SkipE (SkipE e%E))) (at level 80, format "'return'  e") : expr_scope.

(* We define this in terms of expressions in order to be able to `bind` the skips.
  This is what enables us to use [wp_step_fupdN] in a sensible way that allows
  us to regain the right masks. Formulating with [SkipS] would require us to
  stick with an empty mask for [s].
 *)
Definition SkipES := ExprS (SkipE (Val [])).
Arguments SkipES : simpl never.
Global Typeclasses Opaque SkipES.
Definition AnnotStmt (n : nat) {A} (a : A) (s : stmt) := Nat.iter n SkipES s.
Notation "'annot:' a ; s" := (AnnotStmt 1%nat a s%E)
  (at level 80, s at level 200, format "'annot:'  a ;  s") : expr_scope.
Arguments AnnotStmt : simpl never.
Global Typeclasses Opaque AnnotStmt.

Definition Move (o : order) (ot : op_type) (memcast : bool) (e : expr) := Deref o ot memcast e.
Notation "'move{' ot , o , mc } e" := (Move o (UntypedOp ot) mc e%E) (at level 9, format "'move{' ot ,  o ,  mc }  e") : expr_scope.
Notation "'move{' ot } e" := (Move Na1Ord (UntypedOp ot) true e%E) (at level 9, format "'move{' ot }  e") : expr_scope.
Arguments Move : simpl never.
Global Typeclasses Opaque Move.

(* This uses a syn_type at the surface level so that we have the syn_type annotation still available in the type system *)
Definition Box `{!LayoutAlg} (st : syn_type) :=
  let ly := (use_layout_alg' st) in
  Alloc (Val $ i2v (ly_size ly) usize_t) (Val $ i2v (ly_align_log ly) usize_t).
Notation "'box{' st '}'" := (Box st) (at level 9, format "'box{' st }") : expr_scope.
Arguments Box : simpl never.
Global Typeclasses Opaque Box.


Inductive location_info :=
| LocationInfo (file : string) (line_start column_start line_end column_end : Z).

Definition LocInfo {B} (a : location_info) (b : B) := b.
Arguments LocInfo : simpl never.
Global Typeclasses Opaque LocInfo.
Notation "'locinfo:' a ; b" := (LocInfo (B:=stmt) a b%E)
  (at level 80, b at level 200, format "'[v' 'locinfo:'  a ';' '/' b ']'") : expr_scope.
Notation LocInfoE := (LocInfo (B:=expr)).

Definition MacroE (m : list expr → expr) (es : list expr) := m es.
Arguments MacroE : simpl never.
Global Typeclasses Opaque MacroE.

(* One could probably get rid of this type class by swallowing the
substitutions in MacroE, i.e. make it parametrized by a list of names
and a list of expressions which are substituted in m. (Then one can
maybe also get rid of es?) *)
Class MacroWfSubst (m : list expr → expr) : Prop :=
  macro_wf_subst x v es: subst x v (m es) = m (subst x v <$> es)
.

(* Like [MacroE m es] but checks that [m es] is equal to [e] *)
Notation CheckedMacroE m es e := (ltac:(
   let rec get_head e := match e with
                         | ?f ?a => get_head f
                         | ?x => x
                         end in
   let mhead := get_head constr:(m%function) in
   let munf := (eval unfold mhead in (m%function)) in
   let esunf := (eval unfold LocInfo in (es%list)) in
   let eunf := (eval unfold LocInfo in e) in
   (* idtac munf; *)
   unify (munf esunf) eunf with typeclass_instances;
   exact (MacroE m es))) (only parsing).


Lemma annot_expr_S {A} n (a : A) e:
  AnnotExpr (S n) a e = SkipE (AnnotExpr n a e).
Proof. done. Qed.
Lemma annot_expr_S_r {A} n (a : A) e:
  AnnotExpr (S n) a e = (AnnotExpr n a (SkipE e)).
Proof. by rewrite /AnnotExpr Nat.iter_succ_r. Qed.
Lemma annot_stmt_S {A} n (a : A) s:
  AnnotStmt (S n) a s = SkipES (AnnotStmt n a s).
Proof. done. Qed.
Lemma annot_stmt_S_r {A} n (a : A) s:
  AnnotStmt (S n) a s = (AnnotStmt n a (SkipES s)).
Proof. by rewrite /AnnotStmt Nat.iter_succ_r. Qed.

(** Call notation including lifetime instantiation *)
Definition CallE (ef : expr) (eκs : list string) (es : list expr) := Call ef es.
Arguments CallE : simpl  never.
Global Typeclasses Opaque CallE.

(*** Layouts and structs *)
Definition StructInit' (sl : struct_layout) (fs : list (string * expr)) : expr :=
  let fs : gmap string expr := list_to_map fs in
  let fn idly := default (Val (replicate (ly_size idly.2) MPoison)) (x ← idly.1; fs !! x) in
  Concat (fn <$> sl_members sl).
Definition StructInit `{!LayoutAlg} (sls : struct_layout_spec) (fs : list (string * expr)) : expr :=
  let sl : struct_layout := use_struct_layout_alg' sls in
  StructInit' sl fs.
Global Typeclasses Opaque StructInit.
Arguments StructInit : simpl never.


Definition EnumInit `{!LayoutAlg} (els : enum_layout_spec) (variant : string) (ty : rust_type) (e : expr) : expr :=
  let sts : gmap string syn_type := list_to_map els.(els_variants) in
  let variant_st := default UnitSynType (sts !! variant) in
  let ul := use_union_layout_alg' (uls_of_els els) in
  let variant_ly := use_layout_alg' variant_st in
  let padding := Val (replicate (ly_size ul - ly_size variant_ly) MPoison) in
  let discriminant_map : gmap string Z := list_to_map (els.(els_tag_int)) in
  let discriminant : Z := default 0%Z (discriminant_map !! variant) in
  StructInit (sls_of_els els) [("discriminant", Val (i2v discriminant els.(els_tag_it))); ("data", Concat [e; padding])].
Global Typeclasses Opaque EnumInit.
Arguments EnumInit : simpl never.

(* NOTE: in contrast to Caesium, this uses isize_t, because LLVMs GEP uses signed integer offsets
      https://llvm.org/docs/LangRef.html#getelementptr-instruction *)
Definition GetMember' (e : expr) (sl : struct_layout) (m : var_name) : expr :=
  (e at_offset{u8, PtrOp, IntOp isize_t} Val (default [MPoison] (offset_of sl.(sl_members) m ≫= (λ m, val_of_Z (Z.of_nat m) isize_t None))))%E.
Definition GetMember `{!LayoutAlg} (e : expr) (sls : struct_layout_spec) (m : var_name) : expr :=
  let sl := use_struct_layout_alg' sls in
  GetMember' e sl m.
Notation "e 'at{' s } m" := (GetMember e%E s m) (at level 10, format "e  'at{' s }  m") : expr_scope.
Global Typeclasses Opaque GetMember.
Arguments GetMember : simpl never.

Definition OffsetOf `{!LayoutAlg} (sls : struct_layout_spec) (m : var_name) : expr :=
  let sl := use_struct_layout_alg' sls in
  (default StuckE (Val <$> (offset_of sl.(sl_members) m) ≫= (λ m, val_of_Z (Z.of_nat m) isize_t None)))%E.
Global Typeclasses Opaque OffsetOf.
Arguments OffsetOf : simpl never.

Definition GetMemberUnion (e : expr) (uls : union_layout_spec) (m : var_name) : expr := (e)%E.
Notation "e 'at_union{' uls } m" := (GetMemberUnion e%E uls m) (at level 10, format "e  'at_union{' uls }  m") : expr_scope.
Global Typeclasses Opaque GetMemberUnion.
Arguments GetMemberUnion : simpl never.

(* NOTE: this uses isize_t instead of usize_t (in RefinedC) *)
Definition OffsetOfUnion (ul : union_layout_spec) (m : var_name) : expr := (i2v 0 isize_t).
Global Typeclasses Opaque OffsetOfUnion.
Arguments OffsetOfUnion : simpl never.

Definition EnumDiscriminant `{!LayoutAlg} (els : enum_layout_spec) (e : expr) : expr :=
  let el := use_enum_layout_alg' els in
  GetMember' e el "discriminant".
Global Typeclasses Opaque EnumDiscriminant.
Arguments EnumDiscriminant : simpl never.

Definition EnumData `{!LayoutAlg} (els : enum_layout_spec) (variant : var_name) (e : expr) : expr :=
  let el := use_enum_layout_alg' els in
  GetMemberUnion (GetMember' e el "data") (uls_of_els els) variant.
Global Typeclasses Opaque EnumData.
Arguments EnumData : simpl never.

(** Shift a location by [z] times the size of [ly]. *)
Definition OffsetLocSt `{!LayoutAlg} (l : loc) (st : syn_type) (z : Z) : loc := (l +ₗ (use_layout_alg' st).(ly_size) * z).
Notation "l 'offsetst{' st '}ₗ' z" := (OffsetLocSt l%L st z%Z)
  (at level 39, format "l  'offsetst{' st '}ₗ'  z", left associativity) : loc_scope.
Global Typeclasses Opaque OffsetLocSt.
Arguments OffsetLocSt : simpl never.

Definition GetMemberLocSt `{!LayoutAlg} (l : loc) (s : struct_layout_spec) (m : var_name) : loc :=
  (l +ₗ Z.of_nat (default 0%nat (offset_of (use_struct_layout_alg' s).(sl_members) m))).
Notation "l 'atst{' s '}ₗ' m" := (GetMemberLocSt l s m) (at level 10, format "l  'atst{' s '}ₗ'  m") : stdpp_scope.
Global Typeclasses Opaque GetMemberLocSt.
Arguments GetMemberLocSt : simpl never.

Definition GetEnumDataLocSt `{!LayoutAlg} (l : loc) (els : enum_layout_spec) : loc :=
  let el := use_enum_layout_alg' els in
  (l +ₗ Z.of_nat (default 0%nat (offset_of el.(sl_members) "data"))).
Definition GetEnumDiscriminantLocSt `{!LayoutAlg} (l : loc) (els : enum_layout_spec) : loc :=
  let el := use_enum_layout_alg' els in
  (l +ₗ Z.of_nat (default 0%nat (offset_of el.(sl_members) "discriminant"))).


(* TODO: maybe change this if we ever have different offsets *)
(*Definition GetMemberUnionLocSt (l : loc) (ul : union_layout_spec) (m : var_name) : loc := (l).*)
(*Notation "l 'at_unionst{' ul '}ₗ' m" := (GetMemberUnionLocSt l ul m) (at level 10, format "l  'at_union{' ul '}ₗ'  m") : stdpp_scope.*)
(*Global Typeclasses Opaque GetMemberUnionLocSt.*)
(*Arguments GetMemberUnionLocSt : simpl never.*)

Notation zst_val := ([] : val).

(*** Tests *)
Example test1 (l : loc) ly ot :
  (l <-{ly} use{ot}(&l +{PtrOp, IntOp usize_t} (l ={PtrOp, PtrOp, i32} l)); ExprS (Call l [ (l : expr); (l : expr)]) (l <-{ly, ScOrd} l; Goto "a"))%E =
  (AssignSE Na1Ord ly l (Use Na1Ord ot true (BinOp AddOp PtrOp (IntOp usize_t) (AddrOf l) (BinOp (EqOp i32) PtrOp PtrOp l l))))
      (ExprS (Call l [ Val (val_of_loc l); Val (val_of_loc l)]) ((AssignSE ScOrd ly l l) (Goto "a"))).
Proof. simpl. reflexivity. Abort.

Example test_get_member `{!LayoutAlg} (l : loc) (sls : struct_layout_spec) ot :
  (!{ot} (!{ot, ScOrd} l) at{sls} "a")%E = GetMember (Deref Na1Ord ot true (Deref ScOrd ot true l%E)) sls "a".
Proof. simpl. reflexivity. Abort.
