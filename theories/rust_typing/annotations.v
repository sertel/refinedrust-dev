From refinedrust Require Import base.

Inductive stop_annot : Type :=
  StopAnnot.

(** Annotation for starting a local lifetime [n ⊑ ⨅ sup].
  [n] will contain a fresh atomic lifetime, which is the handle to end [n]. *)
Inductive startlft_annot : Type :=
  StartLftAnnot (n : string) (sup : list string).

(** Similar to startlft, but do not include a new atomic lifetime in n, thus making [n = ⨅ sup]. *)
Inductive aliaslft_annot : Type :=
  AliasLftAnnot (n : string) (sup : list string).

(** Annotation for ending a local lifetime n. *)
Inductive endlft_annot : Type :=
  EndLftAnnot (n : string).

(** Annotation for extending a local lifetime n ⊑ ⨅ κs to be equal to ⨅ κs. *)
Inductive extend_annot : Type :=
  ExtendLftAnnot (n : string).


(** Annotation for stratifying the context at this point. *)
Inductive stratify_context_annot : Type :=
  StratifyContextAnnot.

(** Annotation for creating a dynamic inclusion of a lifetime κ1 ⊑ κ2 *)
Inductive includelft_annot : Type :=
  DynIncludeLftAnnot (n1 n2 : string).

(** Annotation for copying the entry n2 ↦ κ in the name map for n1, so that n1 ↦ κ. *)
Inductive copylftname_annot : Type :=
  CopyLftNameAnnot (n1 n2 : string).

(** LftNameTrees for copying lifetime names *)
Inductive LftNameTree : Set :=
  | LftNameTreeLeaf
  | LftNameTreeRef (lft : string) (t : LftNameTree)
  (* TODO struct etc *)
.

(** Annotation for shortening the lifetime of an expression *)
Inductive shortenlft_annot : Type :=
  ShortenLftAnnot (t : LftNameTree).

(** Annotation for adding lifetime names to the context for the semantic lifetimes of the given expression *)
Inductive get_lft_names_annot : Type :=
  GetLftNamesAnnot (t : LftNameTree).

(** This indicates that a goto to the head of a loop is following.
  Invariants are specified in the context. *)
Inductive loop_start_annot : Type :=
  | InitLoopAnnot.

(** This asserts that an expression has a particular syntactic Rust type by triggering subtyping to the intended type. *)
Inductive assert_type_annot : Type :=
  | AssertTypeAnnot (ty : rust_type).

(** TODO: just a place holder until we handle drops properly. *)
Inductive drop_annot : Type :=
  | DropAnnot.

(** Annotation to extract a value assignment for the given expression.
  This is a hack we currently need due to restricted evar instantiation on function calls. *)
Inductive extract_value_annot : Type :=
  | ExtractValueAnnot.
