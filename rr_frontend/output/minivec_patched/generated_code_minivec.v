From caesium Require Import lang notation.
From refinedrust Require Import typing.

Section RawVec_sls.
  Context `{!typeGS Σ}.

  Definition RawVec_sls (T_st : syn_type) : struct_layout_spec := mk_sls "RawVec" [
    ("ptr", PtrSynType);
    ("cap", IntSynType USize);
    ("_marker", UnitSynType)] StructReprRust.
End RawVec_sls.

Section Vec_sls.
  Context `{!typeGS Σ}.

  Definition Vec_sls (T_st : syn_type) : struct_layout_spec := mk_sls "Vec" [
    ("buf", (syn_type_of_sls ((RawVec_sls (T_st)))));
    ("len", IntSynType USize)] StructReprRust.
End Vec_sls.

Section std_option_Option_els.
  Context `{!typeGS Σ}.

  Definition std_option_Option_None_sls  : struct_layout_spec := mk_sls "std_option_Option_None" [] StructReprRust.

  Definition std_option_Option_Some_sls T_st : struct_layout_spec := mk_sls "std_option_Option_Some" [
    ("0", T_st)] StructReprRust.

  Program Definition std_option_Option_els (T_st : syn_type): enum_layout_spec := mk_els "std_option_Option" ISize [
    ("None", std_option_Option_None_sls  : syn_type);
    ("Some", std_option_Option_Some_sls T_st : syn_type)] EnumReprRust [("None", 0); ("Some", 1)] _ _ _ _.
  Next Obligation. repeat first [econstructor | set_solver]. Qed.
  Next Obligation. done. Qed.
  Next Obligation. repeat first [econstructor | set_solver]. Qed.
  Next Obligation. repeat first [econstructor | init_cache; solve_goal]. Qed.
Global Typeclasses Opaque std_option_Option_els.
End std_option_Option_els.

Section code.
Context `{!typeGS Σ}.
Open Scope printing_sugar.

Definition RawVecTasstd_ops_Drop_drop_def (std_mem_size_of_T_loc : loc) (free_array_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("elem_size", (it_layout USize) : layout);
  ("__3", (it_layout U8) : layout);
  ("__4", (it_layout U8) : layout);
  ("__5", (it_layout USize) : layout);
  ("__6", (it_layout U8) : layout);
  ("__7", (it_layout USize) : layout);
  ("__8", (layout_of unit_sl) : layout);
  ("__9", (it_layout USize) : layout);
  ("__10", void* : layout);
  ("__11", void* : layout)
 ];
 f_code :=
  <[
  "_bb7" :=
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb8"
  ]>%E $
  <[
  "_bb4" :=
   if{ BoolOp }: use{ BoolOp } ("__3") then
    Goto "_bb5"
   else
    Goto "_bb7"
  ]>%E $
  <[
  "_bb1" :=
   "__5" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   "__4" <-{ BoolOp } (use{ IntOp USize } ("__5")) != { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   if{ BoolOp }: use{ BoolOp } ("__4") then
    Goto "_bb3"
   else
    Goto "_bb2"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft4" "ulft__";
   "elem_size" <-{ IntOp USize } CallE std_mem_size_of_T_loc [] [@{expr} ];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb8" :=
   (*annot: StratifyContextAnnot;*)
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb6" :=
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb8"
  ]>%E $
  <[
  "_bb3" :=
   "__7" <-{ IntOp USize } use{ IntOp USize } ("elem_size");
   "__6" <-{ BoolOp } (use{ IntOp USize } ("__7")) != { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   "__3" <-{ BoolOp } use{ BoolOp } ("__6");
   Goto "_bb4"
  ]>%E $
  <[
  "_bb5" :=
   "__9" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   "__11" <-{ PtrOp } use{ PtrOp } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "ptr");
   "__10" <-{ PtrOp } use{ PtrOp } ("__11");
   "__8" <-{ StructOp unit_sl [] } CallE free_array_T_loc [] [@{expr} use{ IntOp USize } ("__9"); use{ PtrOp } ("__10")];
   Goto "_bb6"
  ]>%E $
  <[
  "_bb2" :=
   "__3" <-{ BoolOp } val_of_bool false;
   Goto "_bb4"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_insert_def (std_ptr_write_T_loc : loc) (ptr_add_T_loc : loc) (Vec_T_cap_T_loc : loc) (Vec_T_ptr_T_loc : loc) (RawVec_T_grow_T_loc : loc) (std_ptr_copy_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("index", (it_layout USize) : layout);
  ("elem", (use_layout_alg' T_st) : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("__4", (layout_of unit_sl) : layout);
  ("__5", (it_layout U8) : layout);
  ("__6", (it_layout U8) : layout);
  ("__7", (it_layout USize) : layout);
  ("__8", (it_layout USize) : layout);
  ("__9", (layout_of unit_sl) : layout);
  ("__10", (layout_of unit_sl) : layout);
  ("__11", (it_layout U8) : layout);
  ("__12", (it_layout USize) : layout);
  ("__13", void* : layout);
  ("__14", (it_layout USize) : layout);
  ("__15", (layout_of unit_sl) : layout);
  ("__16", void* : layout);
  ("__17", (layout_of unit_sl) : layout);
  ("__18", void* : layout);
  ("__19", void* : layout);
  ("__20", void* : layout);
  ("__21", void* : layout);
  ("__22", (it_layout USize) : layout);
  ("__23", void* : layout);
  ("__24", void* : layout);
  ("__25", void* : layout);
  ("__26", (it_layout USize) : layout);
  ("__27", (it_layout USize) : layout);
  ("__28", (it_layout USize) : layout);
  ("__29", (it_layout USize) : layout);
  ("__30", (it_layout USize) : layout);
  ("__31", (it_layout USize) : layout);
  ("__32", (it_layout USize) : layout);
  ("__33", (layout_of unit_sl) : layout);
  ("__34", void* : layout);
  ("__35", void* : layout);
  ("__36", void* : layout);
  ("__37", (it_layout USize) : layout);
  ("__38", (use_layout_alg' T_st) : layout);
  ("__39", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb13" :=
   "__29" <-{ IntOp USize } use{ IntOp USize } ("__32");
   "__17" <-{ StructOp unit_sl [] } CallE std_ptr_copy_T_loc [] [@{expr} use{ PtrOp } ("__18"); use{ PtrOp } ("__23"); use{ IntOp USize } ("__29")];
   Goto "_bb14"
  ]>%E $
  <[
  "_bb19" :=
   (*annot: StratifyContextAnnot;*)
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb1" :=
   StuckS
  ]>%E $
  <[
  "_bb17" :=
   "__39" <-{ IntOp USize } (use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len")) +c{ IntOp USize , IntOp USize } (I2v (1) U64);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb18"
  ]>%E $
  <[
  "_bb4" :=
   annot: StartLftAnnot "llft7" ["plft11"];
   "__16" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["RawVec_inv_t"] [RSTTyVar "T"]), "llft7" } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "buf"));
   annot: CopyLftNameAnnot "plft18" "plft13";
   "__15" <-{ StructOp unit_sl [] } CallE RawVec_T_grow_T_loc ["plft18"] [@{expr} use{ PtrOp } ("__16")];
   annot: EndLftAnnot "llft7";
   Goto "_bb5"
  ]>%E $
  <[
  "_bb8" :=
   annot: EndLftAnnot "llft8";
   "__22" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__19" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__20"); use{ IntOp USize } ("__22")];
   Goto "_bb9"
  ]>%E $
  <[
  "_bb15" :=
   annot: EndLftAnnot "llft10";
   "__37" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__34" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__35"); use{ IntOp USize } ("__37")];
   Goto "_bb16"
  ]>%E $
  <[
  "_bb12" :=
   "__30" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__31" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__32" <-{ IntOp USize } (use{ IntOp USize } ("__30")) -c{ IntOp USize , IntOp USize } (use{ IntOp USize } ("__31"));
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb13"
  ]>%E $
  <[
  "_bb2" :=
   "__4" <-{ StructOp unit_sl [] } zst_val;
   annot: StartLftAnnot "llft6" ["plft11"];
   "__13" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft6" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft17" "plft12";
   "__12" <-{ IntOp USize } CallE Vec_T_cap_T_loc ["plft17"] [@{expr} use{ PtrOp } ("__13")];
   annot: EndLftAnnot "llft6";
   Goto "_bb3"
  ]>%E $
  <[
  "_bb16" :=
   "__38" <-{ (use_op_alg' T_st) } use{ (use_op_alg' T_st) } ("elem");
   "__33" <-{ StructOp unit_sl [] } CallE std_ptr_write_T_loc [] [@{expr} use{ PtrOp } ("__34"); use{ (use_op_alg' T_st) } ("__38")];
   Goto "_bb17"
  ]>%E $
  <[
  "_bb6" :=
   "__10" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb7"
  ]>%E $
  <[
  "_bb11" :=
   "__26" <-{ IntOp USize } use{ IntOp USize } ("__28");
   "__23" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__24"); use{ IntOp USize } ("__26")];
   Goto "_bb12"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft11" "ulft__";
   "__7" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__8" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__6" <-{ BoolOp } (use{ IntOp USize } ("__7")) ≤{ IntOp USize , IntOp USize , U8 } (use{ IntOp USize } ("__8"));
   "__5" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__6"));
   if{ BoolOp }: use{ BoolOp } ("__5") then
    Goto "_bb1"
   else
    Goto "_bb2"
  ]>%E $
  <[
  "_bb5" :=
   annot: EndLftAnnot "llft7";
   "__10" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb7"
  ]>%E $
  <[
  "_bb3" :=
   annot: EndLftAnnot "llft6";
   "__14" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__11" <-{ BoolOp } (use{ IntOp USize } ("__12")) = { IntOp USize , IntOp USize , U8 } (use{ IntOp USize } ("__14"));
   if{ BoolOp }: use{ BoolOp } ("__11") then
    Goto "_bb4"
   else
    Goto "_bb6"
  ]>%E $
  <[
  "_bb7" :=
   annot: StartLftAnnot "llft8" ["plft11"];
   "__21" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft14" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft8" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft19" "plft14";
   "__20" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft19"] [@{expr} use{ PtrOp } ("__21")];
   annot: EndLftAnnot "llft8";
   Goto "_bb8"
  ]>%E $
  <[
  "_bb9" :=
   "__18" <-{ PtrOp } use{ PtrOp } ("__19");
   annot: StartLftAnnot "llft9" ["plft11"];
   "__25" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft9" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft20" "plft15";
   "__24" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft20"] [@{expr} use{ PtrOp } ("__25")];
   annot: EndLftAnnot "llft9";
   Goto "_bb10"
  ]>%E $
  <[
  "_bb14" :=
   annot: StartLftAnnot "llft10" ["plft11"];
   "__36" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft16" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft10" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft21" "plft16";
   "__35" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft21"] [@{expr} use{ PtrOp } ("__36")];
   annot: EndLftAnnot "llft10";
   Goto "_bb15"
  ]>%E $
  <[
  "_bb10" :=
   annot: EndLftAnnot "llft9";
   "__27" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__28" <-{ IntOp USize } (use{ IntOp USize } ("__27")) +c{ IntOp USize , IntOp USize } (I2v (1) U64);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb11"
  ]>%E $
  <[
  "_bb18" :=
   (!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len" <-{ IntOp USize } use{ IntOp USize } ("__39");
   "__0" <-{ StructOp unit_sl [] } zst_val;
   (*expr: AnnotExpr 0 DropAnnot ("elem");*)
   Goto "_bb19"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition main_def : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   "__0" <-{ StructOp unit_sl [] } zst_val;
   (*annot: StratifyContextAnnot;*)
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition RawVec_T_with_capacity_def (std_mem_size_of_T_loc : loc) (ptr_dangling_T_loc : loc) (check_array_layoutable_T_loc : loc) (alloc_array_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("capacity", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) : layout);
  ("__2", (it_layout U8) : layout);
  ("__3", (it_layout U8) : layout);
  ("__4", (it_layout USize) : layout);
  ("__5", (it_layout U8) : layout);
  ("__6", (it_layout USize) : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", (it_layout USize) : layout);
  ("__10", (layout_of unit_sl) : layout);
  ("__11", (layout_of unit_sl) : layout);
  ("__12", (it_layout U8) : layout);
  ("__13", (it_layout U8) : layout);
  ("__14", (it_layout USize) : layout);
  ("__15", (layout_of unit_sl) : layout);
  ("ptr", void* : layout);
  ("__17", (it_layout USize) : layout);
  ("__18", void* : layout);
  ("__19", void* : layout);
  ("__20", (it_layout USize) : layout);
  ("__21", (layout_of unit_sl) : layout)
 ];
 f_code :=
  <[
  "_bb11" :=
   "__19" <-{ PtrOp } use{ PtrOp } ("ptr");
   "__18" <-{ PtrOp } use{ PtrOp } ("__19");
   "__20" <-{ IntOp USize } use{ IntOp USize } ("capacity");
   "__21" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } StructInit ((RawVec_sls (T_st))) [("ptr", use{ PtrOp } ("__18") : expr); ("cap", use{ IntOp USize } ("__20") : expr); ("_marker", use{ StructOp unit_sl [] } ("__21") : expr)];
   Goto "_bb12"
  ]>%E $
  <[
  "_bb2" :=
   "__6" <-{ IntOp USize } use{ IntOp USize } ("capacity");
   "__5" <-{ BoolOp } (use{ IntOp USize } ("__6")) = { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   "__2" <-{ BoolOp } use{ BoolOp } ("__5");
   Goto "_bb3"
  ]>%E $
  <[
  "_bb9" :=
   StuckS
  ]>%E $
  <[
  "_bb8" :=
   "__12" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__13"));
   if{ BoolOp }: use{ BoolOp } ("__12") then
    Goto "_bb9"
   else
    Goto "_bb10"
  ]>%E $
  <[
  "_bb6" :=
   "__7" <-{ PtrOp } use{ PtrOp } ("__8");
   "__9" <-{ IntOp USize } use{ IntOp USize } ("capacity");
   "__10" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } StructInit ((RawVec_sls (T_st))) [("ptr", use{ PtrOp } ("__7") : expr); ("cap", use{ IntOp USize } ("__9") : expr); ("_marker", use{ StructOp unit_sl [] } ("__10") : expr)];
   Goto "_bb12"
  ]>%E $
  <[
  "_bb12" :=
   (*annot: StratifyContextAnnot;*)
   return (use{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } ("__0"))
  ]>%E $
  <[
  "_bb10" :=
   "__11" <-{ StructOp unit_sl [] } zst_val;
   "__17" <-{ IntOp USize } use{ IntOp USize } ("capacity");
   "ptr" <-{ PtrOp } CallE alloc_array_T_loc [] [@{expr} use{ IntOp USize } ("__17")];
   Goto "_bb11"
  ]>%E $
  <[
  "_bb7" :=
   "__14" <-{ IntOp USize } use{ IntOp USize } ("capacity");
   "__13" <-{ BoolOp } CallE check_array_layoutable_T_loc [] [@{expr} use{ IntOp USize } ("__14")];
   Goto "_bb8"
  ]>%E $
  <[
  "_bb5" :=
   "__8" <-{ PtrOp } CallE ptr_dangling_T_loc [] [@{expr} ];
   Goto "_bb6"
  ]>%E $
  <[
  "_bb0" :=
   "__4" <-{ IntOp USize } CallE std_mem_size_of_T_loc [] [@{expr} ];
   Goto "_bb4"
  ]>%E $
  <[
  "_bb1" :=
   "__2" <-{ BoolOp } val_of_bool true;
   Goto "_bb3"
  ]>%E $
  <[
  "_bb4" :=
   "__3" <-{ BoolOp } (use{ IntOp USize } ("__4")) = { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   if{ BoolOp }: use{ BoolOp } ("__3") then
    Goto "_bb1"
   else
    Goto "_bb2"
  ]>%E $
  <[
  "_bb3" :=
   if{ BoolOp }: use{ BoolOp } ("__2") then
    Goto "_bb5"
   else
    Goto "_bb7"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_push_def (Vec_T_cap_T_loc : loc) (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (std_ptr_write_T_loc : loc) (RawVec_T_grow_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("elem", (use_layout_alg' T_st) : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("__3", (layout_of unit_sl) : layout);
  ("__4", (it_layout U8) : layout);
  ("__5", (it_layout USize) : layout);
  ("__6", (it_layout USize) : layout);
  ("__7", void* : layout);
  ("__8", (layout_of unit_sl) : layout);
  ("__9", void* : layout);
  ("__10", (layout_of unit_sl) : layout);
  ("__11", (layout_of unit_sl) : layout);
  ("__12", void* : layout);
  ("__13", void* : layout);
  ("__14", void* : layout);
  ("__15", (it_layout USize) : layout);
  ("__16", (use_layout_alg' T_st) : layout);
  ("__17", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb6" :=
   annot: EndLftAnnot "llft6";
   "__15" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__12" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__13"); use{ IntOp USize } ("__15")];
   Goto "_bb7"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft7" "ulft__";
   "__5" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   annot: StartLftAnnot "llft4" ["plft7"];
   "__7" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft8" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft4" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft11" "plft8";
   "__6" <-{ IntOp USize } CallE Vec_T_cap_T_loc ["plft11"] [@{expr} use{ PtrOp } ("__7")];
   annot: EndLftAnnot "llft4";
   Goto "_bb1"
  ]>%E $
  <[
  "_bb8" :=
   "__10" <-{ StructOp unit_sl [] } zst_val;
   "__17" <-{ IntOp USize } (use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len")) +c{ IntOp USize , IntOp USize } (I2v (1) U64);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb9"
  ]>%E $
  <[
  "_bb7" :=
   "__16" <-{ (use_op_alg' T_st) } use{ (use_op_alg' T_st) } ("elem");
   "__11" <-{ StructOp unit_sl [] } CallE std_ptr_write_T_loc [] [@{expr} AnnotExpr 1 ExtractValueAnnot (use{ PtrOp } ("__12")); use{ (use_op_alg' T_st) } ("__16")];
   Goto "_bb8"
  ]>%E $
  <[
  "_bb9" :=
   (!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len" <-{ IntOp USize } use{ IntOp USize } ("__17");
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb10"
  ]>%E $
  <[
  "_bb4" :=
   "__3" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb5"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft4";
   "__4" <-{ BoolOp } (use{ IntOp USize } ("__5")) = { IntOp USize , IntOp USize , U8 } (use{ IntOp USize } ("__6"));
   if{ BoolOp }: use{ BoolOp } ("__4") then
    Goto "_bb2"
   else
    Goto "_bb4"
  ]>%E $
  <[
  "_bb2" :=
   annot: StartLftAnnot "llft5" ["plft7"];
   "__9" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft9" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["RawVec_inv_t"] [RSTTyVar "T"]), "llft5" } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "buf"));
   annot: CopyLftNameAnnot "plft12" "plft9";
   "__8" <-{ StructOp unit_sl [] } CallE RawVec_T_grow_T_loc ["plft12"] [@{expr} use{ PtrOp } ("__9")];
   annot: EndLftAnnot "llft5";
   Goto "_bb3"
  ]>%E $
  <[
  "_bb3" :=
   annot: EndLftAnnot "llft5";
   "__3" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb5"
  ]>%E $
  <[
  "_bb10" :=
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb5" :=
   annot: StartLftAnnot "llft6" ["plft7"];
   "__14" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft10" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft6" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft13" "plft10";
   "__13" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft13"] [@{expr} use{ PtrOp } ("__14")];
   annot: EndLftAnnot "llft6";
   Goto "_bb6"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_ptr_def (RawVec_T_ptr_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", void* : layout);
  ("__2", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft5" "ulft_a";
   annot: CopyLftNameAnnot "plft4" "plft5";
   "__2" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft6" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft4" } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "buf"));
   annot: CopyLftNameAnnot "plft7" "plft6";
   "__0" <-{ PtrOp } CallE RawVec_T_ptr_T_loc ["plft7"] [@{expr} use{ PtrOp } ("__2")];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   (*annot: StratifyContextAnnot;*)
   return (use{ PtrOp } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition RawVec_T_grow_def (check_array_layoutable_T_loc : loc) (realloc_array_T_loc : loc) (alloc_array_T_loc : loc) (std_mem_size_of_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("__2", (layout_of unit_sl) : layout);
  ("__3", (it_layout U8) : layout);
  ("__4", (it_layout U8) : layout);
  ("__5", (it_layout USize) : layout);
  ("__6", (layout_of unit_sl) : layout);
  ("new_cap", (it_layout USize) : layout);
  ("__8", (it_layout U8) : layout);
  ("__9", (it_layout USize) : layout);
  ("__11", (it_layout USize) : layout);
  ("__12", (it_layout USize) : layout);
  ("__13", (layout_of unit_sl) : layout);
  ("__14", (it_layout U8) : layout);
  ("__15", (it_layout U8) : layout);
  ("__16", (it_layout USize) : layout);
  ("__17", (layout_of unit_sl) : layout);
  ("new_ptr", void* : layout);
  ("__19", (it_layout U8) : layout);
  ("__20", (it_layout USize) : layout);
  ("__21", (it_layout USize) : layout);
  ("old_ptr", void* : layout);
  ("__23", (it_layout USize) : layout);
  ("__24", void* : layout);
  ("__25", void* : layout);
  ("__26", (it_layout USize) : layout);
  ("__27", void* : layout);
  ("__28", void* : layout);
  ("__29", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb1" :=
   "__4" <-{ BoolOp } (use{ IntOp USize } ("__5")) != { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   "__3" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__4"));
   if{ BoolOp }: use{ BoolOp } ("__3") then
    Goto "_bb2"
   else
    Goto "_bb3"
  ]>%E $
  <[
  "_bb8" :=
   "__14" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__15"));
   if{ BoolOp }: use{ BoolOp } ("__14") then
    Goto "_bb9"
   else
    Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   "__13" <-{ StructOp unit_sl [] } zst_val;
   "__20" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   "__19" <-{ BoolOp } (use{ IntOp USize } ("__20")) = { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   if{ BoolOp }: use{ BoolOp } ("__19") then
    Goto "_bb11"
   else
    Goto "_bb12"
  ]>%E $
  <[
  "_bb6" :=
   "new_cap" <-{ IntOp USize } use{ IntOp USize } ("__12");
   "new_cap" <-{ IntOp USize } use{ IntOp USize } ("new_cap");
   Goto "_bb7"
  ]>%E $
  <[
  "_bb13" :=
   Goto "_bb15"
  ]>%E $
  <[
  "_bb3" :=
   "__2" <-{ StructOp unit_sl [] } zst_val;
   "__9" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   "__8" <-{ BoolOp } (use{ IntOp USize } ("__9")) = { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   if{ BoolOp }: use{ BoolOp } ("__8") then
    Goto "_bb4"
   else
    Goto "_bb5"
  ]>%E $
  <[
  "_bb11" :=
   "__21" <-{ IntOp USize } use{ IntOp USize } ("new_cap");
   "new_ptr" <-{ PtrOp } CallE alloc_array_T_loc [] [@{expr} use{ IntOp USize } ("__21")];
   Goto "_bb13"
  ]>%E $
  <[
  "_bb5" :=
   "__11" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   "__12" <-{ IntOp USize } (I2v (2) U64) ×c{ IntOp USize , IntOp USize } (use{ IntOp USize } ("__11"));
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb6"
  ]>%E $
  <[
  "_bb4" :=
   "new_cap" <-{ IntOp USize } I2v (1) U64;
   Goto "_bb7"
  ]>%E $
  <[
  "_bb2" :=
   StuckS
  ]>%E $
  <[
  "_bb9" :=
   StuckS
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft8" "ulft__";
   "__5" <-{ IntOp USize } CallE std_mem_size_of_T_loc [] [@{expr} ];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb15" :=
   "__28" <-{ PtrOp } use{ PtrOp } ("new_ptr");
   "__27" <-{ PtrOp } use{ PtrOp } ("__28");
   (!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "ptr" <-{ PtrOp } use{ PtrOp } ("__27");
   "__29" <-{ IntOp USize } use{ IntOp USize } ("new_cap");
   (!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap" <-{ IntOp USize } use{ IntOp USize } ("__29");
   "__0" <-{ StructOp unit_sl [] } zst_val;
   (*annot: StratifyContextAnnot;*)
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb12" :=
   "old_ptr" <-{ PtrOp } use{ PtrOp } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "ptr");
   "__23" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   "__25" <-{ PtrOp } use{ PtrOp } ("old_ptr");
   "__24" <-{ PtrOp } use{ PtrOp } ("__25");
   "__26" <-{ IntOp USize } use{ IntOp USize } ("new_cap");
   "new_ptr" <-{ PtrOp } CallE realloc_array_T_loc [] [@{expr} use{ IntOp USize } ("__23"); AnnotExpr 1 ExtractValueAnnot (use{ PtrOp } ("__24")); use{ IntOp USize } ("__26")];
   Goto "_bb14"
  ]>%E $
  <[
  "_bb7" :=
   "__16" <-{ IntOp USize } use{ IntOp USize } ("new_cap");
   "__15" <-{ BoolOp } CallE check_array_layoutable_T_loc [] [@{expr} use{ IntOp USize } ("__16")];
   Goto "_bb8"
  ]>%E $
  <[
  "_bb14" :=
   Goto "_bb15"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_new_def (RawVec_T_new_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (syn_type_of_sls ((Vec_sls (T_st))))) : layout);
  ("__1", (use_layout_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) : layout)
 ];
 f_code :=
  <[
  "_bb2" :=
   (*annot: StratifyContextAnnot;*)
   return (use{ (use_op_alg' (syn_type_of_sls ((Vec_sls (T_st))))) } ("__0"))
  ]>%E $
  <[
  "_bb0" :=
   "__1" <-{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } CallE RawVec_T_new_T_loc [] [@{expr} ];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   "__0" <-{ (use_op_alg' (syn_type_of_sls ((Vec_sls (T_st))))) } StructInit ((Vec_sls (T_st))) [("buf", use{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } ("__1") : expr); ("len", I2v (0) U64 : expr)];
   (*expr: AnnotExpr 0 DropAnnot ("__1");*)
   Goto "_bb2"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_cap_def (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft4" "ulft_a";
   "__0" <-{ IntOp USize } use{ IntOp USize } (((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "buf") at{ ((RawVec_sls (T_st))) } "cap");
   (*annot: StratifyContextAnnot;*)
   return (use{ IntOp USize } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_remove_def (std_ptr_copy_T_loc : loc) (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (std_ptr_read_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("index", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' T_st) : layout);
  ("__3", (layout_of unit_sl) : layout);
  ("__4", (it_layout U8) : layout);
  ("__5", (it_layout U8) : layout);
  ("__6", (it_layout USize) : layout);
  ("__7", (it_layout USize) : layout);
  ("__8", (layout_of unit_sl) : layout);
  ("__9", (it_layout USize) : layout);
  ("result", (use_layout_alg' T_st) : layout);
  ("__11", void* : layout);
  ("__12", void* : layout);
  ("__13", void* : layout);
  ("__14", void* : layout);
  ("__15", (it_layout USize) : layout);
  ("__16", (layout_of unit_sl) : layout);
  ("__17", void* : layout);
  ("__18", void* : layout);
  ("__19", void* : layout);
  ("__20", void* : layout);
  ("__21", (it_layout USize) : layout);
  ("__22", (it_layout USize) : layout);
  ("__23", (it_layout USize) : layout);
  ("__24", void* : layout);
  ("__25", void* : layout);
  ("__26", void* : layout);
  ("__27", (it_layout USize) : layout);
  ("__28", (it_layout USize) : layout);
  ("__29", (it_layout USize) : layout);
  ("__30", (it_layout USize) : layout);
  ("__31", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb8" :=
   "__21" <-{ IntOp USize } use{ IntOp USize } ("__23");
   "__18" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__19"); use{ IntOp USize } ("__21")];
   Goto "_bb9"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft9" "ulft__";
   "__6" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__7" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__5" <-{ BoolOp } (use{ IntOp USize } ("__6")) <{ IntOp USize , IntOp USize , U8 } (use{ IntOp USize } ("__7"));
   "__4" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__5"));
   if{ BoolOp }: use{ BoolOp } ("__4") then
    Goto "_bb1"
   else
    Goto "_bb2"
  ]>%E $
  <[
  "_bb3" :=
   (!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len" <-{ IntOp USize } use{ IntOp USize } ("__9");
   annot: StartLftAnnot "llft6" ["plft9"];
   "__14" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft10" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft6" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft13" "plft10";
   "__13" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft13"] [@{expr} use{ PtrOp } ("__14")];
   annot: EndLftAnnot "llft6";
   Goto "_bb4"
  ]>%E $
  <[
  "_bb2" :=
   "__3" <-{ StructOp unit_sl [] } zst_val;
   "__9" <-{ IntOp USize } (use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len")) -c{ IntOp USize , IntOp USize } (I2v (1) U64);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb3"
  ]>%E $
  <[
  "_bb6" :=
   annot: StartLftAnnot "llft7" ["plft9"];
   "__20" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft11" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft14" "plft11";
   "__19" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft14"] [@{expr} use{ PtrOp } ("__20")];
   annot: EndLftAnnot "llft7";
   Goto "_bb7"
  ]>%E $
  <[
  "_bb4" :=
   annot: EndLftAnnot "llft6";
   "__15" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__12" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__13"); use{ IntOp USize } ("__15")];
   Goto "_bb5"
  ]>%E $
  <[
  "_bb7" :=
   annot: EndLftAnnot "llft7";
   "__22" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__23" <-{ IntOp USize } (use{ IntOp USize } ("__22")) +c{ IntOp USize , IntOp USize } (I2v (1) U64);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb11" :=
   "__29" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__30" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__31" <-{ IntOp USize } (use{ IntOp USize } ("__29")) -c{ IntOp USize , IntOp USize } (use{ IntOp USize } ("__30"));
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb12"
  ]>%E $
  <[
  "_bb12" :=
   "__28" <-{ IntOp USize } use{ IntOp USize } ("__31");
   "__16" <-{ StructOp unit_sl [] } CallE std_ptr_copy_T_loc [] [@{expr} use{ PtrOp } ("__17"); use{ PtrOp } ("__24"); use{ IntOp USize } ("__28")];
   Goto "_bb13"
  ]>%E $
  <[
  "_bb9" :=
   "__17" <-{ PtrOp } use{ PtrOp } ("__18");
   annot: StartLftAnnot "llft8" ["plft9"];
   "__26" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft8" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft15" "plft12";
   "__25" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft15"] [@{expr} use{ PtrOp } ("__26")];
   annot: EndLftAnnot "llft8";
   Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   annot: EndLftAnnot "llft8";
   "__27" <-{ IntOp USize } use{ IntOp USize } ("index");
   "__24" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__25"); use{ IntOp USize } ("__27")];
   Goto "_bb11"
  ]>%E $
  <[
  "_bb1" :=
   StuckS
  ]>%E $
  <[
  "_bb13" :=
   "__0" <-{ (use_op_alg' T_st) } use{ (use_op_alg' T_st) } ("result");
   (*expr: AnnotExpr 0 DropAnnot ("result");*)
   Goto "_bb14"
  ]>%E $
  <[
  "_bb14" :=
   (*annot: StratifyContextAnnot;*)
   return (use{ (use_op_alg' T_st) } ("__0"))
  ]>%E $
  <[
  "_bb5" :=
   "__11" <-{ PtrOp } use{ PtrOp } ("__12");
   "result" <-{ (use_op_alg' T_st) } CallE std_ptr_read_T_loc [] [@{expr} use{ PtrOp } ("__11")];
   Goto "_bb6"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition RawVec_T_ptr_def (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", void* : layout);
  ("__2", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft4" "ulft__";
   "__2" <-{ PtrOp } use{ PtrOp } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "ptr");
   "__0" <-{ PtrOp } use{ PtrOp } ("__2");
   (*annot: StratifyContextAnnot;*)
   return (use{ PtrOp } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition RawVec_T_cap_def (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft4" "ulft__";
   "__0" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((RawVec_sls (T_st))) } "cap");
   (*annot: StratifyContextAnnot;*)
   return (use{ IntOp USize } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition RawVec_T_new_def (ptr_dangling_T_loc : loc) (std_mem_size_of_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) : layout);
  ("cap", (it_layout USize) : layout);
  ("__2", (it_layout U8) : layout);
  ("__3", (it_layout USize) : layout);
  ("__4", void* : layout);
  ("__5", void* : layout);
  ("__6", (it_layout USize) : layout);
  ("__7", (layout_of unit_sl) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   "__3" <-{ IntOp USize } CallE std_mem_size_of_T_loc [] [@{expr} ];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb2" :=
   "cap" <-{ IntOp USize } UnOp (NotIntOp) (IntOp USize) (I2v (0) U64);
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   "__5" <-{ PtrOp } CallE ptr_dangling_T_loc [] [@{expr} ];
   Goto "_bb5"
  ]>%E $
  <[
  "_bb1" :=
   "__2" <-{ BoolOp } (use{ IntOp USize } ("__3")) = { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   if{ BoolOp }: use{ BoolOp } ("__2") then
    Goto "_bb2"
   else
    Goto "_bb3"
  ]>%E $
  <[
  "_bb5" :=
   "__4" <-{ PtrOp } use{ PtrOp } ("__5");
   "__6" <-{ IntOp USize } use{ IntOp USize } ("cap");
   "__7" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } StructInit ((RawVec_sls (T_st))) [("ptr", use{ PtrOp } ("__4") : expr); ("cap", use{ IntOp USize } ("__6") : expr); ("_marker", use{ StructOp unit_sl [] } ("__7") : expr)];
   (*annot: StratifyContextAnnot;*)
   return (use{ (use_op_alg' (syn_type_of_sls ((RawVec_sls (T_st))))) } ("__0"))
  ]>%E $
  <[
  "_bb3" :=
   "cap" <-{ IntOp USize } I2v (0) U64;
   Goto "_bb4"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_get_mut_def (Vec_T_get_unchecked_mut_T_loc : loc) (Vec_T_len_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("index", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) : layout);
  ("__3", (it_layout U8) : layout);
  ("__4", (it_layout USize) : layout);
  ("__5", (it_layout USize) : layout);
  ("__6", void* : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", void* : layout);
  ("__10", (it_layout USize) : layout)
 ];
 f_code := 
  <[
  "_bb3" :=
   annot: StartLftAnnot "llft6" ["plft14"];
   "__7" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTTyVar "T"), "llft6" } (!{ PtrOp } ( "__8" )));
   (* TODO inserted the right lifetime manually *)
   "__0" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } EnumInit ((std_option_Option_els (PtrSynType))) "Some" (RSTLitType ["std_option_Option_ty"] [RSTRef Mut "plft13" (RSTTyVar "T")]) (StructInit ((std_option_Option_Some_sls (PtrSynType))) [("0", use{ PtrOp } ("__7") : expr)]);
   (* TODO manually inserted extendlft *)
   annot: ExtendLftAnnot "llft5";
   annot: ExtendLftAnnot "llft6";
   Goto "_bb5"
  ]>%E $
  <[
  "_bb4" :=
  (* TODO inserted the right lifetime manually *)
   "__0" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } EnumInit ((std_option_Option_els (PtrSynType))) "None" (RSTLitType ["std_option_Option_ty"] [RSTRef Mut "plft11" (RSTTyVar "T")]) (StructInit (std_option_Option_None_sls) []);
   Goto "_bb5"
  ]>%E $
  <[
  "_bb2" :=
   annot: StartLftAnnot "llft5" ["plft11"];
   "__9" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Vec_inv_t"] [RSTTyVar "T"]), "llft5" } (!{ PtrOp } ( "self" )));
   "__10" <-{ IntOp USize } use{ IntOp USize } ("index");
   annot: CopyLftNameAnnot "plft17" "plft15";
   "__8" <-{ PtrOp } CallE Vec_T_get_unchecked_mut_T_loc ["plft17"] [@{expr} use{ PtrOp } ("__9"); use{ IntOp USize } ("__10")];
   (* TODO manually inserted *)
   annot: CopyLftNameAnnot "plft14" "plft17";
   Goto "_bb3"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft11" "ulft__";
   "__4" <-{ IntOp USize } use{ IntOp USize } ("index");
   annot: StartLftAnnot "llft4" ["plft11"];
   "__6" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft4" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft16" "plft12";
   "__5" <-{ IntOp USize } CallE Vec_T_len_T_loc ["plft16"] [@{expr} use{ PtrOp } ("__6")];
   annot: EndLftAnnot "llft4";
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft4";
   "__3" <-{ BoolOp } (use{ IntOp USize } ("__4")) <{ IntOp USize , IntOp USize , U8 } (use{ IntOp USize } ("__5"));
   if{ BoolOp }: use{ BoolOp } ("__3") then
    Goto "_bb2"
   else
    Goto "_bb4"
  ]>%E $
  <[
  "_bb5" :=
   return (use{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.


Definition Vec_T_get_def (Vec_T_len_T_loc : loc) (Vec_T_get_unchecked_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("index", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) : layout);
  ("__3", (it_layout U8) : layout);
  ("__4", (it_layout USize) : layout);
  ("__5", (it_layout USize) : layout);
  ("__6", void* : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", void* : layout);
  ("__10", (it_layout USize) : layout)
 ];
 f_code := 
  <[
  "_bb1" :=
   "__3" <-{ BoolOp } (use{ IntOp USize } ("__4")) <{ IntOp USize , IntOp USize , U8 } (use{ IntOp USize } ("__5"));
   if{ BoolOp }: use{ BoolOp } ("__3") then
    Goto "_bb2"
   else
    Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   (* TODO manually inserted the right lifetime *)
   "__0" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } EnumInit ((std_option_Option_els (PtrSynType))) "None" (RSTLitType ["std_option_Option_ty"] [RSTRef Shr "plft16" (RSTTyVar "T")]) (StructInit (std_option_Option_None_sls) []);
   Goto "_bb5"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft11" "ulft__";
   "__4" <-{ IntOp USize } use{ IntOp USize } ("index");
   annot: CopyLftNameAnnot "plft4" "plft11";
   "__6" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft4" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft16" "plft12";
   "__5" <-{ IntOp USize } CallE Vec_T_len_T_loc ["plft16"] [@{expr} use{ PtrOp } ("__6")];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb5" :=
   return (use{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } ("__0"))
  ]>%E $
  <[
  "_bb2" :=
   annot: CopyLftNameAnnot "plft5" "plft11";
   "__9" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft5" } (!{ PtrOp } ( "self" )));
   "__10" <-{ IntOp USize } use{ IntOp USize } ("index");
   annot: CopyLftNameAnnot "plft17" "plft15";
   "__8" <-{ PtrOp } CallE Vec_T_get_unchecked_T_loc ["plft17"] [@{expr} use{ PtrOp } ("__9"); use{ IntOp USize } ("__10")];
   annot: CopyLftNameAnnot "plft14" "plft17";
   Goto "_bb3"
  ]>%E $
  <[
  "_bb3" :=
   annot: CopyLftNameAnnot "plft6" "plft14";
   "__7" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft6" } (!{ PtrOp } ( "__8" )));
   (* TODO manually inserted the right lifetime *)
   "__0" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } EnumInit ((std_option_Option_els (PtrSynType))) "Some" (RSTLitType ["std_option_Option_ty"] [RSTRef Shr "plft13" (RSTTyVar "T")]) (StructInit ((std_option_Option_Some_sls (PtrSynType))) [("0", use{ PtrOp } ("__7") : expr)]);
   Goto "_bb5"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.



Definition Vec_T_get_unchecked_mut_def (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("index", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", void* : layout);
  ("__3", void* : layout);
  ("__4", void* : layout);
  ("p", void* : layout);
  ("__6", void* : layout);
  ("__7", void* : layout);
  ("__8", (it_layout USize) : layout);
  ("__9", (it_layout USize) : layout);
  ("ret", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft11" "ulft__";
   "__9" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   annot: StartLftAnnot "llft4" ["plft11"];
   "__7" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft14" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft4" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft16" "plft14";
   "__6" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft16"] [@{expr} use{ PtrOp } ("__7")];
   annot: EndLftAnnot "llft4";
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft4";
   "__8" <-{ IntOp USize } use{ IntOp USize } ("index");
   "p" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__6"); use{ IntOp USize } ("__8")];
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   annot: StartLftAnnot "llft6" ["plft11"];
   "ret" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTTyVar "T"), "llft6" } (!{ PtrOp } ( "p" )));
   annot: ExtendLftAnnot "llft6";
   (* TODO I edited the code, some of the annotations currently are wrong *)
   (*"ret" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTTyVar "T"), "plft5" } (!{ PtrOp } ( "p" )));*)
   (*annot: StartLftAnnot "llft6" ["plft15"];*)
   (*"__4" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTTyVar "T"), "llft6" } (!{ PtrOp } ( "ret" )));*)
   (*annot: StartLftAnnot "llft7" ["plft13"];*)
   (*"__3" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTTyVar "T"), "llft7" } (!{ PtrOp } ( "__4" )));*)
   (*annot: StartLftAnnot "llft8" ["plft12"];*)
   (*"__0" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft10" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTTyVar "T"), "llft8" } (!{ PtrOp } ( "__3" )));*)

   (*annot: StratifyContextAnnot;*)
   return (use{ PtrOp } ("ret"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_len_def (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft4" "ulft__";
   "__0" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   (*annot: StratifyContextAnnot;*)
   return (use{ IntOp USize } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_pop_def (Vec_T_ptr_T_loc : loc) (std_ptr_read_T_loc : loc) (ptr_add_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (syn_type_of_els ((std_option_Option_els (T_st))))) : layout);
  ("__2", (it_layout U8) : layout);
  ("__3", (it_layout USize) : layout);
  ("__4", (it_layout USize) : layout);
  ("__5", (use_layout_alg' T_st) : layout);
  ("__6", void* : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", void* : layout);
  ("__10", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb3" :=
   (!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len" <-{ IntOp USize } use{ IntOp USize } ("__4");
   annot: StartLftAnnot "llft4" ["plft5"];
   "__9" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft6" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft4" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft7" "plft6";
   "__8" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft7"] [@{expr} use{ PtrOp } ("__9")];
   annot: EndLftAnnot "llft4";
   Goto "_bb4"
  ]>%E $
  <[
  "_bb6" :=
   "__0" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (T_st))))) } EnumInit ((std_option_Option_els (T_st))) "Some" (RSTLitType ["std_option_Option_ty"] [RSTTyVar "T"]) (StructInit ((std_option_Option_Some_sls (T_st))) [("0", use{ (use_op_alg' T_st) } ("__5") : expr)]);
   (*expr: AnnotExpr 0 DropAnnot ("__5");*)
   Goto "_bb7"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft5" "ulft__";
   "__3" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__2" <-{ BoolOp } (use{ IntOp USize } ("__3")) = { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   if{ BoolOp }: use{ BoolOp } ("__2") then
    Goto "_bb1"
   else
    Goto "_bb2"
  ]>%E $
  <[
  "_bb4" :=
   annot: EndLftAnnot "llft4";
   "__10" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   "__7" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__8"); use{ IntOp USize } ("__10")];
   Goto "_bb5"
  ]>%E $
  <[
  "_bb7" :=
   Goto "_bb8"
  ]>%E $
  <[
  "_bb5" :=
   "__6" <-{ PtrOp } use{ PtrOp } ("__7");
   "__5" <-{ (use_op_alg' T_st) } CallE std_ptr_read_T_loc [] [@{expr} use{ PtrOp } ("__6")];
   Goto "_bb6"
  ]>%E $
  <[
  "_bb1" :=
   "__0" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (T_st))))) } EnumInit ((std_option_Option_els (T_st))) "None" (RSTLitType ["std_option_Option_ty"] [RSTTyVar "T"]) (StructInit ((std_option_Option_None_sls )) []);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb2" :=
   "__4" <-{ IntOp USize } (use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len")) -c{ IntOp USize , IntOp USize } (I2v (1) U64);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb3"
  ]>%E $
  <[
  "_bb8" :=
   return (use{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (T_st))))) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

(* TODO manually added Option::unwrap shim *)
Definition std_option_Option_T_unwrap_def (T_st : syn_type) : function := {|
 f_args := [
  ("self", (use_layout_alg' (syn_type_of_els ((std_option_Option_els (T_st))))) : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' T_st) : layout);
  ("__2", (it_layout ISize) : layout);
  ("val", (use_layout_alg' T_st) : layout);
  ("__4", (layout_of unit_sl) : layout)
 ];
 f_code := 
  <[
  "_bb6" :=
   return (use{ (use_op_alg' T_st) } ("__0"))
  ]>%E $
  <[
  "_bb3" :=
   StuckS
  ]>%E $
  <[
  "_bb4" :=
   "val" <-{ (use_op_alg' T_st) } use{ (use_op_alg' T_st) } ((EnumData (((std_option_Option_els (T_st)))) "Some" ("self")) at{ ((std_option_Option_Some_sls (T_st))) } "0");
   "__0" <-{ (use_op_alg' T_st) } use{ (use_op_alg' T_st) } ("val");
   Goto "_bb5"
  ]>%E $
  <[
  "_bb1" :=
   StuckS
  ]>%E $
  <[
  "_bb0" :=
   "__2" <-{ IntOp ISize } use{ IntOp ISize } (EnumDiscriminant (((std_option_Option_els (T_st)))) ("self"));
   Switch (ISize : int_type) (use{ IntOp ISize } ("__2")) (<[ 1%Z := 1%nat ]> $ <[ 0%Z := 0%nat ]> $ ∅) ([Goto "_bb1"; Goto "_bb2"]) (Goto "_bb3")
  ]>%E $
  <[
  "_bb2" :=
   Goto "_bb4"
  ]>%E $
  <[
  "_bb5" :=
   Goto "_bb6"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.


Definition get_mut_client_def (Vec_T_new_i32_loc : loc) (Vec_T_push_i32_loc : loc) (Vec_T_get_mut_i32_loc : loc) (std_option_Option_unwrap_def_muti32_loc : loc) : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("x", (use_layout_alg' (syn_type_of_sls ((Vec_sls (IntSynType I32))))) : layout);
  ("__2", (layout_of unit_sl) : layout);
  ("__3", void* : layout);
  ("__4", (layout_of unit_sl) : layout);
  ("__5", void* : layout);
  ("__6", (layout_of unit_sl) : layout);
  ("__7", void* : layout);
  ("xr", void* : layout);
  ("__9", (use_layout_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) : layout);
  ("__10", void* : layout);
  ("__11", (layout_of unit_sl) : layout);
  ("__12", (it_layout U8) : layout);
  ("__13", (it_layout U8) : layout);
  ("__14", (it_layout I32) : layout);
  ("__15", (layout_of unit_sl) : layout);
  ("__16", (layout_of unit_sl) : layout);
  ("__17", (it_layout U8) : layout);
  ("__18", (it_layout U8) : layout);
  ("__19", (it_layout I32) : layout);
  ("__20", void* : layout);
  ("__21", (use_layout_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) : layout);
  ("__22", void* : layout);
  ("__23", (layout_of unit_sl) : layout)
 ];
 f_code := 
  <[
  "_bb9" :=
   annot: CopyLftNameAnnot "plft10" "plft19";
  (* TODO: currently this erroneously generates an instantiation for a lifetime ["plft10"]. Manually removed it. *)
   "__20" <-{ PtrOp } CallE std_option_Option_unwrap_def_muti32_loc [] [@{expr} use{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } ("__21")];
   Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   "__19" <-{ IntOp I32 } use{ IntOp I32 } (!{ PtrOp } ( "__20" ));
   "__18" <-{ BoolOp } (use{ IntOp I32 } ("__19")) = { IntOp I32 , IntOp I32 , U8 } (I2v (42) I32);
   annot: EndLftAnnot "llft9";
   "__17" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__18"));
   if{ BoolOp }: use{ BoolOp } ("__17") then
    Goto "_bb11"
   else
    Goto "_bb12"
  ]>%E $
  <[
  "_bb1" :=
   annot: StartLftAnnot "llft3" [];
   "__3" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Vec_inv_t"] [RSTInt I32]), "llft3" } ("x"));
   annot: CopyLftNameAnnot "plft21" "plft12";
   "__2" <-{ StructOp unit_sl [] } CallE Vec_T_push_i32_loc ["plft21"] [@{expr} use{ PtrOp } ("__3"); I2v (100) I32];
   annot: EndLftAnnot "llft3";
   Goto "_bb2"
  ]>%E $
  <[
  "_bb12" :=
   "__16" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ StructOp unit_sl [] } zst_val;
   (*expr: AnnotExpr 0 DropAnnot ("x");*)
   Goto "_bb13"
  ]>%E $
  <[
  "_bb13" :=
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb11" :=
   StuckS
  ]>%E $
  <[
  "_bb6" :=
   "__14" <-{ IntOp I32 } use{ IntOp I32 } (!{ PtrOp } ( "xr" ));
   "__13" <-{ BoolOp } (use{ IntOp I32 } ("__14")) = { IntOp I32 , IntOp I32 , U8 } (I2v (200) I32);
   "__12" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__13"));
   if{ BoolOp }: use{ BoolOp } ("__12") then
    Goto "_bb7"
   else
    Goto "_bb8"
  ]>%E $
  <[
  "_bb4" :=
   annot: EndLftAnnot "llft5";
   annot: StartLftAnnot "llft6" [];
   "__10" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft17" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Vec_inv_t"] [RSTInt I32]), "llft6" } ("x"));
   annot: CopyLftNameAnnot "plft24" "plft17";
   "__9" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } CallE Vec_T_get_mut_i32_loc ["plft24"] [@{expr} use{ PtrOp } ("__10"); I2v (1) U64];
   (* TODO fix update of lft name map here, manually added *)
   annot: CopyLftNameAnnot "plft16" "plft24";
   Goto "_bb5"
  ]>%E $
  <[
  "_bb2" :=
   annot: EndLftAnnot "llft3";
   annot: StartLftAnnot "llft4" [];
   "__5" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Vec_inv_t"] [RSTInt I32]), "llft4" } ("x"));
   annot: CopyLftNameAnnot "plft22" "plft13";
   "__4" <-{ StructOp unit_sl [] } CallE Vec_T_push_i32_loc ["plft22"] [@{expr} use{ PtrOp } ("__5"); I2v (200) I32];
   annot: EndLftAnnot "llft4";
   Goto "_bb3"
  ]>%E $
  <[
  "_bb5" :=
   annot: CopyLftNameAnnot "plft7" "plft16";
   (* TODO: currently this erroneously generates an instantiation for a lifetime ["plft7"]. Manually removed it. *)
   "xr" <-{ PtrOp } CallE std_option_Option_unwrap_def_muti32_loc [] [@{expr} use{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } ("__9")];
   Goto "_bb6"
  ]>%E $
  <[
  "_bb0" :=
   "x" <-{ (use_op_alg' (syn_type_of_sls ((Vec_sls (IntSynType I32))))) } CallE Vec_T_new_i32_loc [] [@{expr} ];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb8" :=
   "__11" <-{ StructOp unit_sl [] } zst_val;
   !{ PtrOp } ( "xr" ) <-{ IntOp I32 } I2v (42) I32;
   annot: EndLftAnnot "llft6";
   annot: StartLftAnnot "llft9" [];
   "__22" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Vec_inv_t"] [RSTInt I32]), "llft9" } ("x"));
   annot: CopyLftNameAnnot "plft25" "plft20";
   "__21" <-{ (use_op_alg' (syn_type_of_els ((std_option_Option_els (PtrSynType))))) } CallE Vec_T_get_mut_i32_loc ["plft25"] [@{expr} use{ PtrOp } ("__22"); I2v (1) U64];
   (* TODO same *)
   annot: CopyLftNameAnnot "plft19" "plft25";
   Goto "_bb9"
  ]>%E $
  <[
  "_bb7" :=
   annot: EndLftAnnot "llft6";
   StuckS
  ]>%E $
  <[
  "_bb3" :=
   annot: EndLftAnnot "llft4";
   annot: StartLftAnnot "llft5" [];
   "__7" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft14" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Vec_inv_t"] [RSTInt I32]), "llft5" } ("x"));
   annot: CopyLftNameAnnot "plft23" "plft14";
   "__6" <-{ StructOp unit_sl [] } CallE Vec_T_push_i32_loc ["plft23"] [@{expr} use{ PtrOp } ("__7"); I2v (300) I32];
   annot: EndLftAnnot "llft5";
   Goto "_bb4"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Vec_T_get_unchecked_def (Vec_T_ptr_T_loc : loc) (ptr_add_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [
  ("self", void* : layout);
  ("index", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", void* : layout);
  ("__3", (it_layout USize) : layout);
  ("p", void* : layout);
  ("__5", void* : layout);
  ("__6", void* : layout);
  ("__7", (it_layout USize) : layout);
  ("ret", void* : layout)
 ];
 f_code := 
  <[
  "_bb2" :=
   (* TODO: manually constrained this by ulft__ *)
   (* TODO maybe this should just be copylftannot instead? *)
   annot: StartLftAnnot "plft5" ["ulft__"];
   "ret" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft11" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft5" } (!{ PtrOp } ( "p" )));
   annot: CopyLftNameAnnot "plft6" "plft11";
   "__0" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft8" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft6" } (!{ PtrOp } ( "ret" )));
   annot: ExtendLftAnnot "plft5";
   return (use{ PtrOp } ("__0"))
  ]>%E $
  <[
  "_bb1" :=
   "__7" <-{ IntOp USize } use{ IntOp USize } ("index");
   "p" <-{ PtrOp } CallE ptr_add_T_loc [] [@{expr} use{ PtrOp } ("__5"); use{ IntOp USize } ("__7")];
   Goto "_bb2"
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft9" "ulft__";
   "__3" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ ((Vec_sls (T_st))) } "len");
   annot: CopyLftNameAnnot "plft4" "plft9";
   "__6" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft10" (LftNameTreeLeaf))) (&ref{ Shr, None, "plft4" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "plft12" "plft10";
   "__5" <-{ PtrOp } CallE Vec_T_ptr_T_loc ["plft12"] [@{expr} use{ PtrOp } ("__6")];
   Goto "_bb1"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.



End code.
