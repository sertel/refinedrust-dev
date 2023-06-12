From caesium Require Import lang notation.
From refinedrust Require Import typing shims.

Section code.
Context `{!typeGS Σ}.
Open Scope printing_sugar.

Definition box_add_42_def : function := {|
 f_args := [
  ("x", void* : layout)
 ];
 f_local_vars := [
  ("__0", void* : layout);
  ("__2", (it_layout I32) : layout)
 ];
 f_code := 
  <[
  "_bb1" :=
   !{ PtrOp } ( "x" ) <-{ IntOp I32 } use{ IntOp I32 } ("__2");
   "__0" <-{ PtrOp } use{ PtrOp } ("x");
   Goto "_bb2"
  ]>%E $
  <[
  "_bb0" :=
   "__2" <-{ IntOp I32 } (use{ IntOp I32 } (!{ PtrOp } ( "x" ))) +c{ IntOp I32 , IntOp I32 } (I2v (42) I32);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb1"
  ]>%E $
  <[
  "_bb2" :=
   return (use{ PtrOp } ("__0"))
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
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition mut_ref_add_42_def : function := {|
 f_args := [
  ("x", void* : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("__2", (it_layout I32) : layout)
 ];
 f_code := 
  <[
  "_bb1" :=
   !{ PtrOp } ( "x" ) <-{ IntOp I32 } use{ IntOp I32 } ("__2");
   "__0" <-{ StructOp unit_sl [] } zst_val;
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft4" "ulft__";
   "__2" <-{ IntOp I32 } (use{ IntOp I32 } (!{ PtrOp } ( "x" ))) +c{ IntOp I32 , IntOp I32 } (I2v (42) I32);
   assert{ BoolOp }: (val_of_bool false) = { BoolOp , BoolOp , U8 } (val_of_bool false);
   Goto "_bb1"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition mut_ref_add_client_def (mut_ref_add_42_loc : loc) : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("z", (it_layout I32) : layout);
  ("__2", (layout_of unit_sl) : layout);
  ("__3", void* : layout);
  ("__4", void* : layout);
  ("__5", (layout_of unit_sl) : layout);
  ("__6", (it_layout U8) : layout);
  ("__7", (it_layout U8) : layout);
  ("__8", (it_layout I32) : layout);
  ("__9", (layout_of unit_sl) : layout)
 ];
 f_code := 
  <[
  "_bb0" :=
   "z" <-{ IntOp I32 } I2v (1) I32;
   annot: StartLftAnnot "llft3" [];
   "__4" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft7" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTInt I32), "llft3" } ("z"));
   annot: StartLftAnnot "llft4" ["plft7"];
   "__3" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft6" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTInt I32), "llft4" } (!{ PtrOp } ( "__4" )));
   annot: CopyLftNameAnnot "plft8" "plft6";
   "__2" <-{ StructOp unit_sl [] } CallE mut_ref_add_42_loc ["plft8"] [@{expr} use{ PtrOp } ("__3")];
   annot: EndLftAnnot "llft4";
   annot: EndLftAnnot "llft3";
   Goto "_bb1"
  ]>%E $
  <[
  "_bb2" :=
   StuckS
  ]>%E $
  <[
  "_bb3" :=
   "__5" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ StructOp unit_sl [] } zst_val;
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft3";
   annot: EndLftAnnot "llft4";
   "__8" <-{ IntOp I32 } use{ IntOp I32 } ("z");
   "__7" <-{ BoolOp } (use{ IntOp I32 } ("__8")) = { IntOp I32 , IntOp I32 , U8 } (I2v (43) I32);
   "__6" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__7"));
   if{ BoolOp }: use{ BoolOp } ("__6") then
    Goto "_bb2"
   else
    Goto "_bb3"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition assert_pair_def : function := {|
 f_args := [
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("x", (use_layout_alg' (syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) : layout);
  ("xr", void* : layout);
  ("__3", (layout_of unit_sl) : layout);
  ("__4", (it_layout U8) : layout);
  ("__5", (it_layout U8) : layout);
  ("__6", (it_layout U8) : layout);
  ("__7", (it_layout I32) : layout);
  ("__8", (it_layout U8) : layout);
  ("__9", (it_layout I32) : layout);
  ("__10", (layout_of unit_sl) : layout)
 ];
 f_code := 
  <[
  "_bb1" :=
   "__5" <-{ BoolOp } val_of_bool false;
   Goto "_bb3"
  ]>%E $
  <[
  "_bb4" :=
   StuckS
  ]>%E $
  <[
  "_bb2" :=
   "__9" <-{ IntOp I32 } use{ IntOp I32 } (("x") at{ ((tuple2_sls (IntSynType I32) (IntSynType I32))) } "1");
   "__8" <-{ BoolOp } (use{ IntOp I32 } ("__9")) = { IntOp I32 , IntOp I32 , U8 } (I2v (1) I32);
   "__5" <-{ BoolOp } use{ BoolOp } ("__8");
   Goto "_bb3"
  ]>%E $
  <[
  "_bb5" :=
   "__3" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ StructOp unit_sl [] } zst_val;
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  <[
  "_bb0" :=
   "x" <-{ (use_op_alg' (syn_type_of_sls ((tuple2_sls (IntSynType I32) (IntSynType I32))))) } StructInit ((tuple2_sls (IntSynType I32) (IntSynType I32))) [("0", I2v (0) I32 : expr); ("1", I2v (1) I32 : expr)];
   annot: StartLftAnnot "llft3" [];
   "xr" <-{ PtrOp } AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft5" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTInt I32), "llft3" } (("x") at{ ((tuple2_sls (IntSynType I32) (IntSynType I32))) } "0"));
   !{ PtrOp } ( "xr" ) <-{ IntOp I32 } I2v (42) I32;
   annot: EndLftAnnot "llft3";
   "__7" <-{ IntOp I32 } use{ IntOp I32 } (("x") at{ ((tuple2_sls (IntSynType I32) (IntSynType I32))) } "0");
   "__6" <-{ BoolOp } (use{ IntOp I32 } ("__7")) = { IntOp I32 , IntOp I32 , U8 } (I2v (42) I32);
   if{ BoolOp }: use{ BoolOp } ("__6") then
    Goto "_bb2"
   else
    Goto "_bb1"
  ]>%E $
  <[
  "_bb3" :=
   "__4" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (use{ BoolOp } ("__5"));
   if{ BoolOp }: use{ BoolOp } ("__4") then
    Goto "_bb4"
   else
    Goto "_bb5"
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

End code.