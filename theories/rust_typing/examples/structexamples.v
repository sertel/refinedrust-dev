From caesium Require Import lang notation tactics.
From lithium Require Export tactics.
From refinedrust Require typing.

Program Definition unit_layout : struct_layout := 
  {| sl_members := [] |}.
Solve Obligations with solve_struct_obligations.

Definition fields_def := list (var_name * layout).
(* get the named fields *)
Fixpoint named_fields (sl_fields : field_list) : list (var_name * layout) :=
  foldr (λ '(n, ly) acc, match n with Some n => (n, ly) :: acc | _ => acc end) [] sl_fields.

(* TODO: generalize to permutations + subset? (it should work even when we ignore some named fields, I think, and reordering is allowed) *)
Definition sl_has_members (fields : list (var_name * layout)) (sl : struct_layout) := 
  fields = named_fields (sl.(sl_members)).


(*
  We pose the following restrictions: 
  - no DSTs currently
  - we pick a particular repr(C)-like representation for enums to encode them in terms of structs + unions
  - for generics, we compute a bound on the size. This makes a few assumptions that require that the layout algorithm that will be used is in some sense "sane": 
      - we require that all data we use has at most 128bit/16byte/4logbyte alignment
      - we require that the layout algorithm is at least as efficient (in terms of size) as the repr(C) layout algorithm.
          TODO we may want to relax that to a constant factor?


  Note that we do not model the following things:
  - Caesium fixes an endianness.
  - Caesium fixes the size of pointers to 64 bits.
  - Structs layouts are currently assumed to be determined by their component's layouts, not necessarily their types.
  - The model of enums follows repr(C).
  - We assume that fields are not reordered in structs.
  - ...


 Note: Maybe it would be interesting at some point to switch to a more abstract memory model that would allow us to model more things. e.g. Krebbers-style CH2O. 
  The semantics would directly know about structs/unions/enums, and pointers would be paths through objects.

 Would this also remove some of the trouble with the quite concrete layouts we have currently? We might be able to encode the fact that we don't care about how concretely data is layed out when we have some tree-like model.

 Of course, the Q is: what is the right balance between abstraction and fine-grained information? We still want to be able to have repr(C) stuff to reason about memcasts etc.

=> This is not the most relevant thing for now. It will be more relevant to get good verification results for unsafe code later on, though, but finding a good memory model (possibly with support for Stacked Borrows/Tree Borrows) is something that is an entirely new challenge that is orthogonal.


   For now, we remain in this somewhat awkward spot where we don't work with a fully concrete model (because we can't with generics) but don't mdoel all of the implementation-defined stuff of Rust.
 *)


(* 

  The size bounds are anyways kind of awkward, no matter what we do.
  In principle, the most reasonable thing would be to just remove the bound from the language model.
  That then kind of assumes, for it to be a reasonable thing overall, that we don't have bounds. 
  Then also the oracle thing would be reasonable.


 *)



Class MemEnv : Type := {
  struct_layout_alg : fields_def → string → struct_layout;
  struct_layout_alg_correct : ∀ def name, 
    sl_has_members def (struct_layout_alg def name);
}.


Module oracle.

  Section my_struct_gen_def.
    Context `{MemEnv}.
    Context (T_ly : layout).

    Definition my_struct_gen_members : fields_def := [("a", T_ly); ("b", void* ); ("c", T_ly)].

    Definition my_struct_gen_layout : struct_layout := struct_layout_alg my_struct_gen_members "my_struct".
    Lemma my_struct_gen_layout_mems : sl_has_members my_struct_gen_members my_struct_gen_layout.
    Proof. apply struct_layout_alg_correct. Qed.
  End my_struct_gen_def.

  (* But what stops me in the proof from just instantiating it with some way too large type, and then derive a contradiction? Can I somehow convincingly seal that? *)
  (* TODO: *)
End oracle.


(** Other approach where the oracle gets a correct layout already as a certificate that it can be layed out. *)
(* This has the disadvantage of carrying around ugly size bounds everywhere.... 
    (and if there are multiple generics involved in a definition, they are interdependent.. )
*)

(*
Class MemEnv : Type := {
  (* The layout algorithm, as a guarantee that the data can be layed out, can already assume that there exists a suitable layout. *)
  struct_layout_alg : fields_def → string → struct_layout → struct_layout;
  struct_layout_alg_correct : ∀ def name sl, 
    sl_has_members def sl →
    sl_has_members def (struct_layout_alg def name sl);
}.
*)

(* Maximum alignment of generics is 16 bytes or 128 bits. *)
Definition max_align_log : nat := 4.

(* Generate padding to correctly align the field starting at [offset] *)
Definition pad_field (offset : nat) (align_log : nat) : layout :=
  let alignment := (2^align_log)%nat in
  let misalignment := (offset `mod` alignment)%nat in
  if decide (misalignment > 0%nat) then 
    Layout (alignment - misalignment)%nat 0%nat 
  else Layout 0%nat 0%nat.
(* Alignment of a struct. *)
Definition struct_align_log (fields : fields_def) :=
  foldr Nat.max 0%nat ((λ '(_, ly), ly.(ly_align_log)) <$> fields).

Fixpoint layout_struct_with_reprC' (full_align : nat) (offset : nat) (fields : fields_def) : field_list := 
  match fields with 
  | [] => 
      (* pad the end of the struct to match its alignment *)
      let pad := pad_field offset full_align in
      [(None, pad)]
  | (x, ly) :: fields =>
      let pad := pad_field offset ly.(ly_align_log) in
      let r := layout_struct_with_reprC' full_align (pad.(ly_size) + ly.(ly_size) + offset) fields in
      (None, pad) :: (Some x, ly) :: r
  end.
Definition layout_struct_with_reprC (fields : fields_def) : field_list :=
  layout_struct_with_reprC' (struct_align_log fields) 0%nat fields.
Lemma check_fields_aligned_reprC fields pos : check_fields_aligned (layout_struct_with_reprC fields) pos = true.
Proof.
  induction fields as [ | [x ly] fields] in pos |-*.
  - cbn. unfold pad_field. cbn. 
    case_decide; first lia. unfold ly_align. cbn. 
    rewrite Z.mod_1_r. case_bool_decide; last lia. done.
  - cbn. rewrite !andb_true_iff. split_and!.
Abort.

Ltac solve_size_bound :=
  cbv delta -[Z.add Z.max Z.lt Nat.succ Z.pow Z.mul Z.of_nat Nat.add foldl sum_list fmap Nat.pow max_list Z.opp] in *; 
  simpl;
  lia. 

Section arbitrary_layouts.
  (* Consider 

      struct my_struct {
        a : i32,
        c : Box<i32>  
      }

    Rust does not make any layout guarantees (except if it is declared as repr(C)).
    As an approximation of this, we can do the verification for all struct_layouts with the right members.
    Ideally, we want to do our verification no matter what valid concrete layout the compiler chooses.
   *)

  (* TODO: parameteize over pointer size? or set statically. *)
  (* TODO: packed structs? not handled by current def. *)
  (* TODO: max size of structs (Signed size_t) *)
  Section my_struct_def.
    Definition my_struct_members : fields_def := [("a", it_layout i16); ("b", void*)].

    Program Definition my_struct_sl_reprC : struct_layout :=
      {| sl_members := [(Some "a", it_layout i32); (None, Layout 4%nat 0%nat); (Some "b", void* )]; |}.
    Solve Obligations with solve_struct_obligations.
    (*Lemma my_struct_reprC_members : sl_has_members my_struct_members my_struct_sl_reprC.*)
    (*Proof. reflexivity. Qed.*)
  End my_struct_def.

  (*
  Section my_struct_gen_def.
    Context (T_ly : layout) (T_ly_align_bound : T_ly.(ly_align_log) ≤ max_align_log).
    Definition my_struct_gen_members : fields_def := [("a", T_ly); ("b", void* ); ("c", T_ly)].

    Definition size_bound_of_my_struct_gen : Z :=
      sum_list (ly_size <$> my_struct_gen_members.*2) + 
      (* this is quite a loose bound *)
      2^max_align_log * length (my_struct_gen_members).

    (*Program Definition my_struct_sl_reprC : struct_layout :=*)
      (*{| sl_members := [(Some "a", it_layout i32); (None, Layout 4%nat 0%nat); (Some "b", void* )]; |}.*)
    (*Solve Obligations with solve_struct_obligations.*)

    (*Lemma my_struct_reprC_members : sl_has_members my_struct_members my_struct_sl_reprC.*)
    (*Proof. reflexivity. Qed.*)

    (* Want to calculate the correct number of alignment bits. 
        TODO: how to do this in an easy way?
     *)
    (* Examples: 
        0, 1 => 2  
     *)


    (* Note: key to making all of this feasible/modular would be to resolve this to _concrete_ bounds on the size at some point. 
        i.e.: solve the equation for size(T)
    *)
    (* moreover, just assume that align_log < 8 or so. Since alignment in structs goes by max and we don't have stuff > 128 bits, that seems fine *)
    (* a very loose bound for structs: just assume we need the maximum possible padding, 2^7, between every two fields *)
    (* under that condition, we should always be able to define the repr(C) layout. *)

    (* the alignment of the whole struct *)
    Definition my_struct_gen_align fields : nat := 
      struct_align_log fields.

    Program Definition my_struct_gen_reprC : struct_layout :=
      {| sl_members :=
          [(Some "a", T_ly); (None, Layout (pad_field T_ly.(ly_size) (void*.(ly_align_log))) 0%nat); 
          (Some "b", void* ); (None, Layout (pad_field (void*.(ly_size)) (T_ly.(ly_align_log))) 0%nat);
          (Some "c", T_ly); (None, Layout (pad_field (T_ly.(ly_size)) (my_struct_gen_align)) 0%nat)]
      |}.
    Next Obligation.
      done.
    Qed.
    Next Obligation.
      simpl. 
      (* TODO: padding *)
    Admitted.
    Next Obligation. 
      simpl. 
      (* TODO: prove that alignment is fine *)
    Admitted.
  End my_struct_gen_def.

  (* experiments for the size bound approach *)
  Definition max_size_in_fun (T_ly : layout) : Z := 
    foldl Z.max 0%Z [size_of_my_struct_gen T_ly; (Z.of_nat (layout_of unit_layout).(ly_size))].

  (* how can we bound the alignment? *)
  (* we always need at most 63 padding bits, assuming that none of our types has alignment greater than 8byte. *)

  Section fundef.
    Context (T_ly : layout) (Hsz : max_size_in_fun T_ly < max_int size_t + 1).
    (* assumption for the function *)
    (* from Hsz, we should be able to define repr(C) layouts to pass to the oracle *)



  End fundef.


  Section inst.
    (* we instantiate the function's assumptions *)
    Goal (max_size_in_fun (i32) < max_int size_t + 1)%Z.
    Proof. 
      solve_size_bound.
    Abort.

    (* this should also be compositional: in the assumption of our own function, we can just include the (instantiated) assumptions of the other functions we are using *)
  End inst.
   *)
 
End arbitrary_layouts.


(** Old approach where we have parameters for all used layouts is below: *)

(* 
   fn my_struct_bar(x : my_struct) -> i32{
     let y = x.a;
     42  
   }
*)
Section assume.
  Context (my_struct_sl : struct_layout). 


  (* 
      

       
      fn do_something<T>(x : T) where T: Sized {
        // use some structs
      }
      ∀ T: type, safe(do_something<T>)


      oracle: 
        - sizeof((T, i32)) <= isize_max
      above proposal: 
        - provide layout for (T, i32)
      just bound size for generic types statically
        - not clear how that works with nesting. 
      try to just "assume" it:
        - 
      assumes for "layout is fine", we abort otherwise: 
        -> try out this approach.

     struct_members + proof: struct members fit in isize -> struct_layout 

   *)


  Context (my_struct_sl_has_members : sl_has_members my_struct_members my_struct_sl).

  Definition my_struct_bar : function := {|
   f_args := [
    ("x", my_struct_sl : layout)
   ];
   f_local_vars := [
    ("__0", it_layout i32);
    ("y", it_layout i16)
   ];
   f_code :=
    <["_bb0" :=
     "y" <-{ IntOp i16 } use{IntOp i16} ("x" at{my_struct_sl} "a");
     "__0" <-{ IntOp i32 } i2v 42 i32;
     Return (use{ IntOp i32 } ("__0"))
    ]>%E $
    ∅;
   f_init := "_bb0";
  |}.
End assume.

Section generics.
  (* 
    Consider the struct
      struct<T> my_struct2 {
        a : T,
        b : i32,
     }
   *)

  Section my_struct2_def.
    Context (T_ly : layout).

    Definition my_struct2_members := [("a", T_ly); ("b", it_layout i32)].
  
    (* no repr(C) definition as it is generic *)
  End my_struct2_def.

  (* 
     fn my_struct2_bar<T>(x : my_struct2<T>) -> i32 {
       let y = x.a;
       42  
     }
  *)
  Section assume.
    Context (T_ly : layout).
    (* build in more assumptions into T_ly: has size <= isize_max 
    *)

    (* 
      assume (exists_layout my_struct2_members)
    *)


    (*Context (my_struct2_sl : struct_layout). *)


    Context (my_struct2_sl_has_members : sl_has_members (my_struct2_members T_ly) my_struct2_sl).
    Definition my_struct2_bar : function := {|
     f_args := [
      ("x", my_struct2_sl : layout)
     ];
     f_local_vars := [
      ("__0", it_layout i32);
      ("y", it_layout i16)
     ];
     f_code :=
      <["_bb0" :=
       "y" <-{ UntypedOp T_ly } use{UntypedOp T_ly } ("x" at{my_struct2_sl} "a");
       "__0" <-{ IntOp i32 } i2v 42 i32;
       Return (use{ IntOp i32 } ("__0"))
      ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
  End assume.

  Section spec.
    (* the specification and proof should also be generic in the layout, as well as T *)
    Import typing.
    Context `{typeGS Σ}.
    Context (rt : Type) (T : type rt). 
    Context (my_struct2_sl : struct_layout).
    Context (my_struct2_sl_has_members : sl_has_members (my_struct2_members T.(ty_layout)) my_struct2_sl).
  End spec.

  Section monomorphic_client.
    (*
      fn foo(x : my_struct2<i32>) {
        my_struct2_bar(x);
      }
    *)
    Context (my_struct2_sl : struct_layout). 
    Context (my_struct2_sl_has_members : sl_has_members (my_struct2_members i32) my_struct2_sl).
    
    Context (my_struct2_bar_loc : loc).

    Definition foo : function := {|
     f_args := [
      ("x", my_struct2_sl : layout)
     ];
     f_local_vars := [
      ("__0", unit_layout : layout);
      ("__1", unit_layout : layout)
     ];
     f_code :=
      <["_bb0" :=
       "__1" <-{UntypedOp unit_layout} Call my_struct2_bar_loc [use{UntypedOp my_struct2_sl} "x"]; 
       "__0" <-{ UntypedOp unit_layout } (Val []);
       Return (use{ UntypedOp unit_layout } ("__0"))
      ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
  End monomorphic_client.
  Section monomorphic_client_proof.

    (*fntbl_entry my_struct2_bar_loc (my_struct2_bar i32 my_struct2_sl)*)
  End monomorphic_client_proof.

  (* What's the tldr of this?
    - when defining a struct, we should define the list of actual members.
    - when defining a function using a struct, we just assume _some_ layout for that struct
    - when proving a specification for such a function, we assume sl_has_members for that layout

    - when defining a function with type parameters, we assume some layout
    - when proving a specification for a generic function, we assume some rtype and instantiate the code's layout with that type's layout
   *)

  (* For enums/structs, for now: 
    - only handle layouts that do not reorder the struct fields.
    - for enums, this means in particular that it is a 
          struct {
            variant: usize,
            content: union ...
          } 
  *)
End generics.

Section tuples.
  (* Tuples are like structs, but they don't get a special name. *)

End tuples.

(* Not a goal currently: deal with layout optimizations like the one for Option that rustc does. 
    - in a sense, the following representation is too concrete.

  unsafe code can even rely on this layout optimization specifically for Option.


    Alternative: introduce enums as first-class constructs into Caesium for a less concrete model. 
 *)
Section enum.
  (* Represent an enum as struct with discriminant + union of variants *)

  (* the other repr with discriminant in each variant is NOT equivalent. TODO: think about why. 

    enum repr(C) -> some RFC2195 TODO lookup.
  *)

  (* TODO rust unions allow different padding at start for different variants; look at this. 
    -> Shelve this.
  *)


  (* global oracle = member_list + identifier -> layout 
      => different structs with same fields can have different layout
  
  *)

  (* 
      enum Option<T> {
        Some(t : T),
        None 
      }

   *)


  (* We define structs for each of the variants *)

  Section variant_def.
    Context (T_ly : layout).
    Definition Option_T_Some_members : fields_def := [("t", T_ly)].
  End variant_def.

  Section variant_def.
    Context (T_ly : layout).
    Definition Option_T_None_members : fields_def := [].
  End variant_def.

  Section union_def.
    Context (T_ly : layout).
    Context (Option_T_Some_sl : struct_layout).
    Context (Option_T_None_sl : struct_layout).
    
    Definition Option_T_union_members : fields_def := [("Some", Option_T_Some_sl : layout); ("None", Option_T_None_sl : layout)].
  End union_def. 

  Section enum_def.
    Context (T_ly : layout).
    Context (Option_T_Some_sl : struct_layout).
    Context (Option_T_None_sl : struct_layout).
    Context (Option_T_union_ul : union_layout).
    
    Definition Option_T_members : fields_def := [("discriminant", u64 : layout); ("data", Option_T_union_ul : layout)].
  End enum_def.

  Section reprC_i32.
    Program Definition Option_i32_Some_reprC_sl : struct_layout := 
      {| sl_members := [(Some "t", i32 : layout)] |}.
    Solve Obligations with solve_struct_obligations.

    Program Definition Option_i32_None_reprC_sl : struct_layout :=
      {| sl_members := [] |}.
    Solve Obligations with solve_struct_obligations.

    Program Definition Option_i32_union_reprC_ul : union_layout :=
      {| ul_members := [("Some", Option_i32_Some_reprC_sl); ("None", Option_i32_None_reprC_sl)] |}.
    Solve Obligations with solve_struct_obligations.

    Program Definition Option_i32_reprC_sl : struct_layout :=
      {| sl_members := [(Some "discriminant", u64); (Some "data", Option_i32_union_reprC_ul)] |}.
    Solve Obligations with solve_struct_obligations.
  End reprC_i32.

  (*
     fn unwrap(x : Option<T>) -> T {
        match x {
          None => assert!(false),
          Some(i) => i
        }
     } 
   *) 


  Section unwrap_code.
    Context (T_ly : layout).
    Context (Option_T_Some_sl : struct_layout).
    Context (Option_T_None_sl : struct_layout).
    Context (Option_T_union_ul : union_layout).
    Context (Option_T_sl : struct_layout).

    Definition unwrap : function := {|
     f_args := [
      ("x", Option_T_sl : layout)
     ];
     f_local_vars := [
      ("__0", unit_layout : layout);
      ("__1", unit_layout : layout)
     ];
     f_code :=
      <["_bb0" :=
        Switch u64 (use{IntOp u64} ("x" at{Option_T_sl} "discriminant")) (<[0%Z := 0%nat]> (∅ : gmap Z nat)) [Goto "_bb1"] (Goto "_bb2")
       ]>%E $ 
      <["_bb1" := 
        "__0" <-{UntypedOp T_ly} use{UntypedOp T_ly} ((("x" at{Option_T_sl} "data") at_union{Option_T_union_ul} "Some") at{Option_T_Some_sl} "t");
        Return (use{UntypedOp T_ly} "__0")
      ]>%E $
      <["_bb2" := 
        StuckS
      ]>%E $
       ∅;
     f_init := "_bb0";
    |}.
  End unwrap_code.


End enum.
