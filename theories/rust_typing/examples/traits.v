From refinedrust Require Import typing.


(** Some experiments with traits and trait translation *)

(*
trait<T> Foo<T> {
  #[rr::params(x)]
  #[rr::args(x)]
  #[rr::returns("()")]
  fn foo(x : T) -> (); 
}
 *)
Section foo_spec.
  Context `{typeGS Σ}.

  Definition type_of_foo {rt} (T : type rt) := 
    fn(∀ (x) : rt, (λ ϝ, []); x @ T; True)
      → ∃ () : unit, () @ unit_t; (True).
End foo_spec.

(* 
fn bar<T>(x : T) where T : Foo {
  x.foo();
}
*)
Section bar_code.
  Context (T_ly : layout).
  Definition bar (Foo_T_foo_loc : loc) : function := {|
   f_args := [("x", T_ly)];
   f_local_vars := [
    ("__0", unit_layout : layout)
   ];
   f_code :=
    <["_bb0" :=
     expr: Call Foo_T_foo_loc [use{UntypedOp T_ly} "x"];
     "__0" <-{ UntypedOp (unit_layout) } zst_val;
     Return (use{ UntypedOp (unit_layout) } ("__0"))
    ]>%E $
    ∅;
   f_init := "_bb0";
  |}.
End bar_code.
Section bar_spec.
  Context `{typeGS Σ}.
  Definition type_of_bar π {rt} (foo_loc : loc) := 
    fn(∀ (T, r) : (type rt * rt), (λ ϝ, []); r @ T;
      □foo_loc ◁ᵥ{π} foo_loc @ function_ptr [T.(ty_layout)] (type_of_foo T)) 
      → ∃ (x) : unit, x @ unit_t; (True).

  Lemma bar_typed π {rt} foo_loc T_ly :  
    ⊢ typed_function π (bar T_ly foo_loc) (type_of_bar π (rt := rt) foo_loc).
  Proof.
    iStartProof.
    start_function "bar" ( (T, r) ) => arg_x local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.

    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
    (* TODO extend the solver to handle these generic things *)
  Abort.
End bar_spec.

(* 
impl Foo<i32> for i32 {
  fn foo(x : i32) -> () {
    ()   
  }
}
 *)
Section Foo_i32_code.
  Context `{typeGS Σ}.

  Definition foo_i32 : function := {|
   f_args := [("x", i32 : layout)];
   f_local_vars := [
    ("__0", unit_layout : layout)
   ];
   f_code :=
    <["_bb0" :=
     "__0" <-{ UntypedOp (unit_layout) } zst_val;
     Return (use{ UntypedOp (unit_layout) } ("__0"))
    ]>%E $
    ∅;
   f_init := "_bb0";
  |}.
End Foo_i32_code.
Section Foo_i32_spec.
  Context `{typeGS Σ}.

  Lemma foo_i32_typed π :  
    ⊢ typed_function π (foo_i32) (type_of_foo (int i32)).
  Proof.
    iStartProof.
    start_function "foo_i32" ( r ) => arg_x local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.

    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  Qed.
End Foo_i32_spec.

(* 
fn baz() {
  bar::<i32>(42)
}
 *)
Section baz_code.
  Context `{typeGS Σ}.

  Definition baz (bar_i32_loc : loc) : function := {|
   f_args := [];
   f_local_vars := [
    ("__0", unit_layout : layout)
   ];
   f_code :=
    <["_bb0" :=
     expr: Call bar_i32_loc [Val(i2v 42 i32)];
     "__0" <-{ UntypedOp (unit_layout) } zst_val;
     Return (use{ UntypedOp (unit_layout) } ("__0"))
    ]>%E $
    ∅;
   f_init := "_bb0";
  |}.
End baz_code.
Section baz_spec.
  Context `{typeGS Σ}.
  Definition type_of_baz := 
    fn(∀ () : (), (λ ϝ, []); True)
      → ∃ () : unit, () @ unit_t; (True).

  (* Not sure if this is bad: the function requires code for foo, even though it doesn't directly call it (but transitively, and this is locally visible in the code of baz) *)
  Lemma baz_typed π foo_i32_loc bar_i32_loc :  
    □foo_i32_loc ◁ᵥ{π} foo_i32_loc @ function_ptr [i32 : layout] (type_of_foo (int i32)) -∗  
    □bar_i32_loc ◁ᵥ{π} bar_i32_loc @ function_ptr [i32 : layout] (type_of_bar π (rt := Z) foo_i32_loc) -∗
    typed_function π (baz bar_i32_loc) (type_of_baz).
  Proof.
    iStartProof.
    start_function "foo_i32" ( () ) => local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.

    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  Qed.
End baz_spec.


(* Q: in this setting, how do I say that certain impls are generic in other things? 
  For instance: 

  impl<'a> Foo for &'a i32 {
    fn foo(x : &'a i32) -> () {
      ()   
    }
  }

or: 
  impl<T> Foo for (T, T) {
    fn foo(x : (T, T)) -> () {
      ()   
    }
  }
  

  Essentially: an implementation of the type should be able to introduce new parameters? 
*)

Section Foo_T_T_code.
  Context `{typeGS Σ}.
  Axiom T_pair_layout : layout → layout → struct_layout.

  Definition foo_T_T (T_ly : layout) : function := {|
   f_args := [("x", T_pair_layout T_ly T_ly: layout)];
   f_local_vars := [
    ("__0", unit_layout : layout)
   ];
   f_code :=
    <["_bb0" :=
     "__0" <-{ UntypedOp (unit_layout) } zst_val;
     Return (use{ UntypedOp (unit_layout) } ("__0"))
    ]>%E $
    ∅;
   f_init := "_bb0";
  |}.
End Foo_T_T_code.

Section Foo_T_T_spec.
  Context `{typeGS Σ}.

  (* If the function was standing on its own: *)
  Definition type_of_foo_T_T {rt} := 
    fn(∀ (T, r) : (type rt * (place_rfn rt * place_rfn rt)), (λ ϝ, []); r @ pair_t T T (T_pair_layout T.(ty_layout) T.(ty_layout)); True)
      → ∃ (x) : unit, x @ unit_t; (True).

  Lemma foo_T_T_typed {rt} T_ly π :  
    ⊢ typed_function π (foo_T_T T_ly) (type_of_foo_T_T (rt :=rt)).
  Proof.
    iStartProof.
    start_function "foo_T_T" ( (T, r) ) => arg_x local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.
    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  Qed.

  (* but now: (this has the parameter at Coq level) *)
  Lemma foo_T_T_typed' {rt} T_ly (T : type rt) π :  
    ⊢ typed_function π (foo_T_T T_ly) (type_of_foo (pair_t T T (T_pair_layout T.(ty_layout) T.(ty_layout)))).
  Proof.
    iStartProof.
    start_function "foo_T_T" ( r ) => arg_x local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.
    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  Qed.
  (* i.e., saying: forall T, I can get a function pointer to a function foo<(T, T)> *)


  (* Can I prove some subtyping relation between the two? 
    ->: Assume I have the first type assignment. Give me a T for the second one. Give me all the parameters for the second one, now I can instantiate the first one. This works fine.
    <- Assume I have the seocnd type assignment. Introduce all the parameters for the first one. Now can instantiate the second one.
        This works fine, too.


    Point: It's just a bit of quantifier commutation, nothing bad.
    In practice: I'd still like to assume the "direct" specification (i.e. the second one), because that better matches and is what I actually require.
      But the question is at which point to specialize. 
  *)
End Foo_T_T_spec.

(* Which of the specs can I actually use? *)
(* 
 fn foobaz<T>(x : T * T) {
  bar::<(T, T)>(x)
}
 *)
Section foobaz_code.
  Context `{typeGS Σ}.

  Definition foobaz (T_ly : layout) (bar_T_T_loc : loc) : function := {|
   f_args := [("x", T_pair_layout T_ly T_ly : layout)];
   f_local_vars := [
    ("__0", unit_layout : layout)
   ];
   f_code :=
    <["_bb0" :=
     expr: Call bar_T_T_loc [use{UntypedOp (T_pair_layout T_ly T_ly)} "x"];
     "__0" <-{ UntypedOp (unit_layout) } zst_val;
     Return (use{ UntypedOp (unit_layout) } ("__0"))
    ]>%E $
    ∅;
   f_init := "_bb0";
  |}.
End foobaz_code.
Section foobaz_spec.
  Context `{typeGS Σ}.

  (* This uses the spec that we'd give it on its own *)
  Definition type_of_foobaz {rt} (T_ly : layout) := 
    fn(∀ (T, r1, r2) : (type rt * rt * rt), (λ ϝ, []); (PlaceIn r1, PlaceIn r2) @ pair_t T T (T_pair_layout T_ly T_ly); True)
      → ∃ () : unit, () @ unit_t; (True).

  Lemma foobaz_typed π {rt} T_ly bar_T_T_loc foo_T_T_loc :  
    □foo_T_T_loc ◁ᵥ{π} foo_T_T_loc @ function_ptr [T_pair_layout T_ly T_ly : layout] (type_of_foo_T_T (rt := rt)) -∗  
    □bar_T_T_loc ◁ᵥ{π} bar_T_T_loc @ function_ptr [T_pair_layout T_ly T_ly : layout] 
      (type_of_bar π (rt := (place_rfn rt * place_rfn rt)) foo_T_T_loc) -∗
    typed_function π (foobaz T_ly bar_T_T_loc) (type_of_foobaz (rt := rt) T_ly).
  Proof.
    iStartProof.
    start_function "foobaz" ( ((T & r1) & r2) ) => arg_x local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.

    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
    (* Of course, this doesn't quite work: we'd need to prove a subsumption for the type now. 
      
    *)
  (*Qed.*)
  Abort.

  (* This uses the "direct" spec *)
  (* Note that we need to "glue" the function assumption directly into the type of foobaz here, as the instance for (T, T) depends on T at the logic-level, not at the function level. *)
  (* So this one is not as great... *)
  Definition type_of_foobaz' {rt} π (T_ly : layout) (foo_T_T_loc : loc ) := 
    fn(∀ (T, r1, r2) : (type rt * rt * rt), (λ ϝ, []); (PlaceIn r1, PlaceIn r2) @ pair_t T T (T_pair_layout T_ly T_ly); 
    □foo_T_T_loc ◁ᵥ{π} foo_T_T_loc @ function_ptr [T_pair_layout T_ly T_ly : layout] (type_of_foo (pair_t T T (T_pair_layout T_ly T_ly))))
      → ∃ () : unit, () @ unit_t; (True).
  Lemma foobaz_typed' π {rt} T_ly bar_T_T_loc foo_T_T_loc :  
    □bar_T_T_loc ◁ᵥ{π} bar_T_T_loc @ function_ptr [T_pair_layout T_ly T_ly : layout] 
      (type_of_bar π (rt := (place_rfn rt * place_rfn rt)) foo_T_T_loc) -∗
    typed_function π (foobaz T_ly bar_T_T_loc) (type_of_foobaz' (rt := rt) π T_ly foo_T_T_loc ).
  Proof.
    iStartProof.
    start_function "foobaz" ( ((T & r1) & r2) ) => arg_x local_0. 
    intros.
    init_lfts (∅).
    repeat liRStep; liShow.

    Unshelve. 
    all: li_unshelve_sidecond; sidecond_hook.
  (*Qed.*)
  Abort.

  (* Downside: it is basically impossible to properly comprehend this... *)
  (* 
    Also: I wonder if having to include it in the spec as an assumption, below receiving the type, is the right thing.

    Is there some kind of system as for what belongs where?
      e.g. why is bar in a different position as foo? 

    I guess the difference is: for foo we use an instance which depends on the generic. for bar we merely call a function that works for any parameter and just need to predetermine the layout.

    Also the difference is: When another function uses the function, the _caller_ needs to care about providing the ones that directly appear in the type, while the ones that appear only in the statement are provided by adequacy/the linking theorem.

    TODO: think more about the core principles underlying this.
   *)

  (* 
      One Q: should I just assume the formulation of a particular instance that is being used (not necessarily fully specialized to how i actually use it) or rather require something specialized to what I require?
        This might also have implications on where/how we resolve which instances actually get used.
    
      -> Is a function pointer that I assuem there for one trait instance or for one specializationi of a trait instance? 
          -> It might be somewhere in-between. E.g. consider that we anyways have to specify the layout for generics already, so it can't really be the fully generic instance.
          -> so maybe just make it consistent and take it as corresponding to concrete specializations.
          -> otoh, the middle point also seems to be valid, since I anyways need to quantify over the layout; so making it fully generic modulo the layout seems like a fine design choice.


      -> Trait resolution time: 
          - if I assume fully specialized, then we essentially resolve it in adequacy when linking up. [also may have multiple function assumptions for the same instances?]
              Specialization: Instance + layout + type (as far as possible)
          - if I just assume generic instances, I might in principle have conflicts. These get resolved at codegen time, and the type checker doesn't have to do anything for that, because the locaiton keys which one we use.
              Specialization: Instance + layout
        => In both cases, the type system itself doesn't need to do any resolution. It is essentially performed at code generation time. Only the degree of specialization is really different.
   *)
End foobaz_spec.





(* Improving ergonomics of this handling... can we encapsulate stuff into a typeclass for instance? 
  [ e.g. : does it make sense to somehow shift the resolution to typeclass search instead of doing it statically? ]
   
  
  Point: other code that uses it doesn't care about the concrete code that implements the trait, but only about the spec + a function ptr (location) implementing it. 
  The existential for the code can be dispatched at linking time (adequacy).


  For bundling up a whole trait: 
    - create a definition that takes a list of locations and does a bigsep? 
  For associated types: 
    - what happens if I quantify over some implementor of the trait? -> I get some arbitrary type there. I only know that it is "coherent" among the trait methods
      one option: quantify externally (universally) over the type.
      other option: bundle it in the "implements trait" assumption, existentially. I think I prefer the latter, since it makes types easier to read.
      Need some special support in the start_function automation to destruct that. 

    e.g. for Iterator: 
      implements_Iterator {rt] (T : type rt) (fn_locs : list loc) := 
        ∃ Item_rt (Item_type : type Item_rt), 
          match_functions fn_locs fn_types 
           where fn_types := [next : &mut T -> Option<Item_type>; ... ]
           and match_functions fn_locs fn_types := [∗ list] l; ty ∈ fn_locs; fn_types, l ◁ l @ fn_ptr ty 
      
*)









(** ** The special case of drop *)
(** Drop is a bit special due to drop glue:
  
    Also, there are essentially two Drop "traits" that we care about: 
    - one is the Drop from Rust, which we should try to translate faithfully. It is handled as a normal 
    - the other is DoDrop, which is auto-generated and corresponds to what the drop glue does, roughly.
       I.e.: it will first call Drop (if it is implemented), then go over all "droppable" fields of a struct and DoDrop them. All non-"droppable" fields are ghost-dropped.
       Finally, all the ownership collected from the second step is collected and returned.

       "droppable" fields include box, structs, enums, unions. (everything which may have some ownership/memory that needs to be freed?), but in particular not references or integers.

    DoDrop features custom postconditions per type. Arguably, it maybe just shouldn't be seen as a trait, but as some "normal" function that is called in the background. 

    NOTE: Drop is also somewhat weird in that it takes only a mutable reference, but often it will deinitialize the type and break some invariants that will normally hold. This is also why Drop::drop can normally not be called explicitly.
    Conjecture: I think that Drop should always uphold safety invariants of the structs fields, so that the drop glue may afterwards safely call drop on them. But it may be break the safety invariant of the whole struct itself.
      In most interesting cases, this means that it deinitializes memory and leaves some raw pointers dangling (which doesn't affect their safety invariants!).

    How do we model this adequately?


    For the case of box, maybe just manually implement it for now, instead of translating properly. We anyways do that for other things already.
*)


(*

  trait<T> Drop<T> {
    // NOTE: this mutable reference will in general not uphold the safety invariants associated with it.
    // Thus, we should semantically interpret it as an owned pointer. 

    fn drop(&mut self);
  }

  impl<T> Drop<Box<T>> {
      unsafe {
        drop_in_place(self.ptr.as_ptr());
        // this should be translated to our intrinsic memdealloc operation
        // and this is not actually what happens in Rust, because Rust's box doesn't use the Global API
        let c: NonNull<T> = self.ptr.into();
        Global.deallocate(c.cast(), Layout::new::<T>())
        
        // Note: after this, the type contract of Box is broken, because there is no backing memory anymore, even though we just have a mutable ref..
      }
  }


  unsafe fn drop_in_place<T: ?Sized>(to_drop: *mut T) {
      // implemented as a compiler intrinsic, doesn't have an actual impl
      // replaced by drop glue
  }
  // i.e.: drop_in_place is essentially the DoDrop function impl.


  DoDrop<Box>(mut self) {
    drop(&mut self); 
    // this isn't really a box here anymore!

    // do nothing, because Unique<T> doesn't have an interesting Drop/DoDrop implementation
    // I move out of it here, is that fine? I think it should be.
    Unique::do_drop(self.ptr);
   }

 *)

(* 
  For the translation: make drop get an owned_ptr essentially (it's really not a mutable reference from a safety invariant perspective).
  
  Q: how does it differ from a Box?
    We don't have the right to deallocate the pointer. Maybe we want to have an extra own_ptr type that doesn't have this, similar to lambdarust, and replace the box ltype with that.
  
  How does box relate to own_ptr?
    it just has the deallocation permission on top?

  Essentially, we need to handle raw/owned pointers properly. drop should also return some ownership _explicitly_, but what that is will depend on the concrete implementation.
    In principle, that ownership is similar to a mutable reference: we are not allowed to deallocate or move out of it.
    But we are allowed to remove some "logical" ownership (e.g. the ownership of an allocated Unique, or the backing memory of a Vec) that is not directly captured by the Rust types, and leave some pointers dangling.


 *)

(* 
  What is the simplest working solution to get drop working to a reasonable degree? 
  - two orthogonal challenges: the interface trouble with the Rust Drop trait, and the dynamic drop check stuff
  - what is safe to say: to handle drop for generics, we will require every type T to provide a drop shim, 
       of type T → () [to support unsized types, need to have *mut T -> () where the raw pointer has ownership.
    This will consume ownership [ in the unsized case, we afterwards get a location pointing to uninit].
    For simple types/copy types that don't need any dropping (like i32), this will just be empty. 
    Internally, this should handle both Drop and the drop glue.


  For now, we manually write these drop shims. Later on, we generate them from the Drop implementation.


  When instantiating generics with mutable references, what about getting back observations? 
   - we may say that the drop shim returns ghost_drop. This may be passed through to the postcond of the function.
  -> drop shims have custom postconditions per type. How do we formulate this well for generics? 

 *)







(* TODO: work out some examples with this *)

(** Some experiments with Drop *)

