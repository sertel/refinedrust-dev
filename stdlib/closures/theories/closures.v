From refinedrust Require Import typing.


(** FnMut closures: FnMut closures have state (of type [S]) that gets mutated on every call. *)
Class FnMut (S : Type) (args : list Type) (ret : Type) := mk_fnmut {
  fnmut_call_rel : S → hlist id args → S → ret → Prop;
}.

(** Fn closures: Fn closures have state (of type [S]) that does not get mutated. *)
Class Fn (S : Type) (args : list Type) (ret : Type) := mk_fn {
  fn_call_rel : S → hlist id args → ret → Prop;
}.

(** FnOnce closures *)
Class FnOnce (S : Type) (args : list Type) (ret : Type) := mk_fnonce {
  fnonce_call_rel : S → hlist id args → ret → Prop;
}.

(* Conversion *)
Definition Fn_to_FnOnce_call_rel {S : Type} {args: list Type} {ret : Type} (FN : Fn S args ret) : FnOnce S args ret :=
  mk_fnonce _ _ _ FN.(fn_call_rel).
Definition FnMut_to_Fn_call_rel {S : Type} {args: list Type} {ret : Type} (FN : FnMut S args ret) : Fn S args ret :=
  mk_fn _ _ _ (λ s args ret, ∃ s', FN.(fnmut_call_rel) s args s' ret).



(* Shortcomings of this:
   - we can only specify things on the refinements.
     We cannot state custom types.
     We cannot require custom ownership. <--- This is a BIG limitation.
   - One way to require custom ownership would be to include it in the state of the closure.
     But even then it is quite limited.
   - Typeclass resolution will not really work.
     Instead, these should be explicitly passed parameters.

   
  How can we fix this?
   1) embed iProps. I could use fn_params for instance.
      But it has to match with the signature and return type, so maybe a variant of that.
   2) additionally have iProp fields for pre and post. 
      


 *)

Record FnOnce2 `{!typeGS Σ} := mk_fnonce2 {
  fnonce_call_spec : sigT (λ T, T → fn_params);
}.

(* Now this is quite similar to the trait spec encoding. *)
(* If I use explicitly passed parameters, I think there's not much difference to just using the trait mechanism directly. *)




