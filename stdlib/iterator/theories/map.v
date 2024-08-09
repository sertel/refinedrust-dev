From refinedrust Require Import typing.
From stdlib.iterator.theories Require Import iterator.
From stdlib.closures.theories Require Import closures.

(* 

 *)

(* State of the map iterator *)
(*
Record MapIterator 
  {it_state : Type} (A B : Type) (IT : Iterator it_state A)
  (*(clos_state : Type) *)
  (*(CL : FnMut*)
  := mk_map_iterator {
  (* TODO: instead, this should also contain the state of the closure *)
  map_it_fn : A → B;
  map_it_state : it_state;
}.

Arguments map_it_state {_ _ _ _}.
Arguments map_it_fn {_ _ _ _}.

Global Instance map_iterator {it_state : Type} (A B : Type) (IT : Iterator it_state A) : Iterator (MapIterator A B IT) B :=
{|
  iterator_next s1 e s2 := 
    ∃ e', IT.(iterator_next) s1.(map_it_state) e' s2.(map_it_state) ∧ s1.(map_it_fn) e' = e ∧ s2.(map_it_fn) = s1.(map_it_fn);
|}.
*)
