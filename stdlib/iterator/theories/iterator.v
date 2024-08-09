From refinedrust Require Import typing.

(* 
  iteration state for vector:
  - (index)
  - remaining vector elements that will be output
  - (for mut: information to resolve previous elements)

   next for vec::IterMut:
    it_state: (x :: remaining_els, vars)
    ∃ γi,
    it_state: (remaining_els, vars ++ [γi])
    returns (#x, γi)

    put into our generic interface: 
      Define type 
        Record VecIterMutState (T_rt : Type) := {
          vec_iter_mut_state_remaining : list T_rt;
          vec_iter_mut_state_vars : list gname;
        }.

      Refine vec::IterMut by VecIterMutState

      Define an instance of Iterator, 
      Definition vec_iterator (T_rt : Type) := {|
        iterator_state := VecIterMutState T_rt;
        iterator_next s1 elem s2 :=
          ∃ remaining, s1.(vec_iter_mut_state_remaining) = elem :: remaining ∧
          ∃ γi, ....
      |}.
    


   If I drop vec::IterMut:
    then I get an observation of the whole vector having the vars elements

  Note: iterator_next needs to be a relation, as it may allocate new ghost resources
    This relation is pure, but we need to prove the reflection of it into Iris when proving the spec


  Important: the class should be indexed by the state type, not by the elem type, as that is relevant for inference and avoiding ambiguity.
 *)


Class Iterator (it_state : Type) (it_elem : Type) := {
  iterator_next : it_state → it_elem → it_state → Prop;
  iterator_done : it_state → Prop;
  iterator_done_dec x : Decision (iterator_done x);
}.

