From refinedrust Require Import typing.

Class Steppable (A : Type) := {
  steppable_add : A → nat → option A;
  steppable_sub : A → nat → option A;
  steppable_interval : A → A → option nat;
}.

#[export]
Instance steppable_Z : Steppable Z := {|
  steppable_add a s := Some (a + s);
  steppable_sub a s := Some (a - s);
  steppable_interval a b := if bool_decide (b - a >= 0)%Z then Some (Z.to_nat (b - a)) else None;
|}.
