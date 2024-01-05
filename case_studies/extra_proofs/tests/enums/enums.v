From refinedrust Require Import typing.

Inductive sizes :=
 | Sz1
 | Sz2.

Global Instance sizes_inhabited : Inhabited sizes := populate Sz1.

Inductive result T U :=
| Ok (x : T)
| Err (x : U).
Arguments Ok {_ _}.
Arguments Err {_ _}.

Global Instance result_inhabited T U :
  Inhabited T →
  Inhabited (result T U).
Proof.
  intros ?. exact (populate (Ok inhabitant)).
Qed.
