From refinedrust.automation Require Import solvers.

(** Instead of finding good names, just keep the autogenerated name. *)
Ltac rename_layouts_core H cont :=
  cont H.
