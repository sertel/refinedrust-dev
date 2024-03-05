From refinedrust Require Export automation.
Set Default Proof Using "Type".

(** * File to import for debugging sidecondition solving *)

Ltac hooks.shelve_sidecond_hook ::=
    match goal with
    | |- False => fail 4
    | |- _ => idtac
    end.
