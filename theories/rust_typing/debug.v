From refinedrust Require Export automation.
Set Default Proof Using "Type".

Ltac hooks.shelve_sidecond_hook ::=
    match goal with
    | |- False => fail 4
    | |- _ => idtac
    end.
