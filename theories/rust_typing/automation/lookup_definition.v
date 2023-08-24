(** * Lookup definitions *)
From Ltac2 Require Ltac2.
From iris Require string_ident.
Module StringConstr.
  Import Ltac2 string_ident.

  Local Ltac2 rec make_message (s : (Std.reference) list) := match s with
    | [] => Message.of_string "]"
    | x :: s =>
        let cstr := Env.instantiate x in
        Message.concat (Message.of_constr cstr)
          (Message.concat (Message.of_string "; ") (make_message s))
    end.
  Ltac2 Type exn ::= [ MultipleMatches(message) | NoMatches | NotAConstr ].
  Ltac2 ident_to_constr (s : ident list) :=
    let ref := Env.expand s in
    match ref with
    | msg :: rs =>
        match rs with
        | [] => ()
        | _ =>
          let msg := make_message rs in
          Control.throw (MultipleMatches (Message.concat (Message.of_string "other matches: [") msg))
        end;
        let cstr := Env.instantiate msg in
        Some(cstr)
    | _ => None
    end.

  Ltac2 rec list_string_to_ident (s : constr) : (ident list) := 
    match! s with
    | nil => []
    | cons ?str ?rest =>
        let ident := StringToIdent.coq_string_to_ident str in
        let rest_ident := list_string_to_ident rest in
        ident :: rest_ident
    end.

  Ltac2 coq_string_list_to_constr (s : constr) : constr :=
    let idents := list_string_to_ident s in
    let cstr := ident_to_constr idents in
    match cstr with
    | Some cstr =>
        cstr
    | None =>
        Control.throw NoMatches
    end.

  Ltac2 run_ltac1_with_constr (cont : Ltac1.t) (x : constr) :=
    Ltac1.apply cont ([(Ltac1.of_constr x)])
      (fun (x : Ltac1.t) => Ltac1.run x).
  Ltac2 string_to_ltac1_constr (cont : Ltac1.t) (x : constr) :=
    run_ltac1_with_constr cont (StringConstr.coq_string_list_to_constr x).

  Ltac2 ltac1_constr_to_constr (cont : Ltac1.t) (x : Ltac1.t) :=
    match Ltac1.to_constr x with
    | Some s => string_to_ltac1_constr cont s
    | None => Control.throw NotAConstr
    end.
End StringConstr.

(** Looks up a definition with name [s].
   [cont] is a continuation that will be called with the looked-up term of form [@s]
    (i.e. all arguments are expected to be given explicitly).
   [s] is a constr of [list string] type giving a suffix of the fully qualified path. 

   This will fail if there are multiple possible matches of [s].
 *)
Ltac lookup_definition cont s :=
  let run := ltac2:(s cont |- StringConstr.ltac1_constr_to_constr cont s) in
  run s cont.

(*
Require Import String.
From stdpp Require Import base.
Local Open Scope string_scope.
Goal True.
Proof.
  lookup_definition ltac:(fun x => idtac x) constr:(["list"]).

  (* NOTE: fails due to ambiguity! *)
  (*lookup_definition ltac:(fun x => idtac x) constr:(["concat"]).*)

  lookup_definition ltac:(fun x => idtac x) constr:(["List"; "concat"]).
Abort.
 *)
