From refinedrust Require Import type programs.
From lithium Require Import hooks all.

(* Initialize the [named_lfts] assertion with external lifetimes.
   Usually called after [start_function].
 *)
Tactic Notation "init_lfts" uconstr(map) :=
  unshelve iPoseProof (named_lfts_init (map : gmap string lft)) as "-#?"; [apply _ .. |].
  (*specialize (tt : LFT_MAP map) as lfts.*)

Tactic Notation "init_tyvars" uconstr(M) :=
  specialize (tt : TYVAR_MAP M) as tyvars.

Definition BLOCK_PRECOND `{!typeGS Σ} (bid : label) (P : iProp Σ) : Set := unit.
Arguments BLOCK_PRECOND : simpl never.

Definition CASE_DISTINCTION_INFO {B} (info : B) (* (i : list location_info) *) : Set := unit.
Arguments CASE_DISTINCTION_INFO : simpl never.

Definition CODE_MARKER (rf : runtime_function) : runtime_function := rf.
Notation "'HIDDEN'" := (CODE_MARKER _) (only printing).
Arguments CODE_MARKER : simpl never.
Ltac unfold_code_marker_and_compute_map_lookup :=
  unfold CODE_MARKER in *;
  match goal with
    | |- f_code (rf_fn ?FN) !! _ = Some _ => unfold rf_fn, f_code, FN
  end;
  compute_map_lookup.

Definition RETURN_MARKER `{!typeGS Σ} (R : @typed_stmt_R_t Σ) : @typed_stmt_R_t Σ := R.
Notation "'HIDDEN'" := (RETURN_MARKER _) (only printing).
(* simplify RETURN_MARKER as soon as it is applied enough in the goal *)
Arguments RETURN_MARKER _ _ /.

(* Function name marker *)
Definition FUNCTION_NAME (s : string) := s.
Arguments FUNCTION_NAME : simpl never.
Notation "'HIDDEN'" := (FUNCTION_NAME _) (only printing).

(** marker for tactics that have already exploited a particular fact *)
Definition NO_ENRICH {A} (a : A) := a.
Global Typeclasses Opaque NO_ENRICH.
Arguments NO_ENRICH : simpl never.
Lemma dont_enrich {A} : A → NO_ENRICH A.
Proof. apply NO_ENRICH. Defined.
Ltac unfold_no_enrich :=
  repeat match goal with
  | H : context[NO_ENRICH ?a] |- _ => unfold NO_ENRICH in H
  end.

(** Sidecondition caching *)

(** Design decisions:
   - How do we represent the cache?

     Should we just have an opaque marker that we unfold?
     => Go with this for now.

     Should we pack stuff into a special list or so?
     + This would be reflected directly in the proof term and not easily go away
     + Might be more efficient for matching when we don't need it.

   - Have tactics for entering things into the cache, for adding the cache to the context, etc.
    invariant: no duplicates in the cache.


 *)
Definition CACHED {A : Type} (a : A) := a.
Global Typeclasses Opaque CACHED.
Arguments CACHED : simpl never.
Notation "'CACHED'" := (CACHED _) (only printing).
Lemma enter_cache {A} : A → CACHED A.
Proof. apply CACHED. Defined.

Ltac open_cache :=
  repeat match goal with
  | H : context[CACHED ?a] |- _ => unfold CACHED in H
  end.


(** Hook to process an assumption [H] before entering it into the cache. *)
Ltac enter_cache_hook H cont :=
  cont H.
Ltac enter_cache H :=
  enter_cache_hook H ltac:(fun Hn => apply enter_cache in Hn).
(** Unsafe version that bypasses the hooks *)
Ltac enter_cache_unsafe H :=
  apply enter_cache in H.

Ltac specialize_cache T :=
  let Hn := fresh in
  specialize T as Hn;
  enter_cache Hn.
Ltac assert_is_not_cached H :=
  lazymatch type of H with
  | CACHED _ => fail
  | _ => idtac
  end.

(** Case distinctions *)
Ltac add_case_distinction_info info :=
  let Hcase := fresh "HCASE" in
  have Hcase := (() : (CASE_DISTINCTION_INFO info))
  (*get_loc_info ltac:(fun icur =>*)
  (*let Hcase := fresh "HCASE" in*)
  (*have Hcase := (() : (CASE_DISTINCTION_INFO hint info icur)))*)
.

(** * Tactics cleaning the proof state *)
Ltac clear_unused_vars :=
  repeat match goal with
         | H1 := FUNCTION_NAME _, H : ?T |- _ =>
           lazymatch T with
           (* Keep cache *)
           | CACHED _ => fail
           (* Keep current location and case distinction info. *)
           (*| CURRENT_LOCATION _ _ => fail*)
           (*| CASE_DISTINCTION_INFO _ _ _ => fail*)
           | _ => idtac
           end;
           let ty := (type of T) in
           match ty with | Type => clear H | Set => clear H end
         end.

Ltac prepare_sideconditions :=
  li_unfold_lets_in_context;
  unfold_instantiated_evars;
  repeat match goal with | H : BLOCK_PRECOND _ _ |- _ => clear H end;
  (* get rid of Q *)
  repeat match goal with | H := CODE_MARKER _ |- _ => clear H end;
  repeat match goal with | H := RETURN_MARKER _ |- _ => clear H end;
  unfold_no_enrich;
  clear_unused_vars.

Ltac solve_goal_prepare_hook ::=
  prepare_sideconditions;
  repeat match goal with | H : CASE_DISTINCTION_INFO _ |- _ =>  clear H end.

(** * Tactics for showing failures to the user *)

(*Ltac print_current_location :=*)
  (*try lazymatch reverse goal with*)
      (*| H : CURRENT_LOCATION ?l ?up_to_date |- _ =>*)
        (*let rec print_loc_info l :=*)
            (*match l with*)
            (*| ?i :: ?l =>*)
              (*lazymatch eval unfold i in i with*)
              (*| LocationInfo ?f ?ls ?cs ?le ?ce =>*)
                (*let f := eval unfold f in f in*)
                (*idtac "Location:" f "[" ls ":" cs "-" le ":" ce "]";*)
                (*print_loc_info l*)
              (*end*)
            (*| [] => idtac "up to date:" up_to_date*)
            (*end in*)
        (*print_loc_info l;*)
        (*clear H*)
      (*end.*)

Ltac print_case_distinction_info :=
  repeat lazymatch reverse goal with
  | H : CASE_DISTINCTION_INFO ?hint ?i (* ?l *) |- _ =>
    lazymatch i with
    | (?a, ?b) => idtac "Case distinction" a "->" b
    | ?a => idtac "Case distinction" a
    end;
    (*
    lazymatch l with
    | ?i :: ?l =>
      lazymatch eval unfold i in i with
      | LocationInfo ?f ?ls ?cs ?le ?ce =>
        let f := eval unfold f in f in
        idtac "at" f "[" ls ":" cs "-" le ":" ce "]"
      end
    | [] => idtac
    end;
     *)
    clear H
  end.

Ltac print_coq_hyps :=
  try match reverse goal with
  | H : ?X |- _ =>
    lazymatch X with
    | BLOCK_PRECOND _ _ => fail
    | gFunctors => fail
    | typeGS _ => fail
    | ghost_varG _ _ => fail
    (*| globalGS _ => fail*)
    | _ => idtac H ":" X; fail
    end
  end.

Ltac print_goal :=
  (*print_current_location;*)
  print_case_distinction_info;
  idtac "Goal:";
  print_coq_hyps;
  idtac "---------------------------------------";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "";
  idtac "".

Ltac print_typesystem_goal fn :=
  lazymatch goal with
  | |- ?P ∧ ?Q =>
    idtac "Cannot instantiate evar in" fn  "!";
    (*print_current_location;*)
    (*print_case_distinction_info;*)
    idtac "Goal:";
    print_coq_hyps;
    idtac "---------------------------------------";
    idtac P;
    (* TODO: Should we print the continuation? It might confuse the user and
       it usually is not helpful. *)
    (* idtac ""; *)
    (* idtac "Continuation:"; *)
    (* idtac Q; *)
    idtac "";
    idtac "";
    admit
  | |- _ =>
    idtac "Type system got stuck in function" fn  "!";
    print_goal; admit
  end.

Ltac print_sidecondition_goal fn :=
  idtac "Cannot solve side condition in function" fn "!";
  print_goal; admit.

Ltac print_remaining_shelved_goal fn :=
  idtac "Shelved goal remaining in " fn "!";
  print_goal; admit.

