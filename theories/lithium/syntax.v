From lithium Require Export base.
From lithium Require Import definitions hooks.

Import environments.

Module li.
Section lithium.
  Context {Σ : gFunctors}.

  (* Alternative names: prove, assert, consume *)
  Definition exhale (P T : iProp Σ) : iProp Σ :=
    P ∗ T.
  (* Alternative names: intro, assume, produce *)
  Definition inhale (P T : iProp Σ) : iProp Σ :=
    P -∗ T.

  Definition all {A} : (A → iProp Σ) → iProp Σ :=
    bi_forall.
  Definition exist {A} : (A → iProp Σ) → iProp Σ :=
    bi_exist.

  Definition done : iProp Σ := True.
  Definition false : iProp Σ := False.

  Definition and : iProp Σ → iProp Σ → iProp Σ :=
    bi_and.
  Definition and_map {K A} `{!EqDecision K} `{!Countable K}
    (m : gmap K A) (Φ : K → A → iProp Σ) : iProp Σ :=
    big_opM bi_and Φ m.

  Definition find_in_context : ∀ fic : find_in_context_info, (fic.(fic_A) → iProp Σ) → iProp Σ :=
    find_in_context.

  Definition case_if : Prop → iProp Σ → iProp Σ → iProp Σ :=
    case_if.
  Definition case_destruct {A} : A → (A → bool → iProp Σ) → iProp Σ :=
    @case_destruct Σ A.

  Definition drop_spatial : iProp Σ → iProp Σ :=
    bi_intuitionistically.

  Definition tactic {A} : ((A → iProp Σ) → iProp Σ) → (A → iProp Σ) → iProp Σ :=
    @li_tactic Σ A.

  Definition accu : (iProp Σ → iProp Σ) → iProp Σ :=
    accu.

  Definition trace {A} : A → iProp Σ → iProp Σ :=
    @li_trace Σ A.

  Definition subsume : iProp Σ → iProp Σ → iProp Σ → iProp Σ :=
    subsume.
  (* TODO: Should we also have a syntax for subsume list? *)

  Definition ret (T : iProp Σ) : iProp Σ := T.
  Definition iterate [A B] : (B → A → A) → A → list B → A :=
    @foldr A B.

  Definition bind0 (P : iProp Σ → iProp Σ) (T : iProp Σ) : iProp Σ := P T.
  Definition bind1 {A1} (P : (A1 → iProp Σ) → iProp Σ) (T : A1 → iProp Σ) : iProp Σ := P T.
  Definition bind2 {A1 A2} (P : (A1 → A2 → iProp Σ) → iProp Σ) (T : A1 → A2 → iProp Σ) : iProp Σ := P T.
  Definition bind3 {A1 A2 A3} (P : (A1 → A2 → A3 → iProp Σ) → iProp Σ) (T : A1 → A2 → A3 → iProp Σ) : iProp Σ := P T.
  Definition bind4 {A1 A2 A3 A4} (P : (A1 → A2 → A3 → A4 → iProp Σ) → iProp Σ) (T : A1 → A2 → A3 → A4 → iProp Σ) : iProp Σ := P T.
  Definition bind5 {A1 A2 A3 A4 A5} (P : (A1 → A2 → A3 → A4 → A5 → iProp Σ) → iProp Σ) (T : A1 → A2 → A3 → A4 → A5 → iProp Σ) : iProp Σ := P T.
End lithium.
End li.

Declare Scope lithium_scope.
Delimit Scope lithium_scope with LI.
Global Open Scope lithium_scope.

Declare Custom Entry lithium.

(* notation principle: notations that look like an application (e.g.
return or inhale) don't have a colon after the name. More fancy
notations have a colon after the first identifiers (e.g. pattern:).
This might also be necessary to avoid registering keywords.*)
Notation "'[{' e } ]" := e
  (e custom lithium at level 200,
    format "'[hv' [{  '[hv' e ']'  '/' } ] ']'") : lithium_scope.
Notation "{ x }" := x (in custom lithium, x constr).

Notation "'inhale' x" := (li.inhale x) (in custom lithium at level 0, x constr,
                           format "'inhale'  '[' x ']'") : lithium_scope.
Notation "'exhale' x" := (li.exhale x) (in custom lithium at level 0, x constr,
                           format "'exhale'  '[' x ']'") : lithium_scope.

Notation "∀ x .. y , P" := (li.all (λ x, .. (li.all (λ y, P)) ..))
    (in custom lithium at level 100, x binder, y binder, P at level 100, right associativity,
        format "'[' ∀  x  ..  y , ']'  '/' P") : lithium_scope.
Notation "∃ x .. y , P" := (li.exist (λ x, .. (li.exist (λ y, P)) ..))
    (in custom lithium at level 100, x binder, y binder, P at level 100, right associativity,
        format "'[' ∃  x  ..  y , ']'  '/' P") : lithium_scope.

Notation "'done'" := (li.done) (in custom lithium at level 0) : lithium_scope.
Notation "'false'" := (li.false) (in custom lithium at level 0) : lithium_scope.

(* Making this a recursive notation is tricky because it is not clear,
where the and: would end, see
https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Problem.20with.20right.20associative.20recursive.20notation/near/365455519 *)
Notation "'and:' | x | y" := (li.and x y)
   (in custom lithium at level 100, x at level 100, y at level 100,
       format "'[hv' and:  '/' |  '[hv' x ']'  '/' |  '[hv' y  ']' ']'") : lithium_scope.
(* Notation "'and_map:' m | k v , P" := (li.and_map (λ k v, P) m) *)
    (* (in custom lithium at level 100, k binder, v binder, m constr, P at level 100, *)
        (* format "'[hv' 'and_map:'  m  '/' |  k  v ,  '[hv' P ']' ']'") : lithium_scope. *)
Notation "'and_map' x" := (li.and_map x) (in custom lithium at level 0, x constr,
                           format "'and_map'  '[' x ']'") : lithium_scope.

Notation "'find_in_context' x" := (li.find_in_context x) (in custom lithium at level 0, x constr,
                           format "'find_in_context'  '[' x ']'") : lithium_scope.

Notation "'if:' P | G1 | G2" := (li.case_if P G1 G2)
    (in custom lithium at level 100, P constr, G1, G2 at level 100,
        format "'[hv' 'if:'  P  '/' |  '[hv' G1 ']'  '/' |  '[hv' G2 ']' ']'") : lithium_scope.
Notation "'destruct' x" := (li.case_destruct x) (in custom lithium at level 0, x constr,
                           format "'destruct'  '[' x ']'") : lithium_scope.

Notation "'drop_spatial'" := (li.drop_spatial) (in custom lithium at level 0) : lithium_scope.

Notation "'tactic' x" := (li.tactic x) (in custom lithium at level 0, x constr,
                           format "'tactic'  '[' x ']'") : lithium_scope.

Notation "'accu'" := (li.accu) (in custom lithium at level 0) : lithium_scope.

Notation "'trace' x" := (li.trace x) (in custom lithium at level 0, x constr,
                           format "'trace'  '[' x ']'") : lithium_scope.

Notation "x :> y" := (li.subsume x y) (in custom lithium at level 0, x constr, y constr,
                           format "'[' x ']'  :>  '[' y ']'") : lithium_scope.

Notation "'return' x" := (li.ret x) (in custom lithium at level 0, x constr,
                           format "'return'  '[' x ']'") : lithium_scope.
(* TODO: figure out if it makes sense to handle this to liToSyntax *)
Notation "'iterate:' l '{{' x T , P } }" :=
  (λ T, li.iterate (λ x T, P) T l)
    (in custom lithium at level 0, l constr, x binder, T binder, P at level 100,
        format "'[hv  ' 'iterate:'  l  '{{' x  T ,  '/' P } } ']'") : lithium_scope.
Notation "'iterate:' l 'with' a1 '{{' x T x1 , P } }" :=
  (λ T, li.iterate (λ x T x1, P) T l a1)
    (in custom lithium at level 0, l constr, a1 constr, x binder, T binder, x1 binder,
        P at level 100,
        format "'[hv  ' 'iterate:'  l  'with'  a1  '{{' x  T  x1 ,  '/' P } } ']'") : lithium_scope.
Notation "'iterate:' l 'with' a1 , a2 '{{' x T x1 x2 , P } }" :=
  (λ T, li.iterate (λ x T x1 x2, P) T l a1 a2)
    (in custom lithium at level 0, l constr, a1 constr, a2 constr, x binder, T binder,
        x1 binder, x2 binder, P at level 100,
        format "'[hv  ' 'iterate:'  l  'with'  a1 ,  a2  '{{' x  T  x1  x2 ,  '/' P } } ']'") : lithium_scope.
Notation "'iterate:' l 'with' a1 , a2 , a3 '{{' x T x1 x2 x3 , P } }" :=
  (λ T, li.iterate (λ x T x1 x2 x3, P) T l a1 a2 a3)
    (in custom lithium at level 0, l constr, a1 constr, a2 constr, a3 constr, x binder, T binder,
        x1 binder, x2 binder, x3 binder, P at level 100,
        format "'[hv  ' 'iterate:'  l  'with'  a1 ,  a2 ,  a3  '{{' x  T  x1  x2  x3 ,  '/' P } } ']'") : lithium_scope.


Notation "y ; z" := (li.bind0 y z)
  (in custom lithium at level 100, z at level 100,
      format "y ;  '/' z") : lithium_scope.
Notation "x ← y ; z" := (li.bind1 y (λ x : _, z))
  (in custom lithium at level 0, x name, y at level 99, z at level 100,
      format "x  ←  y ;  '/' z") : lithium_scope.
Notation "' x ← y ; z" := (li.bind1 y (λ x : _, z))
  (in custom lithium at level 0, x strict pattern, y at level 99, z at level 100,
      format "' x  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 ← y ; z" := (li.bind2 y (λ x1 x2 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 100, x1 name, x2 name,
      format "x1 ,  x2  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , ' x2 ← y ; z" := (li.bind2 y (λ x1 x2 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 100, x1 name, x2 strict pattern,
      format "x1 ,  ' x2  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 , x3 ← y ; z" := (li.bind3 y (λ x1 x2 x3 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 100, x1 name, x2 name, x3 name,
      format "x1 ,  x2 ,  x3  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 , x3 , x4 ← y ; z" := (li.bind4 y (λ x1 x2 x3 x4 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 100, x1 name, x2 name, x3 name, x4 name,
      format "x1 ,  x2 ,  x3 ,  x4  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 , x3 , x4 , x5 ← y ; z" := (li.bind5 y (λ x1 x2 x3 x4 x5 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 100, x1 name, x2 name, x3 name, x4 name, x5 name,
      format "x1 ,  x2 ,  x3 ,  x4 ,  x5  ←  y ;  '/' z") : lithium_scope.

Notation "P 'where' x1 .. xn ':-' Q" := (∀ x1, .. (∀ xn, Q ⊢ P) ..)
   (at level 99, Q custom lithium at level 100, x1 binder, xn binder, only parsing) : stdpp_scope.
Notation "P ':-' Q" := (Q ⊢ P)
  (at level 99, Q custom lithium at level 100, only parsing) : stdpp_scope.

(* for find_in_context: *)
Notation "'pattern:' x .. y , P ; G" :=
  (li.exist (λ x, .. (li.exist (λ y, li.bind0 (li.exhale P) G)) .. ))
    (in custom lithium at level 100, x binder, y binder, P constr, G at level 100, only parsing) : lithium_scope.

Declare Reduction liFromSyntax_eval :=
  cbv [ li.exhale li.inhale li.all li.exist li.done li.false li.and li.and_map
        li.find_in_context li.case_if li.case_destruct li.drop_spatial li.tactic
        li.accu li.trace li.subsume li.ret li.iterate
        li.bind0 li.bind1 li.bind2 li.bind3 li.bind4 li.bind5 ].

Ltac liFromSyntaxTerm c :=
  eval liFromSyntax_eval in c.

Ltac liFromSyntax :=
  match goal with
  | |- ?P =>
      let Q := liFromSyntaxTerm P in
      change (Q)
  end.

Ltac liFromSyntaxGoal :=
  match goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
      let Q := liFromSyntaxTerm P in
      change (envs_entails Δ Q)
  end.

Notation "'[type_from_syntax' x ]" :=
    ltac:(let t := type of x in let t := liFromSyntaxTerm t in exact t) (only parsing).

Definition liToSyntax_UNFOLD_MARKER {A} (x : A) : A := x.
(* This tactic heurisitically converts the goal to the Lithium syntax.
It is not perfect as it might convert occurences to Lithium syntax
that should stay in Iris syntax, so it should only be used for
debugging and pretty printing.
TODO: Build a proper version using Ltac2, see
https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Controlling.20printing.20of.20patters.20in.20binders/near/363637321
 *)
Ltac liToSyntax :=
  liFromSyntax; (* make sure that we are not adding things twice, especially around user-defined functions *)
  liToSyntax_hook;
  change (bi_sep ?a) with (li.bind0 (li.exhale (liToSyntax_UNFOLD_MARKER a)));
  change (bi_wand ?a) with (li.bind0 (li.inhale (liToSyntax_UNFOLD_MARKER a)));
  change (@bi_forall (iPropI ?Σ) ?A) with (@li.all Σ A);
  change (@bi_exist (iPropI ?Σ) ?A) with (@li.exist Σ A);
  change (@bi_pure (iPropI ?Σ) True) with (@li.done Σ);
  change (@bi_pure (iPropI ?Σ) False) with (@li.false Σ);
  repeat (progress change (big_opM bi_and ?f ?m) with (li.bind2 (li.and_map m) f));
  change (@bi_and (iPropI ?Σ)) with (@li.and Σ);
  change (find_in_context ?a) with (li.bind1 (li.find_in_context a));
  change (@case_if ?Σ ?P) with (@li.case_if Σ P);
  change (@case_destruct ?Σ ?A ?a) with (li.bind2 (@li.case_destruct Σ A a));
  change (@bi_intuitionistically (iPropI ?Σ)) with (li.bind0 (@li.drop_spatial Σ));
  change (li_tactic ?t) with (li.bind1 (li.tactic t));
  change (@accu ?Σ) with (li.bind1 (@li.accu Σ));
  change (@li_trace ?Σ ?A ?t) with (li.bind0 (@li.trace Σ A t));
  change (subsume ?a ?b) with (li.bind0 (li.subsume (liToSyntax_UNFOLD_MARKER a) (liToSyntax_UNFOLD_MARKER b)));
  change (subsume_list ?A ?ig ?l1 ?l2 ?f) with (li.bind0 (subsume_list A ig l1 l2 f));
  (* Try to at least unfold some spurious conversions. *)
  repeat (first [
              progress change (liToSyntax_UNFOLD_MARKER (li.bind0 (@li.exhale ?Σ ?a) ?b))
              with (a ∗ liToSyntax_UNFOLD_MARKER b)%I
            | progress change (liToSyntax_UNFOLD_MARKER (li.bind0 (@li.drop_spatial ?Σ) ?b))
              with (□ liToSyntax_UNFOLD_MARKER b)%I ]);
  change (liToSyntax_UNFOLD_MARKER (@li.done ?Σ)) with (@bi_pure (iPropI Σ) True);
  change (liToSyntax_UNFOLD_MARKER (@li.false ?Σ)) with (@bi_pure (iPropI Σ) False);
  unfold liToSyntax_UNFOLD_MARKER.

Ltac liToSyntaxGoal :=
  iEval ( liToSyntax ).

(* The following looses the printing of patterns and is extremely slow
when going under many binders (e.g. typed_place). *)
(*
Ltac to_li c :=
  lazymatch c with
  | bi_sep ?P ?G =>
      refine (li.bind0 (li.exhale P) _);
      to_li G
  | bi_wand ?P ?G =>
      refine (li.bind0 (li.inhale P) _);
      to_li G
  | @bi_forall _ ?A (fun x => @?G x) =>
      refine (@li.all _ A (λ x, _));
      let y := eval lazy beta in (G x) in
      to_li y
  | @bi_exist _ ?A (fun x => @?G x) =>
      refine (@li.exist _ A (λ x, _));
      let y := eval lazy beta in (G x) in
      to_li y
  | @bi_exist _ ?A (fun x => @?G x) =>
      refine (@li.exist _ A (λ x, _));
      let y := eval lazy beta in (G x) in
      to_li y
  | True%I => refine (li.done)
  | ?P (fun x => @?G x) =>
      (* idtac x; *)
      refine (li.bind1 P (λ x, _));
      let y := eval lazy beta in (G x) in
      (* idtac y; *)
      to_li y
  | match ?x with | (a, b) => @?G a b end =>
      refine (match x with | (a, b) => _ end);
      let y := eval lazy beta in (G a b) in
      (* idtac y;       *)
      to_li y
  | ?G =>
      refine (G)
  end.

Ltac goal_to_li :=
  match goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
      let x := fresh in
      unshelve evar (x : bi_car PROP); [to_li P|];
      change (envs_entails Δ x); unfold x; clear x
  end.
*)

Module li_test.
Section test.

  Context {Σ : gFunctors}.
  Parameter check_wp : ∀ (e : Z) (T : Z → iProp Σ), iProp Σ.
  Parameter get_tuple : ∀ (T : (Z * Z * Z) → iProp Σ), iProp Σ.

  Local Ltac liToSyntax_hook ::=
    change (check_wp ?x) with (li.bind1 (check_wp x));
    change (get_tuple) with (li.bind1 (get_tuple)).

  Lemma ex1_1 :
    ⊢ get_tuple (λ '(x1, x2, x3), ⌜x1 = 0⌝ ∗ subsume False False True).
  Proof.
    iStartProof.
    (* Important: '(...) syntax should be preserved *)
    liToSyntax.
    liFromSyntax.
  Abort.

  Lemma ex1_1 :
    ⊢ [{ '(x1, x2, x3) ← {get_tuple}; exhale ⌜x1 = 0⌝; done }].
  Proof.
    iStartProof.
    liFromSyntax.
  Abort.

  Lemma ex1_3 :
    ⊢ ∀ n1 n2, (⌜n1 + Z.to_nat n2 > 0⌝ ∗ ⌜n2 = 1⌝) -∗
     check_wp (n1 + 1) (λ v,
       ∃ n' : nat, (⌜v = n'⌝ ∗ ⌜n' > 0⌝) ∗ li_trace 1 $ accu (λ P,
       find_in_context (FindDirect (λ '(n, m), ⌜n =@{Z} m⌝)) (λ '(n, m), ⌜n = m⌝ ∗
       get_tuple (λ '(x1, x2, x3), □ ⌜x1 = 0⌝ ∗ (P ∧
         □ [∧ map] a↦'(b1, b2)∈{[1 := (1, 1)]}, ⌜a = b1⌝ ∗
         case_if (n' = 1) (case_destruct n' (λ n'' b,
          ⌜b = b⌝ ∗ ⌜n'' = 0⌝ ∗ subsume True True (True ∗ True ∗ True ∗ True ∗ True ∗ True))) False))))).
  Proof.
    iStartProof.
    liToSyntax.
    liFromSyntax.
  Abort.

  Lemma iterate0 ls :
    ⊢@{iProp Σ} [{ iterate: ls {{x T,
                         exhale ⌜x = 1⌝;
                         return T}};
         exhale ⌜[] = ls⌝;
         done}].
  Proof. Abort.

  Lemma iterate1 (ls : list Z) :
    ⊢@{iProp Σ} [{ a ← iterate: ls with [] {{x T a,
                         exhale ⌜a = []⌝;
                         exhale ⌜a = []⌝;
                         exhale ⌜a = []⌝;
                         return T (a ++ [x])}};
         exhale ⌜a = ls⌝;
         done}].
  Proof. Abort.

  Lemma iterate2 (ls : list Z) :
    ⊢@{iProp Σ} [{ a, b ← iterate: ls with [], [] {{x T a b,
                         exhale ⌜a = b⌝;
                         exhale ⌜a = []⌝;
                         exhale ⌜a = []⌝;
                         return T (a ++ [x]) (b ++ [x])}};
         exhale ⌜a = ls⌝;
         done}].
  Proof. Abort.

  Lemma iterate3 (ls : list Z) :
    ⊢@{iProp Σ} [{ a, b, c ← iterate: ls with [], [], [] {{x T a b c,
                         exhale ⌜a = b⌝;
                         exhale ⌜a = c⌝;
                         exhale ⌜a = []⌝;
                         return T (a ++ [x]) (b ++ [x]) (c ++ [x])}};
         exhale ⌜a = ls⌝;
         exhale ⌜a = b⌝;
         done}].
  Proof. Abort.

End test.
End li_test.
