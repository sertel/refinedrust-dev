(* TODO: something breaks with the lft logic notations as soon as we import this *)
(*From refinedc.lang Require Import rust.*)
From iris.bi Require Export fractional.
From refinedrust Require Export base.
From refinedrust Require Export ghost_var_dfrac.


(*
Section retraction.
  Context {X Y : Type}.
  Record retraction (f : X → Y) (g : Y → option X) := {
    retraction_left_inv : ∀ x, g (f x) = Some x;
    retraction_right_inv : ∀ y x, g y = Some x → f x = y;
  }.

  (* TODO: lemmas about this *)
End retraction.
Arguments retraction_left_inv { _ _ _ _ }.
Arguments retraction_right_inv { _ _ _ _ }.

(** Closed-world refinement *)
Section rfn.
  Context (RT : Type).

  Class RTInj (C : Type → Type) := {
    RTInj_into : C RT → RT;
    RTInj_match : RT → option (C RT);
    RTInj_retraction : retraction RTInj_into RTInj_match;
  }.

  Global Instance RTInj_inj `{RTInj C} : Inj (=) (=) (RTInj_into).
  Proof.
    intros a b Heq. specialize (retraction_left_inv RTInj_retraction a). rewrite Heq.  
    rewrite (retraction_left_inv RTInj_retraction). intros [= <-]; done.
  Qed.
End rfn.
Global Arguments RTInj_into {_ _ _}.
Global Arguments RTInj_match {_ _ _}. 

Section test.
  Context {RT} 
    `{RTInj RT (const Z)}
    `{RTInj RT list}
  .

  Definition Z_rt : RT := RTInj_into 5%Z.
  Definition list_rt : RT := RTInj_into [RTInj_into 42%Z; Z_rt].

  Definition match_list (x : RT) := 
    if RTInj_match (C := list) x is Some xs then 
      if RTInj_match (C := const Z) (hd (RTInj_into 0%Z) xs) is Some 42%Z then true else false
      else false.

  Eval hnf in (match_list list_rt).



  (* Of course, this doesn't simplify, and simplification/matching is needed a lot in the typing rules. *)
  (* Q is: can I hide that sufficiently in the typing rules, so that it doesn't actually happen? 
      Ideally, the interface would remain very much the same as it is now. 


     In principle: Since everything is anyways indexed, I could just do the injection only at the ghost-variable uses. 
      At all other places, just keep it as it is now. This should be relatively easy to encapsulate while not complicating the typing rules much.
     We might even be able to completely encapsulate that in the ghostvar assertions.
      - for that, RTInj needs to be able to compose constructors structurally... that seems hard. 
        currently, we'd need to insert the injections everywhere manually at every nesting point. 
        



      Point: I need to somehow compose these injections. That seems difficult. 

      e.g. for mutable refs. I need to know that I can inject the refinement type of the nested thing, and that I have the suitable constructor available.
      How do I do that? For the nested thing, would assume RTInj (const rt). 
      That is hard to demonstrate. 
   *)


  (* Otherwise, we could either:
    - use a lot of symbolic reasoning to do these things. That's not so nice, tbh. 
    - define one instantiation statically when we do the typechecking so it can compute, instead of defining it just for adequacy. 
        We can still keep the whole type system generic over it, but when we actually want to verify programs, we instantiate a global typeclass to declare the refinement type.
        Of course, Q: how to verify libraries generically. Verifying libraries is a pretty big point for us, esp. around generics.
          Point: in the generic code, the generic refinement is a leaf that doesn't need any interaction computation. 
          It's fine if there is a `RTInj_into r` that doesn't simplify or so. 
              Might I need RTInj_match (RTInj_into r) and simplify that? I think not, since all my typing rules that want to match will fall into the "type is opaque" case, so I can't simplify anyways and won't even try to do that.   
        Caveat that remains: I need to reinstantiate the type everytime.

        Can I define the type with an "extension point"?
            I want to take the union of some types without loosing computationality.
        

        
        
   *)


  (* Or just do refinements where we treat the injections as purely symbolic, i.e. everywhere in the typing rules we also have the injections.
    Essentially, the injections would be at similar palces as the place_rfn, since that is how we are able to nest them? 


    ltypes are refined by place_rfn RT.
    Ghost variables will store an RT.
      
    mut_ref.own_val κ v (r: RT, γ) :=
       gvar_obs γ r ∗ 
       &pin κ ( ∃ r', gvar_auth γ r' ∗ ∃ r'' : rt, RT_match r' = Some r'' ∗ inner.own ... )

    then get gvar_obs γ r, without the knowledge that it actually is something of the right type. but maybe that is fine.

    mut_lty_own κ l (r : place_rfn (RT * gname)) (Owned wl) := 
      ∃ r', rfn_interp_owned r r' ∗ 
      

     
    
   *)

End test. 
   *)

Section sigma.
  Record RT : Type := RT_into {
    RT_rt : Type; 
    RT_r : RT_rt;
    }.
  Global Arguments RT_into {_}.

  Import EqNotations.
  Lemma RT_rt_eq (x y : RT) : 
    x = y → RT_rt x = RT_rt y.
  Proof.
    inversion 1. done.
  Qed.
  Lemma RT_r_eq (x y : RT) (Heq : x = y) :
    rew Heq in RT_r x = RT_r y.
  Proof.
    inversion Heq. subst. done.
  Qed.

  Lemma RT_into_inj T (x y : T) :
    RT_into x = RT_into y → x = y.
  Proof.
    revert x y.
    enough (∀ a b : RT, a = b → ∀ Heq' : RT_rt a = RT_rt b, rew [id] Heq' in RT_r a = RT_r b) as H.
    { intros x y Heq. by specialize (H _ _ Heq eq_refl). }
    intros a b Heq. destruct Heq. intros Heq.
    specialize (UIP_t _ _ _ Heq eq_refl) as ->. done.
  Qed.

End sigma.

(* NOTE: In principle, I'd like to keep the refinements themselves as-is. Just for the ghost variables, I want to pack stuff up. Maybe the bundling into the sigma types is a good way to achieve that. 
    Potentially, that even works as a general abstraction in the gvar interface.
  *)
Section ghost_variables.
  Context `{ghost_varG Σ RT} {T : Type}.
  Implicit Types (γ : gname) (t : T).

  Definition gvar_auth γ t := ghost_var γ (DfracOwn (1/2)) (RT_into t).
  Definition gvar_obs γ t := ghost_var γ (DfracOwn (1/2)) (RT_into t).
  Definition gvar_pobs γ t := ghost_var γ DfracDiscarded (RT_into t).

  Global Instance gvar_pobs_persistent γ t : Persistent (gvar_pobs γ t).
  Proof. apply _. Qed.

  Lemma gvar_alloc t :
    ⊢ |==> ∃ γ, gvar_auth γ t ∗ gvar_obs γ t.
  Proof.
    iMod (ghost_var_alloc (RT_into t)) as "(%γ & (? & ?))".
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma gvar_update {γ t1 t2} t :
    gvar_auth γ t1 -∗ gvar_obs γ t2 ==∗ gvar_auth γ t ∗ gvar_obs γ t.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma gvar_obs_persist γ t :
    gvar_obs γ t ==∗ gvar_pobs γ t.
  Proof. iApply ghost_var_discard. Qed.

  Lemma gvar_agree γ t1 t2:
    gvar_auth γ t1 -∗ gvar_obs γ t2 -∗ ⌜t1 = t2⌝.
  Proof. 
    iIntros "H1 H2". 
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.

  Lemma gvar_pobs_agree γ t1 t2:
    gvar_auth γ t1 -∗ gvar_pobs γ t2 -∗ ⌜t1 = t2⌝.
  Proof. 
    iIntros "H1 H2". 
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.

  Definition Rel2 (γ1 γ2 : gname) (R : T → T → Prop) : iProp Σ :=
    ∃ v1 v2, gvar_auth γ1 v1 ∗ gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.

  Lemma Rel2_use_pobs γ1 γ2 R v1 :
    gvar_pobs γ1 v1 -∗ Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iPoseProof (gvar_pobs_agree with "Hauth1 Hobs1") as "->".
    eauto with iFrame.
  Qed.

  Lemma Rel2_use_obs γ1 γ2 R v1 :
    gvar_obs γ1 v1 -∗ Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2 ∗ gvar_obs γ1 v1 ∗ gvar_auth γ1 v1 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iDestruct (gvar_agree with "Hauth1 Hobs1") as %->.
    eauto with iFrame.
  Qed.

  Lemma Rel2_use_trivial γ1 γ2 R :
    Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2.
  Proof.
    iIntros "(%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    eauto with iFrame.
  Qed.

  Global Instance Rel2_timeless γ1 γ2 R : Timeless (Rel2 γ1 γ2 R).
  Proof. apply _. Qed.

  (* TODO: define Rel, etc. *)
End ghost_variables.
