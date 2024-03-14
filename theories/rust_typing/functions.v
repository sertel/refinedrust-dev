From refinedrust Require Export type.
From refinedrust Require Import programs uninit.
Set Default Proof Using "Type".
  
(** * Function types *)

(* "entry-point" statement *)
Definition to_runtime_function (fn : function) (lsa lsv : list loc) (lya lyv : list layout) : runtime_function :=
  let rf := subst_function (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1) (val_of_loc <$> (lsa ++ lsv))) fn in
  {| rf_fn := rf; rf_locs := zip lsa lya ++ zip lsv lyv |}.
Definition introduce_typed_stmt {Σ} `{!typeGS Σ} (π : thread_id) (E : elctx) (L : llctx) (ϝ : lft) (fn : function) (lsa lsv : list loc) (lya lyv : list layout) (R : typed_stmt_R_t) : iProp Σ :=
  let rf := to_runtime_function fn lsa lsv lya lyv in
  typed_stmt π E L (Goto fn.(f_init)) rf R ϝ.
Global Typeclasses Opaque to_runtime_function.
Global Typeclasses Opaque introduce_typed_stmt.
Global Arguments introduce_typed_stmt : simpl never.


(* TODO: equip function types with namespace parameters for atomic and non-atomic invariants that need to be active when calling it. *)

Fixpoint prod_vec (A : Type) (n : nat) : Type :=
  match n with
  | 0 => ()%type
  | S n => (prod_vec A n * A)%type
  end.
Fixpoint list_to_tup {A} (l : list A) : prod_vec A (length l) :=
  match l with
  | [] => tt
  | x :: xs => (list_to_tup xs, x)
  end.

Section function.
  (* [A] is the parameter type (i.e., it bundles up all the Coq-level parameters of a function) *)
  (* [n] is the number of lifetime parameters *)
  Context `{!typeGS Σ} {A : Type} {lfts : nat}.
  (* function return type and condition *)
  (* this does not take an rtype, since we essentially pull that part out to
     [fp_rtype] and [fp_fr] below, in order to support existential quantifiers *)
  Record fn_ret := mk_FR {
    fr_rt : Type;
    fr_ty : type fr_rt;
    fr_ref : fr_rt;
    fr_R : thread_id → iProp Σ;
  }.

  Record fn_params := FP {
    (** Argument types with refinement.
      We also directly require an inG proof for ghost variables to that type.
      Maybe there is a nicer way to bundle that up?
    *)
    fp_atys : list (@sigT Type (λ rt, type rt * rt)%type);
    (* bundled assume condition *)
    fp_Pa : thread_id → iProp Σ;
    (* external lifetimes, parameterized over a lifetime for the function *)
    fp_elctx : lft → elctx;
    (* existential condition for return type *)
    fp_extype : Type;
    (* return type *)
    fp_fr: fp_extype → fn_ret;
  }.

  (**
     Compute a [fn_params] definition that includes the required lifetime constraints for the
     used argument and return types (according to their typeclass instances).
     This is currently a bit more restrictive than it needs to be:
     We don't allow [retty] to depend on [exty], since [exty] should not quantify over any lifetimes for this computation to work.
     FIXME Maybe we can generalize this with some more typeclass magic.
   *)
  Definition map_rtype : (@sigT Type (λ rt, type rt * rt)%type) → rtype :=
    (λ '(existT rt (ty, _)), {| rt_rty := rt; rt_ty := ty|}).
  Definition FP_wf
      E
      (atys : list (@sigT Type (λ rt, type rt * rt)%type))
      (pa : thread_id → iProp Σ)
      (exty : Type)
      (retrt : Type)
      (retty : type retrt)
      (fr_ref : exty → retrt)
      (fr_R : exty → thread_id → iProp Σ) :=
    FP
      atys
      pa
      (λ ϝ, E ϝ ++
          tyl_wf_E (map map_rtype atys) ++
          tyl_outlives_E (map map_rtype atys) ϝ ++
          ty_wf_E retty ++
          ty_outlives_E retty ϝ)
      exty
      (λ e, mk_FR retrt retty (fr_ref e) (fr_R e)).


  (* the return continuation for type-checking the body.
    We need to be able to transform ownership of the return type given by [typed_stmt]
      to the type + ensures condition that the function really needs to return *)
  Definition fn_ret_prop {B} π (fr : B → fn_ret) : val → iProp Σ :=
    (λ v,
    (* there exists an inhabitant of the spec-level existential *)
      ∃ x,
      (* st. the return type is satisfied *)
      v ◁ᵥ{π} (fr x).(fr_ref) @ (fr x).(fr_ty) ∗
      (* and the ensures-condition is satisfied *)
      (fr x).(fr_R) π ∗
      (* for Lithium compatibility *)
      True)%I.

  Definition fn_arg_layout_assumptions
      (atys : list (@sigT Type (λ rt, type rt * rt)%type)) (lya : list layout) :=
    Forall2 (λ '(existT rt (ty, _)) ly, syn_type_has_layout ty.(ty_syn_type) ly) atys lya.
  Definition fn_local_layout_assumptions
      (sts : list syn_type) (lyv : list layout) :=
    Forall2 (syn_type_has_layout) sts lyv.

  (** This definition is not yet contractive, and also not a full type.
    We do this below in a separate definition. *)
  Definition typed_function π (fn : function) (local_sts : list syn_type) (fp : prod_vec lft lfts → A → fn_params) : iProp Σ :=
    ( (* for any Coq-level parameters *)
      ∀ κs x,
      (* and any duration of the function call *)
      ∀ (ϝ : lft),
      □ (
      let lya := fn.(f_args).*2 in
      let lyv := fn.(f_local_vars).*2 in
      (* the function arg type layouts match what is given in the function [fn]: this is something we assume here *)
      ⌜fn_arg_layout_assumptions (fp κs x).(fp_atys) lya⌝ -∗
      (* the local var layouts also match the specified syn_types *)
      ⌜fn_local_layout_assumptions local_sts lyv⌝ -∗
      ∀ (* for any stack locations that get picked nondeterministically... *)
          (lsa : vec loc (length (fp κs x).(fp_atys)))
          (lsv : vec loc (length fn.(f_local_vars))),
          (* initial stack *)
          let Qinit :=
            (* initial credits from the beta step *)
            credit_store 0 0 ∗
            (* arg ownership *)
            ([∗list] l;t∈lsa;(fp κs x).(fp_atys), let '(existT rt (ty, r)) := t in l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty)) ∗
            (* local vars ownership *)
            ([∗list] l;p∈lsv;local_sts, (l ◁ₗ[π, Owned false] (PlaceIn ()) @ (◁ (uninit p)))) ∗
            (* precondition *)
            (fp κs x).(fp_Pa) π in
          (* external lifetime context: can require external lifetimes syntactically outlive the function lifetime, as well as syntactic constraints between universal lifetimes *)
          let E := ((fp κs x).(fp_elctx) ϝ) in
          (* local lifetime context: the function needs to be alive *)
          let L := [ϝ ⊑ₗ{0} []] in
          Qinit -∗ introduce_typed_stmt π E L ϝ fn lsa lsv lya lyv (
            λ v L2,
            prove_with_subtype E L2 false ProveDirect (fn_ret_prop π (fp κs x).(fp_fr) v) (λ L3 _ R3,
            introduce_with_hooks E L3 R3 (λ L4,
            (* we don't really kill it here, but just need to find it in the context *)
            li_tactic (llctx_find_llft_goal L4 ϝ LlctxFindLftFull) (λ _,
            find_in_context FindCreditStore (λ _, True)
          )))))
    )%I.

  Global Instance typed_function_persistent π fn local_sts fp : Persistent (typed_function π fn local_sts fp) := _.

  (* TODO: need a notion of equivalence on functions? *)

  (** function pointer type. Requires that the location stores a function that has suitable layouts for the fn_params.
      Note that the fn_params may contain generics: this means that only for particular choices of types to instantiate this,
      this is actually a valid function pointer at the type. This is why we expose the list of argument syn_types in this type.
      The caller will have to show, when calling the function, that the instantiations validate the layout assumptions.
  *)
  Program Definition function_ptr (arg_types : list (syn_type)) (fp : prod_vec lft lfts → A → fn_params) : type loc := {|
    st_own π f v := (∃ fn local_sts, ⌜v = val_of_loc f⌝ ∗ fntbl_entry f fn ∗
      ⌜list_map_option use_layout_alg arg_types = Some fn.(f_args).*2⌝ ∗
      (* for the local variables, we need to pick [local_sts] at linking time (in adequacy, when we run the layout algorithm) *)
      ⌜list_map_option use_layout_alg local_sts = Some fn.(f_local_vars).*2⌝ ∗
      ▷ typed_function π fn local_sts fp)%I;
    st_has_op_type ot mt := is_ptr_ot ot;
    st_syn_type := FnPtrSynType;
  |}.
  Next Obligation.
    simpl. iIntros (fal fp π r v) "(%fn & %local_sts & -> & _)". eauto.
  Qed.
  Next Obligation.
    intros ? ? ot mt Hot. apply is_ptr_ot_layout in Hot. rewrite Hot. done.
  Qed.
  Next Obligation.
    simpl. iIntros (lya fp ot mt st π r v Hot).
    destruct mt.
    - eauto.
    - iIntros "(%fn & %local_sts & -> & Hfntbl & %Halg & Hfn)".
      iExists fn, _. iFrame. iPureIntro. split; last done.
      destruct ot; try done. unfold mem_cast. rewrite val_to_of_loc. done.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%fn & % & -> & _)". eauto.
  Qed.
  Global Instance copyable_function_ptr fal fp : Copyable (function_ptr fal fp) := _.
End function.
Section call.
  Context `{!typeGS Σ}.
  Import EqNotations.

  Lemma type_call_fnptr π E L {A : Type} (lfts : nat) eκs l v vl tys T (fp : prod_vec lft lfts → A → fn_params) sta :
    let eκs' := list_to_tup eκs in
    (([∗ list] v;t ∈ vl; tys, let '(existT rt (ty, r)) := t in v ◁ᵥ{π} r @ ty) -∗
      ∃ (Heq : lfts = length eκs),
      ∃ x,
      let κs := (rew <- Heq in eκs') in
      (* show typing for the function's actual arguments. *)
      prove_with_subtype E L false ProveDirect ([∗ list] v;t ∈ vl; (fp κs x).(fp_atys), let '(existT rt (ty, r)) := t in v ◁ᵥ{π} r @ ty) (λ L1 _ R2,
      R2 -∗
      (* the syntypes of the actual arguments match with the syntypes the function assumes *)
      ⌜sta = map (λ '(existT rt (ty, _)), ty.(ty_syn_type)) (fp κs x).(fp_atys)⌝ ∗
      (* precondition *)
      (* TODO it would be good if we could also stratify.
          However a lot of the subsumption instances relating to values need subsume_full.
          Maybe we should port them to a form of owned_subltype?
          but even the logical step thing is problematic.
        *)
      prove_with_subtype E L1 true ProveDirect ((fp κs x).(fp_Pa) π) (λ L2 _ R3,
      ⌜Forall (lctx_lft_alive E L2) (L2.*1.*2)⌝ ∗
      ⌜∀ ϝ, elctx_sat (((λ '(_, κ, _), ϝ ⊑ₑ κ) <$> L2) ++ E) L2 ((fp κs x).(fp_elctx) ϝ)⌝ ∗
      (* postcondition *)
      ∀ v x', (* v = retval, x' = post existential *)
      (* also donate some credits we are generating here *)
      introduce_with_hooks E L2 (£ (S num_cred) ∗ atime 2 ∗ R3 ∗ ((fp κs x).(fp_fr) x').(fr_R) π) (λ L3,
      T L3 v ((fp κs x).(fp_fr) x').(fr_rt) ((fp κs x).(fp_fr) x').(fr_ty) ((fp κs x).(fp_fr) x').(fr_ref))))
    ) ⊢ typed_call π E L eκs v (v ◁ᵥ{π} l @ function_ptr sta fp) vl tys T.
  Proof.
    simpl. iIntros "HT (%fn & %local_sts & -> & He & %Halg & %Halgl & Hfn) Htys" (Φ) "#CTX #HE HL Hna HΦ".
    iDestruct ("HT" with "Htys") as "(%Heq & %x & HP)". subst lfts.
    set (aκs := list_to_tup eκs).
    iApply fupd_wp. iMod ("HP" with "[] [] CTX HE HL") as "(%L1 & % & %R2 & >(Hvl & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(-> & HT)".
    iMod ("HT" with "[] [] CTX HE HL") as "(%L2 & % & %R3 & Hstep & HL & HT)"; [done.. | ].
    iDestruct ("HT") as "(%Hal & %Hsat & Hr)".
    (* initialize the function's lifetime *)
    set (ϝ' := lft_intersect_list (L2.*1.*2)).
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iApply fupd_wp. iMod (lctx_lft_alive_tok_noend_list with "HE HL") as "(%q & Htok & HL & HL_cl')";
      [done | apply Hal | ].
    iDestruct "CTX" as "#(LFT & TIME & LCTX)".
    iMod (llctx_startlft_extra _ _  _ [] with "LFT LCTX Htok") as "(%ϝ & Hϝ & %Hincl & Hkill)"; [set_solver.. | ].
    iPoseProof (Hsat ϝ with "HL []") as "#HE'".
    { iFrame "HE". iApply big_sepL_intro.
      iIntros "!>" (k [κe1 κe2] Hlook).
      apply elem_of_list_lookup_2 in Hlook. simpl.
      apply elem_of_list_fmap in Hlook as (((i & ?) & κs1) & [= <- <-] & ?).
      iApply lft_incl_trans. { iApply lft_incl_syn_sem. done. }
      iApply lft_intersect_list_elem_of_incl.
      rewrite elem_of_list_fmap. exists (i, κe2). split; first done.
      rewrite elem_of_list_fmap. eexists; split; last done. done.
    }

    simpl.
    iAssert ⌜Forall2 has_layout_val vl fn.(f_args).*2⌝%I as %Hall. {
      iClear "Hfn Hr HL Hstep HL_cl HL_cl' Hϝ Hkill".
      move: Halg. move: (fp_atys (fp aκs x)) => atys Hl.
      iInduction (fn.(f_args)) as [|[? ly]] "IH" forall (vl atys Hl).
      { move: Hl => /=. intros ->%list_map_option_nil_inv_r%map_eq_nil. destruct vl => //=. }
      move: Hl.
      simpl. intros (st & atys' & Ha & ? & ?)%list_map_option_cons_inv_r.
      apply map_eq_cons in Ha as (xa & ? & -> & <- & <-).
      destruct vl => //=. iDestruct "Hvl" as "[Hv Hvl]".
      destruct xa as (rt & (ty & r)).
      iDestruct ("IH" with "[//] He Hna HΦ Hvl") as %?.
      iDestruct (ty_has_layout with "Hv") as "(%ly' & % & %)".
      assert (ly = ly') as ->. { by eapply syn_type_has_layout_inj. }
      iPureIntro. constructor => //.
    }

    iAssert (|={⊤}=> [∗ list] v;t ∈ vl;fp_atys (fp aκs x), let 'existT rt (ty, r) := t in v ◁ᵥ{ π} r @ ty)%I with "[Hvl]" as ">Hvl".
    { rewrite -big_sepL2_fupd. iApply (big_sepL2_mono with "Hvl").
      iIntros (?? (rt & (ty & r)) ??) "Hv". eauto with iFrame. }

    iMod (persistent_time_receipt_0) as "Hp".
    (* eliminate the logical step *)
    iEval (rewrite /logical_step) in "Hstep".
    iMod "Hstep" as "(%n & Hc & Hstep)".
    iApply wp_fupd. iModIntro. iModIntro.
    iApply (wp_call_credits with "TIME Hc Hp He") => //. { by apply val_to_of_loc. }
    iIntros "!>" (lsa lsv Hlya) "Ha Hv Hcred Hc".
    iDestruct (big_sepL2_length with "Ha") as %Hlen1.
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    iDestruct (big_sepL2_length with "Hvl") as %Hlen3.

    (* use the credits we got to get the precondition (for the logical step) *)
    iEval (rewrite lc_succ) in "Hcred". iDestruct "Hcred" as "(Hcred & Hcred0)".
    iEval (rewrite additive_time_receipt_succ) in "Hc". iDestruct "Hc" as "(Hc & Hc0)".
    rewrite !Nat.add_0_r. iMod ("Hstep" with "Hcred0 Hc0") as "(HP & HR)".

    apply list_map_option_alt in Halg. apply list_map_option_alt in Halgl.
    iDestruct ("Hfn" $! aκs x ϝ with "[] []") as "Hfn".
    { iPureIntro. move: Halg. rewrite Forall2_fmap_l => Halg.
      eapply Forall2_impl; first done. intros (rt & ty & r) ly; done. }
    { done. }

    have [lsa' ?]: (∃ (ls : vec loc (length (fp_atys (fp aκs x)))), lsa = ls)
      by rewrite -Hlen3 -Hlen1; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.
    have [lsv' ?]: (∃ (ls : vec loc (length (f_local_vars fn))), lsv = ls)
      by rewrite -Hlen2; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.

    iDestruct ("Hfn" $! lsa' lsv') as "Hm". unfold introduce_typed_stmt.
    set (RET_PROP v := (∃ κs',
        llctx_elt_interp (ϝ ⊑ₗ{ 0} κs') ∗ na_own π shrE ∗
        credit_store 0 0 ∗
        ([∗ list] l0 ∈ (zip lsa' (f_args fn).*2 ++ zip lsv' (f_local_vars fn).*2), l0.1 ↦|l0.2|) ∗
        fn_ret_prop π (fp_fr (fp aκs x)) v)%I).
    iExists RET_PROP. iSplitR "Hr HR HΦ HL HL_cl HL_cl' Hkill" => /=.
    - iMod (persistent_time_receipt_0) as "#Htime".
      iApply wps_fupd.
      iApply ("Hm" with "[-Hϝ Hna] [$LFT $TIME $LCTX] HE' [$Hϝ//] Hna []").
      { iFrame.
        (* we use the certificate + other credit to initialize the new functions credit store *)
        iSplitL "Hcred Hc". { rewrite credit_store_eq /credit_store_def. iFrame. }
        move: Hlen1 Hlya. move: (lsa' : list _) => lsa'' Hlen1 Hly. clear RET_PROP lsa' Hall.
        move: Hlen3 Halg. move: (fp_atys (fp aκs x)) => atys Hlen3 Hl.
        move: Hly Hl. move: (f_args fn) => alys Hly Hl.
        iInduction (vl) as [|v vl] "IH" forall (atys lsa'' alys Hlen1 Hly Hlen3 Hl).
        { destruct atys, lsa'' => //. iSplitR => //.
          iPoseProof (big_sepL2_fmap_r (λ x, x.2) (λ _ l v, l ↦|v|)%I with "Hv") as "Hv".
          move: Halgl. rewrite Forall2_fmap_r => Halgl.
          assert ((f_local_vars fn).*2 = use_layout_alg' <$> local_sts) as Heq.
          { clear -Halgl. move: Halgl. generalize (f_local_vars fn) => l.
            induction local_sts as [ | ?? IH] in l |-*; inversion 1; first done.
            simplify_eq/=. f_equiv. { rewrite /use_layout_alg'.
              match goal with | H : use_layout_alg _ = Some _ |- _ => rewrite H end. done. }
            by apply IH. }
          rewrite Heq. rewrite big_sepL2_fmap_r.
          iApply (big_sepL2_wand with "Hv").
          iApply big_sepL2_intro. { rewrite Hlen2. apply Forall2_length in Halgl. done. }
          iIntros "!>" (?? st ? Hlook) => /=. iDestruct 1 as (? Hly') "[%Hly'' Hl]".
          rewrite ltype_own_ofty_unfold /lty_of_ty_own. simpl.
          eapply (Forall2_lookup_l _ _ _ k) in Halgl as (ly & ? & Halg_st); last done.
          simpl in Halg_st. rewrite /use_layout_alg' Halg_st in Hly'. rewrite /use_layout_alg' Halg_st in Hly''.
          iExists _. iSplitR; first done.
          iSplitR; first done. iSplitR; first done.
          iPoseProof (heap_mapsto_loc_in_bounds with "Hl") as "#Hlb".
          rewrite Hly'. iFrame "Hlb". iSplitR; first done.
          iExists _. iSplitR; first done. iModIntro. iExists _. iFrame.
          rewrite uninit_own_spec.
          iExists _. done. }
        destruct atys, lsa'' => //.
        move: Hl. simpl. intros (ly & ? & ? & ? & Ha)%Forall2_cons_inv_l.
        apply map_eq_cons in Ha as ([? ly'] & ? & -> & <- & <-).
        csimpl in *; simplify_eq.
        move: Hly => /(Forall2_cons _ _ _ _)[Hly ?].
        (*apply bind_Some in Hlya as (lys & Hlya & (ly & Halg & [= <- <-])%bind_Some).*)
        iDestruct "Hvl" as "[Hvl ?]".
        iDestruct "Ha" as "[Ha ?]".
        rewrite -bi.sep_assoc. iSplitL "Hvl Ha".
        { destruct s as (rt & (ty & r)).
          rewrite ltype_own_ofty_unfold /lty_of_ty_own.
          iDestruct (ty_has_layout with "Hvl") as "(%ly & % & %Hlyv)".
          assert (ly = ly') as <-. { by eapply syn_type_has_layout_inj. }
          iExists _. iSplitR; first done. iSplitR; first done.
          iPoseProof (ty_own_val_sidecond with "Hvl") as "#$".
          iPoseProof (heap_mapsto_loc_in_bounds with "Ha") as "#Hlb".
          rewrite Hlyv. iSplitR; first done. iSplitR; first done.
          iExists _. iSplitR; first done. iNext. eauto with iFrame. }
        iApply ("IH" with "[//] [//] [//] [//] [$] [$] [$]").
      }
      iIntros (L5 v) "HL Hna Hloc HT".
      iMod ("HT" with "[] [] [] HE' HL") as "(%L3 & %κs1 & %R4 & Hp & HL & HT)"; [done.. |  | ].
      { rewrite /rrust_ctx. iFrame "#". }
      iMod "Hp" as "(Hret & HR)".
      iMod ("HT" with "[] HE' HL HR") as "(%L6 & HL & HT)"; first done.
      rewrite /llctx_find_llft_goal.
      iDestruct "HT" as "(%HL6 & %κs' & %Hfind & HT)".
      destruct Hfind as (L9 & L10 & ? & -> & -> & Hoc).
      unfold llctx_find_lft_key_interp in Hoc. subst.
      iDestruct "HL" as "(_ & Hϝ & _)".
      iDestruct "HT" as ([n' m']) "(Hstore & _)"; simpl.

      subst RET_PROP; simpl.
      iExists _. iFrame.
      iApply (credit_store_mono with "Hstore"); lia.
    - (* handle the postcondition at return *)
      iMod (persistent_time_receipt_0) as "Hpt".
      iIntros "!>" (v). iDestruct 1 as (κs') "(Hϝ & Hna & Hstore & Hls & HPr)".
      iPoseProof (credit_store_borrow with "Hstore") as "(Hcred1 & Hat & _)".
      iExists 1, 0. iFrame.
      simpl. rewrite !big_sepL2_alt. iDestruct (big_sepL_app with "Hls") as "[? ?]".
      rewrite !zip_fmap_r !big_sepL_fmap. iFrame.

      iSplitR. { iPureIntro. apply Forall2_length in Halg.
        rewrite map_length in Halg. rewrite Hlen1 Hlen3 Halg fmap_length. done. }
      iSplitR; first done.
      iIntros "Hcred Hat".
      iPoseProof ("Hkill" with "Hϝ") as "(Htok & Hkill)".
      iMod ("HL_cl'" with "Htok HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
       (*we currently don't actually kill the lifetime, as we don't conceptually need that. *)
      iDestruct ("HPr") as (?) "(Hty & HR2 & _)".
      iMod ("Hr" with "[] HE HL [Hat Hcred HR2 HR]") as "(%L3 & HL & Hr)"; first done.
      { iFrame. }
      iApply ("HΦ" with "HL Hna Hty").
      by iApply ("Hr").
  Qed.
  Global Instance type_call_fnptr_inst π E L {A} (lfts : nat) eκs l v vl fp lya tys :
    TypedCall π E L eκs  v (v ◁ᵥ{π} l @ function_ptr lya fp) vl tys :=
    λ T, i2p (type_call_fnptr π E L (A := A)lfts eκs l v vl tys T fp lya).
End call.

Global Typeclasses Opaque function_ptr.
Global Typeclasses Opaque typed_function.
Arguments fn_ret_prop _ _ _ /.

(* In principle we'd like a notation along these lines, but the recursive pattern for the parameter list isn't supported by Coq. *)

(*
Notation "'fn(∀' x ':' A ',' E ';' r1 '@' T1 ',' .. ',' rN '@' TN ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun x => FP_wf E (@cons type (existT T1%I (r1, _)) .. (@cons type (existT TN%I (rN, _)) (@nil type)) ..) Pa%I B rty (λ y, r%I) (λ y, Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern) : stdpp_scope.
 *)

(* For now, we just define notations for a limited number of arguments (currently up to 6) *)
(* FIXME: proper printing *)
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@nil _) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' r1 '@' T1 ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@cons (@sigT Type _) (existT _ (T1, r1)) (@nil _)) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' r1 '@' T1 ',' r2 '@' T2 ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@cons _ (existT _ (T1, r1)) $ @cons _ (existT _ (T2, r2)) $ (@nil _)) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' r1 '@' T1 ',' r2 '@' T2 ',' r3 '@' T3 ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@cons _ (existT _ (T1, r1)) $ @cons _ (existT _ (T2, r2)) $ @cons _ (existT _ (T3, r3)) $ (@nil _)) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' r1 '@' T1 ',' r2 '@' T2 ',' r3 '@' T3 ',' r4 '@' T4 ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@cons _ (existT _ (T1, r1)) $ @cons _ (existT _ (T2, r2)) $ @cons _ (existT _ (T3, r3)) $ @cons _ (existT _ (T4, r4)) $ (@nil _)) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' r1 '@' T1 ',' r2 '@' T2 ',' r3 '@' T3 ',' r4 '@' T4 ';' r5 '@' T5 ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@cons _ (existT _ (T1, r1)) $ @cons _ (existT _ (T2, r2)) $ @cons _ (existT _ (T3, r3)) $ @cons _ (existT _ (T4, r4)) $ @cons _ (existT _ (T5, r5)) $ (@nil _)) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs : n '|' x ':' A ',' E ';' r1 '@' T1 ',' r2 '@' T2 ',' r3 '@' T3 ',' r4 '@' T4 ';' r5 '@' T5 ';' r6 '@' T6 ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs x => FP_wf E (@cons _ (existT _ (T1, r1)) $ @cons _ (existT _ (T2, r2)) $ @cons _ (existT _ (T3, r3)) $ @cons _ (existT _ (T4, r4)) $ @cons _ (existT _ (T5, r5)) $ @cons _ (existT _ (T6, r6)) $ (@nil _)) Pa%I B _ rty (λ y, r%I) (λ y, Pr%I)) : prod_vec lft n → A → fn_params)
  (at level 99, Pr at level 200, κs pattern, x pattern, y pattern) : stdpp_scope.

Module test.
Definition bla0 `{typeGS Σ} :=
  (fn(∀ ((), κ', κ) : 2 | (x) : unit, (λ f, [(κ', κ)]); (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; λ π, ⌜ (4 > y)%Z⌝).
Definition bla1 `{typeGS Σ} :=
  (fn(∀ (()) : 0 | x : unit, (λ _, []); () @ (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).
Definition bla2 `{typeGS Σ} :=
  (fn(∀ () : 0 | x : unit, (λ _, []); () @ (uninit PtrSynType), () @ (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).
End test.
