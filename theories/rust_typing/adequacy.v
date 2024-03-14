From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From iris.base_logic.lib Require Import ghost_map.
From caesium Require Import ghost_state.
From refinedrust Require Export type.
From refinedrust Require Import programs functions products.
From iris.program_logic Require Export language. (* must be last to get the correct nsteps *)
Set Default Proof Using "Type".

(** * RefinedRust's adequacy proof *)

Class typePreG Σ := PreTypeG {
  type_invG                      :: invGpreS Σ;
  type_na_invG                   :: na_invG Σ;
  type_lftG                      :: lftGpreS Σ;
  type_frac_borrowG              :: frac_borG Σ;
  type_lctxG                     :: lctxGPreS Σ;
  type_ghost_varG                :: ghost_varG Σ RT;
  type_pinnedBorG                :: pinnedBorG Σ;
  type_timeG                     :: timeGpreS Σ;
  type_heap_heap_inG             :: inG Σ (authR heapUR);
  type_heap_alloc_meta_map_inG   :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  type_heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  type_heap_fntbl_inG            :: ghost_mapG Σ addr function;
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
    na_invΣ;
    lftΣ;
    GFunctor (constRF fracR);
    lctxΣ;
    ghost_varΣ RT;
    pinnedBorΣ;
    timeΣ;
    GFunctor (constRF (authR heapUR));
    ghost_mapΣ alloc_id (Z * nat * alloc_kind);
    ghost_mapΣ alloc_id bool;
    ghost_mapΣ addr function].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Definition initial_prog (main : loc) : runtime_expr :=
  coerce_rtexpr (Call main []).

Definition initial_heap_state :=
  {| hs_heap := ∅; hs_allocs := ∅; |}.

Definition initial_state (fns : gmap addr function) :=
  {| st_heap := initial_heap_state; st_fntbl := fns; |}.

Definition main_type `{!typeGS Σ} (P : iProp Σ) :=
  fn(∀ () : 0 | () : (), λ ϝ, []; λ π, P) → ∃ () : (), () @ unit_t; λ π, True.

(** * The main adequacy lemma *)
Lemma refinedrust_adequacy Σ `{!typePreG Σ} `{ALG : LayoutAlg} (thread_mains : list loc) (fns : gmap addr function) n t2 σ2 obs σ:
  σ = {| st_heap := initial_heap_state; st_fntbl := fns; |} →
  (* show that the main functions for the individual threads are well-typed for a provable precondition [P] *)
  (∀ {HtypeG : typeGS Σ},
    ([∗ map] k↦qs∈fns, fntbl_entry (fn_loc k) qs) ={⊤}=∗
      [∗ list] main ∈ thread_mains, ∀ π, ∃ P, main ◁ᵥ{π} main @ function_ptr [] (main_type P) ∗ P) →
  (* if the whole thread pool steps for [n] steps *)
  nsteps (Λ := c_lang) n (initial_prog <$> thread_mains, σ) obs (t2, σ2) →
  (* then it has not gotten stuck *)
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => -> Hwp. apply: wp_strong_adequacy. move => ?.
  (* heap/Caesium stuff *)
  set h := to_heapUR ∅.
  iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  iMod (ghost_map_alloc fns) as (γf) "[Hf Hfm]".
  iMod (ghost_map_alloc_empty (V:=(Z * nat * alloc_kind))) as (γr) "Hr".
  iMod (ghost_map_alloc_empty (V:=bool)) as (γs) "Hs".
  set (HheapG := HeapG _ _ γh _ γr _ γs _ γf).

  (* time credits *)
  iMod (time_init) as "(%Htime & #TIME & Htime)"; first done.
  iMod (own_alloc (i:=(@time_nat_inG Σ Htime)) (● 0 ⋅ ◯ 0)) as (γdis) "[Hdis _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  set (HrefinedCG := RefinedCG _ _ HheapG Htime γdis).
  iMod (additive_time_receipt_0) as "Hat".

  (* lifetime logic stuff *)
  iMod (lft_init _ lft_userE) as "(%Hlft & #LFT)"; [solve_ndisj.. | ].
  iMod (lctx_init) as "(%Hlctx & #LCTX & _)"; [solve_ndisj.. | ].

  set (HtypeG := TypeG _ HrefinedCG Hlft _ _ Hlctx _ _ ALG).
  move: (Hwp HtypeG) => {Hwp}.
  move => Hwp.
  iAssert (|==> [∗ map] k↦qs ∈ fns, fntbl_entry (fn_loc k) qs)%I with "[Hfm]" as ">Hfm". {
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Hfm").
    iIntros "!>" (???) "Hm". rewrite fntbl_entry_eq.
    iExists _. iSplitR; [done|]. by iApply ghost_map_elem_persist.
  }
  iMod (Hwp with "Hfm") as "Hmains".

  iModIntro. iExists _, (replicate (length thread_mains) (λ _, True%I)), _, _.
  iSplitL "Hh Hf Hr Hs Htime Hdis Hat"; last first. 1: iSplitL "Hmains".
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_r; [done|]. iApply (big_sepL_impl with "Hmains").
    iIntros "!#" (? main ?) "Hfn".
    iMod (na_alloc) as "(%π & Hna)".
    iDestruct ("Hfn" $! π) as (P) "[Hmain HP]".
    rewrite /initial_prog.
    iApply (type_call_fnptr π [] [] 0 [] main main [] [] (λ _ _ _ _ _, True%I) (main_type P) [] with "[HP ] Hmain [] [] [] [] [Hna]").
    + iIntros "_". iExists eq_refl, tt.
      iIntros (???) "#CTX #HE HL".
      iModIntro. iExists [], [], True%I.
      iFrame. iSplitR.
      { iApply maybe_logical_step_intro. simpl. eauto. }
      iIntros "_". simpl. iR.
      iIntros (???) "_ _ HL". iModIntro.
      iExists [], [], True%I. iFrame.
      iSplitL "HP". { iApply maybe_logical_step_intro. eauto. }
      simpl. iSplitR. { iPureIntro. by apply Forall_nil. }
      iSplitR. { iPureIntro. intros. apply elctx_sat_nil. }
      iIntros (v []).
      iIntros (??) "_ HL _". eauto with iFrame.
    + by iApply big_sepL2_nil.
    + rewrite /rrust_ctx. iFrame "#".
    + by iApply big_sepL_nil.
    + by iApply big_sepL_nil.
    + iPoseProof (na_own_acc (↑shrN) with "Hna") as "(Hna &_)"; first set_solver. iFrame.
    + iIntros (?????) "HL Hv _". done.
  - iFrame. iIntros (?? _ _ ?) "_ _ _". iApply fupd_mask_intro_discard => //. iPureIntro. by eauto.
  - iFrame.
    rewrite /heap_state_ctx /alloc_meta_ctx /to_alloc_meta_map /alloc_alive_ctx /to_alloc_alive_map.
    iFrame. iR. iExists 0. iFrame.
Qed.

(*Print Assumptions refinedrust_adequacy.*)

(* clients of this:
    - create a function map with monomorphized entries of all the functions they need
        -> this we need to know upfront.
    - from the fntbl_entry we get, build the function_ptr types.
        we use Löb induction as part of that (have a later in the function_ptr type to enable that)
          the induction assumes that we already have fn_ptrs for all the functions we build, at the types that they should have.


  clients of this may also instantiate it with concrete layouts, if they can provide a layout algorithm that computes them.
 *)



(** * Helper functions for using the adequacy lemma *)
Definition fn_lists_to_fns (addrs : list addr) (fns : list function) : gmap addr function :=
  list_to_map (zip addrs fns).

Lemma fn_lists_to_fns_cons `{!refinedcG Σ} addr fn addrs fns :
  length addrs = length fns →
  addr ∉ addrs →
  ([∗ map] k↦qs ∈ fn_lists_to_fns (addr :: addrs) (fn :: fns), fntbl_entry (fn_loc k) qs) -∗
  fntbl_entry (ProvFnPtr, addr) fn ∗ ([∗ map] k↦qs ∈ fn_lists_to_fns addrs fns, fntbl_entry (fn_loc k) qs).
Proof.
  move => Hnotin ?.
  rewrite /fn_lists_to_fns /= big_sepM_insert //; auto.
  apply not_elem_of_list_to_map_1. rewrite fst_zip => //; lia.
Qed.

(** * Tactics for solving conditions in an adequacy proof *)

Ltac adequacy_intro_parameter :=
  repeat lazymatch goal with
         | |- ∀ _ : (), _ => case
         | |- ∀ _ : (_ * _), _ => case
         | |- ∀ _ : _, _ => move => ?
         end.

(*
Ltac adequacy_unfold_equiv :=
  lazymatch goal with
  | |- type_fixpoint _ _ ≡ type_fixpoint _ _ => apply: type_fixpoint_proper; [|move => ??]
  | |- ty_own_val _ _ ≡ ty_own_val _ _ => unfold ty_own_val => /=
  | |-  _ =@{struct_layout} _ => apply: struct_layout_eq
  end.

Ltac adequacy_solve_equiv unfold_tac :=
  first [ eassumption | fast_reflexivity | unfold_type_equiv | adequacy_unfold_equiv | f_contractive | f_equiv' | reflexivity | progress unfold_tac ].

Ltac adequacy_solve_typed_function lemma unfold_tac :=
  iApply typed_function_equiv; [
    done |
    adequacy_intro_parameter => /=; repeat (constructor; [done|]); by constructor |
    | iApply lemma => //; iExists _; repeat iSplit => //];
    adequacy_intro_parameter => /=; eexists eq_refl => /=; split_and!; [..|adequacy_intro_parameter => /=; split_and!];  repeat adequacy_solve_equiv unfold_tac.
 *)
