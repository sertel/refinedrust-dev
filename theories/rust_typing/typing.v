From refinedrust Require Export static type program_rules int int_rules products references functions uninit box programs enum maybe_uninit alias_ptr existentials arrays value generics.
From refinedrust Require Export automation.loc_eq manual automation.

Global Open Scope Z_scope.

Notation Obs := gvar_pobs.

(** Bundle for all ghost state we need *)
Class refinedrustGS Σ := {
  refinedrust_typeGS :: typeGS Σ;
  refinedrust_staticGS :: staticGS Σ;
}.

Ltac instantiate_benign_universals term ::=
  lazymatch type of term with
  | ∀ (_ : gFunctors) (_ : refinedrustGS _), _ =>
      instantiate_benign_universals uconstr:(term _ _)
  | ∀ _ : typeGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | ∀ _ : staticGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | ∀ _ : refinedrustGS _, _ =>  
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | _ =>
      constr:(term)
  end.
