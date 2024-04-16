From refinedrust Require Import type.
From iris.prelude Require Import options.

Section fixpoint_def.
  Context `{!typeGS Σ}.

  Context {T_rt : Type} (T : type T_rt → type T_rt) {HT : TypeContractive T}.

  Axiom fixpoint_t : type T_rt.

End fixpoint_def.
