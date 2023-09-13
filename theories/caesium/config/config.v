From caesium.config Require Import selected_config.

(** Compile time configuration for Caesium.

NOTE: Do not modify selected_config.v! Instead modify the original
configuration file and then use the Makefile to set the desired
configuration. *)

Module Type config_sig.
  (** Should Caesium check that all pointers are well-aligned? *)
  Parameter enforce_alignment : bool.

  Axiom enforce_alignment_value : enforce_alignment = selected_config.enforce_alignment.
End config_sig.

Module caesium_config : config_sig.
  Definition enforce_alignment : bool := selected_config.enforce_alignment.
  Lemma enforce_alignment_value : enforce_alignment = selected_config.enforce_alignment.
  Proof. reflexivity. Qed.
End caesium_config.

Class CaesiumConfigEnforceAlignment : Prop :=
  caesium_config_enforce_alignment : caesium_config.enforce_alignment = true.

Global Hint Extern 0 (CaesiumConfigEnforceAlignment) =>
   (exact caesium_config.enforce_alignment_value) : typeclass_instances.
