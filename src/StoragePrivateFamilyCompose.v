Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import PrivateStorageValidator.
Require Import StateObservation.

(** Composition witness for generic private-storage transformations.

    This is the storage-expansion/privatization core below the CInstr-specific
    scalar wrapper.  The private-storage family carries local use-def, boundary
    copy-in/copy-out, value, compatibility, bounds, and non-escape obligations.
    The composed endpoint is intentionally stated as
    [public_semantic_refinement], so the final theorem reads like ordinary
    semantic refinement under a public observation relation. *)

Module StoragePrivateFamilyCompose
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Private := PrivateStorageValidator PolIRs Observer.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Private.View.

Theorem bounded_private_storage_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (private_params:
           Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_params
             value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after private_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
          value value_eqb value_eqb_sound)
        private_params before mid)
      private_ok ->
    private_ok = true ->
    View.cpvtf_side_condition
      (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
        value value_eqb value_eqb_sound)
      private_params before mid ->
    mayReturn
      (View.cpvtf_check
        Promotion.cscalar_promotion_bounded_family
        promotion_params mid after)
      promotion_ok ->
    promotion_ok = true ->
    View.cpvtf_side_condition
      Promotion.cscalar_promotion_bounded_family
      promotion_params mid after ->
    View.public_semantic_refinement
      (View.compose_view
        (View.cpvtf_input_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_input_view
          (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
            value value_eqb value_eqb_sound)
          private_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
            value value_eqb value_eqb_sound)
          private_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound private_params promotion_params
         before mid after private_ok promotion_ok
         Hprivate_ret Hprivate_ok Hprivate_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hprivate_ret.
  - exact Hprivate_ok.
  - exact Hprivate_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StoragePrivateFamilyCompose.
