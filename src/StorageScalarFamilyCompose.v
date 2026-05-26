Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import ScalarExpansionValidator.
Require Import ScalarPromotionValidator.
Require Import StateObservation.

(** Composition witness for generic scalar-storage transformations.

    This file stays below the CInstr-specific bridge layer.  It composes the
    generic scalar privatization/expansion family with the generic scalar
    promotion/register-replacement family through the shared public-view family
    interface.  The result is stated as [public_semantic_refinement], matching
    the paper-facing endpoint used by the other storage families. *)

Module StorageScalarFamilyCompose
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Expansion := ScalarExpansionValidator PolIRs Observer.
Module Promotion := ScalarPromotionValidator PolIRs.
Module View := Expansion.View.

Theorem bounded_scalar_privatization_then_scalar_promotion_public_semantic_refinement :
  forall (exp_value promo_value: Type)
         (exp_value_eqb: exp_value -> exp_value -> bool)
         (promo_value_eqb: promo_value -> promo_value -> bool)
         (exp_value_eqb_sound:
           forall left right,
             exp_value_eqb left right = true ->
             left = right)
         (promo_value_eqb_sound:
           forall left right,
             promo_value_eqb left right = true ->
             left = right)
         (privatization_params:
           Expansion.scalar_privatization_bounded_value_params exp_value)
         (promotion_params:
           Promotion.scalar_promotion_bounded_compatible_non_escape_value_params
             promo_value)
         before mid after privatization_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Expansion.scalar_privatization_bounded_value_family
          exp_value exp_value_eqb exp_value_eqb_sound)
        privatization_params before mid)
      privatization_ok ->
    privatization_ok = true ->
    View.cpvtf_side_condition
      (Expansion.scalar_privatization_bounded_value_family
        exp_value exp_value_eqb exp_value_eqb_sound)
      privatization_params before mid ->
    mayReturn
      (View.cpvtf_check
        (Promotion.scalar_promotion_bounded_compatible_non_escape_value_family
          promo_value promo_value_eqb promo_value_eqb_sound)
        promotion_params mid after)
      promotion_ok ->
    promotion_ok = true ->
    View.cpvtf_side_condition
      (Promotion.scalar_promotion_bounded_compatible_non_escape_value_family
        promo_value promo_value_eqb promo_value_eqb_sound)
      promotion_params mid after ->
    View.public_semantic_refinement
      (View.compose_view
        (View.cpvtf_input_view
          (Promotion.scalar_promotion_bounded_compatible_non_escape_value_family
            promo_value promo_value_eqb promo_value_eqb_sound)
          promotion_params)
        (View.cpvtf_input_view
          (Expansion.scalar_privatization_bounded_value_family
            exp_value exp_value_eqb exp_value_eqb_sound)
          privatization_params))
      (View.compose_view
        (View.cpvtf_output_view
          (Promotion.scalar_promotion_bounded_compatible_non_escape_value_family
            promo_value promo_value_eqb promo_value_eqb_sound)
          promotion_params)
        (View.cpvtf_output_view
          (Expansion.scalar_privatization_bounded_value_family
            exp_value exp_value_eqb exp_value_eqb_sound)
          privatization_params))
      before after.
Proof.
  intros exp_value promo_value exp_value_eqb promo_value_eqb
         exp_value_eqb_sound promo_value_eqb_sound
         privatization_params promotion_params
         before mid after privatization_ok promotion_ok
         Hpriv_ret Hpriv_ok Hpriv_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hpriv_ret.
  - exact Hpriv_ok.
  - exact Hpriv_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageScalarFamilyCompose.
