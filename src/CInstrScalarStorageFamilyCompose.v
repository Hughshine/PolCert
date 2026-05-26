Require Import CInstrScalarExpansionValidatorBridge.
Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import StateObservation.

(** Composition witness for concrete CInstr scalar-storage families.

    This theorem composes two parameterized public-refinement family instances:
    bounded scalar privatization followed by bounded scalar promotion.  It
    deliberately exposes only composed public views, not the internal
    scalar-expansion or promotion contract records. *)

Module CInstrScalarStorageFamilyCompose
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Expansion := CInstrScalarExpansionValidatorBridge PolIRs Observer.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Expansion.View.

Theorem bounded_privatization_then_promotion_public_refinement :
  forall (privatization_params:
            Expansion.cscalar_privatization_bounded_params)
         (promotion_params:
            Promotion.cscalar_promotion_bounded_params)
         before mid after privatization_ok promotion_ok,
    mayReturn
      (Expansion.cscalar_privatization_bounded_check
        privatization_params before mid)
      privatization_ok ->
    privatization_ok = true ->
    Expansion.cscalar_privatization_bounded_side_condition
      privatization_params before mid ->
    mayReturn
      (Promotion.cscalar_promotion_bounded_check
        promotion_params mid after)
      promotion_ok ->
    promotion_ok = true ->
    Promotion.cscalar_promotion_bounded_side_condition
      promotion_params mid after ->
    View.view_refinement
      (View.compose_view
        (View.cpvtf_input_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_input_view
          Expansion.cscalar_privatization_bounded_family
          privatization_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          Expansion.cscalar_privatization_bounded_family
          privatization_params))
      before after.
Proof.
  intros privatization_params promotion_params before mid after
         privatization_ok promotion_ok
         Hpriv_ret Hpriv_ok Hpriv_side
         Hpromo_ret Hpromo_ok Hpromo_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hpriv_ret.
  - exact Hpriv_ok.
  - exact Hpriv_side.
  - exact Hpromo_ret.
  - exact Hpromo_ok.
  - exact Hpromo_side.
Qed.

End CInstrScalarStorageFamilyCompose.
