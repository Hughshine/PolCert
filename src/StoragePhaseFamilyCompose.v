Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PhaseSeparationValidator.
Require Import PolIRs.

(** Composition witness for phase/double-buffering transformations.

    Phase-separated storage protocols are the double-buffering/ping-pong case:
    the target executes through phase boundaries, reuses physical buffers across
    phases, and exposes only a projected final live-out boundary.  The family
    instance keeps visibility, overwrite safety, value flow, projection cover,
    compatibility, bounds, and non-escape obligations internal to the checked
    pass.

    This file deliberately states the composed endpoint as
    [public_semantic_refinement].  That is the paper-facing shape: every target
    execution from an input public view has a matching source execution whose
    final state satisfies the output public view. *)

Module StoragePhaseFamilyCompose (PolIRs: POLIRS).

Module Phase := PhaseSeparationValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Phase.View.

Theorem bounded_phase_projection_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (phase_params:
           Phase.phase_projection_bounded_compatible_non_escape_value_params
             value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after phase_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Phase.phase_projection_bounded_compatible_non_escape_value_family
          value value_eqb value_eqb_sound)
        phase_params before mid)
      phase_ok ->
    phase_ok = true ->
    View.cpvtf_side_condition
      (Phase.phase_projection_bounded_compatible_non_escape_value_family
        value value_eqb value_eqb_sound)
      phase_params before mid ->
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
          (Phase.phase_projection_bounded_compatible_non_escape_value_family
            value value_eqb value_eqb_sound)
          phase_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Phase.phase_projection_bounded_compatible_non_escape_value_family
            value value_eqb value_eqb_sound)
          phase_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound phase_params promotion_params
         before mid after phase_ok promotion_ok
         Hphase_ret Hphase_ok Hphase_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hphase_ret.
  - exact Hphase_ok.
  - exact Hphase_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StoragePhaseFamilyCompose.
