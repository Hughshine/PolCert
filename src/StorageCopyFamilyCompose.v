Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import ScratchpadCopyValidator.

(** Composition witness for copy-mediated storage transformations.

    Scratchpad/packing transformations have a larger witness surface than scalar
    storage rewrites: instance projection, copy protocol order, commit cover,
    public/local mapping, bounds, storage compatibility, value simulation, and
    non-escape.  The component family hides that bookkeeping behind the same
    public-view interface used by scalar and reuse families.  This file checks
    that it composes with later scalar promotion without exposing those internal
    contracts at the top theorem. *)

Module StorageCopyFamilyCompose (PolIRs: POLIRS).

Module Scratchpad := ScratchpadCopyValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Scratchpad.View.

Theorem bounded_scratchpad_copy_then_scalar_promotion_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (scratchpad_params:
           Scratchpad.scratchpad_copy_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after scratchpad_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Scratchpad.scratchpad_copy_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        scratchpad_params before mid)
      scratchpad_ok ->
    scratchpad_ok = true ->
    View.cpvtf_side_condition
      (Scratchpad.scratchpad_copy_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      scratchpad_params before mid ->
    mayReturn
      (View.cpvtf_check
        Promotion.cscalar_promotion_bounded_family
        promotion_params mid after)
      promotion_ok ->
    promotion_ok = true ->
    View.cpvtf_side_condition
      Promotion.cscalar_promotion_bounded_family
      promotion_params mid after ->
    View.view_refinement
      (View.compose_view
        (View.cpvtf_input_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_input_view
          (Scratchpad.scratchpad_copy_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          scratchpad_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Scratchpad.scratchpad_copy_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          scratchpad_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound scratchpad_params promotion_params
         before mid after scratchpad_ok promotion_ok
         Hscratchpad_ret Hscratchpad_ok Hscratchpad_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hscratchpad_ret.
  - exact Hscratchpad_ok.
  - exact Hscratchpad_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageCopyFamilyCompose.
