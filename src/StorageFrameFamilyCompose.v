Require Import CInstrScalarPromotionValidatorBridge.
Require Import FramePreservationValidator.
Require Import ImpureAlarmConfig.
Require Import PolIRs.

(** Composition witness for contextual frame preservation.

    Frame preservation is not a storage remapping by itself.  It is the boundary
    condition that lets a storage-changing fragment be placed back into a larger
    context: transformed writes stay in an allowed-write set, the allowed writes
    are disjoint from context-owned frame cells, and the frame snapshot is
    preserved.  The family hides those finite obligations behind the same public
    semantic refinement interface used by storage transformations. *)

Module StorageFrameFamilyCompose (PolIRs: POLIRS).

Module Frame := FramePreservationValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Frame.View.

Theorem bounded_frame_preservation_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (frame_params:
           Frame.frame_preservation_bounded_value_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after frame_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Frame.frame_preservation_bounded_value_family
          value value_eqb value_eqb_sound)
        frame_params before mid)
      frame_ok ->
    frame_ok = true ->
    View.cpvtf_side_condition
      (Frame.frame_preservation_bounded_value_family
        value value_eqb value_eqb_sound)
      frame_params before mid ->
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
          (Frame.frame_preservation_bounded_value_family
            value value_eqb value_eqb_sound)
          frame_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Frame.frame_preservation_bounded_value_family
            value value_eqb value_eqb_sound)
          frame_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound frame_params promotion_params
         before mid after frame_ok promotion_ok
         Hframe_ret Hframe_ok Hframe_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hframe_ret.
  - exact Hframe_ok.
  - exact Hframe_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageFrameFamilyCompose.
