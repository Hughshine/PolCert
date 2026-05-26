Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import OverlapTilingValidator.
Require Import PolIRs.

(** Composition witness for overlap/private-recomputation transformations.

    The overlap family is the instance-count-changing counterpart to the
    storage-only families: target instances may be duplicated or internal, while
    only commit-role behavior remains public.  Its family instance hides the
    projection, local-closure, value-equivalence, private-storage, bounds,
    compatibility, and non-escape obligations behind the same public-view
    interface used by scalar and copy-mediated storage passes. *)

Module StorageOverlapFamilyCompose (PolIRs: POLIRS).

Module Overlap := OverlapTilingValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Overlap.View.

Theorem bounded_overlap_then_scalar_promotion_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (overlap_params:
           Overlap.overlap_private_ordered_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after overlap_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Overlap.overlap_private_ordered_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        overlap_params before mid)
      overlap_ok ->
    overlap_ok = true ->
    View.cpvtf_side_condition
      (Overlap.overlap_private_ordered_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      overlap_params before mid ->
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
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound overlap_params promotion_params
         before mid after overlap_ok promotion_ok
         Hoverlap_ret Hoverlap_ok Hoverlap_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hoverlap_ret.
  - exact Hoverlap_ok.
  - exact Hoverlap_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem bounded_overlap_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (overlap_params:
           Overlap.overlap_private_ordered_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after overlap_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Overlap.overlap_private_ordered_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        overlap_params before mid)
      overlap_ok ->
    overlap_ok = true ->
    View.cpvtf_side_condition
      (Overlap.overlap_private_ordered_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      overlap_params before mid ->
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
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound overlap_params promotion_params
         before mid after overlap_ok promotion_ok
         Hoverlap_ret Hoverlap_ok Hoverlap_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hoverlap_ret.
  - exact Hoverlap_ok.
  - exact Hoverlap_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageOverlapFamilyCompose.
