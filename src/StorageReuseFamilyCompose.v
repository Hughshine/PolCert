Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import InterArrayReuseValidator.
Require Import PolIRs.
Require Import ReuseConflictValidator.

(** Composition witness for reuse-class storage transformations.

    This file composes a bounded inter-array reuse family with a bounded CInstr
    scalar-promotion family through the shared parameterized public-view
    transform interface.  The theorem is intentionally about public views; the
    reuse mapping, live intervals, conflicts, bounds, and scalar trace remain
    side conditions of the component families. *)

Module StorageReuseFamilyCompose (PolIRs: POLIRS).

Module InterArray := InterArrayReuseValidator PolIRs.
Module Conflict := ReuseConflictValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := InterArray.View.

Theorem bounded_inter_array_reuse_then_scalar_promotion_refinement :
  forall (reuse_params: InterArray.bounded_inter_array_reuse_params)
         (promotion_params: Promotion.cscalar_promotion_bounded_params)
         before mid after reuse_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        InterArray.bounded_inter_array_reuse_family
        reuse_params before mid)
      reuse_ok ->
    reuse_ok = true ->
    View.cpvtf_side_condition
      InterArray.bounded_inter_array_reuse_family
      reuse_params before mid ->
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
          InterArray.bounded_inter_array_reuse_family
          reuse_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          InterArray.bounded_inter_array_reuse_family
          reuse_params))
      before after.
Proof.
  intros reuse_params promotion_params before mid after reuse_ok promotion_ok
         Hreuse_ret Hreuse_ok Hreuse_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hreuse_ret.
  - exact Hreuse_ok.
  - exact Hreuse_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem bounded_inter_array_reuse_then_scalar_promotion_public_semantic_refinement :
  forall (reuse_params: InterArray.bounded_inter_array_reuse_params)
         (promotion_params: Promotion.cscalar_promotion_bounded_params)
         before mid after reuse_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        InterArray.bounded_inter_array_reuse_family
        reuse_params before mid)
      reuse_ok ->
    reuse_ok = true ->
    View.cpvtf_side_condition
      InterArray.bounded_inter_array_reuse_family
      reuse_params before mid ->
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
          InterArray.bounded_inter_array_reuse_family
          reuse_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          InterArray.bounded_inter_array_reuse_family
          reuse_params))
      before after.
Proof.
  intros reuse_params promotion_params before mid after reuse_ok promotion_ok
         Hreuse_ret Hreuse_ok Hreuse_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hreuse_ret.
  - exact Hreuse_ok.
  - exact Hreuse_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem bounded_conflict_reuse_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (reuse_params:
           Conflict.bounded_compatible_live_conflict_reuse_value_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after reuse_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Conflict.bounded_compatible_live_conflict_reuse_value_family
          value value_eqb value_eqb_sound)
        reuse_params before mid)
      reuse_ok ->
    reuse_ok = true ->
    View.cpvtf_side_condition
      (Conflict.bounded_compatible_live_conflict_reuse_value_family
        value value_eqb value_eqb_sound)
      reuse_params before mid ->
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
          (Conflict.bounded_compatible_live_conflict_reuse_value_family
            value value_eqb value_eqb_sound)
          reuse_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Conflict.bounded_compatible_live_conflict_reuse_value_family
            value value_eqb value_eqb_sound)
          reuse_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound reuse_params promotion_params
         before mid after reuse_ok promotion_ok
         Hreuse_ret Hreuse_ok Hreuse_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hreuse_ret.
  - exact Hreuse_ok.
  - exact Hreuse_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageReuseFamilyCompose.
