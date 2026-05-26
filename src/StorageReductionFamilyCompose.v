Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import ReductionMergeValidator.

(** Composition witness for reduction-privatization transformations.

    Reduction merge is the merge-policy counterpart to private storage:
    multiple private accumulators are folded into the source-observable result
    under checked value and algebra witnesses.  The family instance keeps the
    finite merge, compatibility, bounds, and non-escape obligations internal to
    the checked pass and exposes only public-view refinement for composition. *)

Module StorageReductionFamilyCompose (PolIRs: POLIRS).

Module Reduction := ReductionMergeValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Reduction.View.

Theorem bounded_reduction_merge_then_scalar_promotion_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (reduction_params:
           Reduction.reduction_merge_commutative_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after reduction_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Reduction.reduction_merge_commutative_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        reduction_params before mid)
      reduction_ok ->
    reduction_ok = true ->
    View.cpvtf_side_condition
      (Reduction.reduction_merge_commutative_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      reduction_params before mid ->
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
          (Reduction.reduction_merge_commutative_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          reduction_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Reduction.reduction_merge_commutative_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          reduction_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound reduction_params promotion_params
         before mid after reduction_ok promotion_ok
         Hreduction_ret Hreduction_ok Hreduction_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hreduction_ret.
  - exact Hreduction_ok.
  - exact Hreduction_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageReductionFamilyCompose.
