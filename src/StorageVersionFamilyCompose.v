Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import VersionCommitValidator.

(** Composition witness for versioned-storage transformations.

    Version commit/read is the array-expansion-style case: the target may carry
    multiple produced physical versions and then select committed live-outs for
    the public boundary.  The family instance hides commit coverage, read
    selection, value evidence, storage compatibility, bounds, and non-escape
    behind the same public-view interface used by the other storage families. *)

Module StorageVersionFamilyCompose (PolIRs: POLIRS).

Module Version := VersionCommitValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Version.View.

Theorem bounded_version_commit_then_scalar_promotion_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (version_params:
           Version.version_commit_read_fully_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after version_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Version.version_commit_read_fully_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        version_params before mid)
      version_ok ->
    version_ok = true ->
    View.cpvtf_side_condition
      (Version.version_commit_read_fully_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      version_params before mid ->
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
          (Version.version_commit_read_fully_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          version_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Version.version_commit_read_fully_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          version_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound version_params promotion_params
         before mid after version_ok promotion_ok
         Hversion_ret Hversion_ok Hversion_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hversion_ret.
  - exact Hversion_ok.
  - exact Hversion_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

End StorageVersionFamilyCompose.
