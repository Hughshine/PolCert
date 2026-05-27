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

Definition reduction_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Reduction.reduction_merge_commutative_bounded_non_escape_params
          value) :=
  Reduction.reduction_merge_commutative_bounded_non_escape_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_reduction_merge_certificate (value: Type) := {
  brmc_reduction_params :
    Reduction.reduction_merge_commutative_bounded_non_escape_params value;
  brmc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  brmc_mid_program : PolIRs.PolyLang.t;
}.

Arguments brmc_reduction_params {value} _.
Arguments brmc_promotion_params {value} _.
Arguments brmc_mid_program {value} _.

Definition bounded_reduction_merge_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_reduction_merge_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (reduction_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := brmc_reduction_params certificate;
  View.cpfpc_second_params := brmc_promotion_params certificate;
  View.cpfpc_mid_program := brmc_mid_program certificate;
|}.

Definition bounded_reduction_merge_certificate_input_view
    {value: Type}
    (certificate: bounded_reduction_merge_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (brmc_promotion_params certificate))
    (Reduction.reduction_merge_commutative_bounded_non_escape_input_view
      (brmc_reduction_params certificate)).

Definition bounded_reduction_merge_certificate_output_view
    {value: Type}
    (certificate: bounded_reduction_merge_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (brmc_promotion_params certificate))
    (Reduction.reduction_merge_commutative_bounded_non_escape_output_view
      (brmc_reduction_params certificate)).

Definition bounded_reduction_merge_certificate_input_states_match
    {value: Type}
    (certificate: bounded_reduction_merge_certificate value) :=
  View.states_match (bounded_reduction_merge_certificate_input_view certificate).

Definition bounded_reduction_merge_certificate_output_states_match
    {value: Type}
    (certificate: bounded_reduction_merge_certificate value) :=
  View.states_match (bounded_reduction_merge_certificate_output_view certificate).

Definition bounded_reduction_merge_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_reduction_merge_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_refinement
    (bounded_reduction_merge_pair_certificate
      value value_eqb value_eqb_sound certificate)
    source target.

Definition bounded_reduction_merge_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_reduction_merge_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_reduction_merge_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

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

Theorem bounded_reduction_merge_then_scalar_promotion_public_semantic_refinement :
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
    View.public_semantic_refinement
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
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hreduction_ret.
  - exact Hreduction_ok.
  - exact Hreduction_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem accepted_bounded_reduction_merge_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_reduction_merge_certificate value)
         before after,
    bounded_reduction_merge_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_reduction_merge_certificate_input_view certificate)
      (bounded_reduction_merge_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       (reduction_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_reduction_merge_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_reduction_merge_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_reduction_merge_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_reduction_merge_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_reduction_merge_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_reduction_merge_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (reduction_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_reduction_merge_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_reduction_merge_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_reduction_merge_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_reduction_merge_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_reduction_merge_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_reduction_merge_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_reduction_merge_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_reduction_merge_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_reduction_merge_certificate value)
         source target,
    bounded_reduction_merge_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_reduction_merge_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_refines
       _
       _
       (reduction_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_reduction_merge_pair_certificate
          value value_eqb value_eqb_sound certificate)
       source target Haccepted).
Qed.

End StorageReductionFamilyCompose.
