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

Record bounded_scalar_storage_certificate
    (exp_value promo_value: Type) := {
  bssc_privatization_params :
    Expansion.scalar_privatization_bounded_value_params exp_value;
  bssc_promotion_params :
    Promotion.scalar_promotion_bounded_compatible_non_escape_value_params
      promo_value;
  bssc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bssc_privatization_params {exp_value promo_value} _.
Arguments bssc_promotion_params {exp_value promo_value} _.
Arguments bssc_mid_program {exp_value promo_value} _.

Definition scalar_storage_privatization_family
    (exp_value: Type)
    (exp_value_eqb: exp_value -> exp_value -> bool)
    (exp_value_eqb_sound:
      forall left right,
        exp_value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Expansion.scalar_privatization_bounded_value_params exp_value) :=
  Expansion.scalar_privatization_bounded_value_family
    exp_value exp_value_eqb exp_value_eqb_sound.

Definition scalar_storage_promotion_family
    (promo_value: Type)
    (promo_value_eqb: promo_value -> promo_value -> bool)
    (promo_value_eqb_sound:
      forall left right,
        promo_value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Promotion.scalar_promotion_bounded_compatible_non_escape_value_params
          promo_value) :=
  Promotion.scalar_promotion_bounded_compatible_non_escape_value_family
    promo_value promo_value_eqb promo_value_eqb_sound.

Definition bounded_scalar_storage_pair_certificate
    (exp_value promo_value: Type)
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
    (certificate: bounded_scalar_storage_certificate exp_value promo_value)
    : View.checked_parameterized_family_pair_certificate
        (scalar_storage_privatization_family
          exp_value exp_value_eqb exp_value_eqb_sound)
        (scalar_storage_promotion_family
          promo_value promo_value_eqb promo_value_eqb_sound) := {|
  View.cpfpc_first_params := bssc_privatization_params certificate;
  View.cpfpc_second_params := bssc_promotion_params certificate;
  View.cpfpc_mid_program := bssc_mid_program certificate;
|}.

Definition bounded_scalar_storage_certificate_input_view
    {exp_value promo_value: Type}
    (certificate: bounded_scalar_storage_certificate exp_value promo_value)
    : View.view :=
  View.compose_view
    (Promotion.scalar_promotion_bounded_compatible_non_escape_value_input_view
      (bssc_promotion_params certificate))
    (Expansion.scalar_privatization_bounded_value_input_view
      (bssc_privatization_params certificate)).

Definition bounded_scalar_storage_certificate_output_view
    {exp_value promo_value: Type}
    (certificate: bounded_scalar_storage_certificate exp_value promo_value)
    : View.view :=
  View.compose_view
    (Promotion.scalar_promotion_bounded_compatible_non_escape_value_output_view
      (bssc_promotion_params certificate))
    (Expansion.scalar_privatization_bounded_value_output_view
      (bssc_privatization_params certificate)).

Definition bounded_scalar_storage_certificate_input_states_match
    {exp_value promo_value: Type}
    (certificate: bounded_scalar_storage_certificate exp_value promo_value) :=
  View.states_match (bounded_scalar_storage_certificate_input_view certificate).

Definition bounded_scalar_storage_certificate_output_states_match
    {exp_value promo_value: Type}
    (certificate: bounded_scalar_storage_certificate exp_value promo_value) :=
  View.states_match (bounded_scalar_storage_certificate_output_view certificate).

Definition bounded_scalar_storage_certificate_accepted
    (exp_value promo_value: Type)
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
    (certificate: bounded_scalar_storage_certificate exp_value promo_value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_scalar_storage_pair_certificate
      exp_value promo_value exp_value_eqb promo_value_eqb
      exp_value_eqb_sound promo_value_eqb_sound certificate)
    before after.

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

Theorem accepted_bounded_scalar_storage_certificate_public_semantic_refinement :
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
         (certificate:
           bounded_scalar_storage_certificate exp_value promo_value)
         before after,
    bounded_scalar_storage_certificate_accepted
      exp_value promo_value exp_value_eqb promo_value_eqb
      exp_value_eqb_sound promo_value_eqb_sound
      certificate before after ->
    View.public_semantic_refinement
      (bounded_scalar_storage_certificate_input_view certificate)
      (bounded_scalar_storage_certificate_output_view certificate)
      before after.
Proof.
  intros exp_value promo_value exp_value_eqb promo_value_eqb
         exp_value_eqb_sound promo_value_eqb_sound
         certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       (scalar_storage_privatization_family
          exp_value exp_value_eqb exp_value_eqb_sound)
       (scalar_storage_promotion_family
          promo_value promo_value_eqb promo_value_eqb_sound)
       (bounded_scalar_storage_pair_certificate
          exp_value promo_value exp_value_eqb promo_value_eqb
          exp_value_eqb_sound promo_value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_scalar_storage_certificate_state_sound :
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
         (certificate:
           bounded_scalar_storage_certificate exp_value promo_value)
         before after st_target0 st_source0 st_target_after,
    bounded_scalar_storage_certificate_accepted
      exp_value promo_value exp_value_eqb promo_value_eqb
      exp_value_eqb_sound promo_value_eqb_sound
      certificate before after ->
    View.state_view_rel
      (bounded_scalar_storage_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_scalar_storage_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros exp_value promo_value exp_value_eqb promo_value_eqb
         exp_value_eqb_sound promo_value_eqb_sound
         certificate before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (scalar_storage_privatization_family
          exp_value exp_value_eqb exp_value_eqb_sound)
       (scalar_storage_promotion_family
          promo_value promo_value_eqb promo_value_eqb_sound)
       (bounded_scalar_storage_pair_certificate
          exp_value promo_value exp_value_eqb promo_value_eqb
          exp_value_eqb_sound promo_value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_scalar_storage_certificate_semantic_refinement :
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
         (certificate:
           bounded_scalar_storage_certificate exp_value promo_value)
         source target st_target0 st_source0 st_target_after,
    bounded_scalar_storage_certificate_accepted
      exp_value promo_value exp_value_eqb promo_value_eqb
      exp_value_eqb_sound promo_value_eqb_sound
      certificate source target ->
    bounded_scalar_storage_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_scalar_storage_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros exp_value promo_value exp_value_eqb promo_value_eqb
         exp_value_eqb_sound promo_value_eqb_sound
         certificate source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_scalar_storage_certificate_state_sound
       exp_value promo_value exp_value_eqb promo_value_eqb
       exp_value_eqb_sound promo_value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

End StorageScalarFamilyCompose.
