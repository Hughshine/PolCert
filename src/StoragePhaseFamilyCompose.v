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

Definition phase_projection_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Phase.phase_projection_bounded_compatible_non_escape_value_params
          value) :=
  Phase.phase_projection_bounded_compatible_non_escape_value_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_phase_projection_certificate (value: Type) := {
  bppc_phase_params :
    Phase.phase_projection_bounded_compatible_non_escape_value_params value;
  bppc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  bppc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bppc_phase_params {value} _.
Arguments bppc_promotion_params {value} _.
Arguments bppc_mid_program {value} _.

Definition bounded_phase_projection_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_phase_projection_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (phase_projection_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := bppc_phase_params certificate;
  View.cpfpc_second_params := bppc_promotion_params certificate;
  View.cpfpc_mid_program := bppc_mid_program certificate;
|}.

Definition bounded_phase_projection_certificate_input_view
    {value: Type}
    (certificate: bounded_phase_projection_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (bppc_promotion_params certificate))
    (Phase.phase_projection_bounded_compatible_non_escape_value_input_view
      (bppc_phase_params certificate)).

Definition bounded_phase_projection_certificate_output_view
    {value: Type}
    (certificate: bounded_phase_projection_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (bppc_promotion_params certificate))
    (Phase.phase_projection_bounded_compatible_non_escape_value_output_view
      (bppc_phase_params certificate)).

Definition bounded_phase_projection_certificate_input_states_match
    {value: Type}
    (certificate: bounded_phase_projection_certificate value) :=
  View.states_match (bounded_phase_projection_certificate_input_view certificate).

Definition bounded_phase_projection_certificate_output_states_match
    {value: Type}
    (certificate: bounded_phase_projection_certificate value) :=
  View.states_match (bounded_phase_projection_certificate_output_view certificate).

Definition bounded_phase_projection_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_phase_projection_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.public_semantic_refinement
    (bounded_phase_projection_certificate_input_view certificate)
    (bounded_phase_projection_certificate_output_view certificate)
    source target.

Definition bounded_phase_projection_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_phase_projection_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_phase_projection_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

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

Theorem accepted_bounded_phase_projection_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_phase_projection_certificate value)
         before after,
    bounded_phase_projection_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_phase_projection_certificate_input_view certificate)
      (bounded_phase_projection_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.accepted_parameterized_family_pair_certificate_public_semantic_refinement
       _
       _
       (phase_projection_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_phase_projection_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_phase_projection_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_phase_projection_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_phase_projection_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_phase_projection_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_phase_projection_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (phase_projection_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_phase_projection_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_phase_projection_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_phase_projection_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_phase_projection_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_phase_projection_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_phase_projection_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_phase_projection_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_phase_projection_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_phase_projection_certificate value)
         source target,
    bounded_phase_projection_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_phase_projection_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (accepted_bounded_phase_projection_certificate_public_semantic_refinement
       value value_eqb value_eqb_sound certificate
       source target Haccepted).
Qed.

End StoragePhaseFamilyCompose.
