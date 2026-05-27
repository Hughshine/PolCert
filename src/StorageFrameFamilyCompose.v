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

Definition frame_preservation_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Frame.frame_preservation_bounded_value_params value) :=
  Frame.frame_preservation_bounded_value_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_frame_preservation_certificate (value: Type) := {
  bfpc_frame_params : Frame.frame_preservation_bounded_value_params value;
  bfpc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  bfpc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bfpc_frame_params {value} _.
Arguments bfpc_promotion_params {value} _.
Arguments bfpc_mid_program {value} _.

Definition bounded_frame_preservation_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_frame_preservation_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (frame_preservation_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := bfpc_frame_params certificate;
  View.cpfpc_second_params := bfpc_promotion_params certificate;
  View.cpfpc_mid_program := bfpc_mid_program certificate;
|}.

Definition bounded_frame_preservation_certificate_input_view
    {value: Type}
    (certificate: bounded_frame_preservation_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (bfpc_promotion_params certificate))
    (Frame.frame_preservation_bounded_value_input_view
      (bfpc_frame_params certificate)).

Definition bounded_frame_preservation_certificate_output_view
    {value: Type}
    (certificate: bounded_frame_preservation_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (bfpc_promotion_params certificate))
    (Frame.frame_preservation_bounded_value_output_view
      (bfpc_frame_params certificate)).

Definition bounded_frame_preservation_certificate_input_states_match
    {value: Type}
    (certificate: bounded_frame_preservation_certificate value) :=
  View.states_match
    (bounded_frame_preservation_certificate_input_view certificate).

Definition bounded_frame_preservation_certificate_output_states_match
    {value: Type}
    (certificate: bounded_frame_preservation_certificate value) :=
  View.states_match
    (bounded_frame_preservation_certificate_output_view certificate).

Definition bounded_frame_preservation_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_frame_preservation_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_refinement
    (bounded_frame_preservation_pair_certificate
      value value_eqb value_eqb_sound certificate)
    source target.

Definition bounded_frame_preservation_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_frame_preservation_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_frame_preservation_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

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

Theorem accepted_bounded_frame_preservation_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_frame_preservation_certificate value)
         before after,
    bounded_frame_preservation_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_frame_preservation_certificate_input_view certificate)
      (bounded_frame_preservation_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       (frame_preservation_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_frame_preservation_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_frame_preservation_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_frame_preservation_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_frame_preservation_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_frame_preservation_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_frame_preservation_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (frame_preservation_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_frame_preservation_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_frame_preservation_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_frame_preservation_certificate value)
         source target,
    bounded_frame_preservation_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_frame_preservation_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_refines
       _
       _
       (frame_preservation_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_frame_preservation_pair_certificate
          value value_eqb value_eqb_sound certificate)
       source target Haccepted).
Qed.

Theorem accepted_bounded_frame_preservation_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_frame_preservation_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_frame_preservation_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_frame_preservation_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_frame_preservation_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_frame_preservation_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

End StorageFrameFamilyCompose.
