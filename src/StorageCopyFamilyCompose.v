Require Import CInstrScalarPromotionValidatorBridge.
Require Import CopyProtocolValidator.
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

Module Copy := CopyProtocolValidator PolIRs.
Module Scratchpad := ScratchpadCopyValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Scratchpad.View.

Definition scratchpad_copy_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Scratchpad.scratchpad_copy_bounded_non_escape_params value) :=
  Scratchpad.scratchpad_copy_bounded_non_escape_family
    value value_eqb value_eqb_sound.

Definition copy_protocol_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_params
          value) :=
  Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_scratchpad_copy_certificate (value: Type) := {
  bscc_scratchpad_params :
    Scratchpad.scratchpad_copy_bounded_non_escape_params value;
  bscc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  bscc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bscc_scratchpad_params {value} _.
Arguments bscc_promotion_params {value} _.
Arguments bscc_mid_program {value} _.

Definition bounded_scratchpad_copy_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_scratchpad_copy_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (scratchpad_copy_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := bscc_scratchpad_params certificate;
  View.cpfpc_second_params := bscc_promotion_params certificate;
  View.cpfpc_mid_program := bscc_mid_program certificate;
|}.

Definition bounded_scratchpad_copy_certificate_input_view
    {value: Type}
    (certificate: bounded_scratchpad_copy_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (bscc_promotion_params certificate))
    (Scratchpad.scratchpad_copy_bounded_non_escape_input_view
      (bscc_scratchpad_params certificate)).

Definition bounded_scratchpad_copy_certificate_output_view
    {value: Type}
    (certificate: bounded_scratchpad_copy_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (bscc_promotion_params certificate))
    (Scratchpad.scratchpad_copy_bounded_non_escape_output_view
      (bscc_scratchpad_params certificate)).

Definition bounded_scratchpad_copy_certificate_input_states_match
    {value: Type}
    (certificate: bounded_scratchpad_copy_certificate value) :=
  View.states_match
    (bounded_scratchpad_copy_certificate_input_view certificate).

Definition bounded_scratchpad_copy_certificate_output_states_match
    {value: Type}
    (certificate: bounded_scratchpad_copy_certificate value) :=
  View.states_match
    (bounded_scratchpad_copy_certificate_output_view certificate).

Definition bounded_scratchpad_copy_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_scratchpad_copy_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.public_semantic_refinement
    (bounded_scratchpad_copy_certificate_input_view certificate)
    (bounded_scratchpad_copy_certificate_output_view certificate)
    source target.

Definition bounded_scratchpad_copy_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_scratchpad_copy_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_scratchpad_copy_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

Record declared_copy_protocol_certificate (value: Type) := {
  dcpc_copy_params :
    Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_params
      value;
  dcpc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  dcpc_mid_program : PolIRs.PolyLang.t;
}.

Arguments dcpc_copy_params {value} _.
Arguments dcpc_promotion_params {value} _.
Arguments dcpc_mid_program {value} _.

Definition declared_copy_protocol_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: declared_copy_protocol_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (copy_protocol_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := dcpc_copy_params certificate;
  View.cpfpc_second_params := dcpc_promotion_params certificate;
  View.cpfpc_mid_program := dcpc_mid_program certificate;
|}.

Definition declared_copy_protocol_certificate_input_view
    {value: Type}
    (certificate: declared_copy_protocol_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (dcpc_promotion_params certificate))
    (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_input_view
      (dcpc_copy_params certificate)).

Definition declared_copy_protocol_certificate_output_view
    {value: Type}
    (certificate: declared_copy_protocol_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (dcpc_promotion_params certificate))
    (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_output_view
      (dcpc_copy_params certificate)).

Definition declared_copy_protocol_certificate_input_states_match
    {value: Type}
    (certificate: declared_copy_protocol_certificate value) :=
  View.states_match
    (declared_copy_protocol_certificate_input_view certificate).

Definition declared_copy_protocol_certificate_output_states_match
    {value: Type}
    (certificate: declared_copy_protocol_certificate value) :=
  View.states_match
    (declared_copy_protocol_certificate_output_view certificate).

Definition declared_copy_protocol_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: declared_copy_protocol_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.public_semantic_refinement
    (declared_copy_protocol_certificate_input_view certificate)
    (declared_copy_protocol_certificate_output_view certificate)
    source target.

Definition declared_copy_protocol_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: declared_copy_protocol_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (declared_copy_protocol_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

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

Theorem bounded_scratchpad_copy_then_scalar_promotion_public_semantic_refinement :
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
    View.public_semantic_refinement
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
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hscratchpad_ret.
  - exact Hscratchpad_ok.
  - exact Hscratchpad_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem accepted_bounded_scratchpad_copy_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_scratchpad_copy_certificate value)
         before after,
    bounded_scratchpad_copy_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_scratchpad_copy_certificate_input_view certificate)
      (bounded_scratchpad_copy_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.accepted_parameterized_family_pair_certificate_public_semantic_refinement
       _
       _
       (scratchpad_copy_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_scratchpad_copy_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_scratchpad_copy_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_scratchpad_copy_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_scratchpad_copy_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_scratchpad_copy_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_scratchpad_copy_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (scratchpad_copy_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_scratchpad_copy_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_scratchpad_copy_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_scratchpad_copy_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_scratchpad_copy_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_scratchpad_copy_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_scratchpad_copy_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_scratchpad_copy_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_scratchpad_copy_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_scratchpad_copy_certificate value)
         source target,
    bounded_scratchpad_copy_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_scratchpad_copy_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (accepted_bounded_scratchpad_copy_certificate_public_semantic_refinement
       value value_eqb value_eqb_sound certificate
       source target Haccepted).
Qed.

Theorem bounded_copy_protocol_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (copy_params:
           Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_params
             value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after copy_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_family
          value value_eqb value_eqb_sound)
        copy_params before mid)
      copy_ok ->
    copy_ok = true ->
    View.cpvtf_side_condition
      (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_family
        value value_eqb value_eqb_sound)
      copy_params before mid ->
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
          (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_family
            value value_eqb value_eqb_sound)
          copy_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Copy.copy_protocol_declared_bounded_compatible_commit_mapping_value_family
            value value_eqb value_eqb_sound)
          copy_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound copy_params promotion_params
         before mid after copy_ok promotion_ok
         Hcopy_ret Hcopy_ok Hcopy_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hcopy_ret.
  - exact Hcopy_ok.
  - exact Hcopy_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem accepted_declared_copy_protocol_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: declared_copy_protocol_certificate value)
         before after,
    declared_copy_protocol_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (declared_copy_protocol_certificate_input_view certificate)
      (declared_copy_protocol_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.accepted_parameterized_family_pair_certificate_public_semantic_refinement
       _
       _
       (copy_protocol_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (declared_copy_protocol_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_declared_copy_protocol_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: declared_copy_protocol_certificate value)
         before after st_target0 st_source0 st_target_after,
    declared_copy_protocol_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (declared_copy_protocol_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (declared_copy_protocol_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (copy_protocol_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (declared_copy_protocol_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_declared_copy_protocol_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: declared_copy_protocol_certificate value)
         source target st_target0 st_source0 st_target_after,
    declared_copy_protocol_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    declared_copy_protocol_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      declared_copy_protocol_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_declared_copy_protocol_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_declared_copy_protocol_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: declared_copy_protocol_certificate value)
         source target,
    declared_copy_protocol_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    declared_copy_protocol_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (accepted_declared_copy_protocol_certificate_public_semantic_refinement
       value value_eqb value_eqb_sound certificate
       source target Haccepted).
Qed.

End StorageCopyFamilyCompose.
