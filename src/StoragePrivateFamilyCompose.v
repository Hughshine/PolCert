Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import PrivateStorageValidator.
Require Import StateObservation.

(** Composition witness for generic private-storage transformations.

    This is the storage-expansion/privatization core below the CInstr-specific
    scalar wrapper.  The private-storage family carries local use-def, boundary
    copy-in/copy-out, value, compatibility, bounds, and non-escape obligations.
    The composed endpoint is intentionally stated as
    [public_semantic_refinement], so the final theorem reads like ordinary
    semantic refinement under a public observation relation. *)

Module StoragePrivateFamilyCompose
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Private := PrivateStorageValidator PolIRs Observer.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Private.View.

Definition private_storage_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_params
          value) :=
  Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_private_storage_certificate (value: Type) := {
  bpsc_private_params :
    Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_params
      value;
  bpsc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  bpsc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bpsc_private_params {value} _.
Arguments bpsc_promotion_params {value} _.
Arguments bpsc_mid_program {value} _.

Definition bounded_private_storage_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_private_storage_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (private_storage_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := bpsc_private_params certificate;
  View.cpfpc_second_params := bpsc_promotion_params certificate;
  View.cpfpc_mid_program := bpsc_mid_program certificate;
|}.

Definition bounded_private_storage_certificate_input_view
    {value: Type}
    (certificate: bounded_private_storage_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (bpsc_promotion_params certificate))
    (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_input_view
      (bpsc_private_params certificate)).

Definition bounded_private_storage_certificate_output_view
    {value: Type}
    (certificate: bounded_private_storage_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (bpsc_promotion_params certificate))
    (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_output_view
      (bpsc_private_params certificate)).

Definition bounded_private_storage_certificate_input_states_match
    {value: Type}
    (certificate: bounded_private_storage_certificate value) :=
  View.states_match
    (bounded_private_storage_certificate_input_view certificate).

Definition bounded_private_storage_certificate_output_states_match
    {value: Type}
    (certificate: bounded_private_storage_certificate value) :=
  View.states_match
    (bounded_private_storage_certificate_output_view certificate).

Definition bounded_private_storage_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_private_storage_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.public_semantic_refinement
    (bounded_private_storage_certificate_input_view certificate)
    (bounded_private_storage_certificate_output_view certificate)
    source target.

Definition bounded_private_storage_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_private_storage_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_private_storage_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

Theorem bounded_private_storage_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (private_params:
           Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_params
             value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after private_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
          value value_eqb value_eqb_sound)
        private_params before mid)
      private_ok ->
    private_ok = true ->
    View.cpvtf_side_condition
      (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
        value value_eqb value_eqb_sound)
      private_params before mid ->
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
          (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
            value value_eqb value_eqb_sound)
          private_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Private.private_bounded_declared_boundary_unique_compatible_non_escape_value_family
            value value_eqb value_eqb_sound)
          private_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound private_params promotion_params
         before mid after private_ok promotion_ok
         Hprivate_ret Hprivate_ok Hprivate_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hprivate_ret.
  - exact Hprivate_ok.
  - exact Hprivate_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem accepted_bounded_private_storage_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_private_storage_certificate value)
         before after,
    bounded_private_storage_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_private_storage_certificate_input_view certificate)
      (bounded_private_storage_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.accepted_parameterized_family_pair_certificate_public_semantic_refinement
       _
       _
       (private_storage_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_private_storage_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_private_storage_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_private_storage_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_private_storage_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_private_storage_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_private_storage_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (private_storage_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_private_storage_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_private_storage_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_private_storage_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_private_storage_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_private_storage_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_private_storage_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_private_storage_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_private_storage_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_private_storage_certificate value)
         source target,
    bounded_private_storage_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_private_storage_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (accepted_bounded_private_storage_certificate_public_semantic_refinement
       value value_eqb value_eqb_sound certificate
       source target Haccepted).
Qed.

End StoragePrivateFamilyCompose.
