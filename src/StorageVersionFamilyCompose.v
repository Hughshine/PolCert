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

Definition version_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Version.version_commit_read_fully_bounded_non_escape_params value) :=
  Version.version_commit_read_fully_bounded_non_escape_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_version_commit_certificate (value: Type) := {
  bvcc_version_params :
    Version.version_commit_read_fully_bounded_non_escape_params value;
  bvcc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  bvcc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bvcc_version_params {value} _.
Arguments bvcc_promotion_params {value} _.
Arguments bvcc_mid_program {value} _.

Definition bounded_version_commit_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_version_commit_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (version_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := bvcc_version_params certificate;
  View.cpfpc_second_params := bvcc_promotion_params certificate;
  View.cpfpc_mid_program := bvcc_mid_program certificate;
|}.

Definition bounded_version_commit_certificate_input_view
    {value: Type}
    (certificate: bounded_version_commit_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (bvcc_promotion_params certificate))
    (Version.version_commit_read_fully_bounded_non_escape_input_view
      (bvcc_version_params certificate)).

Definition bounded_version_commit_certificate_output_view
    {value: Type}
    (certificate: bounded_version_commit_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (bvcc_promotion_params certificate))
    (Version.version_commit_read_fully_bounded_non_escape_output_view
      (bvcc_version_params certificate)).

Definition bounded_version_commit_certificate_input_states_match
    {value: Type}
    (certificate: bounded_version_commit_certificate value) :=
  View.states_match (bounded_version_commit_certificate_input_view certificate).

Definition bounded_version_commit_certificate_output_states_match
    {value: Type}
    (certificate: bounded_version_commit_certificate value) :=
  View.states_match (bounded_version_commit_certificate_output_view certificate).

Definition bounded_version_commit_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_version_commit_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.public_semantic_refinement
    (bounded_version_commit_certificate_input_view certificate)
    (bounded_version_commit_certificate_output_view certificate)
    source target.

Definition bounded_version_commit_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_version_commit_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_version_commit_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

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

Theorem bounded_version_commit_then_scalar_promotion_public_semantic_refinement :
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
    View.public_semantic_refinement
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
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hversion_ret.
  - exact Hversion_ok.
  - exact Hversion_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem accepted_bounded_version_commit_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_version_commit_certificate value)
         before after,
    bounded_version_commit_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_version_commit_certificate_input_view certificate)
      (bounded_version_commit_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.accepted_parameterized_family_pair_certificate_public_semantic_refinement
       _
       _
       (version_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_version_commit_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_version_commit_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_version_commit_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_version_commit_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_version_commit_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_version_commit_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (version_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_version_commit_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_version_commit_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_version_commit_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_version_commit_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_version_commit_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_version_commit_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_version_commit_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_version_commit_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_version_commit_certificate value)
         source target,
    bounded_version_commit_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_version_commit_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (accepted_bounded_version_commit_certificate_public_semantic_refinement
       value value_eqb value_eqb_sound certificate
       source target Haccepted).
Qed.

End StorageVersionFamilyCompose.
