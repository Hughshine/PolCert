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

Definition inter_array_reuse_family
    : View.checked_parameterized_view_transform_family
        InterArray.bounded_inter_array_reuse_params :=
  InterArray.bounded_inter_array_reuse_family.

Definition conflict_reuse_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Conflict.bounded_compatible_live_conflict_reuse_value_params value) :=
  Conflict.bounded_compatible_live_conflict_reuse_value_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_inter_array_reuse_certificate := {
  biarc_reuse_params : InterArray.bounded_inter_array_reuse_params;
  biarc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  biarc_mid_program : PolIRs.PolyLang.t;
}.

Definition bounded_inter_array_reuse_pair_certificate
    (certificate: bounded_inter_array_reuse_certificate)
    : View.checked_parameterized_family_pair_certificate
        inter_array_reuse_family scalar_promotion_family := {|
  View.cpfpc_first_params := biarc_reuse_params certificate;
  View.cpfpc_second_params := biarc_promotion_params certificate;
  View.cpfpc_mid_program := biarc_mid_program certificate;
|}.

Definition bounded_inter_array_reuse_certificate_input_view
    (certificate: bounded_inter_array_reuse_certificate) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (biarc_promotion_params certificate))
    (InterArray.bounded_inter_array_reuse_input_view
      (biarc_reuse_params certificate)).

Definition bounded_inter_array_reuse_certificate_output_view
    (certificate: bounded_inter_array_reuse_certificate) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (biarc_promotion_params certificate))
    (InterArray.bounded_inter_array_reuse_output_view
      (biarc_reuse_params certificate)).

Definition bounded_inter_array_reuse_certificate_input_states_match
    (certificate: bounded_inter_array_reuse_certificate) :=
  View.states_match
    (bounded_inter_array_reuse_certificate_input_view certificate).

Definition bounded_inter_array_reuse_certificate_output_states_match
    (certificate: bounded_inter_array_reuse_certificate) :=
  View.states_match
    (bounded_inter_array_reuse_certificate_output_view certificate).

Definition bounded_inter_array_reuse_certificate_accepted
    (certificate: bounded_inter_array_reuse_certificate)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_inter_array_reuse_pair_certificate certificate)
    before after.

Record bounded_conflict_reuse_certificate (value: Type) := {
  bcrc_reuse_params :
    Conflict.bounded_compatible_live_conflict_reuse_value_params value;
  bcrc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  bcrc_mid_program : PolIRs.PolyLang.t;
}.

Arguments bcrc_reuse_params {value} _.
Arguments bcrc_promotion_params {value} _.
Arguments bcrc_mid_program {value} _.

Definition bounded_conflict_reuse_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_conflict_reuse_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (conflict_reuse_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := bcrc_reuse_params certificate;
  View.cpfpc_second_params := bcrc_promotion_params certificate;
  View.cpfpc_mid_program := bcrc_mid_program certificate;
|}.

Definition bounded_conflict_reuse_certificate_input_view
    {value: Type}
    (certificate: bounded_conflict_reuse_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (bcrc_promotion_params certificate))
    (Conflict.bounded_compatible_live_conflict_reuse_value_input_view
      (bcrc_reuse_params certificate)).

Definition bounded_conflict_reuse_certificate_output_view
    {value: Type}
    (certificate: bounded_conflict_reuse_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (bcrc_promotion_params certificate))
    (Conflict.bounded_compatible_live_conflict_reuse_value_output_view
      (bcrc_reuse_params certificate)).

Definition bounded_conflict_reuse_certificate_input_states_match
    {value: Type}
    (certificate: bounded_conflict_reuse_certificate value) :=
  View.states_match
    (bounded_conflict_reuse_certificate_input_view certificate).

Definition bounded_conflict_reuse_certificate_output_states_match
    {value: Type}
    (certificate: bounded_conflict_reuse_certificate value) :=
  View.states_match
    (bounded_conflict_reuse_certificate_output_view certificate).

Definition bounded_conflict_reuse_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_conflict_reuse_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_conflict_reuse_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

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

Theorem accepted_bounded_inter_array_reuse_certificate_public_semantic_refinement :
  forall certificate before after,
    bounded_inter_array_reuse_certificate_accepted certificate before after ->
    View.public_semantic_refinement
      (bounded_inter_array_reuse_certificate_input_view certificate)
      (bounded_inter_array_reuse_certificate_output_view certificate)
      before after.
Proof.
  intros certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       inter_array_reuse_family
       scalar_promotion_family
       (bounded_inter_array_reuse_pair_certificate certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_inter_array_reuse_certificate_state_sound :
  forall certificate before after st_target0 st_source0 st_target_after,
    bounded_inter_array_reuse_certificate_accepted certificate before after ->
    View.state_view_rel
      (bounded_inter_array_reuse_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_inter_array_reuse_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros certificate before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       inter_array_reuse_family
       scalar_promotion_family
       (bounded_inter_array_reuse_pair_certificate certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_inter_array_reuse_certificate_semantic_refinement :
  forall certificate source target st_target0 st_source0 st_target_after,
    bounded_inter_array_reuse_certificate_accepted certificate source target ->
    bounded_inter_array_reuse_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_inter_array_reuse_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros certificate source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_inter_array_reuse_certificate_state_sound
       certificate source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
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

Theorem accepted_bounded_conflict_reuse_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_conflict_reuse_certificate value)
         before after,
    bounded_conflict_reuse_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_conflict_reuse_certificate_input_view certificate)
      (bounded_conflict_reuse_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       (conflict_reuse_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_conflict_reuse_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_conflict_reuse_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_conflict_reuse_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_conflict_reuse_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_conflict_reuse_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_conflict_reuse_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (conflict_reuse_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_conflict_reuse_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_conflict_reuse_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_conflict_reuse_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_conflict_reuse_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_conflict_reuse_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_conflict_reuse_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_conflict_reuse_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

End StorageReuseFamilyCompose.
