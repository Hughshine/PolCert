Require Import CInstrScalarExpansionValidatorBridge.
Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import PrivateStorageWitness.
Require Import ScalarExpansionValueWitness.
Require Import ScalarExpansionWitness.
Require Import ScalarPromotionValueWitness.
Require Import StateObservation.
Require Import Values.

(** Composition witness for concrete CInstr scalar-storage families.

    This theorem composes two parameterized public-refinement family instances:
    bounded scalar privatization followed by bounded scalar promotion.  It
    deliberately exposes only composed public views, not the internal
    scalar-expansion or promotion contract records. *)

Module CInstrScalarStorageFamilyCompose
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Expansion := CInstrScalarExpansionValidatorBridge PolIRs Observer.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Expansion.View.

Record bounded_cinstr_scalar_storage_certificate := {
  bcssc_privatization_params :
    Expansion.cscalar_privatization_bounded_params;
  bcssc_promotion_params :
    Promotion.cscalar_promotion_bounded_params;
  bcssc_mid_program : PolIRs.PolyLang.t;
}.

Definition bounded_cinstr_scalar_storage_pair_certificate
    (certificate: bounded_cinstr_scalar_storage_certificate)
    : View.checked_parameterized_family_pair_certificate
        Expansion.cscalar_privatization_bounded_family
        Promotion.cscalar_promotion_bounded_family := {|
  View.cpfpc_first_params := bcssc_privatization_params certificate;
  View.cpfpc_second_params := bcssc_promotion_params certificate;
  View.cpfpc_mid_program := bcssc_mid_program certificate;
|}.

Definition bounded_cinstr_scalar_storage_certificate_input_view
    (certificate: bounded_cinstr_scalar_storage_certificate)
    : View.view :=
  View.checked_parameterized_family_pair_certificate_input_view
    (bounded_cinstr_scalar_storage_pair_certificate certificate).

Definition bounded_cinstr_scalar_storage_certificate_output_view
    (certificate: bounded_cinstr_scalar_storage_certificate)
    : View.view :=
  View.checked_parameterized_family_pair_certificate_output_view
    (bounded_cinstr_scalar_storage_pair_certificate certificate).

Definition bounded_cinstr_scalar_storage_certificate_input_states_match
    (certificate: bounded_cinstr_scalar_storage_certificate) :=
  View.states_match
    (bounded_cinstr_scalar_storage_certificate_input_view certificate).

Definition bounded_cinstr_scalar_storage_certificate_output_states_match
    (certificate: bounded_cinstr_scalar_storage_certificate) :=
  View.states_match
    (bounded_cinstr_scalar_storage_certificate_output_view certificate).

(** Certificate-level semantic facade.

    This is the CInstr scalar-storage analogue of the old semantic refinement
    endpoint, with [State.eq] generalized to certificate-defined input and
    output state views.  The internal two-pass decomposition and intermediate
    program are fields of the certificate, not part of the theorem surface. *)
Definition bounded_cinstr_scalar_storage_semantic_refinement
    (certificate: bounded_cinstr_scalar_storage_certificate)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_refinement
    (bounded_cinstr_scalar_storage_pair_certificate certificate)
    source target.

Definition bounded_cinstr_scalar_storage_certificate_accepted
    (certificate: bounded_cinstr_scalar_storage_certificate)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_cinstr_scalar_storage_pair_certificate certificate)
    before after.

Theorem accepted_bounded_cinstr_scalar_storage_certificate_privatization_trace_summary :
  forall certificate before after,
    bounded_cinstr_scalar_storage_certificate_accepted
      certificate before after ->
    scalar_expansion_value_obligations Values.val
      (Expansion.cspbp_value_trace
         (bcssc_privatization_params certificate)) /\
    scalar_expansion_events_mapped
      (Expansion.cspbp_entries
         (bcssc_privatization_params certificate))
      (scalar_expansion_value_trace_events
         (Expansion.cspbp_value_trace
            (bcssc_privatization_params certificate))) /\
    private_use_def_trace
      (scalar_expansion_private_trace
         (scalar_expansion_value_trace_events
            (Expansion.cspbp_value_trace
               (bcssc_privatization_params certificate)))).
Proof.
  intros certificate before after Haccepted.
  unfold bounded_cinstr_scalar_storage_certificate_accepted in Haccepted.
  unfold bounded_cinstr_scalar_storage_pair_certificate in Haccepted.
  destruct Haccepted as
    [privatization_ok
      [promotion_ok
        [_Hpriv_ret [_Hpriv_ok [Hpriv_side _Hpromotion]]]]].
  exact
    (Expansion.cscalar_privatization_bounded_side_condition_trace_summary
       (bcssc_privatization_params certificate)
       before (bcssc_mid_program certificate)
       Hpriv_side).
Qed.

Theorem accepted_bounded_cinstr_scalar_storage_certificate_promotion_trace_summary :
  forall certificate before after,
    bounded_cinstr_scalar_storage_certificate_accepted
      certificate before after ->
    scalar_value_simulation_obligations Values.val
      (Promotion.cspmp_value_trace
         (bcssc_promotion_params certificate)) /\
    scalar_value_use_def_trace
      (scalar_promotion_value_trace_events
         (Promotion.cspmp_value_trace
            (bcssc_promotion_params certificate))).
Proof.
  intros certificate before after Haccepted.
  unfold bounded_cinstr_scalar_storage_certificate_accepted in Haccepted.
  unfold bounded_cinstr_scalar_storage_pair_certificate in Haccepted.
  destruct Haccepted as
    [privatization_ok
      [promotion_ok
        [_Hpriv_ret
          [_Hpriv_ok
            [_Hpriv_side
              [_Hpromotion_ret
                [_Hpromotion_ok Hpromotion_side]]]]]]].
  exact
    (Promotion.cscalar_promotion_bounded_side_condition_trace_summary
       (bcssc_promotion_params certificate)
       (bcssc_mid_program certificate) after
       Hpromotion_side).
Qed.

Theorem bounded_privatization_then_promotion_public_refinement :
  forall (privatization_params:
            Expansion.cscalar_privatization_bounded_params)
         (promotion_params:
            Promotion.cscalar_promotion_bounded_params)
         before mid after privatization_ok promotion_ok,
    mayReturn
      (Expansion.cscalar_privatization_bounded_check
        privatization_params before mid)
      privatization_ok ->
    privatization_ok = true ->
    Expansion.cscalar_privatization_bounded_side_condition
      privatization_params before mid ->
    mayReturn
      (Promotion.cscalar_promotion_bounded_check
        promotion_params mid after)
      promotion_ok ->
    promotion_ok = true ->
    Promotion.cscalar_promotion_bounded_side_condition
      promotion_params mid after ->
    View.view_refinement
      (View.compose_view
        (View.cpvtf_input_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_input_view
          Expansion.cscalar_privatization_bounded_family
          privatization_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          Expansion.cscalar_privatization_bounded_family
          privatization_params))
      before after.
Proof.
  intros privatization_params promotion_params before mid after
         privatization_ok promotion_ok
         Hpriv_ret Hpriv_ok Hpriv_side
         Hpromo_ret Hpromo_ok Hpromo_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hpriv_ret.
  - exact Hpriv_ok.
  - exact Hpriv_side.
  - exact Hpromo_ret.
  - exact Hpromo_ok.
  - exact Hpromo_side.
Qed.

Theorem bounded_privatization_then_promotion_public_semantic_refinement :
  forall (privatization_params:
            Expansion.cscalar_privatization_bounded_params)
         (promotion_params:
            Promotion.cscalar_promotion_bounded_params)
         before mid after privatization_ok promotion_ok,
    mayReturn
      (Expansion.cscalar_privatization_bounded_check
        privatization_params before mid)
      privatization_ok ->
    privatization_ok = true ->
    Expansion.cscalar_privatization_bounded_side_condition
      privatization_params before mid ->
    mayReturn
      (Promotion.cscalar_promotion_bounded_check
        promotion_params mid after)
      promotion_ok ->
    promotion_ok = true ->
    Promotion.cscalar_promotion_bounded_side_condition
      promotion_params mid after ->
    View.public_semantic_refinement
      (View.compose_view
        (View.cpvtf_input_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_input_view
          Expansion.cscalar_privatization_bounded_family
          privatization_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          Expansion.cscalar_privatization_bounded_family
          privatization_params))
      before after.
Proof.
  intros privatization_params promotion_params before mid after
         privatization_ok promotion_ok
         Hpriv_ret Hpriv_ok Hpriv_side
         Hpromo_ret Hpromo_ok Hpromo_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hpriv_ret.
  - exact Hpriv_ok.
  - exact Hpriv_side.
  - exact Hpromo_ret.
  - exact Hpromo_ok.
  - exact Hpromo_side.
Qed.

Theorem accepted_bounded_cinstr_scalar_storage_certificate_public_semantic_refinement :
  forall certificate before after,
    bounded_cinstr_scalar_storage_certificate_accepted
      certificate before after ->
    View.public_semantic_refinement
      (bounded_cinstr_scalar_storage_certificate_input_view certificate)
      (bounded_cinstr_scalar_storage_certificate_output_view certificate)
      before after.
Proof.
  intros certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       Expansion.cscalar_privatization_bounded_family
       Promotion.cscalar_promotion_bounded_family
       (bounded_cinstr_scalar_storage_pair_certificate certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_cinstr_scalar_storage_certificate_state_sound :
  forall certificate before after st_target0 st_source0 st_target_after,
    bounded_cinstr_scalar_storage_certificate_accepted
      certificate before after ->
    View.state_view_rel
      (bounded_cinstr_scalar_storage_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_cinstr_scalar_storage_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros certificate before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       Expansion.cscalar_privatization_bounded_family
       Promotion.cscalar_promotion_bounded_family
       (bounded_cinstr_scalar_storage_pair_certificate certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_cinstr_scalar_storage_certificate_refines :
  forall certificate source target,
    bounded_cinstr_scalar_storage_certificate_accepted
      certificate source target ->
    bounded_cinstr_scalar_storage_semantic_refinement
      certificate source target.
Proof.
  intros certificate source target Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_refines
       _
       _
       Expansion.cscalar_privatization_bounded_family
       Promotion.cscalar_promotion_bounded_family
       (bounded_cinstr_scalar_storage_pair_certificate certificate)
       source target Haccepted).
Qed.

Theorem accepted_bounded_cinstr_scalar_storage_certificate_semantic_refinement :
  forall certificate source target st_target0 st_source0 st_target_after,
    bounded_cinstr_scalar_storage_certificate_accepted
      certificate source target ->
    bounded_cinstr_scalar_storage_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_cinstr_scalar_storage_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros certificate source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_cinstr_scalar_storage_certificate_state_sound
       certificate source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

End CInstrScalarStorageFamilyCompose.
