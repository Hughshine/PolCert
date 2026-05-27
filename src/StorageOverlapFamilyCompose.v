Require Import CInstrScalarPromotionValidatorBridge.
Require Import ImpureAlarmConfig.
Require Import OverlapTilingValidator.
Require Import PolIRs.

(** Composition witness for overlap/private-recomputation transformations.

    The overlap family is the instance-count-changing counterpart to the
    storage-only families: target instances may be duplicated or internal, while
    only commit-role behavior remains public.  Its family instance hides the
    projection, local-closure, value-equivalence, private-storage, bounds,
    compatibility, and non-escape obligations behind the same public-view
    interface used by scalar and copy-mediated storage passes. *)

Module StorageOverlapFamilyCompose (PolIRs: POLIRS).

Module Overlap := OverlapTilingValidator PolIRs.
Module Promotion := CInstrScalarPromotionValidatorBridge PolIRs.
Module View := Overlap.View.

Definition overlap_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (Overlap.overlap_private_ordered_bounded_non_escape_params value) :=
  Overlap.overlap_private_ordered_bounded_non_escape_family
    value value_eqb value_eqb_sound.

Definition scalar_promotion_family
    : View.checked_parameterized_view_transform_family
        Promotion.cscalar_promotion_bounded_params :=
  Promotion.cscalar_promotion_bounded_family.

Record bounded_overlap_certificate (value: Type) := {
  boc_overlap_params :
    Overlap.overlap_private_ordered_bounded_non_escape_params value;
  boc_promotion_params : Promotion.cscalar_promotion_bounded_params;
  boc_mid_program : PolIRs.PolyLang.t;
}.

Arguments boc_overlap_params {value} _.
Arguments boc_promotion_params {value} _.
Arguments boc_mid_program {value} _.

Definition bounded_overlap_pair_certificate
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_overlap_certificate value)
    : View.checked_parameterized_family_pair_certificate
        (overlap_family value value_eqb value_eqb_sound)
        scalar_promotion_family := {|
  View.cpfpc_first_params := boc_overlap_params certificate;
  View.cpfpc_second_params := boc_promotion_params certificate;
  View.cpfpc_mid_program := boc_mid_program certificate;
|}.

Definition bounded_overlap_certificate_input_view
    {value: Type}
    (certificate: bounded_overlap_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_input_view
      (boc_promotion_params certificate))
    (Overlap.overlap_private_ordered_bounded_non_escape_input_view
      (boc_overlap_params certificate)).

Definition bounded_overlap_certificate_output_view
    {value: Type}
    (certificate: bounded_overlap_certificate value) : View.view :=
  View.compose_view
    (Promotion.cscalar_promotion_bounded_output_view
      (boc_promotion_params certificate))
    (Overlap.overlap_private_ordered_bounded_non_escape_output_view
      (boc_overlap_params certificate)).

Definition bounded_overlap_certificate_input_states_match
    {value: Type}
    (certificate: bounded_overlap_certificate value) :=
  View.states_match (bounded_overlap_certificate_input_view certificate).

Definition bounded_overlap_certificate_output_states_match
    {value: Type}
    (certificate: bounded_overlap_certificate value) :=
  View.states_match (bounded_overlap_certificate_output_view certificate).

Definition bounded_overlap_semantic_refinement
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_overlap_certificate value)
    (source target: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_refinement
    (bounded_overlap_pair_certificate
      value value_eqb value_eqb_sound certificate)
    source target.

Definition bounded_overlap_certificate_accepted
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    (certificate: bounded_overlap_certificate value)
    (before after: PolIRs.PolyLang.t) : Prop :=
  View.checked_parameterized_family_pair_certificate_accepted
    (bounded_overlap_pair_certificate
      value value_eqb value_eqb_sound certificate)
    before after.

Theorem bounded_overlap_then_scalar_promotion_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (overlap_params:
           Overlap.overlap_private_ordered_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after overlap_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Overlap.overlap_private_ordered_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        overlap_params before mid)
      overlap_ok ->
    overlap_ok = true ->
    View.cpvtf_side_condition
      (Overlap.overlap_private_ordered_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      overlap_params before mid ->
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
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound overlap_params promotion_params
         before mid after overlap_ok promotion_ok
         Hoverlap_ret Hoverlap_ok Hoverlap_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_view_transform_family_pair_compose.
  - exact Hoverlap_ret.
  - exact Hoverlap_ok.
  - exact Hoverlap_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem bounded_overlap_then_scalar_promotion_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (overlap_params:
           Overlap.overlap_private_ordered_bounded_non_escape_params value)
         (promotion_params:
           Promotion.cscalar_promotion_bounded_params)
         before mid after overlap_ok promotion_ok,
    mayReturn
      (View.cpvtf_check
        (Overlap.overlap_private_ordered_bounded_non_escape_family
          value value_eqb value_eqb_sound)
        overlap_params before mid)
      overlap_ok ->
    overlap_ok = true ->
    View.cpvtf_side_condition
      (Overlap.overlap_private_ordered_bounded_non_escape_family
        value value_eqb value_eqb_sound)
      overlap_params before mid ->
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
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      (View.compose_view
        (View.cpvtf_output_view
          Promotion.cscalar_promotion_bounded_family
          promotion_params)
        (View.cpvtf_output_view
          (Overlap.overlap_private_ordered_bounded_non_escape_family
            value value_eqb value_eqb_sound)
          overlap_params))
      before after.
Proof.
  intros value value_eqb value_eqb_sound overlap_params promotion_params
         before mid after overlap_ok promotion_ok
         Hoverlap_ret Hoverlap_ok Hoverlap_side
         Hpromotion_ret Hpromotion_ok Hpromotion_side.
  eapply View.checked_parameterized_public_semantic_family_pair_compose.
  - exact Hoverlap_ret.
  - exact Hoverlap_ok.
  - exact Hoverlap_side.
  - exact Hpromotion_ret.
  - exact Hpromotion_ok.
  - exact Hpromotion_side.
Qed.

Theorem accepted_bounded_overlap_certificate_public_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_overlap_certificate value)
         before after,
    bounded_overlap_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.public_semantic_refinement
      (bounded_overlap_certificate_input_view certificate)
      (bounded_overlap_certificate_output_view certificate)
      before after.
Proof.
  intros value value_eqb value_eqb_sound certificate before after Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_public_semantic_sound
       _
       _
       (overlap_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_overlap_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after Haccepted).
Qed.

Theorem accepted_bounded_overlap_certificate_state_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_overlap_certificate value)
         before after st_target0 st_source0 st_target_after,
    bounded_overlap_certificate_accepted
      value value_eqb value_eqb_sound certificate before after ->
    View.state_view_rel
      (bounded_overlap_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      after st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        before st_source0 st_source_after /\
      View.state_view_rel
        (bounded_overlap_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (View.checked_parameterized_family_pair_certificate_state_sound
       _
       _
       (overlap_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_overlap_pair_certificate
          value value_eqb value_eqb_sound certificate)
       before after st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_overlap_certificate_semantic_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_overlap_certificate value)
         source target st_target0 st_source0 st_target_after,
    bounded_overlap_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_overlap_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolIRs.PolyLang.instance_list_semantics
      target st_target0 st_target_after ->
    exists st_source_after,
      PolIRs.PolyLang.instance_list_semantics
        source st_source0 st_source_after /\
      bounded_overlap_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  exact
    (accepted_bounded_overlap_certificate_state_sound
       value value_eqb value_eqb_sound certificate
       source target st_target0 st_source0 st_target_after
       Haccepted Hinput Htarget).
Qed.

Theorem accepted_bounded_overlap_certificate_refines :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         (certificate: bounded_overlap_certificate value)
         source target,
    bounded_overlap_certificate_accepted
      value value_eqb value_eqb_sound certificate source target ->
    bounded_overlap_semantic_refinement
      value value_eqb value_eqb_sound certificate source target.
Proof.
  intros value value_eqb value_eqb_sound certificate
         source target Haccepted.
  exact
    (View.checked_parameterized_family_pair_certificate_refines
       _
       _
       (overlap_family value value_eqb value_eqb_sound)
       scalar_promotion_family
       (bounded_overlap_pair_certificate
          value value_eqb value_eqb_sound certificate)
       source target Haccepted).
Qed.

End StorageOverlapFamilyCompose.
