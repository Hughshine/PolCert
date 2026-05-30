Require Import List.

Require Import CInstrScalarPromotionWitness.
Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import PrivateStorageWitness.
Require Import ScalarPromotionValidator.
Require Import ScalarPromotionValueWitness.
Require Import ScalarPromotionWitness.
Require Import StateView.
Require Import StorageBoundsWitness.
Require Import StorageCompatibilityWitness.
Require Import Values.

Import ListNotations.

(** Bridge from CInstr-derived scalar promotion traces to the view-level
    scalar-promotion wrappers.

    This keeps the top theorem shape in [ScalarPromotionValidator]: the result
    is still a [view_refinement].  The CInstr trace is used only to discharge
    the value-simulation side condition. *)

Module CInstrScalarPromotionValidatorBridge (PolIRs: POLIRS).

Module Scalar := ScalarPromotionValidator PolIRs.
Module View := Scalar.View.

Theorem cinstr_trace_scalar_promotion_value_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout value_trace
         public_cells frame_cells
         before source_view after ok,
    mayReturn
      (Scalar.check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout
      (scalar_promotion_value_trace_events value_trace) = true ->
    cscalar_promotion_value_trace_simulates value_trace ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    Scalar.promotion_source_view_refines_view
      input_view output_view source_view after ->
    Scalar.scalar_promotion_value_view_contract
      Values.val input_view output_view source_cell scalar_cell
      source_liveout
      (scalar_promotion_value_trace_events value_trace)
      value_trace public_cells frame_cells
      source_view after /\
    View.view_refinement
      input_view
      (Scalar.promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout value_trace
         public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Htrace Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout
       (scalar_promotion_value_trace_events value_trace)
       Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (cscalar_promotion_value_trace_obligations
       value_trace Htrace)
    as Hvalue_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Scalar.Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem cinstr_trace_scalar_promotion_compatible_value_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok,
    mayReturn
      (Scalar.check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout
      (scalar_promotion_value_trace_events value_trace) = true ->
    cscalar_promotion_value_trace_simulates value_trace ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    Scalar.promotion_source_view_refines_view
      input_view output_view source_view after ->
    Scalar.scalar_promotion_compatible_value_view_contract
      Values.val input_view output_view source_cell scalar_cell
      source_liveout
      (scalar_promotion_value_trace_events value_trace)
      value_trace logical_specs scalar_specs
      public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (Scalar.promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Htrace Hcompat Hseparation Hsemantics.
  pose proof
    (cinstr_trace_scalar_promotion_value_view_correct
       input_view output_view source_cell scalar_cell source_liveout
       value_trace public_cells frame_cells
       before source_view after ok
       Hret Hok Hpromotion Htrace Hseparation Hsemantics)
    as [Hbase Hview].
  pose proof
    (check_storage_compatibilityb_sound
       [(source_cell, scalar_cell)] logical_specs scalar_specs Hcompat)
    as Hcompat_obligations.
  destruct Hbase as
    [Hpromotion_obligations Hvalue_obligations
     Hseparation_obligations _Hsemantic_refinement].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem cinstr_trace_scalar_promotion_bounded_compatible_non_escape_value_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok,
    mayReturn
      (Scalar.check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout
      (scalar_promotion_value_trace_events value_trace) = true ->
    cscalar_promotion_value_trace_simulates value_trace ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_storage_boundsb source_bounds [source_cell] = true ->
    check_storage_boundsb scalar_bounds [scalar_cell] = true ->
    check_private_non_escapeb [scalar_cell] escaped_cells = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    Scalar.promotion_source_view_refines_view
      input_view output_view source_view after ->
    Scalar.scalar_promotion_bounded_compatible_non_escape_value_view_contract
      Values.val input_view output_view source_cell scalar_cell
      source_liveout
      (scalar_promotion_value_trace_events value_trace)
      value_trace logical_specs scalar_specs
      source_bounds scalar_bounds escaped_cells public_cells frame_cells
      source_view after /\
    View.view_refinement
      input_view
      (Scalar.promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Htrace Hcompat Hsource_bounds
         Hscalar_bounds Hnon_escape Hseparation Hsemantics.
  pose proof
    (cinstr_trace_scalar_promotion_compatible_value_view_correct
       input_view output_view source_cell scalar_cell source_liveout
       value_trace logical_specs scalar_specs public_cells frame_cells
       before source_view after ok
       Hret Hok Hpromotion Htrace Hcompat Hseparation Hsemantics)
    as [Hbase Hview].
  pose proof
    (check_storage_boundsb_sound
       source_bounds [source_cell] Hsource_bounds)
    as Hsource_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       scalar_bounds [scalar_cell] Hscalar_bounds)
    as Hscalar_bounds_obligations.
  pose proof
    (check_private_non_escapeb_sound
       [scalar_cell] escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

(** Public facade: the storage/value witness package is used only to justify the
    endpoint relation.  Downstream composition should consume this theorem shape
    rather than the feature-specific contract records above. *)

Theorem cinstr_trace_scalar_promotion_public_view_refinement :
  forall input_view output_view
         source_cell scalar_cell source_liveout value_trace
         public_cells frame_cells
         before source_view after ok,
    mayReturn
      (Scalar.check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout
      (scalar_promotion_value_trace_events value_trace) = true ->
    cscalar_promotion_value_trace_simulates value_trace ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    Scalar.promotion_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (Scalar.promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout value_trace
         public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Htrace Hseparation Hsemantics.
  pose proof
    (cinstr_trace_scalar_promotion_value_view_correct
       input_view output_view source_cell scalar_cell source_liveout
       value_trace public_cells frame_cells
       before source_view after ok
       Hret Hok Hpromotion Htrace Hseparation Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Theorem cinstr_trace_scalar_promotion_compatible_public_view_refinement :
  forall input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok,
    mayReturn
      (Scalar.check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout
      (scalar_promotion_value_trace_events value_trace) = true ->
    cscalar_promotion_value_trace_simulates value_trace ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    Scalar.promotion_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (Scalar.promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Htrace Hcompat Hseparation Hsemantics.
  pose proof
    (cinstr_trace_scalar_promotion_compatible_value_view_correct
       input_view output_view source_cell scalar_cell source_liveout
       value_trace logical_specs scalar_specs public_cells frame_cells
       before source_view after ok
       Hret Hok Hpromotion Htrace Hcompat Hseparation Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Theorem cinstr_trace_scalar_promotion_bounded_public_view_refinement :
  forall input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok,
    mayReturn
      (Scalar.check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout
      (scalar_promotion_value_trace_events value_trace) = true ->
    cscalar_promotion_value_trace_simulates value_trace ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_storage_boundsb source_bounds [source_cell] = true ->
    check_storage_boundsb scalar_bounds [scalar_cell] = true ->
    check_private_non_escapeb [scalar_cell] escaped_cells = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    Scalar.promotion_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (Scalar.promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Htrace Hcompat Hsource_bounds
         Hscalar_bounds Hnon_escape Hseparation Hsemantics.
  pose proof
    (cinstr_trace_scalar_promotion_bounded_compatible_non_escape_value_view_correct
       input_view output_view source_cell scalar_cell source_liveout
       value_trace logical_specs scalar_specs source_bounds scalar_bounds
       escaped_cells public_cells frame_cells before source_view after ok
       Hret Hok Hpromotion Htrace Hcompat Hsource_bounds Hscalar_bounds
       Hnon_escape Hseparation Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record cscalar_promotion_bounded_params := {
  cspmp_input_view : View.view;
  cspmp_output_view : View.view;
  cspmp_source_cell : MemCell;
  cspmp_scalar_cell : MemCell;
  cspmp_source_liveout : bool;
  cspmp_value_trace : scalar_promotion_value_trace Values.val;
  cspmp_logical_specs : list storage_spec;
  cspmp_scalar_specs : list storage_spec;
  cspmp_source_bounds : list array_bounds;
  cspmp_scalar_bounds : list array_bounds;
  cspmp_escaped_cells : list MemCell;
  cspmp_public_cells : list MemCell;
  cspmp_frame_cells : list MemCell;
  cspmp_source_view : Scalar.PolyLang.t;
}.

Definition cscalar_promotion_bounded_input_view
    (params: cscalar_promotion_bounded_params) : View.view :=
  cspmp_input_view params.

Definition cscalar_promotion_bounded_output_view
    (params: cscalar_promotion_bounded_params) : View.view :=
  Scalar.promotion_pipeline_final_view (cspmp_output_view params).

Definition cscalar_promotion_bounded_check
    (params: cscalar_promotion_bounded_params)
    (before after: Scalar.PolyLang.t) : imp bool :=
  Scalar.check_promotion_source_view before (cspmp_source_view params).

Definition cscalar_promotion_bounded_side_condition
    (params: cscalar_promotion_bounded_params)
    (before after: Scalar.PolyLang.t) : Prop :=
  check_scalar_promotionb
    (cspmp_source_cell params)
    (cspmp_scalar_cell params)
    (cspmp_source_liveout params)
    (scalar_promotion_value_trace_events (cspmp_value_trace params)) = true /\
  cscalar_promotion_value_trace_simulates (cspmp_value_trace params) /\
  check_storage_compatibilityb
    [(cspmp_source_cell params, cspmp_scalar_cell params)]
    (cspmp_logical_specs params)
    (cspmp_scalar_specs params) = true /\
  check_storage_boundsb
    (cspmp_source_bounds params)
    [cspmp_source_cell params] = true /\
  check_storage_boundsb
    (cspmp_scalar_bounds params)
    [cspmp_scalar_cell params] = true /\
  check_private_non_escapeb
    [cspmp_scalar_cell params]
    (cspmp_escaped_cells params) = true /\
  check_private_separationb
    [cspmp_scalar_cell params]
    (cspmp_public_cells params)
    (cspmp_frame_cells params) = true /\
  Scalar.promotion_source_view_refines_view
    (cspmp_input_view params)
    (cspmp_output_view params)
    (cspmp_source_view params)
    after.

Theorem cscalar_promotion_bounded_side_condition_trace_summary :
  forall params before after,
    cscalar_promotion_bounded_side_condition params before after ->
    scalar_value_simulation_obligations Values.val
      (cspmp_value_trace params) /\
    scalar_value_use_def_trace
      (scalar_promotion_value_trace_events
         (cspmp_value_trace params)).
Proof.
  intros params before after Hside.
  destruct Hside as [_ [Htrace _]].
  eapply cscalar_promotion_value_trace_sound_and_usedef.
  exact Htrace.
Qed.

Theorem cscalar_promotion_bounded_side_condition_contract :
  forall params before after,
    cscalar_promotion_bounded_side_condition params before after ->
    Scalar.scalar_promotion_bounded_compatible_non_escape_value_view_contract
      Values.val
      (cspmp_input_view params)
      (cspmp_output_view params)
      (cspmp_source_cell params)
      (cspmp_scalar_cell params)
      (cspmp_source_liveout params)
      (scalar_promotion_value_trace_events (cspmp_value_trace params))
      (cspmp_value_trace params)
      (cspmp_logical_specs params)
      (cspmp_scalar_specs params)
      (cspmp_source_bounds params)
      (cspmp_scalar_bounds params)
      (cspmp_escaped_cells params)
      (cspmp_public_cells params)
      (cspmp_frame_cells params)
      (cspmp_source_view params)
      after.
Proof.
  intros
    [input_view output_view source_cell scalar_cell source_liveout value_trace
     logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
     public_cells frame_cells source_view]
    before after Hside.
  simpl in *.
  destruct Hside as
    [Hpromotion
     [Htrace
      [Hcompat
       [Hsource_bounds
        [Hscalar_bounds
         [Hnon_escape [Hseparation Hsemantics]]]]]]].
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout
       (scalar_promotion_value_trace_events value_trace)
       Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (cscalar_promotion_value_trace_obligations
       value_trace Htrace)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       [(source_cell, scalar_cell)] logical_specs scalar_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_storage_boundsb_sound
       source_bounds [source_cell] Hsource_bounds)
    as Hsource_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       scalar_bounds [scalar_cell] Hscalar_bounds)
    as Hscalar_bounds_obligations.
  pose proof
    (check_private_non_escapeb_sound
       [scalar_cell] escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  constructor.
  - constructor.
    + exact Hpromotion_obligations.
    + exact Hvalue_obligations.
    + exact Hseparation_obligations.
    + exact Hcompat_obligations.
    + exact Hsemantics.
  - exact Hsource_bounds_obligations.
  - exact Hscalar_bounds_obligations.
  - exact Hnon_escape_obligations.
Qed.

Theorem cscalar_promotion_bounded_family_sound :
  forall params before after ok,
    mayReturn
      (cscalar_promotion_bounded_check params before after) ok ->
    ok = true ->
    cscalar_promotion_bounded_side_condition params before after ->
    View.view_refinement
      (cscalar_promotion_bounded_input_view params)
      (cscalar_promotion_bounded_output_view params)
      before after.
Proof.
  intros params before after ok Hret Hok Hside.
  destruct params as
    [input_view output_view source_cell scalar_cell source_liveout value_trace
     logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
     public_cells frame_cells source_view].
  simpl in *.
  destruct Hside as
    [Hpromotion
     [Htrace
      [Hcompat
       [Hsource_bounds
        [Hscalar_bounds
         [Hnon_escape [Hseparation Hsemantics]]]]]]].
  eapply cinstr_trace_scalar_promotion_bounded_public_view_refinement; eauto.
Qed.

Definition cscalar_promotion_bounded_family
    : View.checked_parameterized_view_transform_family
        cscalar_promotion_bounded_params := {|
  generic_cpvtf_input_view :=
    cscalar_promotion_bounded_input_view;
  generic_cpvtf_output_view :=
    cscalar_promotion_bounded_output_view;
  generic_cpvtf_check :=
    cscalar_promotion_bounded_check;
  generic_cpvtf_side_condition :=
    cscalar_promotion_bounded_side_condition;
  generic_cpvtf_check_sound :=
    cscalar_promotion_bounded_family_sound;
|}.

End CInstrScalarPromotionValidatorBridge.
