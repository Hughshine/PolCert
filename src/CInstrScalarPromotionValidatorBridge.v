Require Import List.

Require Import CInstrScalarPromotionWitness.
Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import PrivateStorageWitness.
Require Import ScalarPromotionValidator.
Require Import ScalarPromotionValueWitness.
Require Import ScalarPromotionWitness.
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

End CInstrScalarPromotionValidatorBridge.
