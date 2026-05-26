Require Import List.

Require Import CInstrScalarExpansionWitness.
Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import ScalarExpansionValidator.
Require Import ScalarExpansionValueWitness.
Require Import ScalarExpansionWitness.
Require Import StateObservation.
Require Import StorageBoundsWitness.
Require Import StorageCompatibilityWitness.
Require Import Values.

Import ListNotations.

(** Bridge from CInstr-derived scalar expansion traces to the view-level
    scalar privatization wrapper.

    [CInstrScalarExpansionWitness] proves that ordered CInstr read/write
    witnesses discharge the generic scalar-expansion value-flow obligation.
    [ScalarExpansionValidator] packages storage bookkeeping and public-view
    erasure into the top-level scalar-privatization theorem shape.  This file
    connects the two without making the final theorem expose the CInstr trace:
    the trace is one semantic side condition used to build the value-core
    obligations. *)

Module CInstrScalarExpansionValidatorBridge
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Scalar := ScalarExpansionValidator PolIRs Observer.
Module Private := Scalar.Private.
Module Witness := Scalar.Witness.
Module View := Scalar.View.

Theorem cinstr_trace_pure_scalar_privatization_value_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         value_trace before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    Scalar.check_scalar_privatization_coreb
      hidden_cells private_cells source_domain source_cells entries events =
    true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    scalar_expansion_value_trace_events value_trace = events ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.scalar_privatization_value_core_obligations
      Values.val hidden_cells private_cells source_domain source_cells
      entries events value_trace /\
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         value_trace before source_view after ok
         Hret Hok Hcore Htrace Hevents Hprivate.
  pose proof
    (Scalar.check_scalar_privatization_coreb_sound
       hidden_cells private_cells source_domain source_cells entries events
       Hcore)
    as Hcore_obligations.
  pose proof
    (cscalar_expansion_value_trace_obligations
       entries value_trace Htrace)
    as Hvalue_obligations.
  pose proof
    (Scalar.checked_pure_scalar_privatization_correct
       hidden_cells private_cells source_domain source_cells entries events
       before source_view after ok Hret Hok Hcore Hprivate)
    as [_ Hview].
  split.
  - constructor.
    + exact Hcore_obligations.
    + exact Hvalue_obligations.
    + exact Hevents.
  - exact Hview.
Qed.

Theorem cinstr_trace_bounded_pure_scalar_privatization_value_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    Scalar.check_bounded_pure_scalar_privatizationb
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    scalar_expansion_value_trace_events value_trace = events ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.bounded_value_pure_scalar_privatization_obligations
      Values.val hidden_cells private_cells source_domain source_cells
      entries events value_trace private_bounds source_specs private_specs
      escaped_cells /\
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok
         Hret Hok Hbounded Htrace Hevents Hprivate.
  pose proof
    (Scalar.check_bounded_pure_scalar_privatizationb_sound
       hidden_cells private_cells source_domain source_cells entries events
       private_bounds source_specs private_specs escaped_cells Hbounded)
    as Hbounded_obligations.
  pose proof
    (Scalar.checked_bounded_pure_scalar_privatization_correct
       hidden_cells private_cells source_domain source_cells entries events
       private_bounds source_specs private_specs escaped_cells
       before source_view after ok Hret Hok Hbounded Hprivate)
    as [_ Hview].
  destruct Hbounded_obligations as
    [Hcore_obligations Hbounds Hcompatible Hnon_escape].
  pose proof
    (cscalar_expansion_value_trace_obligations
       entries value_trace Htrace)
    as Hvalue_obligations.
  split.
  - constructor.
    + constructor.
      * exact Hcore_obligations.
      * exact Hvalue_obligations.
      * exact Hevents.
    + exact Hbounds.
    + exact Hcompatible.
    + exact Hnon_escape.
  - exact Hview.
Qed.

End CInstrScalarExpansionValidatorBridge.
