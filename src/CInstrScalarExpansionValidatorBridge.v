Require Import Bool.
Require Import List.

Require Import CInstrScalarExpansionWitness.
Require Import InstanceProjectionWitness.
Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import PrivateStorageWitness.
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

Definition check_scalar_privatization_static_coreb
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry) : bool :=
  mem_cells_subsetb private_cells hidden_cells &&
  mem_cells_subsetb (scalar_expansion_source_cells entries) hidden_cells &&
  logical_instances_subsetb
    (scalar_expansion_instances entries) source_domain &&
  mem_cells_subsetb
    (scalar_expansion_source_cells entries) source_cells &&
  mem_cells_subsetb
    (scalar_expansion_private_cells entries) private_cells &&
  scalar_expansion_keys_nodupb (scalar_expansion_entry_keys entries) &&
  mem_cells_nodupb (scalar_expansion_private_cells entries).

Lemma check_scalar_privatization_static_coreb_sound :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace,
    check_scalar_privatization_static_coreb
      hidden_cells private_cells source_domain source_cells entries = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Scalar.scalar_privatization_core_obligations
      hidden_cells private_cells source_domain source_cells entries
      (scalar_expansion_value_trace_events value_trace).
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace Hcheck Htrace.
  unfold check_scalar_privatization_static_coreb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hprivate_unique].
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hkeys].
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hprivates].
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hsources].
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hinstances].
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hprivate_hidden Hsource_hidden].
  constructor.
  - constructor.
    + intros instance Hin.
      eapply logical_instances_subsetb_sound; eauto.
    + intros source_cell Hin.
      eapply mem_cells_subsetb_sound; eauto.
    + intros private_cell Hin.
      eapply mem_cells_subsetb_sound; eauto.
    + apply scalar_expansion_keys_nodupb_sound.
      exact Hkeys.
    + apply mem_cells_nodupb_sound.
      exact Hprivate_unique.
    + unfold cscalar_expansion_value_trace_simulates in Htrace.
      eapply cscalar_expansion_value_trace_events_mapped.
      exact Htrace.
    + eapply cscalar_expansion_value_trace_private_use_def.
      exact Htrace.
  - apply Witness.private_cells_hidden_sound.
    exact Hsource_hidden.
  - apply Witness.private_cells_hidden_sound.
    exact Hprivate_hidden.
Qed.

Theorem cinstr_trace_static_pure_scalar_privatization_value_events_correct :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_scalar_privatization_static_coreb
      hidden_cells private_cells source_domain source_cells entries = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.scalar_privatization_value_core_obligations
      Values.val hidden_cells private_cells source_domain source_cells
      entries (scalar_expansion_value_trace_events value_trace)
      value_trace /\
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok
         Hret Hok Hstatic Htrace Hprivate.
  pose proof
    (check_scalar_privatization_static_coreb_sound
       hidden_cells private_cells source_domain source_cells entries
       value_trace Hstatic Htrace)
    as Hcore.
  pose proof
    (cscalar_expansion_value_trace_obligations
       entries value_trace Htrace)
    as Hvalue_obligations.
  unfold check_scalar_privatization_static_coreb in Hstatic.
  apply andb_true_iff in Hstatic.
  destruct Hstatic as [Hstatic _Hprivate_unique].
  apply andb_true_iff in Hstatic.
  destruct Hstatic as [Hstatic _Hkeys].
  apply andb_true_iff in Hstatic.
  destruct Hstatic as [Hstatic _Hprivates].
  apply andb_true_iff in Hstatic.
  destruct Hstatic as [Hstatic _Hsources].
  apply andb_true_iff in Hstatic.
  destruct Hstatic as [Hstatic _Hinstances].
  apply andb_true_iff in Hstatic.
  destruct Hstatic as [Hprivate_hidden _Hsource_hidden].
  pose proof
    (Private.checked_hidden_private_expansion_view_correct
       hidden_cells private_cells before source_view after ok
       Hret Hok Hprivate_hidden Hprivate)
    as Hview.
  split.
  - constructor.
    + exact Hcore.
    + exact Hvalue_obligations.
    + reflexivity.
  - unfold Scalar.pure_scalar_privatization_refinement,
           Scalar.pure_scalar_privatization_view,
           Scalar.pure_scalar_privatization_final_view.
    exact Hview.
Qed.

Definition check_bounded_scalar_privatization_static_coreb
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (private_bounds: list array_bounds)
    (source_specs private_specs: list storage_spec)
    (escaped_cells: list MemCell) : bool :=
  check_scalar_privatization_static_coreb
    hidden_cells private_cells source_domain source_cells entries &&
  check_storage_boundsb private_bounds private_cells &&
  check_storage_compatibilityb
    (Scalar.scalar_expansion_storage_mapping entries)
    source_specs private_specs &&
  check_private_non_escapeb private_cells escaped_cells.

Theorem cinstr_trace_static_bounded_pure_scalar_privatization_value_events_correct :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_bounded_scalar_privatization_static_coreb
      hidden_cells private_cells source_domain source_cells entries
      private_bounds source_specs private_specs escaped_cells = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.bounded_value_pure_scalar_privatization_obligations
      Values.val hidden_cells private_cells source_domain source_cells
      entries (scalar_expansion_value_trace_events value_trace)
      value_trace private_bounds source_specs private_specs
      escaped_cells /\
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok
         Hret Hok Hcheck Htrace Hprivate.
  unfold check_bounded_scalar_privatization_static_coreb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hstatic & Hbounds) & Hcompatible) & Hnon_escape).
  pose proof
    (cinstr_trace_static_pure_scalar_privatization_value_events_correct
       hidden_cells private_cells source_domain source_cells entries
       value_trace before source_view after ok
       Hret Hok Hstatic Htrace Hprivate)
    as [Hvalue_core Hview].
  pose proof
    (check_storage_boundsb_sound
       private_bounds private_cells Hbounds)
    as Hbounds_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       (Scalar.scalar_expansion_storage_mapping entries)
       source_specs private_specs Hcompatible)
    as Hcompatible_obligations.
  pose proof
    (check_private_non_escapeb_sound
       private_cells escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  split.
  - constructor.
    + exact Hvalue_core.
    + exact Hbounds_obligations.
    + exact Hcompatible_obligations.
    + exact Hnon_escape_obligations.
  - exact Hview.
Qed.

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

Theorem cinstr_trace_pure_scalar_privatization_value_events_correct :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    Scalar.check_scalar_privatization_coreb
      hidden_cells private_cells source_domain source_cells entries
      (scalar_expansion_value_trace_events value_trace) = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.scalar_privatization_value_core_obligations
      Values.val hidden_cells private_cells source_domain source_cells
      entries (scalar_expansion_value_trace_events value_trace)
      value_trace /\
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok
         Hret Hok Hcore Htrace Hprivate.
  eapply cinstr_trace_pure_scalar_privatization_value_correct.
  - exact Hret.
  - exact Hok.
  - exact Hcore.
  - exact Htrace.
  - reflexivity.
  - exact Hprivate.
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

Theorem cinstr_trace_bounded_pure_scalar_privatization_value_events_correct :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    Scalar.check_bounded_pure_scalar_privatizationb
      hidden_cells private_cells source_domain source_cells entries
      (scalar_expansion_value_trace_events value_trace)
      private_bounds source_specs private_specs escaped_cells = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.bounded_value_pure_scalar_privatization_obligations
      Values.val hidden_cells private_cells source_domain source_cells
      entries (scalar_expansion_value_trace_events value_trace)
      value_trace private_bounds source_specs private_specs
      escaped_cells /\
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok
         Hret Hok Hbounded Htrace Hprivate.
  eapply cinstr_trace_bounded_pure_scalar_privatization_value_correct.
  - exact Hret.
  - exact Hok.
  - exact Hbounded.
  - exact Htrace.
  - reflexivity.
  - exact Hprivate.
Qed.

(** Public facade: CInstr traces and scalar-expansion contracts are proof
    ingredients.  The compositional endpoint is only the public-view refinement
    that hides the source temporary cells and the generated private cells. *)

Theorem cinstr_trace_static_pure_scalar_privatization_public_refinement :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_scalar_privatization_static_coreb
      hidden_cells private_cells source_domain source_cells entries = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok
         Hret Hok Hstatic Htrace Hprivate.
  pose proof
    (cinstr_trace_static_pure_scalar_privatization_value_events_correct
       hidden_cells private_cells source_domain source_cells entries
       value_trace before source_view after ok
       Hret Hok Hstatic Htrace Hprivate)
    as [_ Hview].
  exact Hview.
Qed.

Theorem cinstr_trace_static_bounded_pure_scalar_privatization_public_refinement :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_bounded_scalar_privatization_static_coreb
      hidden_cells private_cells source_domain source_cells entries
      private_bounds source_specs private_specs escaped_cells = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok
         Hret Hok Hbounded Htrace Hprivate.
  pose proof
    (cinstr_trace_static_bounded_pure_scalar_privatization_value_events_correct
       hidden_cells private_cells source_domain source_cells entries
       value_trace private_bounds source_specs private_specs escaped_cells
       before source_view after ok
       Hret Hok Hbounded Htrace Hprivate)
    as [_ Hview].
  exact Hview.
Qed.

Theorem cinstr_trace_pure_scalar_privatization_public_refinement :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    Scalar.check_scalar_privatization_coreb
      hidden_cells private_cells source_domain source_cells entries
      (scalar_expansion_value_trace_events value_trace) = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace before source_view after ok
         Hret Hok Hcore Htrace Hprivate.
  pose proof
    (cinstr_trace_pure_scalar_privatization_value_events_correct
       hidden_cells private_cells source_domain source_cells entries
       value_trace before source_view after ok
       Hret Hok Hcore Htrace Hprivate)
    as [_ Hview].
  exact Hview.
Qed.

Theorem cinstr_trace_bounded_pure_scalar_privatization_public_refinement :
  forall hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    Scalar.check_bounded_pure_scalar_privatizationb
      hidden_cells private_cells source_domain source_cells entries
      (scalar_expansion_value_trace_events value_trace)
      private_bounds source_specs private_specs escaped_cells = true ->
    cscalar_expansion_value_trace_simulates entries value_trace ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Scalar.pure_scalar_privatization_refinement
      hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries
         value_trace private_bounds source_specs private_specs escaped_cells
         before source_view after ok
         Hret Hok Hbounded Htrace Hprivate.
  pose proof
    (cinstr_trace_bounded_pure_scalar_privatization_value_events_correct
       hidden_cells private_cells source_domain source_cells entries
       value_trace private_bounds source_specs private_specs escaped_cells
       before source_view after ok
       Hret Hok Hbounded Htrace Hprivate)
    as [_ Hview].
  exact Hview.
Qed.

End CInstrScalarExpansionValidatorBridge.
