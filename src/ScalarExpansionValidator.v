Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import StateObservation.
Require Import PrivateStorageWitness.
Require Import PrivateStorageValidator.
Require Import InstanceProjectionWitness.
Require Import ScalarExpansionWitness.
Require Import ScalarExpansionValueWitness.
Require Import ReuseConflictWitness.
Require Import StorageBoundsWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for scalar privatization / expansion.

    [ScalarExpansionWitness] checks the finite renaming layer: dynamic
    [(source instance, source scalar cell)] keys select target-private cells,
    events use those selections consistently, and the resulting private trace
    is write-before-read.  This module connects that finite layer to the common
    private-erasure theorem shape already used by [PrivateStorageValidator].

    The checker still does not prove expression-level value simulation.  The
    caller supplies the same semantic refinement hypothesis required by the
    private-storage validator. *)

Module ScalarExpansionValidator
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Private := PrivateStorageValidator PolIRs Observer.
Module Witness := Private.Witness.
Module View := Private.View.

Definition pure_scalar_privatization_view
    (hidden_cells: list MemCell) : View.view :=
  Private.private_erasure_view
    (Witness.hidden_identity_cell_view hidden_cells).

Definition pure_scalar_privatization_final_view
    (hidden_cells: list MemCell) : View.view :=
  Private.private_pipeline_final_view
    (Witness.hidden_identity_cell_view hidden_cells).

Definition pure_scalar_privatization_refinement
    (hidden_cells: list MemCell)
    (before after: Private.PolyLang.t) : Prop :=
  View.view_refinement
    (pure_scalar_privatization_view hidden_cells)
    (pure_scalar_privatization_final_view hidden_cells)
    before after.

Fixpoint scalar_expansion_storage_mapping
    (entries: list scalar_expansion_entry) : reuse_mapping :=
  match entries with
  | [] => []
  | entry :: tail =>
      (expansion_source_cell entry, expansion_private_cell entry) ::
      scalar_expansion_storage_mapping tail
  end.

Lemma scalar_expansion_entry_in_storage_mapping :
  forall entries entry,
    In entry entries ->
    In (expansion_source_cell entry, expansion_private_cell entry)
       (scalar_expansion_storage_mapping entries).
Proof.
  induction entries as [|head tail IH]; intros entry Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst. left. reflexivity.
    + right. apply IH. exact Hin_tail.
Qed.

Record scalar_expansion_view_contract
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event)
    (source_view after: Private.PolyLang.t) : Prop := {
  sevc_scalar_expansion :
    scalar_expansion_obligations
      source_domain source_cells private_cells entries events;
  sevc_source_hidden :
    Witness.private_cells_hidden
      (scalar_expansion_source_cells entries) hidden_cells;
  sevc_private_hidden :
    Witness.private_cells_hidden private_cells hidden_cells;
  sevc_semantic_refinement :
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after;
}.

Record scalar_expansion_bounded_compatible_non_escape_view_contract
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event)
    (private_bounds: list array_bounds)
    (source_specs private_specs: list storage_spec)
    (escaped_cells: list MemCell)
    (source_view after: Private.PolyLang.t) : Prop := {
  sebcnevvc_base :
    scalar_expansion_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      source_view after;
  sebcnevvc_private_bounds :
    storage_bounds_obligations private_bounds private_cells;
  sebcnevvc_storage_compatible :
    storage_compatibility_obligations
      (scalar_expansion_storage_mapping entries)
      source_specs private_specs;
  sebcnevvc_non_escape :
    private_non_escape_obligations private_cells escaped_cells;
}.

Record scalar_privatization_core_obligations
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event) : Prop := {
  spco_scalar_expansion :
    scalar_expansion_obligations
      source_domain source_cells private_cells entries events;
  spco_source_hidden :
    Witness.private_cells_hidden
      (scalar_expansion_source_cells entries) hidden_cells;
  spco_private_hidden :
    Witness.private_cells_hidden private_cells hidden_cells;
}.

Definition check_scalar_privatization_coreb
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event) : bool :=
  mem_cells_subsetb private_cells hidden_cells &&
  mem_cells_subsetb (scalar_expansion_source_cells entries) hidden_cells &&
  check_scalar_expansionb
    source_domain source_cells private_cells entries events.

Lemma check_scalar_privatization_coreb_sound :
  forall hidden_cells private_cells source_domain source_cells entries events,
    check_scalar_privatization_coreb
      hidden_cells private_cells source_domain source_cells entries events =
    true ->
    scalar_privatization_core_obligations
      hidden_cells private_cells source_domain source_cells entries events.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         Hcheck.
  unfold check_scalar_privatization_coreb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hprivate_hidden & Hsource_hidden) & Hscalar).
  constructor.
  - apply check_scalar_expansionb_sound.
    exact Hscalar.
  - apply Witness.private_cells_hidden_sound.
    exact Hsource_hidden.
  - apply Witness.private_cells_hidden_sound.
    exact Hprivate_hidden.
Qed.

Record bounded_pure_scalar_privatization_obligations
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event)
    (private_bounds: list array_bounds)
    (source_specs private_specs: list storage_spec)
    (escaped_cells: list MemCell) : Prop := {
  bpspo_core :
    scalar_privatization_core_obligations
      hidden_cells private_cells source_domain source_cells entries events;
  bpspo_private_bounds :
    storage_bounds_obligations private_bounds private_cells;
  bpspo_storage_compatible :
    storage_compatibility_obligations
      (scalar_expansion_storage_mapping entries)
      source_specs private_specs;
  bpspo_non_escape :
    private_non_escape_obligations private_cells escaped_cells;
}.

Record scalar_privatization_value_core_obligations
    (value: Type)
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event)
    (value_trace: scalar_expansion_value_trace value) : Prop := {
  spvco_core :
    scalar_privatization_core_obligations
      hidden_cells private_cells source_domain source_cells entries events;
  spvco_value_flow :
    scalar_expansion_value_obligations value value_trace;
  spvco_value_trace_events :
    scalar_expansion_value_trace_events value_trace = events;
}.

Definition check_scalar_privatization_value_coreb
    {value: Type}
    (value_eqb: value -> value -> bool)
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event)
    (value_trace: scalar_expansion_value_trace value) : bool :=
  check_scalar_privatization_coreb
    hidden_cells private_cells source_domain source_cells entries events &&
  check_scalar_expansion_value_traceb value_eqb value_trace &&
  scalar_expansion_events_eqb
    (scalar_expansion_value_trace_events value_trace)
    events.

Lemma check_scalar_privatization_value_coreb_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells source_domain source_cells entries events
         value_trace,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    check_scalar_privatization_value_coreb
      value_eqb hidden_cells private_cells source_domain source_cells entries
      events value_trace = true ->
    scalar_privatization_value_core_obligations
      value hidden_cells private_cells source_domain source_cells entries
      events value_trace.
Proof.
  intros value value_eqb hidden_cells private_cells source_domain source_cells
         entries events value_trace Hvalue_eqb Hcheck.
  unfold check_scalar_privatization_value_coreb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hcore & Hvalue) & Hevents).
  constructor.
  - apply check_scalar_privatization_coreb_sound.
    exact Hcore.
  - constructor.
    unfold check_scalar_expansion_value_traceb in Hvalue.
    apply
      (check_scalar_expansion_value_trace_fromb_sound value value_eqb).
    + exact Hvalue_eqb.
    + exact Hvalue.
  - apply scalar_expansion_events_eqb_eq.
    exact Hevents.
Qed.

Definition check_bounded_pure_scalar_privatizationb
    (hidden_cells private_cells: list MemCell)
    (source_domain: list logical_instance)
    (source_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event)
    (private_bounds: list array_bounds)
    (source_specs private_specs: list storage_spec)
    (escaped_cells: list MemCell) : bool :=
  check_scalar_privatization_coreb
    hidden_cells private_cells source_domain source_cells entries events &&
  check_storage_boundsb private_bounds private_cells &&
  check_storage_compatibilityb
    (scalar_expansion_storage_mapping entries)
    source_specs private_specs &&
  check_private_non_escapeb private_cells escaped_cells.

Lemma check_bounded_pure_scalar_privatizationb_sound :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells,
    check_bounded_pure_scalar_privatizationb
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells = true ->
    bounded_pure_scalar_privatization_obligations
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells Hcheck.
  unfold check_bounded_pure_scalar_privatizationb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hcore & Hbounds) & Hcompatible) & Hnon_escape).
  constructor.
  - apply check_scalar_privatization_coreb_sound.
    exact Hcore.
  - apply check_storage_boundsb_sound.
    exact Hbounds.
  - apply check_storage_compatibilityb_sound.
    exact Hcompatible.
  - apply check_private_non_escapeb_sound.
    exact Hnon_escape.
Qed.

Theorem checked_scalar_expansion_view_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    mem_cells_subsetb private_cells hidden_cells = true ->
    mem_cells_subsetb (scalar_expansion_source_cells entries) hidden_cells = true ->
    check_scalar_expansionb
      source_domain source_cells private_cells entries events = true ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    scalar_expansion_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      source_view after /\
    View.view_refinement
      (Private.private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (Private.private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         before source_view after ok Hret Hok Hhidden Hsource_hidden
         Hscalar Hprivate.
  pose proof
    (check_scalar_expansionb_sound
       source_domain source_cells private_cells entries events Hscalar)
    as Hscalar_obligations.
  pose proof
    (Witness.private_cells_hidden_sound private_cells hidden_cells Hhidden)
    as Hprivate_hidden.
  pose proof
    (Witness.private_cells_hidden_sound
       (scalar_expansion_source_cells entries) hidden_cells Hsource_hidden)
    as Hsource_cells_hidden.
  split.
  - constructor; assumption.
  - eapply Private.checked_hidden_private_expansion_view_correct.
    + exact Hret.
    + exact Hok.
    + exact Hhidden.
    + exact Hprivate.
Qed.

Theorem checked_pure_scalar_privatization_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_scalar_privatization_coreb
      hidden_cells private_cells source_domain source_cells entries events =
    true ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    scalar_privatization_core_obligations
      hidden_cells private_cells source_domain source_cells entries events /\
    pure_scalar_privatization_refinement hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         before source_view after ok Hret Hok Hcore Hprivate.
  pose proof
    (check_scalar_privatization_coreb_sound
       hidden_cells private_cells source_domain source_cells entries events
       Hcore)
    as Hcore_obligations.
  unfold check_scalar_privatization_coreb in Hcore.
  repeat rewrite andb_true_iff in Hcore.
  destruct Hcore as ((Hprivate_hidden & Hsource_hidden) & Hscalar).
  pose proof
    (checked_scalar_expansion_view_correct
       hidden_cells private_cells source_domain source_cells entries events
       before source_view after ok
       Hret Hok Hprivate_hidden Hsource_hidden Hscalar Hprivate)
    as [_ Hview].
  split.
  - exact Hcore_obligations.
  - unfold pure_scalar_privatization_refinement,
           pure_scalar_privatization_view,
           pure_scalar_privatization_final_view.
    exact Hview.
Qed.

Theorem checked_value_pure_scalar_privatization_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells source_domain source_cells entries events
         value_trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_scalar_privatization_value_coreb
      value_eqb hidden_cells private_cells source_domain source_cells entries
      events value_trace = true ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    scalar_privatization_value_core_obligations
      value hidden_cells private_cells source_domain source_cells entries
      events value_trace /\
    pure_scalar_privatization_refinement hidden_cells before after.
Proof.
  intros value value_eqb hidden_cells private_cells source_domain source_cells
         entries events value_trace before source_view after ok
         Hvalue_eqb Hret Hok Hcheck Hprivate.
  pose proof
    (check_scalar_privatization_value_coreb_sound
       value value_eqb hidden_cells private_cells source_domain source_cells
       entries events value_trace Hvalue_eqb Hcheck)
    as Hvalue_obligations.
  unfold check_scalar_privatization_value_coreb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hcore & _Hvalue) & _Hevents).
  pose proof
    (checked_pure_scalar_privatization_correct
       hidden_cells private_cells source_domain source_cells entries events
       before source_view after ok
       Hret Hok Hcore Hprivate)
    as [_ Hview].
  split.
  - exact Hvalue_obligations.
  - exact Hview.
Qed.

Theorem scalar_expansion_view_event_uses_declared_private :
  forall hidden_cells private_cells source_domain source_cells entries events
         source_view after event,
    scalar_expansion_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      source_view after ->
    In event events ->
    In (expansion_event_private_cell event) private_cells.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         source_view after event Hcontract Hin.
  destruct Hcontract as [Hscalar _ _ _].
  eapply scalar_expansion_event_uses_declared_private; eauto.
Qed.

Lemma scalar_expansion_entry_source_cell_in :
  forall entries entry,
    In entry entries ->
    In (expansion_source_cell entry)
       (scalar_expansion_source_cells entries).
Proof.
  induction entries as [|head tail IH]; intros entry Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst. left. reflexivity.
    + right. apply IH. exact Hin_tail.
Qed.

Theorem scalar_expansion_view_entry_source_cell_hidden :
  forall hidden_cells private_cells source_domain source_cells entries events
         source_view after entry,
    scalar_expansion_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      source_view after ->
    In entry entries ->
    In (expansion_source_cell entry) hidden_cells.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         source_view after entry Hcontract Hin.
  destruct Hcontract as [_ Hsource_hidden _ _].
  eapply Hsource_hidden.
  eapply scalar_expansion_entry_source_cell_in.
  exact Hin.
Qed.

Theorem scalar_expansion_view_event_source_cell_hidden :
  forall hidden_cells private_cells source_domain source_cells entries events
         source_view after event,
    scalar_expansion_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      source_view after ->
    In event events ->
    In (expansion_event_source_cell event) hidden_cells.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         source_view after event Hcontract Hin.
  destruct Hcontract as [Hscalar Hsource_hidden _ _].
  destruct Hscalar as [_ _ _ _ _ Hevents _].
  unfold scalar_expansion_events_mapped in Hevents.
  unfold scalar_expansion_event_mapped in Hevents.
  pose proof (Hevents event Hin) as Hlookup.
  apply scalar_expansion_lookup_sound in Hlookup.
  destruct Hlookup as
    (entry & Hin_entry & _ & Hsource & _).
  rewrite <- Hsource.
  eapply Hsource_hidden.
  eapply scalar_expansion_entry_source_cell_in.
  exact Hin_entry.
Qed.

Theorem checked_scalar_expansion_bounded_compatible_non_escape_view_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    mem_cells_subsetb private_cells hidden_cells = true ->
    mem_cells_subsetb (scalar_expansion_source_cells entries) hidden_cells = true ->
    check_scalar_expansionb
      source_domain source_cells private_cells entries events = true ->
    check_storage_boundsb private_bounds private_cells = true ->
    check_storage_compatibilityb
      (scalar_expansion_storage_mapping entries)
      source_specs private_specs = true ->
    check_private_non_escapeb private_cells escaped_cells = true ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    scalar_expansion_bounded_compatible_non_escape_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells
      source_view after /\
    View.view_refinement
      (Private.private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (Private.private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         before source_view after ok
         Hret Hok Hhidden Hsource_hidden Hscalar Hbounds Hcompatible
         Hnon_escape Hprivate.
  pose proof
    (checked_scalar_expansion_view_correct
       hidden_cells private_cells source_domain source_cells entries events
       before source_view after ok
       Hret Hok Hhidden Hsource_hidden Hscalar Hprivate)
    as [Hbase Hview].
  pose proof
    (check_storage_boundsb_sound
       private_bounds private_cells Hbounds)
    as Hbounds_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       (scalar_expansion_storage_mapping entries)
       source_specs private_specs Hcompatible)
    as Hcompatible_obligations.
  pose proof
    (check_private_non_escapeb_sound
       private_cells escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_bounded_pure_scalar_privatization_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    check_bounded_pure_scalar_privatizationb
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells = true ->
    Private.private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    bounded_pure_scalar_privatization_obligations
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells /\
    pure_scalar_privatization_refinement hidden_cells before after.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         before source_view after ok Hret Hok Hcheck Hprivate.
  pose proof
    (check_bounded_pure_scalar_privatizationb_sound
       hidden_cells private_cells source_domain source_cells entries events
       private_bounds source_specs private_specs escaped_cells Hcheck)
    as Hbounded_obligations.
  unfold check_bounded_pure_scalar_privatizationb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hcore & Hbounds) & Hcompatible) & Hnon_escape).
  unfold check_scalar_privatization_coreb in Hcore.
  repeat rewrite andb_true_iff in Hcore.
  destruct Hcore as ((Hprivate_hidden & Hsource_hidden) & Hscalar).
  pose proof
    (checked_scalar_expansion_bounded_compatible_non_escape_view_correct
       hidden_cells private_cells source_domain source_cells entries events
       private_bounds source_specs private_specs escaped_cells
       before source_view after ok
       Hret Hok Hprivate_hidden Hsource_hidden Hscalar Hbounds
       Hcompatible Hnon_escape Hprivate)
    as [_ Hview].
  split.
  - exact Hbounded_obligations.
  - unfold pure_scalar_privatization_refinement,
           pure_scalar_privatization_view,
           pure_scalar_privatization_final_view.
    exact Hview.
Qed.

Theorem scalar_expansion_event_private_cell_within_bounds :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         source_view after event,
    scalar_expansion_bounded_compatible_non_escape_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells
      source_view after ->
    In event events ->
    cell_within_declared_bounds
      private_bounds (expansion_event_private_cell event).
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         source_view after event Hcontract Hin.
  destruct Hcontract as [Hbase Hbounds _ _].
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - eapply scalar_expansion_view_event_uses_declared_private; eauto.
Qed.

Theorem scalar_expansion_event_private_cell_not_escaped :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         source_view after event,
    scalar_expansion_bounded_compatible_non_escape_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells
      source_view after ->
    In event events ->
    ~ In (expansion_event_private_cell event) escaped_cells.
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         source_view after event Hcontract Hin.
  destruct Hcontract as [Hbase _ _ Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  eapply scalar_expansion_view_event_uses_declared_private; eauto.
Qed.

Theorem scalar_expansion_entry_storage_compatible :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         source_view after entry,
    scalar_expansion_bounded_compatible_non_escape_view_contract
      hidden_cells private_cells source_domain source_cells entries events
      private_bounds source_specs private_specs escaped_cells
      source_view after ->
    In entry entries ->
    storage_mapping_entry_compatible
      source_specs private_specs
      (expansion_source_cell entry, expansion_private_cell entry).
Proof.
  intros hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         source_view after entry Hcontract Hin.
  destruct Hcontract as [_ _ Hcompatible _].
  destruct Hcompatible as [_ _ Hmapping].
  eapply Hmapping.
  apply scalar_expansion_entry_in_storage_mapping.
  exact Hin.
Qed.

End ScalarExpansionValidator.
