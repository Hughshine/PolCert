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

Theorem checked_scalar_expansion_view_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    mem_cells_subsetb private_cells hidden_cells = true ->
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
         before source_view after ok Hret Hok Hhidden Hscalar Hprivate.
  pose proof
    (check_scalar_expansionb_sound
       source_domain source_cells private_cells entries events Hscalar)
    as Hscalar_obligations.
  pose proof
    (Witness.private_cells_hidden_sound private_cells hidden_cells Hhidden)
    as Hprivate_hidden.
  split.
  - constructor; assumption.
  - eapply Private.checked_hidden_private_expansion_view_correct.
    + exact Hret.
    + exact Hok.
    + exact Hhidden.
    + exact Hprivate.
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
  destruct Hcontract as [Hscalar _ _].
  eapply scalar_expansion_event_uses_declared_private; eauto.
Qed.

Theorem checked_scalar_expansion_bounded_compatible_non_escape_view_correct :
  forall hidden_cells private_cells source_domain source_cells entries events
         private_bounds source_specs private_specs escaped_cells
         before source_view after ok,
    mayReturn (Private.check_private_source_view before source_view) ok ->
    ok = true ->
    mem_cells_subsetb private_cells hidden_cells = true ->
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
         Hret Hok Hhidden Hscalar Hbounds Hcompatible Hnon_escape Hprivate.
  pose proof
    (checked_scalar_expansion_view_correct
       hidden_cells private_cells source_domain source_cells entries events
       before source_view after ok
       Hret Hok Hhidden Hscalar Hprivate)
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
