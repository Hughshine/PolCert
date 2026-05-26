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

End ScalarExpansionValidator.
