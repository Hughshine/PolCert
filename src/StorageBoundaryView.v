Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import CellView.
Require Import StorageWitness.
Require Import StateObservation.
Require Import ViewPipeline.
Require Import ReuseConflictWitness.
Require Import ReuseStateView.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** Shared boundary-view contract for storage-backed endpoint relations.

    Many storage transformations have the same final-observation shape:

      logical source cell  ->  physical target cell at the boundary

    Layout remapping, phase projection, contraction/inter-array reuse, and
    copy-out from local storage all need this finite map.  Feature-specific
    validators still prove their own scheduling, lifetime, copy, or algebraic
    obligations, but they should not each invent a different final-state
    relation.  This module packages the common endpoint fact:

      - the finite map covers the source-observable boundary cells;
      - the mapped physical cells have compatible storage specs;
      - the target/source states are related by the reusable
        [StateObservation] cell-view relation.

    The existing [State.eq] route remains the identity instance outside this
    module. *)

Module StorageBoundaryView
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.
Module ReuseView := ReuseStateView PolIRs Observer.
Module Observation := ReuseView.Observation.

Definition storage_boundary_output_view
    (mapping: reuse_mapping)
    (source_cells: list MemCell) : View.view :=
  ReuseView.reuse_boundary_view mapping source_cells.

Definition storage_boundary_cell_view
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (Hboundary:
       reuse_boundary_obligations mapping source_cells)
    : Observation.cell_view :=
  ReuseView.reuse_boundary_cell_view
    mapping source_cells Hboundary.

Definition storage_boundary_generic_cell_view
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (Hboundary:
       reuse_boundary_obligations mapping source_cells)
    : generic_cell_view :=
  Observation.cell_view_to_generic
    (storage_boundary_cell_view mapping source_cells Hboundary).

Record storage_boundary_view_contract
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec) : Prop := {
  sbvc_boundary :
    reuse_boundary_obligations mapping source_cells;
  sbvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
}.

Definition check_storage_boundary_viewb
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec) : bool :=
  check_reuse_boundaryb mapping source_cells &&
  check_storage_compatibilityb
    mapping logical_specs physical_specs.

Theorem check_storage_boundary_viewb_sound :
  forall mapping source_cells logical_specs physical_specs,
    check_storage_boundary_viewb
      mapping source_cells logical_specs physical_specs = true ->
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs.
Proof.
  intros mapping source_cells logical_specs physical_specs Hcheck.
  unfold check_storage_boundary_viewb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hboundary Hstorage].
  constructor.
  - apply check_reuse_boundaryb_sound.
    exact Hboundary.
  - apply check_storage_compatibilityb_sound.
    exact Hstorage.
Qed.

Definition storage_boundary_contract_cell_view
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec)
    (contract:
       storage_boundary_view_contract
         mapping source_cells logical_specs physical_specs)
    : Observation.cell_view :=
  storage_boundary_cell_view
    mapping source_cells (sbvc_boundary _ _ _ _ contract).

Theorem storage_boundary_contract_cell_view_rel :
  forall mapping source_cells logical_specs physical_specs contract,
    Observation.cell_view_state_view
      (storage_boundary_contract_cell_view
         mapping source_cells logical_specs physical_specs contract) =
    storage_boundary_output_view mapping source_cells.
Proof.
  reflexivity.
Qed.

Definition storage_boundary_contract_generic_cell_view
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec)
    (contract:
       storage_boundary_view_contract
         mapping source_cells logical_specs physical_specs)
    : generic_cell_view :=
  storage_boundary_generic_cell_view
    mapping source_cells (sbvc_boundary _ _ _ _ contract).

Theorem storage_boundary_contract_generic_cell_view_rel :
  forall mapping source_cells logical_specs physical_specs contract,
    Observation.generic_cell_view_state_view
      (storage_boundary_contract_generic_cell_view
         mapping source_cells logical_specs physical_specs contract) =
    storage_boundary_output_view mapping source_cells.
Proof.
  reflexivity.
Qed.

Record storage_boundary_refinement_contract
    (input_view: View.view)
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  sbrc_boundary_view :
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs;
  sbrc_semantic_refinement :
    View.view_refinement
      input_view
      (storage_boundary_output_view mapping source_cells)
      source_view after;
}.

Record storage_boundary_transform_contract
    (mapping: reuse_mapping)
    (source_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec)
    (before after: PolyLang.t) : Prop := {
  sbtc_boundary_view :
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs;
  sbtc_access_remap :
    Observation.Storage.pprog_same_instance_access_remap
      (ReuseView.reuse_boundary_cell_relation mapping source_cells)
      before after;
  sbtc_view_refinement :
    View.view_refinement
      (storage_boundary_output_view mapping source_cells)
      (storage_boundary_output_view mapping source_cells)
      before after;
}.

Theorem storage_boundary_transform_contract_generic :
  forall mapping source_cells logical_specs physical_specs
         (boundary_contract:
            storage_boundary_view_contract
              mapping source_cells logical_specs physical_specs)
         before after,
    Observation.Storage.pprog_same_instance_access_remap
      (ReuseView.reuse_boundary_cell_relation mapping source_cells)
      before after ->
    View.view_refinement
      (storage_boundary_output_view mapping source_cells)
      (storage_boundary_output_view mapping source_cells)
      before after ->
    Observation.generic_cell_view_transform_contract
      (storage_boundary_contract_generic_cell_view
         mapping source_cells logical_specs physical_specs boundary_contract)
      before after.
Proof.
  intros mapping source_cells logical_specs physical_specs boundary_contract
         before after Haccess Hview.
  constructor.
  - exact Haccess.
  - rewrite storage_boundary_contract_generic_cell_view_rel.
    exact Hview.
Qed.

Theorem checked_storage_boundary_transform_contract_correct :
  forall mapping source_cells logical_specs physical_specs before after,
    check_storage_boundary_viewb
      mapping source_cells logical_specs physical_specs = true ->
    Observation.Storage.pprog_same_instance_access_remap
      (ReuseView.reuse_boundary_cell_relation mapping source_cells)
      before after ->
    View.view_refinement
      (storage_boundary_output_view mapping source_cells)
      (storage_boundary_output_view mapping source_cells)
      before after ->
    exists contract,
      storage_boundary_transform_contract
        mapping source_cells logical_specs physical_specs before after /\
      Observation.generic_cell_view_transform_contract
        (storage_boundary_contract_generic_cell_view
           mapping source_cells logical_specs physical_specs contract)
        before after.
Proof.
  intros mapping source_cells logical_specs physical_specs before after
         Hboundary Haccess Hview.
  pose proof
    (check_storage_boundary_viewb_sound
       mapping source_cells logical_specs physical_specs Hboundary)
    as Hboundary_contract.
  exists Hboundary_contract.
  split.
  - constructor; assumption.
  - eapply storage_boundary_transform_contract_generic; eauto.
Qed.

Definition storage_boundary_pipeline_final_view
    (mapping: reuse_mapping)
    (source_cells: list MemCell) : View.view :=
  Pipeline.pipeline_final_view
    (storage_boundary_output_view mapping source_cells).

Theorem checked_storage_boundary_refinement_correct :
  forall input_view mapping source_cells logical_specs physical_specs
         before source_view after ok,
    mayReturn
      (Pipeline.check_source_view before source_view) ok ->
    ok = true ->
    check_storage_boundary_viewb
      mapping source_cells logical_specs physical_specs = true ->
    View.view_refinement
      input_view
      (storage_boundary_output_view mapping source_cells)
      source_view after ->
    storage_boundary_refinement_contract
      input_view mapping source_cells logical_specs physical_specs
      source_view after /\
    View.view_refinement
      input_view
      (storage_boundary_pipeline_final_view mapping source_cells)
      before after.
Proof.
  intros input_view mapping source_cells logical_specs physical_specs
         before source_view after ok Hret Hok Hboundary Hsemantics.
  pose proof
    (check_storage_boundary_viewb_sound
       mapping source_cells logical_specs physical_specs Hboundary)
    as Hboundary_contract.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view
         (storage_boundary_output_view mapping source_cells)
         before source_view after ok);
      assumption.
Qed.

End StorageBoundaryView.
