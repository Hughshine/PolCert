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

Theorem storage_boundary_source_cell_covered :
  forall mapping source_cells logical_specs physical_specs source_cell,
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs ->
    In source_cell source_cells ->
    exists target_cell,
      reuse_cell_relation mapping target_cell source_cell.
Proof.
  intros mapping source_cells logical_specs physical_specs
         source_cell Hcontract Hin.
  destruct Hcontract as [Hboundary _].
  destruct Hboundary as [_ Hcovered].
  eapply Hcovered; eauto.
Qed.

Theorem storage_boundary_mapping_entry_compatible_specs :
  forall mapping source_cells logical_specs physical_specs mapping_entry,
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs ->
    In mapping_entry mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = fst mapping_entry /\
      storage_spec_cell physical_spec = snd mapping_entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping source_cells logical_specs physical_specs mapping_entry
         Hcontract Hin.
  destruct Hcontract as [_ Hcompatible].
  eapply storage_compatibility_mapping_entry_specs; eauto.
Qed.

Theorem storage_boundary_lookup_compatible_specs :
  forall mapping source_cells logical_specs physical_specs
         logical_cell physical_cell,
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping source_cells logical_specs physical_specs
         logical_cell physical_cell Hcontract Hlookup.
  pose proof
    (reuse_lookup_sound logical_cell physical_cell mapping Hlookup)
    as [Hin | (logical_cell' & Hin & Heq)].
  - pose proof
      (storage_boundary_mapping_entry_compatible_specs
         mapping source_cells logical_specs physical_specs
         (logical_cell, physical_cell) Hcontract Hin)
      as (logical_spec & physical_spec & Hlogical_in & Hphysical_in &
          Hlogical_cell & Hphysical_cell & Hspecs).
    exists logical_spec, physical_spec.
    simpl in Hlogical_cell, Hphysical_cell.
    split.
    + exact Hlogical_in.
    + split.
      * exact Hphysical_in.
      * split.
        -- exact Hlogical_cell.
        -- split.
           ++ exact Hphysical_cell.
           ++ exact Hspecs.
  - subst logical_cell'.
    pose proof
      (storage_boundary_mapping_entry_compatible_specs
         mapping source_cells logical_specs physical_specs
         (logical_cell, physical_cell) Hcontract Hin)
      as (logical_spec & physical_spec & Hlogical_in & Hphysical_in &
          Hlogical_cell & Hphysical_cell & Hspecs).
    exists logical_spec, physical_spec.
    simpl in Hlogical_cell, Hphysical_cell.
    split.
    + exact Hlogical_in.
    + split.
      * exact Hphysical_in.
      * split.
        -- exact Hlogical_cell.
        -- split.
           ++ exact Hphysical_cell.
           ++ exact Hspecs.
Qed.

Theorem storage_boundary_source_cell_compatible_target :
  forall mapping source_cells logical_specs physical_specs source_cell,
    storage_boundary_view_contract
      mapping source_cells logical_specs physical_specs ->
    In source_cell source_cells ->
    exists target_cell logical_spec physical_spec,
      reuse_cell_relation mapping target_cell source_cell /\
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = source_cell /\
      storage_spec_cell physical_spec = target_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping source_cells logical_specs physical_specs
         source_cell Hcontract Hin.
  pose proof
    (storage_boundary_source_cell_covered
       mapping source_cells logical_specs physical_specs
       source_cell Hcontract Hin)
    as (target_cell & Hrelation).
  pose proof Hrelation as Hlookup.
  unfold reuse_cell_relation in Hlookup.
  pose proof
    (storage_boundary_lookup_compatible_specs
       mapping source_cells logical_specs physical_specs
       source_cell target_cell Hcontract Hlookup)
    as (logical_spec & physical_spec & Hlogical_in & Hphysical_in &
        Hlogical_cell & Hphysical_cell & Hspecs).
  exists target_cell, logical_spec, physical_spec.
  split.
  - exact Hrelation.
  - split.
    + exact Hlogical_in.
    + split.
      * exact Hphysical_in.
      * split.
        -- exact Hlogical_cell.
        -- split.
           ++ exact Hphysical_cell.
           ++ exact Hspecs.
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
