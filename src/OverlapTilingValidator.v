Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import PrivateStorageWitness.
Require Import ReuseConflictWitness.
Require Import InstanceProjectionWitness.
Require Import OverlapClosureWitness.
Require Import OverlapValueWitness.
Require Import OverlapStorageWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** Combined wrapper for overlapped tiling / private recomputation.

    Overlap is primarily an instance-count-changing transformation: target
    computations may duplicate source instances, but only commit-role instances
    are source-visible.  If a transformation materializes tile-private halo or
    local storage, it also needs a separation witness.

    This module provides two composable theorem shapes:

      - no-private overlap: projection + commit exact cover;
      - private-buffer overlap: projection + commit exact cover + private
        storage separation.
      - closure-aware overlap: projection + commit exact cover + finite
        tile-local dependence closure, optionally with private separation.
      - ordered closure-aware overlap: the same local closure, plus a finite
        producer-before-consumer condition for tile-produced dependencies.

    Dependence closure and value equivalence of recomputed/internal instances
    are separate obligations: the finite closure witness records where each
    dependency may come from, while the value witness records that every
    projected recomputation has the same finite value as the source instance it
    represents. *)

Module OverlapTilingValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_overlap_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_overlap_source_view_correct :
  forall before source_view ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition overlap_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record overlap_no_private_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (source_view after: PolyLang.t) : Prop := {
  onp_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  onp_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (private_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  op_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  op_private_separation :
    private_separation_obligations
      private_cells public_cells frame_cells;
  op_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (source_view after: PolyLang.t) : Prop := {
  oc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  oc_closure :
    overlap_closure_obligations tiles;
  oc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (private_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  opc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  opc_closure :
    overlap_closure_obligations tiles;
  opc_private_separation :
    private_separation_obligations
      private_cells public_cells frame_cells;
  opc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_ordered_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (source_view after: PolyLang.t) : Prop := {
  ooc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  ooc_closure :
    overlap_ordered_closure_obligations tiles;
  ooc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_ordered_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (private_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  opoc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  opoc_closure :
    overlap_ordered_closure_obligations tiles;
  opoc_private_separation :
    private_separation_obligations
      private_cells public_cells frame_cells;
  opoc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_ordered_closure_compatible_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (private_cells public_cells frame_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  opocc_base :
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after;
  opocc_storage_compatible :
    storage_compatibility_obligations
      private_mapping logical_specs private_specs;
}.

Record overlap_private_ordered_closure_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (target_values: list (overlap_value_entry value))
    (private_cells public_cells frame_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  opoccv_compatible_base :
    overlap_private_ordered_closure_compatible_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after;
  opoccv_values :
    overlap_value_obligations
      value (overlap_tiles_targets tiles) target_values;
}.

Record overlap_private_ordered_closure_compatible_value_storage_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (target_values: list (overlap_value_entry value))
    (private_cells public_cells frame_cells commit_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (writes: list overlap_write)
    (source_view after: PolyLang.t) : Prop := {
  opoccvs_value_base :
    overlap_private_ordered_closure_compatible_value_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after;
  opoccvs_writes :
    overlap_storage_obligations
      private_cells commit_cells (overlap_tiles_targets tiles) writes;
}.

Record overlap_private_ordered_closure_bounded_compatible_value_storage_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (target_values: list (overlap_value_entry value))
    (private_cells public_cells frame_cells commit_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (private_bounds commit_bounds: list array_bounds)
    (writes: list overlap_write)
    (source_view after: PolyLang.t) : Prop := {
  opocbcvs_storage_base :
    overlap_private_ordered_closure_compatible_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs writes source_view after;
  opocbcvs_private_bounds :
    storage_bounds_obligations private_bounds private_cells;
  opocbcvs_commit_bounds :
    storage_bounds_obligations commit_bounds commit_cells;
}.

Record overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (target_values: list (overlap_value_entry value))
    (private_cells public_cells frame_cells commit_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (private_bounds commit_bounds: list array_bounds)
    (escaped_cells: list MemCell)
    (writes: list overlap_write)
    (source_view after: PolyLang.t) : Prop := {
  opocbcnevs_bounded_storage_base :
    overlap_private_ordered_closure_bounded_compatible_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs private_bounds commit_bounds
      writes source_view after;
  opocbcnevs_non_escape :
    private_non_escape_obligations private_cells escaped_cells;
}.

Definition overlap_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_overlap_no_private_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_no_private_view_contract
      input_view output_view source_domain source_liveouts targets
      source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets
         before source_view after ok Hret Hok Hprojection Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts targets Hprojection)
    as Hprojection_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_closureb tiles = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok
         Hret Hok Hprojection Hclosure Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_ordered_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok
         Hret Hok Hprojection Hclosure Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_ordered_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets
         private_cells public_cells frame_cells
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_view_contract
      input_view output_view source_domain source_liveouts targets
      private_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets
         private_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts targets Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_private_separationb_sound
       private_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hclosure Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  pose proof
    (check_private_separationb_sound
       private_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_ordered_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hclosure Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_ordered_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  pose proof
    (check_private_separationb_sound
       private_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_ordered_closure_compatible_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_compatible_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok
         Hret Hok Hprojection Hclosure Hseparation Hstorage Hsemantics.
  pose proof
    (checked_overlap_private_ordered_closure_view_correct
       input_view output_view source_domain source_liveouts tiles
       private_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hclosure Hseparation Hsemantics)
    as [Hbase Hview].
  pose proof
    (check_storage_compatibilityb_sound
       private_mapping logical_specs private_specs Hstorage)
    as Hstorage_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_overlap_private_ordered_closure_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    check_overlap_valueb
      value_eqb (overlap_tiles_targets tiles) target_values = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_compatible_value_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok
         Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
         Hvalues Hsemantics.
  pose proof
    (check_overlap_valueb_sound
       value value_eqb Hvalue_eqb
       (overlap_tiles_targets tiles) target_values Hvalues)
    as Hvalue_obligations.
  pose proof
    (checked_overlap_private_ordered_closure_compatible_view_correct
       input_view output_view source_domain source_liveouts tiles
       private_cells public_cells frame_cells
       private_mapping logical_specs private_specs
       before source_view after ok
       Hret Hok Hprojection Hclosure Hseparation Hstorage Hsemantics)
    as [Hcompatible_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_overlap_private_ordered_closure_compatible_value_storage_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs writes
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    check_overlap_valueb
      value_eqb (overlap_tiles_targets tiles) target_values = true ->
    check_overlap_storageb
      private_cells commit_cells (overlap_tiles_targets tiles) writes = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_compatible_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs writes source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs writes
         before source_view after ok
         Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
         Hvalues Hwrites Hsemantics.
  pose proof
    (check_overlap_storageb_sound
       private_cells commit_cells (overlap_tiles_targets tiles) writes Hwrites)
    as Hwrite_obligations.
  pose proof
    (checked_overlap_private_ordered_closure_compatible_value_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts tiles target_values
       private_cells public_cells frame_cells
       private_mapping logical_specs private_specs
       before source_view after ok
       Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
       Hvalues Hsemantics)
    as [Hvalue_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_overlap_private_ordered_closure_bounded_compatible_value_storage_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds writes
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    check_storage_boundsb private_bounds private_cells = true ->
    check_storage_boundsb commit_bounds commit_cells = true ->
    check_overlap_valueb
      value_eqb (overlap_tiles_targets tiles) target_values = true ->
    check_overlap_storageb
      private_cells commit_cells (overlap_tiles_targets tiles) writes = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_bounded_compatible_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs private_bounds commit_bounds
      writes source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds writes
         before source_view after ok
         Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
         Hprivate_bounds Hcommit_bounds Hvalues Hwrites Hsemantics.
  pose proof
    (check_storage_boundsb_sound
       private_bounds private_cells Hprivate_bounds)
    as Hprivate_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       commit_bounds commit_cells Hcommit_bounds)
    as Hcommit_bounds_obligations.
  pose proof
    (checked_overlap_private_ordered_closure_compatible_value_storage_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts tiles target_values
       private_cells public_cells frame_cells commit_cells
       private_mapping logical_specs private_specs writes
       before source_view after ok
       Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
       Hvalues Hwrites Hsemantics)
    as [Hstorage_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         escaped_cells writes
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    check_storage_boundsb private_bounds private_cells = true ->
    check_storage_boundsb commit_bounds commit_cells = true ->
    check_private_non_escapeb private_cells escaped_cells = true ->
    check_overlap_valueb
      value_eqb (overlap_tiles_targets tiles) target_values = true ->
    check_overlap_storageb
      private_cells commit_cells (overlap_tiles_targets tiles) writes = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs private_bounds commit_bounds
      escaped_cells writes source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         escaped_cells writes before source_view after ok
         Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
         Hprivate_bounds Hcommit_bounds Hnon_escape Hvalues Hwrites Hsemantics.
  pose proof
    (check_private_non_escapeb_sound
       private_cells escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (checked_overlap_private_ordered_closure_bounded_compatible_value_storage_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts tiles target_values
       private_cells public_cells frame_cells commit_cells
       private_mapping logical_specs private_specs private_bounds commit_bounds
       writes before source_view after ok
       Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
       Hprivate_bounds Hcommit_bounds Hvalues Hwrites Hsemantics)
    as [Hbounded_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         escaped_cells writes
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    check_storage_boundsb private_bounds private_cells = true ->
    check_storage_boundsb commit_bounds commit_cells = true ->
    check_private_non_escapeb private_cells escaped_cells = true ->
    check_overlap_valueb
      value_eqb (overlap_tiles_targets tiles) target_values = true ->
    check_overlap_storageb
      private_cells commit_cells (overlap_tiles_targets tiles) writes = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         escaped_cells writes before source_view after ok
         Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
         Hprivate_bounds Hcommit_bounds Hnon_escape Hvalues Hwrites Hsemantics.
  pose proof
    (checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts tiles target_values
       private_cells public_cells frame_cells commit_cells
       private_mapping logical_specs private_specs private_bounds commit_bounds
       escaped_cells writes before source_view after ok
       Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
       Hprivate_bounds Hcommit_bounds Hnon_escape Hvalues Hwrites Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record overlap_private_ordered_bounded_non_escape_params (value: Type) := {
  opobnep_input_view : View.view;
  opobnep_output_view : View.view;
  opobnep_source_domain : list logical_instance;
  opobnep_source_liveouts : list logical_instance;
  opobnep_tiles : list overlap_tile;
  opobnep_target_values : list (overlap_value_entry value);
  opobnep_private_cells : list MemCell;
  opobnep_public_cells : list MemCell;
  opobnep_frame_cells : list MemCell;
  opobnep_commit_cells : list MemCell;
  opobnep_private_mapping : reuse_mapping;
  opobnep_logical_specs : list storage_spec;
  opobnep_private_specs : list storage_spec;
  opobnep_private_bounds : list array_bounds;
  opobnep_commit_bounds : list array_bounds;
  opobnep_escaped_cells : list MemCell;
  opobnep_writes : list overlap_write;
  opobnep_source_view : PolyLang.t;
}.

Definition overlap_private_ordered_bounded_non_escape_input_view {value: Type}
    (params: overlap_private_ordered_bounded_non_escape_params value)
    : View.view :=
  opobnep_input_view value params.

Definition overlap_private_ordered_bounded_non_escape_output_view {value: Type}
    (params: overlap_private_ordered_bounded_non_escape_params value)
    : View.view :=
  overlap_pipeline_final_view (opobnep_output_view value params).

Definition overlap_private_ordered_bounded_non_escape_check {value: Type}
    (params: overlap_private_ordered_bounded_non_escape_params value)
    (before after: PolyLang.t) : imp bool :=
  check_overlap_source_view before (opobnep_source_view value params).

Definition overlap_private_ordered_bounded_non_escape_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params: overlap_private_ordered_bounded_non_escape_params value)
    (before after: PolyLang.t) : Prop :=
  check_instance_projectionb
    (opobnep_source_domain value params)
    (opobnep_source_liveouts value params)
    (overlap_tiles_targets (opobnep_tiles value params)) = true /\
  check_overlap_ordered_closureb
    (opobnep_tiles value params) = true /\
  check_private_separationb
    (opobnep_private_cells value params)
    (opobnep_public_cells value params)
    (opobnep_frame_cells value params) = true /\
  check_storage_compatibilityb
    (opobnep_private_mapping value params)
    (opobnep_logical_specs value params)
    (opobnep_private_specs value params) = true /\
  check_storage_boundsb
    (opobnep_private_bounds value params)
    (opobnep_private_cells value params) = true /\
  check_storage_boundsb
    (opobnep_commit_bounds value params)
    (opobnep_commit_cells value params) = true /\
  check_private_non_escapeb
    (opobnep_private_cells value params)
    (opobnep_escaped_cells value params) = true /\
  check_overlap_valueb
    value_eqb
    (overlap_tiles_targets (opobnep_tiles value params))
    (opobnep_target_values value params) = true /\
  check_overlap_storageb
    (opobnep_private_cells value params)
    (opobnep_commit_cells value params)
    (overlap_tiles_targets (opobnep_tiles value params))
    (opobnep_writes value params) = true /\
  overlap_source_view_refines_view
    (opobnep_input_view value params)
    (opobnep_output_view value params)
    (opobnep_source_view value params)
    after.

Theorem overlap_private_ordered_bounded_non_escape_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (overlap_private_ordered_bounded_non_escape_check params before after)
      ok ->
    ok = true ->
    overlap_private_ordered_bounded_non_escape_side_condition
      value_eqb params before after ->
    View.view_refinement
      (overlap_private_ordered_bounded_non_escape_input_view params)
      (overlap_private_ordered_bounded_non_escape_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view source_domain source_liveouts tiles target_values
     private_cells public_cells frame_cells commit_cells private_mapping
     logical_specs private_specs private_bounds commit_bounds escaped_cells
     writes source_view].
  simpl in *.
  destruct Hside as
    [Hprojection
     [Hclosure
      [Hseparation
       [Hstorage
        [Hprivate_bounds
         [Hcommit_bounds
          [Hnon_escape
           [Hvalues [Hwrites Hsemantics]]]]]]]]].
  eapply
    checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_public_refinement;
    eauto.
Qed.

Definition overlap_private_ordered_bounded_non_escape_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (overlap_private_ordered_bounded_non_escape_params value) := {|
  generic_cpvtf_input_view :=
    overlap_private_ordered_bounded_non_escape_input_view;
  generic_cpvtf_output_view :=
    overlap_private_ordered_bounded_non_escape_output_view;
  generic_cpvtf_check :=
    overlap_private_ordered_bounded_non_escape_check;
  generic_cpvtf_side_condition :=
    overlap_private_ordered_bounded_non_escape_side_condition value_eqb;
  generic_cpvtf_check_sound :=
    overlap_private_ordered_bounded_non_escape_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem overlap_closure_contract_dependency_consumer_in_targets :
  forall input_view output_view source_domain source_liveouts tiles
         source_view after tile dep,
    overlap_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_consumer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         source_view after tile dep Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _].
  eapply overlap_closure_dependency_consumer_in_targets; eauto.
Qed.

Theorem overlap_closure_contract_dependency_available :
  forall input_view output_view source_domain source_liveouts tiles
         source_view after tile dep,
    overlap_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    In (overlap_dependency_producer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         source_view after tile dep Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _].
  eapply overlap_closure_dependency_available; eauto.
Qed.

Theorem overlap_ordered_closure_contract_dependency_consumer_in_targets :
  forall input_view output_view source_domain source_liveouts tiles
         source_view after tile dep,
    overlap_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_consumer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         source_view after tile dep Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _].
  eapply overlap_ordered_closure_dependency_consumer_in_targets; eauto.
Qed.

Theorem overlap_ordered_closure_contract_dependency_available :
  forall input_view output_view source_domain source_liveouts tiles
         source_view after tile dep,
    overlap_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    In (overlap_dependency_producer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         source_view after tile dep Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _].
  eapply overlap_ordered_closure_dependency_available; eauto.
Qed.

Theorem overlap_ordered_closure_contract_dependency_ordered :
  forall input_view output_view source_domain source_liveouts tiles
         source_view after tile dep,
    overlap_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    source_precedes_in_sources
      (overlap_dependency_producer dep)
      (overlap_dependency_consumer dep)
      (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         source_view after tile dep Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _].
  eapply overlap_ordered_closure_dependency_ordered; eauto.
Qed.

Theorem overlap_private_ordered_closure_contract_dependency_consumer_in_targets :
  forall input_view output_view source_domain source_liveouts tiles
         private_cells public_cells frame_cells source_view after tile dep,
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_consumer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         private_cells public_cells frame_cells source_view after tile dep
         Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _ _].
  eapply overlap_ordered_closure_dependency_consumer_in_targets; eauto.
Qed.

Theorem overlap_private_ordered_closure_contract_dependency_available :
  forall input_view output_view source_domain source_liveouts tiles
         private_cells public_cells frame_cells source_view after tile dep,
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    In (overlap_dependency_producer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         private_cells public_cells frame_cells source_view after tile dep
         Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _ _].
  eapply overlap_ordered_closure_dependency_available; eauto.
Qed.

Theorem overlap_private_ordered_closure_contract_dependency_ordered :
  forall input_view output_view source_domain source_liveouts tiles
         private_cells public_cells frame_cells source_view after tile dep,
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    source_precedes_in_sources
      (overlap_dependency_producer dep)
      (overlap_dependency_consumer dep)
      (projected_sources (overlap_tile_targets tile)).
Proof.
  intros input_view output_view source_domain source_liveouts tiles
         private_cells public_cells frame_cells source_view after tile dep
         Hcontract Htile Hdep.
  destruct Hcontract as [_ Hclosure _ _].
  eapply overlap_ordered_closure_dependency_ordered; eauto.
Qed.

Theorem overlap_internal_write_within_private_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         writes source_view after write,
    overlap_private_ordered_closure_bounded_compatible_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs private_bounds commit_bounds
      writes source_view after ->
    In write writes ->
    projected_role (overlap_write_target write) = Internal ->
    cell_within_declared_bounds private_bounds (overlap_write_cell write).
Proof.
  intros value input_view output_view source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         writes source_view after write Hcontract Hin Hrole.
  destruct Hcontract as [Hbase Hprivate_bounds _].
  eapply storage_bounds_cell_within
    with (cells := private_cells); eauto.
  destruct Hbase as [_ Hwrites].
  eapply overlap_storage_internal_write_private; eauto.
Qed.

Theorem overlap_commit_write_within_commit_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         writes source_view after write,
    overlap_private_ordered_closure_bounded_compatible_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs private_bounds commit_bounds
      writes source_view after ->
    In write writes ->
    projected_role (overlap_write_target write) = Commit ->
    cell_within_declared_bounds commit_bounds (overlap_write_cell write).
Proof.
  intros value input_view output_view source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         writes source_view after write Hcontract Hin Hrole.
  destruct Hcontract as [Hbase _ Hcommit_bounds].
  eapply storage_bounds_cell_within
    with (cells := commit_cells); eauto.
  destruct Hbase as [_ Hwrites].
  eapply overlap_storage_commit_write_public; eauto.
Qed.

Theorem overlap_internal_write_not_escaped :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         escaped_cells writes source_view after write,
    overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells commit_cells
      private_mapping logical_specs private_specs private_bounds commit_bounds
      escaped_cells writes source_view after ->
    In write writes ->
    projected_role (overlap_write_target write) = Internal ->
    ~ In (overlap_write_cell write) escaped_cells.
Proof.
  intros value input_view output_view source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells commit_cells
         private_mapping logical_specs private_specs private_bounds commit_bounds
         escaped_cells writes source_view after write Hcontract Hin Hrole.
  destruct Hcontract as [Hbase Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  destruct Hbase as [Hbounded_base _ _].
  destruct Hbounded_base as [_ Hwrites].
  eapply overlap_storage_internal_write_private; eauto.
Qed.

End OverlapTilingValidator.
