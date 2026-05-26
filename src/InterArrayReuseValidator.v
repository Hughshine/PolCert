Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import ReuseConflictWitness.
Require Import LifetimeConflictWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.
Require Import InterArrayReuseWitness.

Import ListNotations.

(** View-level wrapper for inter-array storage reuse.

    [InterArrayReuseWitness] packages live-interval cover, conflict-safe reuse,
    and storage compatibility.  This validator layer gives that finite witness
    the same endpoint theorem shape used by the other storage features:

      source program -> source_view -> target program

    The actual output observation remains a supplied [output_view].  For a
    concrete inter-array reuse pass, that view will usually be a reuse-boundary
    projection from shared physical cells back to the source logical cells. *)

Module InterArrayReuseValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_inter_array_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_inter_array_source_view_correct :
  forall before source_view ok,
    mayReturn (check_inter_array_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition inter_array_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record inter_array_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (logical_specs physical_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  iarvc_reuse :
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs;
  iarvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  iarvc_semantic_refinement :
    inter_array_source_view_refines_view
      input_view output_view source_view after;
}.

Record bounded_inter_array_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (physical_bounds: list array_bounds)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (logical_specs physical_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  biarvc_reuse :
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs;
  biarvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  biarvc_target_bounds :
    storage_bounds_obligations
      physical_bounds (reuse_mapping_targets mapping);
  biarvc_semantic_refinement :
    inter_array_source_view_refines_view
      input_view output_view source_view after;
}.

Definition inter_array_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_inter_array_reuse_view_correct :
  forall input_view output_view mapping intervals conflicts
         logical_specs physical_specs before source_view after ok,
    mayReturn (check_inter_array_source_view before source_view) ok ->
    ok = true ->
    check_inter_array_reuseb
      mapping intervals conflicts logical_specs physical_specs = true ->
    inter_array_source_view_refines_view
      input_view output_view source_view after ->
    inter_array_reuse_view_contract
      input_view output_view mapping intervals conflicts
      logical_specs physical_specs source_view after /\
    View.view_refinement
      input_view
      (inter_array_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping intervals conflicts
         logical_specs physical_specs before source_view after ok
         Hret Hok Hreuse Hsemantics.
  pose proof
    (check_inter_array_reuseb_sound
       mapping intervals conflicts logical_specs physical_specs Hreuse)
    as Hreuse_obligations.
  pose proof
    (inter_array_live_overlaps_reuse_separated
       mapping intervals conflicts logical_specs physical_specs
       Hreuse_obligations)
    as Hlive_reuse_safe.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_bounded_inter_array_reuse_view_correct :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs before source_view after ok,
    mayReturn (check_inter_array_source_view before source_view) ok ->
    ok = true ->
    check_inter_array_reuseb
      mapping intervals conflicts logical_specs physical_specs = true ->
    check_storage_boundsb physical_bounds
      (reuse_mapping_targets mapping) = true ->
    inter_array_source_view_refines_view
      input_view output_view source_view after ->
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after /\
    View.view_refinement
      input_view
      (inter_array_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs before source_view after ok
         Hret Hok Hreuse Hbounds Hsemantics.
  pose proof
    (check_inter_array_reuseb_sound
       mapping intervals conflicts logical_specs physical_specs Hreuse)
    as Hreuse_obligations.
  pose proof
    (inter_array_live_overlaps_reuse_separated
       mapping intervals conflicts logical_specs physical_specs
       Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (check_storage_boundsb_sound
       physical_bounds (reuse_mapping_targets mapping) Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_inter_array_reuse_view_correct
       input_view output_view mapping intervals conflicts
       logical_specs physical_specs before source_view after ok
       Hret Hok Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem bounded_inter_array_reuse_mapping_target_within_bounds :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    cell_within_declared_bounds physical_bounds physical_cell.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell Hcontract Hlookup.
  destruct Hcontract as [_ _ Hbounds _].
  eapply storage_bounds_cell_within
    with (cells := reuse_mapping_targets mapping); eauto.
  exact (reuse_lookup_target_in_targets
           mapping logical_cell physical_cell Hlookup).
Qed.

End InterArrayReuseValidator.
