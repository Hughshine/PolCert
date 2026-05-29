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

Theorem checked_bounded_inter_array_reuse_public_refinement :
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
    View.view_refinement
      input_view
      (inter_array_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs before source_view after ok
         Hret Hok Hreuse Hbounds Hsemantics.
  pose proof
    (checked_bounded_inter_array_reuse_view_correct
       input_view output_view mapping physical_bounds intervals conflicts
       logical_specs physical_specs before source_view after ok
       Hret Hok Hreuse Hbounds Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record bounded_inter_array_reuse_params := {
  biarp_input_view : View.view;
  biarp_output_view : View.view;
  biarp_mapping : reuse_mapping;
  biarp_physical_bounds : list array_bounds;
  biarp_intervals : list live_interval;
  biarp_conflicts : conflict_pairs;
  biarp_logical_specs : list storage_spec;
  biarp_physical_specs : list storage_spec;
  biarp_source_view : PolyLang.t;
}.

Definition bounded_inter_array_reuse_input_view
    (params: bounded_inter_array_reuse_params) : View.view :=
  biarp_input_view params.

Definition bounded_inter_array_reuse_output_view
    (params: bounded_inter_array_reuse_params) : View.view :=
  inter_array_pipeline_final_view (biarp_output_view params).

Definition bounded_inter_array_reuse_check
    (params: bounded_inter_array_reuse_params)
    (before after: PolyLang.t) : imp bool :=
  check_inter_array_source_view before (biarp_source_view params).

Definition bounded_inter_array_reuse_side_condition
    (params: bounded_inter_array_reuse_params)
    (before after: PolyLang.t) : Prop :=
  check_inter_array_reuseb
    (biarp_mapping params)
    (biarp_intervals params)
    (biarp_conflicts params)
    (biarp_logical_specs params)
    (biarp_physical_specs params) = true /\
  check_storage_boundsb
    (biarp_physical_bounds params)
    (reuse_mapping_targets (biarp_mapping params)) = true /\
  inter_array_source_view_refines_view
    (biarp_input_view params)
    (biarp_output_view params)
    (biarp_source_view params)
    after.

Theorem bounded_inter_array_reuse_family_sound :
  forall params before after ok,
    mayReturn
      (bounded_inter_array_reuse_check params before after) ok ->
    ok = true ->
    bounded_inter_array_reuse_side_condition params before after ->
    View.view_refinement
      (bounded_inter_array_reuse_input_view params)
      (bounded_inter_array_reuse_output_view params)
      before after.
Proof.
  intros params before after ok Hret Hok Hside.
  destruct params as
    [input_view output_view mapping physical_bounds intervals conflicts
     logical_specs physical_specs source_view].
  simpl in *.
  destruct Hside as [Hreuse [Hbounds Hsemantics]].
  eapply checked_bounded_inter_array_reuse_public_refinement; eauto.
Qed.

Definition bounded_inter_array_reuse_family
    : View.checked_parameterized_view_transform_family
        bounded_inter_array_reuse_params := {|
  generic_cpvtf_input_view :=
    bounded_inter_array_reuse_input_view;
  generic_cpvtf_output_view :=
    bounded_inter_array_reuse_output_view;
  generic_cpvtf_check :=
    bounded_inter_array_reuse_check;
  generic_cpvtf_side_condition :=
    bounded_inter_array_reuse_side_condition;
  generic_cpvtf_check_sound :=
    bounded_inter_array_reuse_family_sound;
|}.

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

Theorem bounded_inter_array_mapping_pair_within_bounds :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    In (logical_cell, physical_cell) mapping ->
    cell_within_declared_bounds physical_bounds physical_cell.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [_ _ Hbounds _].
  eapply storage_bounds_cell_within
    with (cells := reuse_mapping_targets mapping); eauto.
  eapply reuse_mapping_pair_target_in_targets; eauto.
Qed.

Theorem bounded_inter_array_mapping_pair_cell_relation :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    In (logical_cell, physical_cell) mapping ->
    reuse_cell_relation mapping physical_cell logical_cell.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [Hreuse _ _ _].
  eapply inter_array_mapping_pair_cell_relation; eauto.
Qed.

Theorem bounded_inter_array_mapping_pair_compatible_specs :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    In (logical_cell, physical_cell) mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [Hreuse _ _ _].
  eapply inter_array_mapping_pair_compatible_specs; eauto.
Qed.

Theorem bounded_inter_array_lookup_compatible_specs :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         logical_cell physical_cell Hcontract Hlookup.
  destruct Hcontract as [Hreuse _ _ _].
  eapply inter_array_lookup_compatible_specs; eauto.
Qed.

Theorem bounded_inter_array_overlap_mapped_distinct :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         left right physical_left physical_right,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    In left intervals ->
    In right intervals ->
    li_cell left <> li_cell right ->
    live_interval_overlap left right ->
    reuse_lookup (li_cell left) mapping = Some physical_left ->
    reuse_lookup (li_cell right) mapping = Some physical_right ->
    physical_left <> physical_right.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         left right physical_left physical_right Hcontract
         Hin_left Hin_right Hcells_distinct Hoverlap
         Hlookup_left Hlookup_right.
  destruct Hcontract as [Hreuse _ _ _].
  exact
    (inter_array_overlap_mapped_distinct
       mapping intervals conflicts logical_specs physical_specs
       left right physical_left physical_right
       Hreuse Hin_left Hin_right Hcells_distinct Hoverlap
       Hlookup_left Hlookup_right).
Qed.

Theorem bounded_inter_array_same_physical_not_live_overlap :
  forall input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         left right physical_cell,
    bounded_inter_array_reuse_view_contract
      input_view output_view mapping physical_bounds intervals conflicts
      logical_specs physical_specs source_view after ->
    In left intervals ->
    In right intervals ->
    li_cell left <> li_cell right ->
    reuse_lookup (li_cell left) mapping = Some physical_cell ->
    reuse_lookup (li_cell right) mapping = Some physical_cell ->
    ~ live_interval_overlap left right.
Proof.
  intros input_view output_view mapping physical_bounds intervals conflicts
         logical_specs physical_specs source_view after
         left right physical_cell Hcontract
         Hin_left Hin_right Hcells_distinct Hlookup_left Hlookup_right.
  destruct Hcontract as [Hreuse _ _ _].
  exact
    (inter_array_same_physical_not_live_overlap
       mapping intervals conflicts logical_specs physical_specs
       left right physical_cell Hreuse
       Hin_left Hin_right Hcells_distinct Hlookup_left Hlookup_right).
Qed.

End InterArrayReuseValidator.
