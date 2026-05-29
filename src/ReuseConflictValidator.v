Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import ReuseConflictWitness.
Require Import LifetimeConflictWitness.
Require Import ReuseValueWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** View-level wrapper for conflict-safe non-injective reuse.

    The finite witness proves that the supplied reuse map separates all listed
    conflicts.  A full contraction validator still needs two larger semantic
    facts:

      - the conflict relation over-approximates live-range overlap under the
        schedule;
      - the output view projects logical cells through the reused physical
        storage at the boundary.

    This module deliberately leaves those as the explicit
    [reuse_source_view_refines_view] obligation while making the finite checker
    composable with the existing source-view schedule route. *)

Module ReuseConflictValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_reuse_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_reuse_source_view_correct :
  forall before source_view ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition reuse_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  crvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  crvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  crvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  crvvc_value :
    reuse_value_obligations value mapping entries;
  crvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record live_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  lcrvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  lcrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  lcrvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  lcrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record live_conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  lcrvvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  lcrvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  lcrvvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  lcrvvc_value :
    reuse_value_obligations value mapping entries;
  lcrvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record compatible_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  ccrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  ccrvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  ccrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record compatible_live_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  clcrvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  clcrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  clcrvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  clcrvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  clcrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record compatible_live_conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  clcrvvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  clcrvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  clcrvvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  clcrvvc_value :
    reuse_value_obligations value mapping entries;
  clcrvvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  clcrvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record bounded_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (physical_bounds: list array_bounds)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  bcrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  bcrvc_target_bounds :
    storage_bounds_obligations
      physical_bounds (reuse_mapping_targets mapping);
  bcrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record bounded_compatible_live_conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (physical_bounds: list array_bounds)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  bclcrvvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  bclcrvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  bclcrvvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  bclcrvvc_value :
    reuse_value_obligations value mapping entries;
  bclcrvvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  bclcrvvc_target_bounds :
    storage_bounds_obligations
      physical_bounds (reuse_mapping_targets mapping);
  bclcrvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Definition reuse_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_conflict_reuse_view_correct :
  forall input_view output_view mapping conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    conflict_reuse_view_contract
      input_view output_view mapping conflicts source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping conflicts
         before source_view after ok Hret Hok Hreuse Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping conflicts entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    conflict_reuse_value_view_contract
      value input_view output_view mapping conflicts entries
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping conflicts entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hreuse Hvalue Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_live_conflict_reuse_view_correct :
  forall input_view output_view mapping intervals conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    live_conflict_reuse_view_contract
      input_view output_view mapping intervals conflicts
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping intervals conflicts
         before source_view after ok Hret Hok Hlive Hreuse Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (checked_conflict_reuse_view_correct
       input_view output_view mapping conflicts
       before source_view after ok Hret Hok Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_compatible_conflict_reuse_view_correct :
  forall input_view output_view mapping logical_specs physical_specs conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    compatible_conflict_reuse_view_contract
      input_view output_view mapping logical_specs physical_specs conflicts
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping logical_specs physical_specs conflicts
         before source_view after ok Hret Hok Hreuse Hcompat Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_conflict_reuse_view_correct
       input_view output_view mapping conflicts
       before source_view after ok Hret Hok Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_compatible_live_conflict_reuse_view_correct :
  forall input_view output_view mapping logical_specs physical_specs
         intervals conflicts before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    compatible_live_conflict_reuse_view_contract
      input_view output_view mapping logical_specs physical_specs
      intervals conflicts source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping logical_specs physical_specs
         intervals conflicts before source_view after ok
         Hret Hok Hlive Hreuse Hcompat Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_live_conflict_reuse_view_correct
       input_view output_view mapping intervals conflicts
       before source_view after ok Hret Hok Hlive Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_live_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping intervals conflicts entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    live_conflict_reuse_value_view_contract
      value input_view output_view mapping intervals conflicts entries
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping intervals conflicts
         entries before source_view after ok
         Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (checked_conflict_reuse_value_view_correct
       value value_eqb input_view output_view mapping conflicts entries
       before source_view after ok Hvalue_eqb Hret Hok
       Hreuse Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_compatible_live_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping logical_specs physical_specs
         intervals conflicts entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      intervals conflicts entries source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping
         logical_specs physical_specs intervals conflicts entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hcompat Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_live_conflict_reuse_value_view_correct
       value value_eqb input_view output_view mapping
       intervals conflicts entries before source_view after ok
       Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_bounded_conflict_reuse_view_correct :
  forall input_view output_view mapping physical_bounds conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_storage_boundsb physical_bounds
      (reuse_mapping_targets mapping) = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    bounded_conflict_reuse_view_contract
      input_view output_view mapping physical_bounds conflicts
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping physical_bounds conflicts
         before source_view after ok Hret Hok Hreuse Hbounds Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_storage_boundsb_sound
       physical_bounds (reuse_mapping_targets mapping) Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_conflict_reuse_view_correct
       input_view output_view mapping conflicts
       before source_view after ok Hret Hok Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_bounded_compatible_live_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb physical_bounds
      (reuse_mapping_targets mapping) = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hcompat Hbounds Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_storage_boundsb_sound
       physical_bounds (reuse_mapping_targets mapping) Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_compatible_live_conflict_reuse_value_view_correct
       value value_eqb input_view output_view mapping
       logical_specs physical_specs intervals conflicts entries
       before source_view after ok Hvalue_eqb Hret Hok
       Hlive Hreuse Hvalue Hcompat Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_bounded_compatible_live_conflict_reuse_value_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb physical_bounds
      (reuse_mapping_targets mapping) = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hcompat Hbounds Hsemantics.
  pose proof
    (checked_bounded_compatible_live_conflict_reuse_value_view_correct
       value value_eqb input_view output_view mapping logical_specs physical_specs
       physical_bounds intervals conflicts entries before source_view after ok
       Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hcompat Hbounds Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record bounded_compatible_live_conflict_reuse_value_params
    (value: Type) := {
  bclcrvp_input_view : View.view;
  bclcrvp_output_view : View.view;
  bclcrvp_mapping : reuse_mapping;
  bclcrvp_logical_specs : list storage_spec;
  bclcrvp_physical_specs : list storage_spec;
  bclcrvp_physical_bounds : list array_bounds;
  bclcrvp_intervals : list live_interval;
  bclcrvp_conflicts : conflict_pairs;
  bclcrvp_entries : list (reuse_value_entry value);
  bclcrvp_source_view : PolyLang.t;
}.

Definition bounded_compatible_live_conflict_reuse_value_input_view
    {value: Type}
    (params: bounded_compatible_live_conflict_reuse_value_params value)
    : View.view :=
  bclcrvp_input_view value params.

Definition bounded_compatible_live_conflict_reuse_value_output_view
    {value: Type}
    (params: bounded_compatible_live_conflict_reuse_value_params value)
    : View.view :=
  reuse_pipeline_final_view (bclcrvp_output_view value params).

Definition bounded_compatible_live_conflict_reuse_value_check
    {value: Type}
    (params: bounded_compatible_live_conflict_reuse_value_params value)
    (before after: PolyLang.t) : imp bool :=
  check_reuse_source_view before (bclcrvp_source_view value params).

Definition bounded_compatible_live_conflict_reuse_value_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params: bounded_compatible_live_conflict_reuse_value_params value)
    (before after: PolyLang.t) : Prop :=
  check_live_conflictb
    (bclcrvp_intervals value params)
    (bclcrvp_conflicts value params) = true /\
  check_conflict_safe_reuseb
    (bclcrvp_mapping value params)
    (bclcrvp_conflicts value params) = true /\
  check_reuse_valueb
    value value_eqb
    (bclcrvp_mapping value params)
    (bclcrvp_entries value params) = true /\
  check_storage_compatibilityb
    (bclcrvp_mapping value params)
    (bclcrvp_logical_specs value params)
    (bclcrvp_physical_specs value params) = true /\
  check_storage_boundsb
    (bclcrvp_physical_bounds value params)
    (reuse_mapping_targets (bclcrvp_mapping value params)) = true /\
  reuse_source_view_refines_view
    (bclcrvp_input_view value params)
    (bclcrvp_output_view value params)
    (bclcrvp_source_view value params)
    after.

Theorem bounded_compatible_live_conflict_reuse_value_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (bounded_compatible_live_conflict_reuse_value_check
        params before after)
      ok ->
    ok = true ->
    bounded_compatible_live_conflict_reuse_value_side_condition
      value_eqb params before after ->
    View.view_refinement
      (bounded_compatible_live_conflict_reuse_value_input_view params)
      (bounded_compatible_live_conflict_reuse_value_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view mapping logical_specs physical_specs
     physical_bounds intervals conflicts entries source_view].
  simpl in *.
  destruct Hside as
    [Hlive [Hreuse [Hvalue [Hcompat [Hbounds Hsemantics]]]]].
  eapply checked_bounded_compatible_live_conflict_reuse_value_public_refinement;
    eauto.
Qed.

Definition bounded_compatible_live_conflict_reuse_value_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (bounded_compatible_live_conflict_reuse_value_params value) := {|
  generic_cpvtf_input_view :=
    bounded_compatible_live_conflict_reuse_value_input_view;
  generic_cpvtf_output_view :=
    bounded_compatible_live_conflict_reuse_value_output_view;
  generic_cpvtf_check :=
    bounded_compatible_live_conflict_reuse_value_check;
  generic_cpvtf_side_condition :=
    bounded_compatible_live_conflict_reuse_value_side_condition value_eqb;
  generic_cpvtf_check_sound :=
    bounded_compatible_live_conflict_reuse_value_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem bounded_reuse_mapping_target_within_bounds :
  forall input_view output_view mapping physical_bounds conflicts
         source_view after logical_cell physical_cell,
    bounded_conflict_reuse_view_contract
      input_view output_view mapping physical_bounds conflicts
      source_view after ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    cell_within_declared_bounds physical_bounds physical_cell.
Proof.
  intros input_view output_view mapping physical_bounds conflicts
         source_view after logical_cell physical_cell Hcontract Hlookup.
  destruct Hcontract as [_ Hbounds _].
  eapply storage_bounds_cell_within
    with (cells := reuse_mapping_targets mapping); eauto.
  exact (reuse_lookup_target_in_targets
           mapping logical_cell physical_cell Hlookup).
Qed.

Theorem bounded_reuse_mapping_pair_within_bounds :
  forall input_view output_view mapping physical_bounds conflicts
         source_view after logical_cell physical_cell,
    bounded_conflict_reuse_view_contract
      input_view output_view mapping physical_bounds conflicts
      source_view after ->
    In (logical_cell, physical_cell) mapping ->
    cell_within_declared_bounds physical_bounds physical_cell.
Proof.
  intros input_view output_view mapping physical_bounds conflicts
         source_view after logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [_ Hbounds _].
  eapply storage_bounds_cell_within
    with (cells := reuse_mapping_targets mapping); eauto.
  eapply reuse_mapping_pair_target_in_targets; eauto.
Qed.

Theorem compatible_conflict_reuse_mapping_pair_compatible_specs :
  forall input_view output_view mapping logical_specs physical_specs conflicts
         source_view after logical_cell physical_cell,
    compatible_conflict_reuse_view_contract
      input_view output_view mapping logical_specs physical_specs conflicts
      source_view after ->
    In (logical_cell, physical_cell) mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros input_view output_view mapping logical_specs physical_specs conflicts
         source_view after logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [_ Hcompatible _].
  destruct
    (storage_compatibility_mapping_entry_specs
       mapping logical_specs physical_specs
       (logical_cell, physical_cell) Hcompatible Hin)
    as (logical_spec & physical_spec &
        Hlogical_in & Hphysical_in & Hlogical_cell &
        Hphysical_cell & Hcompatible_specs).
  simpl in Hlogical_cell, Hphysical_cell.
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical_in.
  - split.
    + exact Hphysical_in.
    + split.
      * exact Hlogical_cell.
      * split.
        -- exact Hphysical_cell.
        -- exact Hcompatible_specs.
Qed.

Theorem bounded_compatible_live_reuse_mapping_target_within_bounds :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after logical_cell physical_cell,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    cell_within_declared_bounds physical_bounds physical_cell.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after
         logical_cell physical_cell Hcontract Hlookup.
  destruct Hcontract as [_ _ _ _ _ Hbounds _].
  eapply storage_bounds_cell_within
    with (cells := reuse_mapping_targets mapping); eauto.
  exact (reuse_lookup_target_in_targets
           mapping logical_cell physical_cell Hlookup).
Qed.

Theorem bounded_compatible_live_reuse_mapping_pair_within_bounds :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after logical_cell physical_cell,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    In (logical_cell, physical_cell) mapping ->
    cell_within_declared_bounds physical_bounds physical_cell.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after
         logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [_ _ _ _ _ Hbounds _].
  eapply storage_bounds_cell_within
    with (cells := reuse_mapping_targets mapping); eauto.
  eapply reuse_mapping_pair_target_in_targets; eauto.
Qed.

Theorem bounded_compatible_live_reuse_mapping_pair_compatible_specs :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after logical_cell physical_cell,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    In (logical_cell, physical_cell) mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after
         logical_cell physical_cell Hcontract Hin.
  destruct Hcontract as [_ _ _ _ Hcompatible _ _].
  destruct
    (storage_compatibility_mapping_entry_specs
       mapping logical_specs physical_specs
       (logical_cell, physical_cell) Hcompatible Hin)
    as (logical_spec & physical_spec &
        Hlogical_in & Hphysical_in & Hlogical_cell &
        Hphysical_cell & Hcompatible_specs).
  simpl in Hlogical_cell, Hphysical_cell.
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical_in.
  - split.
    + exact Hphysical_in.
    + split.
      * exact Hlogical_cell.
      * split.
        -- exact Hphysical_cell.
        -- exact Hcompatible_specs.
Qed.

Theorem bounded_compatible_live_reuse_lookup_compatible_specs :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after logical_cell physical_cell,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after
         logical_cell physical_cell Hcontract Hlookup.
  destruct Hcontract as [_ _ _ _ Hcompatible _ _].
  assert (In (logical_cell, physical_cell) mapping) as Hin.
  {
    destruct
      (reuse_lookup_sound logical_cell physical_cell mapping Hlookup)
      as [Hin | (logical_cell' & Hin & Hlogical_eq)].
    - exact Hin.
    - rewrite <- Hlogical_eq in Hin.
      exact Hin.
  }
  destruct
    (storage_compatibility_mapping_entry_specs
       mapping logical_specs physical_specs
       (logical_cell, physical_cell) Hcompatible Hin)
    as (logical_spec & physical_spec &
        Hlogical_in & Hphysical_in & Hlogical_cell &
        Hphysical_cell & Hcompatible_specs).
  simpl in Hlogical_cell, Hphysical_cell.
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical_in.
  - split.
    + exact Hphysical_in.
    + split.
      * exact Hlogical_cell.
      * split.
        -- exact Hphysical_cell.
        -- exact Hcompatible_specs.
Qed.

Theorem bounded_compatible_live_reuse_value_entry_mapping_pair :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after entry,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    In entry entries ->
    exists logical_cell physical_cell,
      In (logical_cell, physical_cell) mapping /\
      logical_cell = rve_logical_cell entry /\
      physical_cell = rve_physical_cell entry /\
      reuse_value_entry_value_match entry.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after entry
         Hcontract Hin.
  destruct Hcontract as [_ _ _ Hvalues _ _ _].
  destruct
    (reuse_value_obligation_entry_in_mapping
       value mapping entries entry Hvalues Hin)
    as ([logical_cell physical_cell] &
        Hmapping_in & Hcells & Hvalue_match).
  unfold reuse_value_entry_cells_match in Hcells.
  simpl in Hcells.
  destruct Hcells as [Hlogical_cell Hphysical_cell].
  exists logical_cell, physical_cell.
  repeat split; assumption.
Qed.

Theorem bounded_compatible_live_reuse_value_entry_values_equal :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after entry,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    In entry entries ->
    rve_logical_value entry = rve_physical_value entry.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after entry
         Hcontract Hin.
  destruct
    (bounded_compatible_live_reuse_value_entry_mapping_pair
       value input_view output_view mapping logical_specs physical_specs
       physical_bounds intervals conflicts entries source_view after entry
       Hcontract Hin)
    as (_ & _ & _ & _ & _ & Hvalue_match).
  exact Hvalue_match.
Qed.

Theorem bounded_compatible_live_reuse_value_entry_within_bounds :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after entry,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    In entry entries ->
    cell_within_declared_bounds physical_bounds (rve_physical_cell entry).
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after entry
         Hcontract Hin.
  destruct
    (bounded_compatible_live_reuse_value_entry_mapping_pair
       value input_view output_view mapping logical_specs physical_specs
       physical_bounds intervals conflicts entries source_view after entry
       Hcontract Hin)
    as (logical_cell & physical_cell &
        Hmapping_in & _ & Hphysical_cell & _).
  rewrite <- Hphysical_cell.
  eapply bounded_compatible_live_reuse_mapping_pair_within_bounds; eauto.
Qed.

Theorem bounded_compatible_live_reuse_value_entry_compatible_specs :
  forall (value: Type) input_view output_view mapping
         logical_specs physical_specs physical_bounds intervals conflicts entries
         source_view after entry,
    bounded_compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      physical_bounds intervals conflicts entries source_view after ->
    In entry entries ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = rve_logical_cell entry /\
      storage_spec_cell physical_spec = rve_physical_cell entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros value input_view output_view mapping logical_specs physical_specs
         physical_bounds intervals conflicts entries source_view after entry
         Hcontract Hin.
  destruct
    (bounded_compatible_live_reuse_value_entry_mapping_pair
       value input_view output_view mapping logical_specs physical_specs
       physical_bounds intervals conflicts entries source_view after entry
       Hcontract Hin)
    as (logical_cell & physical_cell &
        Hmapping_in & Hlogical_cell & Hphysical_cell & _).
  destruct
    (bounded_compatible_live_reuse_mapping_pair_compatible_specs
       value input_view output_view mapping logical_specs physical_specs
       physical_bounds intervals conflicts entries source_view after
       logical_cell physical_cell Hcontract Hmapping_in)
    as (logical_spec & physical_spec &
        Hlogical_in & Hphysical_in & Hlogical_spec_cell &
        Hphysical_spec_cell & Hcompatible_specs).
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical_in.
  - split.
    + exact Hphysical_in.
    + split.
      * rewrite <- Hlogical_cell.
        exact Hlogical_spec_cell.
      * split.
        -- rewrite <- Hphysical_cell.
           exact Hphysical_spec_cell.
        -- exact Hcompatible_specs.
Qed.

End ReuseConflictValidator.
