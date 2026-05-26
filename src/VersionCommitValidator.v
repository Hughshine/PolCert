Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import InstanceProjectionWitness.
Require Import VersionCommitWitness.
Require Import VersionCommitValueWitness.
Require Import VersionReadWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.
Require Import PrivateStorageWitness.

Import ListNotations.

(** View-level wrapper for version selection and commit.

    The finite witness checks exact source-liveout coverage and unique selected
    target versions.  Read-selection witnesses additionally record that
    internal target reads use versions produced by the intended dynamic source
    writes.  Deriving those finite entries from concrete instructions remains
    part of the feature-specific semantic refinement. *)

Module VersionCommitValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_version_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_version_source_view_correct :
  forall before source_view ok,
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition version_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record version_commit_view_contract
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (source_view after: PolyLang.t) : Prop := {
  vcvc_commit :
    version_commit_obligations source_liveouts mapping;
  vcvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (entries: list (version_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcovc_commit :
    version_commit_obligations source_liveouts mapping;
  vcovc_value :
    version_value_obligations value mapping entries;
  vcovc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_compatible_view_contract
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  vccvc_commit :
    version_commit_obligations source_liveouts mapping;
  vccvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  vccvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (entries: list (version_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vccvvc_commit :
    version_commit_obligations source_liveouts mapping;
  vccvvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  vccvvc_value :
    version_value_obligations value mapping entries;
  vccvvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_read_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (commit_entries: list (version_value_entry value))
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (read_entries: list version_read_entry)
    (read_value_entries: list (version_read_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcrcvc_commit_base :
    version_commit_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_entries source_view after;
  vcrcvc_read_selection :
    version_read_selection_obligations
      expected_reads produced_versions read_entries;
  vcrcvc_read_values :
    version_read_value_obligations
      value read_entries read_value_entries;
}.

Record version_commit_bounded_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (physical_bounds: list array_bounds)
    (entries: list (version_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcbcvc_commit :
    version_commit_obligations source_liveouts mapping;
  vcbcvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  vcbcvc_target_bounds :
    storage_bounds_obligations
      physical_bounds (version_commit_versions mapping);
  vcbcvc_value :
    version_value_obligations value mapping entries;
  vcbcvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_read_bounded_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (physical_bounds: list array_bounds)
    (commit_entries: list (version_value_entry value))
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (read_entries: list version_read_entry)
    (read_value_entries: list (version_read_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcrbcvc_commit_base :
    version_commit_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs physical_bounds
      commit_entries source_view after;
  vcrbcvc_read_selection :
    version_read_selection_obligations
      expected_reads produced_versions read_entries;
  vcrbcvc_read_values :
    version_read_value_obligations
      value read_entries read_value_entries;
}.

Record version_commit_read_fully_bounded_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (commit_bounds produced_bounds: list array_bounds)
    (commit_entries: list (version_value_entry value))
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (read_entries: list version_read_entry)
    (read_value_entries: list (version_read_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcrfbcvc_commit_read_base :
    version_commit_read_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds commit_entries
      expected_reads produced_versions read_entries read_value_entries
      source_view after;
  vcrfbcvc_produced_bounds :
    storage_bounds_obligations
      produced_bounds (produced_version_versions produced_versions);
}.

Record version_commit_read_fully_bounded_compatible_non_escape_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (commit_bounds produced_bounds: list array_bounds)
    (escaped_cells: list MemCell)
    (commit_entries: list (version_value_entry value))
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (read_entries: list version_read_entry)
    (read_value_entries: list (version_read_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcrfbcnevc_full_base :
    version_commit_read_fully_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds produced_bounds
      commit_entries expected_reads produced_versions
      read_entries read_value_entries source_view after;
  vcrfbcnevc_produced_non_escape :
    private_non_escape_obligations
      (produced_version_versions produced_versions) escaped_cells;
}.

Definition version_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_version_commit_view_correct :
  forall input_view output_view source_liveouts mapping
         before source_view after ok,
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_view_contract
      input_view output_view source_liveouts mapping source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view source_liveouts mapping
         before source_view after ok Hret Hok Hcommit Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_version_commit_compatible_view_correct :
  forall input_view output_view source_liveouts mapping
         logical_specs physical_specs before source_view after ok,
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_compatible_view_contract
      input_view output_view source_liveouts mapping
      logical_specs physical_specs source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view source_liveouts mapping
         logical_specs physical_specs before source_view after ok
         Hret Hok Hcommit Hcompat Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_version_commit_view_correct
       input_view output_view source_liveouts mapping
       before source_view after ok Hret Hok Hcommit Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_version_valueb value value_eqb mapping entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_value_view_contract
      value input_view output_view source_liveouts mapping entries
      source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping entries before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hvalue Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_version_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_version_commit_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_version_valueb value value_eqb mapping entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs entries source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping logical_specs physical_specs entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hvalue Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_version_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (checked_version_commit_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping entries
       before source_view after ok Hvalue_eqb Hret Hok
       Hcommit Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_read_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_entries
         expected_reads produced_versions read_entries read_value_entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_version_valueb value value_eqb mapping commit_entries = true ->
    check_version_read_selectionb
      expected_reads produced_versions read_entries = true ->
    check_version_read_valueb
      value_eqb read_entries read_value_entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_read_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_entries
      expected_reads produced_versions read_entries read_value_entries
      source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping logical_specs physical_specs commit_entries
         expected_reads produced_versions read_entries read_value_entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_value
         Hread_selection Hread_values Hsemantics.
  pose proof
    (check_version_read_selectionb_sound
       expected_reads produced_versions read_entries Hread_selection)
    as Hread_selection_obligations.
  pose proof
    (check_version_read_valueb_sound
       value value_eqb Hvalue_eqb
       read_entries read_value_entries Hread_values)
    as Hread_value_obligations.
  pose proof
    (checked_version_commit_compatible_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs commit_entries
       before source_view after ok
       Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_value Hsemantics)
    as [Hcommit_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_bounded_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs physical_bounds entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb physical_bounds
      (version_commit_versions mapping) = true ->
    check_version_valueb value value_eqb mapping entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs physical_bounds entries source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts mapping
         logical_specs physical_specs physical_bounds entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hbounds Hvalue Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_storage_boundsb_sound
       physical_bounds (version_commit_versions mapping) Hbounds)
    as Hbounds_obligations.
  pose proof
    (check_version_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (checked_version_commit_compatible_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs entries
       before source_view after ok
       Hvalue_eqb Hret Hok Hcommit Hcompat Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_read_bounded_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs physical_bounds commit_entries
         expected_reads produced_versions read_entries read_value_entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb physical_bounds
      (version_commit_versions mapping) = true ->
    check_version_valueb value value_eqb mapping commit_entries = true ->
    check_version_read_selectionb
      expected_reads produced_versions read_entries = true ->
    check_version_read_valueb
      value_eqb read_entries read_value_entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_read_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs physical_bounds commit_entries
      expected_reads produced_versions read_entries read_value_entries
      source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping logical_specs physical_specs physical_bounds commit_entries
         expected_reads produced_versions read_entries read_value_entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hbounds Hcommit_value
         Hread_selection Hread_values Hsemantics.
  pose proof
    (check_version_read_selectionb_sound
       expected_reads produced_versions read_entries Hread_selection)
    as Hread_selection_obligations.
  pose proof
    (check_version_read_valueb_sound
       value value_eqb Hvalue_eqb
       read_entries read_value_entries Hread_values)
    as Hread_value_obligations.
  pose proof
    (checked_version_commit_bounded_compatible_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs physical_bounds commit_entries
       before source_view after ok
       Hvalue_eqb Hret Hok Hcommit Hcompat Hbounds
       Hcommit_value Hsemantics)
    as [Hcommit_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_read_fully_bounded_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds
         commit_entries expected_reads produced_versions
         read_entries read_value_entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb commit_bounds
      (version_commit_versions mapping) = true ->
    check_storage_boundsb produced_bounds
      (produced_version_versions produced_versions) = true ->
    check_version_valueb value value_eqb mapping commit_entries = true ->
    check_version_read_selectionb
      expected_reads produced_versions read_entries = true ->
    check_version_read_valueb
      value_eqb read_entries read_value_entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_read_fully_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds produced_bounds
      commit_entries expected_reads produced_versions
      read_entries read_value_entries source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping logical_specs physical_specs commit_bounds produced_bounds
         commit_entries expected_reads produced_versions
         read_entries read_value_entries before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_bounds
         Hproduced_bounds Hcommit_value Hread_selection Hread_values
         Hsemantics.
  pose proof
    (check_storage_boundsb_sound
       produced_bounds (produced_version_versions produced_versions)
       Hproduced_bounds)
    as Hproduced_bounds_obligations.
  pose proof
    (checked_version_commit_read_bounded_compatible_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs commit_bounds commit_entries
       expected_reads produced_versions read_entries read_value_entries
       before source_view after ok Hvalue_eqb Hret Hok Hcommit Hcompat
       Hcommit_bounds Hcommit_value Hread_selection Hread_values Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_read_fully_bounded_compatible_non_escape_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb commit_bounds
      (version_commit_versions mapping) = true ->
    check_storage_boundsb produced_bounds
      (produced_version_versions produced_versions) = true ->
    check_private_non_escapeb
      (produced_version_versions produced_versions) escaped_cells = true ->
    check_version_valueb value value_eqb mapping commit_entries = true ->
    check_version_read_selectionb
      expected_reads produced_versions read_entries = true ->
    check_version_read_valueb
      value_eqb read_entries read_value_entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_read_fully_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds produced_bounds escaped_cells
      commit_entries expected_reads produced_versions
      read_entries read_value_entries source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_bounds
         Hproduced_bounds Hnon_escape Hcommit_value Hread_selection
         Hread_values Hsemantics.
  pose proof
    (check_private_non_escapeb_sound
       (produced_version_versions produced_versions) escaped_cells
       Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (checked_version_commit_read_fully_bounded_compatible_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs commit_bounds produced_bounds
       commit_entries expected_reads produced_versions
       read_entries read_value_entries before source_view after ok
       Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_bounds
       Hproduced_bounds Hcommit_value Hread_selection Hread_values
       Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_read_fully_bounded_compatible_non_escape_value_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_storage_boundsb commit_bounds
      (version_commit_versions mapping) = true ->
    check_storage_boundsb produced_bounds
      (produced_version_versions produced_versions) = true ->
    check_private_non_escapeb
      (produced_version_versions produced_versions) escaped_cells = true ->
    check_version_valueb value value_eqb mapping commit_entries = true ->
    check_version_read_selectionb
      expected_reads produced_versions read_entries = true ->
    check_version_read_valueb
      value_eqb read_entries read_value_entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_bounds
         Hproduced_bounds Hnon_escape Hcommit_value Hread_selection
         Hread_values Hsemantics.
  pose proof
    (checked_version_commit_read_fully_bounded_compatible_non_escape_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs commit_bounds produced_bounds escaped_cells
       commit_entries expected_reads produced_versions
       read_entries read_value_entries before source_view after ok
       Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_bounds
       Hproduced_bounds Hnon_escape Hcommit_value Hread_selection
       Hread_values Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record version_commit_read_fully_bounded_non_escape_params (value: Type) := {
  vcrfbnep_input_view : View.view;
  vcrfbnep_output_view : View.view;
  vcrfbnep_source_liveouts : list MemCell;
  vcrfbnep_mapping : version_commit_mapping;
  vcrfbnep_logical_specs : list storage_spec;
  vcrfbnep_physical_specs : list storage_spec;
  vcrfbnep_commit_bounds : list array_bounds;
  vcrfbnep_produced_bounds : list array_bounds;
  vcrfbnep_escaped_cells : list MemCell;
  vcrfbnep_commit_entries : list (version_value_entry value);
  vcrfbnep_expected_reads : list logical_instance;
  vcrfbnep_produced_versions : produced_version_mapping;
  vcrfbnep_read_entries : list version_read_entry;
  vcrfbnep_read_value_entries : list (version_read_value_entry value);
  vcrfbnep_source_view : PolyLang.t;
}.

Definition version_commit_read_fully_bounded_non_escape_input_view
    {value: Type}
    (params: version_commit_read_fully_bounded_non_escape_params value)
    : View.view :=
  vcrfbnep_input_view value params.

Definition version_commit_read_fully_bounded_non_escape_output_view
    {value: Type}
    (params: version_commit_read_fully_bounded_non_escape_params value)
    : View.view :=
  version_pipeline_final_view (vcrfbnep_output_view value params).

Definition version_commit_read_fully_bounded_non_escape_check
    {value: Type}
    (params: version_commit_read_fully_bounded_non_escape_params value)
    (before after: PolyLang.t) : imp bool :=
  check_version_source_view before (vcrfbnep_source_view value params).

Definition version_commit_read_fully_bounded_non_escape_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params: version_commit_read_fully_bounded_non_escape_params value)
    (before after: PolyLang.t) : Prop :=
  check_version_commitb
    (vcrfbnep_source_liveouts value params)
    (vcrfbnep_mapping value params) = true /\
  check_storage_compatibilityb
    (vcrfbnep_mapping value params)
    (vcrfbnep_logical_specs value params)
    (vcrfbnep_physical_specs value params) = true /\
  check_storage_boundsb
    (vcrfbnep_commit_bounds value params)
    (version_commit_versions (vcrfbnep_mapping value params)) = true /\
  check_storage_boundsb
    (vcrfbnep_produced_bounds value params)
    (produced_version_versions
      (vcrfbnep_produced_versions value params)) = true /\
  check_private_non_escapeb
    (produced_version_versions
      (vcrfbnep_produced_versions value params))
    (vcrfbnep_escaped_cells value params) = true /\
  check_version_valueb
    value value_eqb
    (vcrfbnep_mapping value params)
    (vcrfbnep_commit_entries value params) = true /\
  check_version_read_selectionb
    (vcrfbnep_expected_reads value params)
    (vcrfbnep_produced_versions value params)
    (vcrfbnep_read_entries value params) = true /\
  check_version_read_valueb
    value_eqb
    (vcrfbnep_read_entries value params)
    (vcrfbnep_read_value_entries value params) = true /\
  version_source_view_refines_view
    (vcrfbnep_input_view value params)
    (vcrfbnep_output_view value params)
    (vcrfbnep_source_view value params)
    after.

Theorem version_commit_read_fully_bounded_non_escape_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (version_commit_read_fully_bounded_non_escape_check
        params before after)
      ok ->
    ok = true ->
    version_commit_read_fully_bounded_non_escape_side_condition
      value_eqb params before after ->
    View.view_refinement
      (version_commit_read_fully_bounded_non_escape_input_view params)
      (version_commit_read_fully_bounded_non_escape_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view source_liveouts mapping logical_specs physical_specs
     commit_bounds produced_bounds escaped_cells commit_entries expected_reads
     produced_versions read_entries read_value_entries source_view].
  simpl in *.
  destruct Hside as
    [Hcommit
     [Hcompat
      [Hcommit_bounds
       [Hproduced_bounds
        [Hnon_escape
         [Hcommit_value
          [Hread_selection [Hread_values Hsemantics]]]]]]]].
  eapply
    checked_version_commit_read_fully_bounded_compatible_non_escape_value_public_refinement;
    eauto.
Qed.

Definition version_commit_read_fully_bounded_non_escape_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (version_commit_read_fully_bounded_non_escape_params value) := {|
  generic_cpvtf_input_view :=
    version_commit_read_fully_bounded_non_escape_input_view;
  generic_cpvtf_output_view :=
    version_commit_read_fully_bounded_non_escape_output_view;
  generic_cpvtf_check :=
    version_commit_read_fully_bounded_non_escape_check;
  generic_cpvtf_side_condition :=
    version_commit_read_fully_bounded_non_escape_side_condition value_eqb;
  generic_cpvtf_check_sound :=
    version_commit_read_fully_bounded_non_escape_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem version_commit_selected_version_within_bounds :
  forall (value: Type) input_view output_view source_liveouts mapping
         logical_specs physical_specs physical_bounds entries
         source_view after source_cell version_cell,
    version_commit_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs physical_bounds entries source_view after ->
    version_commit_cell_relation mapping version_cell source_cell ->
    cell_within_declared_bounds physical_bounds version_cell.
Proof.
  intros value input_view output_view source_liveouts mapping
         logical_specs physical_specs physical_bounds entries
         source_view after source_cell version_cell Hcontract Hrel.
  destruct Hcontract as [Hcommit _ Hbounds _ _].
  eapply storage_bounds_cell_within
    with (cells := version_commit_versions mapping); eauto.
  eapply version_commit_selected_version_in_versions; eauto.
Qed.

Theorem version_read_selected_version_within_produced_bounds :
  forall (value: Type)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds
         commit_entries expected_reads produced_versions
         read_entries read_value_entries source_view after entry,
    version_commit_read_fully_bounded_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds produced_bounds
      commit_entries expected_reads produced_versions
      read_entries read_value_entries source_view after ->
    In entry read_entries ->
    cell_within_declared_bounds
      produced_bounds (vre_selected_version entry).
Proof.
  intros value input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds
         commit_entries expected_reads produced_versions
         read_entries read_value_entries source_view after entry
         Hcontract Hin.
  destruct Hcontract as [Hbase Hbounds].
  destruct Hbase as [_ Hread_selection _].
  eapply storage_bounds_cell_within
    with (cells := produced_version_versions produced_versions); eauto.
  eapply version_read_selected_version_in_produced_versions; eauto.
Qed.

Theorem version_produced_version_not_escaped :
  forall (value: Type)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries source_view after
         producer version_cell,
    version_commit_read_fully_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds produced_bounds escaped_cells
      commit_entries expected_reads produced_versions
      read_entries read_value_entries source_view after ->
    In (producer, version_cell) produced_versions ->
    ~ In version_cell escaped_cells.
Proof.
  intros value input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries source_view after
         producer version_cell Hcontract Hproduced.
  destruct Hcontract as [_ Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  eapply produced_version_pair_version_in_versions; eauto.
Qed.

Theorem version_read_selected_version_not_escaped :
  forall (value: Type)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries source_view after entry,
    version_commit_read_fully_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_bounds produced_bounds escaped_cells
      commit_entries expected_reads produced_versions
      read_entries read_value_entries source_view after ->
    In entry read_entries ->
    ~ In (vre_selected_version entry) escaped_cells.
Proof.
  intros value input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_bounds produced_bounds escaped_cells
         commit_entries expected_reads produced_versions
         read_entries read_value_entries source_view after entry
         Hcontract Hin.
  destruct Hcontract as [Hbase Hnon_escape].
  destruct Hbase as [Hread_bounded _].
  destruct Hread_bounded as [_ Hread_selection _].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  eapply version_read_selected_version_in_produced_versions; eauto.
Qed.

End VersionCommitValidator.
