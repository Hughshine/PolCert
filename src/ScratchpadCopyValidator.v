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
Require Import CopyProtocolWitness.
Require Import CopyCommitWitness.
Require Import CopyInstanceWitness.
Require Import CopyMappingWitness.
Require Import CopyProtocolValueWitness.
Require Import InstanceProjectionWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** Combined wrapper for scratchpad / packing / copy-mediated local buffers.

    A real copy-mediated transformation is not just one primitive.  It usually
    combines:

      - inserted/helper target instances, checked by an instance projection
        witness;
      - local-buffer fill/use/commit ordering, checked by a copy protocol
        witness;
      - local/private storage separation from public and framed cells.

    This module packages those three finite witnesses under one composable
    [view_refinement] theorem.  The value-simulation proof that copy-in/local
    compute/copy-out implements the source computation is still an explicit
    semantic refinement obligation. *)

Module ScratchpadCopyValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_scratchpad_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_scratchpad_source_view_correct :
  forall before source_view ok,
    mayReturn (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition scratchpad_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record scratchpad_copy_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  scc_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  scc_copy_protocol :
    copy_protocol_wf copy_trace;
  scc_local_separation :
    private_separation_obligations
      local_cells public_cells frame_cells;
  scc_semantic_refinement :
    scratchpad_source_view_refines_view
      input_view output_view source_view after;
}.

Record scratchpad_copy_commit_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  scccc_base :
    scratchpad_copy_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after;
  scccc_commit_cover :
    copy_commit_obligations expected_commit_targets copy_trace;
}.

Record scratchpad_copy_instance_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccic_base :
    scratchpad_copy_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after;
  sccic_instance_trace :
    copy_instance_trace_obligations targets copy_trace;
}.

Record scratchpad_copy_instance_commit_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccicc_base :
    scratchpad_copy_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after;
  sccicc_instance_trace :
    copy_instance_trace_obligations targets copy_trace;
}.

Record scratchpad_copy_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccf_base :
    scratchpad_copy_instance_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after;
  sccf_mapping :
    copy_mapping_obligations mapping copy_trace;
  sccf_value_simulation :
    copy_value_simulation_obligations value value_trace;
}.

Record scratchpad_copy_compatible_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  scccf_base :
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after;
  scccf_storage_compatible :
    storage_compatibility_obligations mapping public_specs local_specs;
}.

Record scratchpad_copy_declared_compatible_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  sccdcf_compatible_base :
    scratchpad_copy_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after;
  sccdcf_mapping_locals_declared :
    copy_mapping_local_declaration_obligations mapping local_cells;
}.

Record scratchpad_copy_fully_declared_compatible_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  sccfdcf_compatible_base :
    scratchpad_copy_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after;
  sccfdcf_mapping_declared :
    copy_mapping_declaration_obligations mapping public_cells local_cells;
}.

Record scratchpad_copy_bounded_declared_compatible_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (bounds: list array_bounds)
    (source_view after: PolyLang.t) : Prop := {
  sccbdcf_declared_base :
    scratchpad_copy_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after;
  sccbdcf_local_bounds :
    storage_bounds_obligations bounds local_cells;
}.

Record scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (public_bounds local_bounds: list array_bounds)
    (source_view after: PolyLang.t) : Prop := {
  sccbfdcf_declared_base :
    scratchpad_copy_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after;
  sccbfdcf_public_bounds :
    storage_bounds_obligations public_bounds public_cells;
  sccbfdcf_local_bounds :
    storage_bounds_obligations local_bounds local_cells;
}.

Record scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (public_bounds local_bounds: list array_bounds)
    (escaped_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccbfdcnef_bounded_base :
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after;
  sccbfdcnef_non_escape :
    private_non_escape_obligations local_cells escaped_cells;
}.

Definition scratchpad_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_scratchpad_copy_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts targets Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_copy_protocol_wfb_sound copy_trace Hcopy)
    as Hcopy_obligations.
  pose proof
    (check_private_separationb_sound
       local_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_scratchpad_copy_commit_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hcommit Hseparation Hsemantics.
  pose proof
    (check_copy_commit_coverb_obligations_sound
       expected_commit_targets copy_trace Hcommit)
    as Hcommit_obligations.
  pose proof
    (checked_scratchpad_copy_view_correct
       input_view output_view
       source_domain source_liveouts targets copy_trace
       local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_instance_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_instance_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hinstance Hseparation Hsemantics.
  pose proof
    (check_copy_instance_traceb_obligations_sound
       targets copy_trace Hinstance)
    as Hinstance_obligations.
  pose proof
    (checked_scratchpad_copy_view_correct
       input_view output_view
       source_domain source_liveouts targets copy_trace
       local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_instance_commit_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_instance_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hcommit Hinstance Hseparation Hsemantics.
  pose proof
    (check_copy_instance_traceb_obligations_sound
       targets copy_trace Hinstance)
    as Hinstance_obligations.
  pose proof
    (checked_scratchpad_copy_commit_view_correct
       input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       copy_trace local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hcommit Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
         Hseparation Hsemantics.
  pose proof
    (check_copy_mappingb_sound mapping copy_trace Hmapping)
    as Hmapping_obligations.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_obligations.
  pose proof
    (checked_scratchpad_copy_instance_commit_view_correct
       input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       copy_trace local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hcommit Hinstance
       Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_compatible_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
         Hseparation Hstorage Hsemantics.
  pose proof
    (check_storage_compatibilityb_sound
       mapping public_specs local_specs Hstorage)
    as Hstorage_obligations.
  pose proof
    (checked_scratchpad_copy_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
       Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_declared_compatible_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_mapping_local_declarationb mapping local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
         Hvalue Hseparation Hstorage Hsemantics.
  pose proof
    (check_copy_mapping_local_declarationb_sound
       mapping local_cells Hdeclared)
    as Hdeclared_obligations.
  pose proof
    (checked_scratchpad_copy_compatible_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       public_specs local_specs
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
       Hseparation Hstorage Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_fully_declared_compatible_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_mapping_declarationb mapping public_cells local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
         Hvalue Hseparation Hstorage Hsemantics.
  pose proof
    (check_copy_mapping_declarationb_sound
       mapping public_cells local_cells Hdeclared)
    as Hdeclared_obligations.
  pose proof
    (checked_scratchpad_copy_compatible_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       public_specs local_specs
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
       Hseparation Hstorage Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_bounded_declared_compatible_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs bounds
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_mapping_local_declarationb mapping local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    check_storage_boundsb bounds local_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_bounded_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs bounds source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs bounds
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
         Hvalue Hseparation Hstorage Hbounds Hsemantics.
  pose proof
    (check_storage_boundsb_sound bounds local_cells Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_scratchpad_copy_declared_compatible_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       public_specs local_specs
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
       Hvalue Hseparation Hstorage Hsemantics)
    as [Hdeclared_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_bounded_fully_declared_compatible_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_mapping_declarationb mapping public_cells local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    check_storage_boundsb public_bounds public_cells = true ->
    check_storage_boundsb local_bounds local_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
         Hvalue Hseparation Hstorage Hpublic_bounds Hlocal_bounds
         Hsemantics.
  pose proof
    (check_storage_boundsb_sound
       public_bounds public_cells Hpublic_bounds)
    as Hpublic_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       local_bounds local_cells Hlocal_bounds)
    as Hlocal_bounds_obligations.
  pose proof
    (checked_scratchpad_copy_fully_declared_compatible_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       public_specs local_specs
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
       Hvalue Hseparation Hstorage Hsemantics)
    as [Hdeclared_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_mapping_declarationb mapping public_cells local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    check_storage_boundsb public_bounds public_cells = true ->
    check_storage_boundsb local_bounds local_cells = true ->
    check_private_non_escapeb local_cells escaped_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
         Hvalue Hseparation Hstorage Hpublic_bounds Hlocal_bounds
         Hnon_escape Hsemantics.
  pose proof
    (check_private_non_escapeb_sound
       local_cells escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (checked_scratchpad_copy_bounded_fully_declared_compatible_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       public_specs local_specs public_bounds local_bounds
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
       Hvalue Hseparation Hstorage Hpublic_bounds Hlocal_bounds
       Hsemantics)
    as [Hbounded_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_mapping_declarationb mapping public_cells local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    check_storage_boundsb public_bounds public_cells = true ->
    check_storage_boundsb local_bounds local_cells = true ->
    check_private_non_escapeb local_cells escaped_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
         Hvalue Hseparation Hstorage Hpublic_bounds Hlocal_bounds
         Hnon_escape Hsemantics.
  pose proof
    (checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       public_specs local_specs public_bounds local_bounds escaped_cells
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hdeclared
       Hvalue Hseparation Hstorage Hpublic_bounds Hlocal_bounds
       Hnon_escape Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record scratchpad_copy_bounded_non_escape_params (value: Type) := {
  scbnep_input_view : View.view;
  scbnep_output_view : View.view;
  scbnep_source_domain : list logical_instance;
  scbnep_source_liveouts : list logical_instance;
  scbnep_targets : list projected_instance;
  scbnep_expected_commit_targets : list MemCell;
  scbnep_mapping : copy_cell_mapping;
  scbnep_copy_trace : list copy_event;
  scbnep_value_trace : copy_value_trace value;
  scbnep_local_cells : list MemCell;
  scbnep_public_cells : list MemCell;
  scbnep_frame_cells : list MemCell;
  scbnep_public_specs : list storage_spec;
  scbnep_local_specs : list storage_spec;
  scbnep_public_bounds : list array_bounds;
  scbnep_local_bounds : list array_bounds;
  scbnep_escaped_cells : list MemCell;
  scbnep_source_view : PolyLang.t;
}.

Definition scratchpad_copy_bounded_non_escape_input_view {value: Type}
    (params: scratchpad_copy_bounded_non_escape_params value) : View.view :=
  scbnep_input_view value params.

Definition scratchpad_copy_bounded_non_escape_output_view {value: Type}
    (params: scratchpad_copy_bounded_non_escape_params value) : View.view :=
  scratchpad_pipeline_final_view (scbnep_output_view value params).

Definition scratchpad_copy_bounded_non_escape_check {value: Type}
    (params: scratchpad_copy_bounded_non_escape_params value)
    (before after: PolyLang.t) : imp bool :=
  check_scratchpad_source_view before (scbnep_source_view value params).

Definition scratchpad_copy_bounded_non_escape_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params: scratchpad_copy_bounded_non_escape_params value)
    (before after: PolyLang.t) : Prop :=
  check_instance_projectionb
    (scbnep_source_domain value params)
    (scbnep_source_liveouts value params)
    (scbnep_targets value params) = true /\
  check_copy_protocol_wfb
    (scbnep_copy_trace value params) = true /\
  check_copy_commit_coverb
    (scbnep_expected_commit_targets value params)
    (scbnep_copy_trace value params) = true /\
  check_copy_instance_traceb
    (scbnep_targets value params)
    (scbnep_copy_trace value params) = true /\
  check_copy_mappingb
    (scbnep_mapping value params)
    (scbnep_copy_trace value params) = true /\
  check_copy_mapping_declarationb
    (scbnep_mapping value params)
    (scbnep_public_cells value params)
    (scbnep_local_cells value params) = true /\
  check_copy_value_traceb
    value_eqb
    (scbnep_value_trace value params) = true /\
  check_private_separationb
    (scbnep_local_cells value params)
    (scbnep_public_cells value params)
    (scbnep_frame_cells value params) = true /\
  check_storage_compatibilityb
    (scbnep_mapping value params)
    (scbnep_public_specs value params)
    (scbnep_local_specs value params) = true /\
  check_storage_boundsb
    (scbnep_public_bounds value params)
    (scbnep_public_cells value params) = true /\
  check_storage_boundsb
    (scbnep_local_bounds value params)
    (scbnep_local_cells value params) = true /\
  check_private_non_escapeb
    (scbnep_local_cells value params)
    (scbnep_escaped_cells value params) = true /\
  scratchpad_source_view_refines_view
    (scbnep_input_view value params)
    (scbnep_output_view value params)
    (scbnep_source_view value params)
    after.

Theorem scratchpad_copy_bounded_non_escape_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (scratchpad_copy_bounded_non_escape_check params before after) ok ->
    ok = true ->
    scratchpad_copy_bounded_non_escape_side_condition
      value_eqb params before after ->
    View.view_refinement
      (scratchpad_copy_bounded_non_escape_input_view params)
      (scratchpad_copy_bounded_non_escape_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view source_domain source_liveouts targets
     expected_commit_targets mapping copy_trace value_trace
     local_cells public_cells frame_cells public_specs local_specs
     public_bounds local_bounds escaped_cells source_view].
  simpl in *.
  destruct Hside as
    [Hprojection
     [Hcopy
      [Hcommit
       [Hinstance
        [Hmapping
         [Hdeclared
          [Hvalue
           [Hseparation
            [Hstorage
             [Hpublic_bounds
              [Hlocal_bounds
               [Hnon_escape Hsemantics]]]]]]]]]]]].
  eapply
    checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_public_refinement;
    eauto.
Qed.

Definition scratchpad_copy_bounded_non_escape_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (scratchpad_copy_bounded_non_escape_params value) := {|
  generic_cpvtf_input_view :=
    scratchpad_copy_bounded_non_escape_input_view;
  generic_cpvtf_output_view :=
    scratchpad_copy_bounded_non_escape_output_view;
  generic_cpvtf_check :=
    scratchpad_copy_bounded_non_escape_check;
  generic_cpvtf_side_condition :=
    scratchpad_copy_bounded_non_escape_side_condition value_eqb;
  generic_cpvtf_check_sound :=
    scratchpad_copy_bounded_non_escape_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem scratchpad_copy_full_target_event :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after target,
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    In target targets ->
    exists event,
      In event copy_trace /\
      projected_role target = copy_event_projected_role event.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after target Hcontract Hin.
  destruct Hcontract as [Hbase _ _].
  destruct Hbase as [_ Hinstance].
  eapply copy_instance_trace_obligation_target_event; eauto.
Qed.

Theorem scratchpad_copy_full_event_target :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after event,
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    In event copy_trace ->
    exists target,
      In target targets /\
      projected_role target = copy_event_projected_role event.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after event Hcontract Hin.
  destruct Hcontract as [Hbase _ _].
  destruct Hbase as [_ Hinstance].
  eapply copy_instance_trace_obligation_event_target; eauto.
Qed.

Theorem scratchpad_copy_full_value_event_entry :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after copy_event',
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    In copy_event' (copy_value_trace_events value_trace) ->
    exists value_event,
      In (copy_event', value_event) value_trace /\
      copy_value_event_kind_matches copy_event' value_event /\
      copy_value_event_values_match value_event.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after copy_event' Hcontract Hin.
  destruct Hcontract as [_ _ Hvalue].
  eapply copy_value_obligation_event_entry; eauto.
Qed.

Theorem scratchpad_copy_full_trace_value_event_entry :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after copy_event',
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In copy_event' copy_trace ->
    exists value_event,
      In (copy_event', value_event) value_trace /\
      copy_value_event_kind_matches copy_event' value_event /\
      copy_value_event_values_match value_event.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after copy_event' Hcontract Hevents Hin.
  destruct Hcontract as [_ _ Hvalue].
  eapply copy_value_obligation_trace_event_entry; eauto.
Qed.

Theorem scratchpad_copy_full_copyin_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after source_cell local_cell source_value local_value,
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    In (CopyIn source_cell local_cell,
        CopyValueIn source_value local_value) value_trace ->
    source_value = local_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after source_cell local_cell source_value local_value
         Hcontract Hin.
  destruct Hcontract as [_ _ Hvalue].
  eapply copy_value_obligation_copyin_values_equal; eauto.
Qed.

Theorem scratchpad_copy_full_copyout_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after local_cell target_cell local_value target_value,
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    In (CopyOut local_cell target_cell,
        CopyValueOut local_value target_value) value_trace ->
    local_value = target_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after local_cell target_cell local_value target_value
         Hcontract Hin.
  destruct Hcontract as [_ _ Hvalue].
  eapply copy_value_obligation_copyout_values_equal; eauto.
Qed.

Theorem scratchpad_copy_full_trace_copyin_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after source_cell local_cell,
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In (CopyIn source_cell local_cell) copy_trace ->
    exists source_value local_value,
      In (CopyIn source_cell local_cell,
          CopyValueIn source_value local_value) value_trace /\
      source_value = local_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after source_cell local_cell
         Hcontract Hevents Hin.
  destruct Hcontract as [_ _ Hvalue].
  eapply copy_value_obligation_trace_copyin_values_equal; eauto.
Qed.

Theorem scratchpad_copy_full_trace_copyout_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after local_cell target_cell,
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In (CopyOut local_cell target_cell) copy_trace ->
    exists local_value target_value,
      In (CopyOut local_cell target_cell,
          CopyValueOut local_value target_value) value_trace /\
      local_value = target_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         source_view after local_cell target_cell
         Hcontract Hevents Hin.
  destruct Hcontract as [_ _ Hvalue].
  eapply copy_value_obligation_trace_copyout_values_equal; eauto.
Qed.

Theorem scratchpad_copy_bounded_fully_declared_compatible_copyin_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after source_cell local_cell source_value local_value,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    In (CopyIn source_cell local_cell,
        CopyValueIn source_value local_value) value_trace ->
    source_value = local_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after source_cell local_cell source_value local_value
         Hcontract Hin.
  destruct Hcontract as [Hdeclared _ _].
  destruct Hdeclared as [Hcompatible _].
  destruct Hcompatible as [Hfull _].
  eapply scratchpad_copy_full_copyin_values_equal; eauto.
Qed.

Theorem scratchpad_copy_bounded_fully_declared_compatible_copyout_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after local_cell target_cell local_value target_value,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    In (CopyOut local_cell target_cell,
        CopyValueOut local_value target_value) value_trace ->
    local_value = target_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after local_cell target_cell local_value target_value
         Hcontract Hin.
  destruct Hcontract as [Hdeclared _ _].
  destruct Hdeclared as [Hcompatible _].
  destruct Hcompatible as [Hfull _].
  eapply scratchpad_copy_full_copyout_values_equal; eauto.
Qed.

Theorem scratchpad_copy_bounded_fully_declared_compatible_trace_copyin_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after source_cell local_cell,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In (CopyIn source_cell local_cell) copy_trace ->
    exists source_value local_value,
      In (CopyIn source_cell local_cell,
          CopyValueIn source_value local_value) value_trace /\
      source_value = local_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after source_cell local_cell
         Hcontract Hevents Hin.
  destruct Hcontract as [Hdeclared _ _].
  destruct Hdeclared as [Hcompatible _].
  destruct Hcompatible as [Hfull _].
  eapply scratchpad_copy_full_trace_copyin_values_equal; eauto.
Qed.

Theorem scratchpad_copy_bounded_fully_declared_compatible_trace_copyout_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after local_cell target_cell,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In (CopyOut local_cell target_cell) copy_trace ->
    exists local_value target_value,
      In (CopyOut local_cell target_cell,
          CopyValueOut local_value target_value) value_trace /\
      local_value = target_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after local_cell target_cell
         Hcontract Hevents Hin.
  destruct Hcontract as [Hdeclared _ _].
  destruct Hdeclared as [Hcompatible _].
  destruct Hcompatible as [Hfull _].
  eapply scratchpad_copy_full_trace_copyout_values_equal; eauto.
Qed.

Theorem scratchpad_copy_non_escape_copyin_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after source_cell local_cell source_value local_value,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In (CopyIn source_cell local_cell,
        CopyValueIn source_value local_value) value_trace ->
    source_value = local_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after source_cell local_cell source_value local_value
         Hcontract Hin.
  destruct Hcontract as [Hbounded _].
  eapply scratchpad_copy_bounded_fully_declared_compatible_copyin_values_equal;
    eauto.
Qed.

Theorem scratchpad_copy_non_escape_copyout_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after local_cell target_cell local_value target_value,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In (CopyOut local_cell target_cell,
        CopyValueOut local_value target_value) value_trace ->
    local_value = target_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after local_cell target_cell local_value target_value
         Hcontract Hin.
  destruct Hcontract as [Hbounded _].
  eapply scratchpad_copy_bounded_fully_declared_compatible_copyout_values_equal;
    eauto.
Qed.

Theorem scratchpad_copy_non_escape_trace_copyin_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after source_cell local_cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In (CopyIn source_cell local_cell) copy_trace ->
    exists source_value local_value,
      In (CopyIn source_cell local_cell,
          CopyValueIn source_value local_value) value_trace /\
      source_value = local_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after source_cell local_cell
         Hcontract Hevents Hin.
  destruct Hcontract as [Hbounded _].
  eapply
    scratchpad_copy_bounded_fully_declared_compatible_trace_copyin_values_equal;
    eauto.
Qed.

Theorem scratchpad_copy_non_escape_trace_copyout_values_equal :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after local_cell target_cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    copy_value_trace_events value_trace = copy_trace ->
    In (CopyOut local_cell target_cell) copy_trace ->
    exists local_value target_value,
      In (CopyOut local_cell target_cell,
          CopyValueOut local_value target_value) value_trace /\
      local_value = target_value.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after local_cell target_cell
         Hcontract Hevents Hin.
  destruct Hcontract as [Hbounded _].
  eapply
    scratchpad_copy_bounded_fully_declared_compatible_trace_copyout_values_equal;
    eauto.
Qed.

Theorem scratchpad_copy_mapping_pair_compatible_specs :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         source_view after public_cell local_cell,
    scratchpad_copy_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after ->
    copy_mapping_pair mapping public_cell local_cell ->
    exists public_spec local_spec,
      In public_spec public_specs /\
      In local_spec local_specs /\
      storage_spec_cell public_spec = public_cell /\
      storage_spec_cell local_spec = local_cell /\
      storage_specs_compatible public_spec local_spec.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         source_view after public_cell local_cell Hcontract Hpair.
  destruct Hcontract as [Hcompatible _].
  destruct Hcompatible as [_ Hstorage].
  pose proof
    (storage_compatibility_mapping_entry_specs
       mapping public_specs local_specs
       (public_cell, local_cell) Hstorage Hpair)
    as (public_spec & local_spec & Hpublic_in & Hlocal_in &
        Hpublic_cell & Hlocal_cell & Hspecs).
  exists public_spec, local_spec.
  simpl in Hpublic_cell, Hlocal_cell.
  split.
  - exact Hpublic_in.
  - split.
    + exact Hlocal_in.
    + split.
      * exact Hpublic_cell.
      * split.
        -- exact Hlocal_cell.
        -- exact Hspecs.
Qed.

Theorem scratchpad_copy_mapping_pair_within_declared_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after public_cell local_cell,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    copy_mapping_pair mapping public_cell local_cell ->
    cell_within_declared_bounds public_bounds public_cell /\
    cell_within_declared_bounds local_bounds local_cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after public_cell local_cell Hcontract Hpair.
  destruct Hcontract as [Hdeclared Hpublic_bounds Hlocal_bounds].
  destruct Hdeclared as [_ Hmapping_declared].
  pose proof
    (copy_mapping_declaration_pair_declared
       mapping public_cells local_cells public_cell local_cell
       Hmapping_declared Hpair)
    as [Hpublic Hlocal].
  split.
  - eapply storage_bounds_cell_within; eauto.
  - eapply storage_bounds_cell_within; eauto.
Qed.

Theorem scratchpad_copy_non_escape_mapping_pair_compatible_specs :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after public_cell local_cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    copy_mapping_pair mapping public_cell local_cell ->
    exists public_spec local_spec,
      In public_spec public_specs /\
      In local_spec local_specs /\
      storage_spec_cell public_spec = public_cell /\
      storage_spec_cell local_spec = local_cell /\
      storage_specs_compatible public_spec local_spec.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after public_cell local_cell Hcontract Hpair.
  destruct Hcontract as [Hbounded _].
  destruct Hbounded as [Hdeclared _ _].
  eapply scratchpad_copy_mapping_pair_compatible_specs; eauto.
Qed.

Theorem scratchpad_copy_non_escape_mapping_pair_within_declared_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after public_cell local_cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    copy_mapping_pair mapping public_cell local_cell ->
    cell_within_declared_bounds public_bounds public_cell /\
    cell_within_declared_bounds local_bounds local_cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after public_cell local_cell Hcontract Hpair.
  destruct Hcontract as [Hbounded _].
  eapply scratchpad_copy_mapping_pair_within_declared_bounds; eauto.
Qed.

Theorem scratchpad_copy_mapping_local_within_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs bounds
         source_view after cell,
    scratchpad_copy_bounded_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs bounds source_view after ->
    In cell (copy_mapping_locals mapping) ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs bounds
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [Hdeclared Hbounds].
  destruct Hdeclared as [_ Hlocal_declared].
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - eapply cmld_mapping_locals_declared; eauto.
Qed.

Theorem scratchpad_copy_mapping_local_not_public :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         source_view after cell,
    scratchpad_copy_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after ->
    In cell (copy_mapping_locals mapping) ->
    ~ In cell public_cells.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [Hcompatible Hlocal_declared].
  destruct Hcompatible as [Hfull _].
  destruct Hfull as [Hinstance_commit _ _].
  destruct Hinstance_commit as [Hcommit _].
  destruct Hcommit as [Hbase _].
  destruct Hbase as [_ _ Hseparation _].
  eapply copy_mapping_declared_local_public_disjoint; eauto.
Qed.

Theorem scratchpad_copy_mapping_public_within_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    In cell (copy_mapping_publics mapping) ->
    cell_within_declared_bounds public_bounds cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after cell Hcontract Hpublic.
  destruct Hcontract as [Hdeclared Hpublic_bounds _].
  destruct Hdeclared as [_ Hmapping_declared].
  eapply storage_bounds_cell_within.
  - exact Hpublic_bounds.
  - eapply cmd_mapping_publics_declared; eauto.
Qed.

Theorem scratchpad_copy_non_escape_mapping_public_within_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In cell (copy_mapping_publics mapping) ->
    cell_within_declared_bounds public_bounds cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell Hcontract Hpublic.
  destruct Hcontract as [Hbounded _].
  eapply scratchpad_copy_mapping_public_within_bounds; eauto.
Qed.

Theorem scratchpad_copy_mapping_local_within_declared_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds source_view after ->
    In cell (copy_mapping_locals mapping) ->
    cell_within_declared_bounds local_bounds cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [Hdeclared _ Hlocal_bounds].
  destruct Hdeclared as [_ Hmapping_declared].
  eapply storage_bounds_cell_within.
  - exact Hlocal_bounds.
  - eapply cmd_mapping_locals_declared; eauto.
Qed.

Theorem scratchpad_copy_non_escape_mapping_local_within_declared_bounds :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In cell (copy_mapping_locals mapping) ->
    cell_within_declared_bounds local_bounds cell.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [Hbounded _].
  eapply scratchpad_copy_mapping_local_within_declared_bounds; eauto.
Qed.

Theorem scratchpad_copy_non_escape_mapping_local_not_public :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In cell (copy_mapping_locals mapping) ->
    ~ In cell public_cells.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [Hbounded _].
  destruct Hbounded as [Hdeclared _ _].
  destruct Hdeclared as [Hcompatible Hmapping_declared].
  destruct Hcompatible as [Hfull _].
  destruct Hfull as [Hinstance_commit _ _].
  destruct Hinstance_commit as [Hcommit _].
  destruct Hcommit as [Hbase _].
  destruct Hbase as [_ _ Hseparation _].
  eapply pso_private_public_disjoint.
  - exact Hseparation.
  - eapply cmd_mapping_locals_declared; eauto.
Qed.

Theorem scratchpad_copy_local_cell_not_escaped :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In cell local_cells ->
    ~ In cell escaped_cells.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell Hcontract Hin.
  destruct Hcontract as [_ Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint; eauto.
Qed.

Theorem scratchpad_copy_mapping_local_not_escaped :
  forall (value: Type)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell,
    scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs public_bounds local_bounds escaped_cells
      source_view after ->
    In cell (copy_mapping_locals mapping) ->
    ~ In cell escaped_cells.
Proof.
  intros value input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs public_bounds local_bounds escaped_cells
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [Hbounded Hnon_escape].
  destruct Hbounded as [Hdeclared _ _].
  destruct Hdeclared as [_ Hmapping_declared].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  eapply cmd_mapping_locals_declared; eauto.
Qed.

End ScratchpadCopyValidator.
