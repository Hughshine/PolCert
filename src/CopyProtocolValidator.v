Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import CopyProtocolWitness.
Require Import CopyCommitWitness.
Require Import CopyMappingWitness.
Require Import CopyProtocolValueWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** View-level wrapper for copy-mediated local storage.

    [CopyProtocolWitness] checks the finite copy/local/commit bookkeeping.  It
    does not prove that target instructions simulate source instructions.  This
    module gives that witness a composable theorem shape:

      1. [before -> source_view] is checked by the existing scheduler route;
      2. [source_view -> after] supplies a feature-specific semantic refinement
         under explicit input/output views;
      3. the copy witness is returned as a local obligation and the whole pass
         composes into one [view_refinement].

    This keeps the protocol checker useful without weakening the existing
    [State.eq] pipeline or pretending that copy bookkeeping is full semantic
    correctness. *)

Module CopyProtocolValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_copy_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_copy_source_view_correct :
  forall before source_view ok,
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition copy_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record copy_protocol_view_contract
    (input_view output_view: View.view)
    (trace: list copy_event)
    (source_view after: PolyLang.t) : Prop := {
  cpvc_protocol :
    copy_protocol_wf trace;
  cpvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpvvc_protocol :
    copy_protocol_wf trace;
  cpvvc_value_simulation :
    copy_value_simulation_obligations value value_trace;
  cpvvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_mapping_view_contract
    (input_view output_view: View.view)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (source_view after: PolyLang.t) : Prop := {
  cpmvc_protocol :
    copy_protocol_wf trace;
  cpmvc_mapping :
    copy_mapping_obligations mapping trace;
  cpmvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_mapping_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpmvvc_protocol :
    copy_protocol_wf trace;
  cpmvvc_mapping :
    copy_mapping_obligations mapping trace;
  cpmvvc_value_simulation :
    copy_value_simulation_obligations value value_trace;
  cpmvvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_commit_mapping_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpcmvvc_protocol :
    copy_protocol_wf trace;
  cpcmvvc_commit_cover :
    copy_commit_obligations expected_commit_targets trace;
  cpcmvvc_mapping :
    copy_mapping_obligations mapping trace;
  cpcmvvc_value_simulation :
    copy_value_simulation_obligations value value_trace;
  cpcmvvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_commit_mapping_bounded_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (expected_commit_targets: list MemCell)
    (commit_bounds: list array_bounds)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpcmbvvc_base :
    copy_protocol_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace source_view after;
  cpcmbvvc_commit_bounds :
    storage_bounds_obligations commit_bounds expected_commit_targets;
}.

Record copy_protocol_declared_bounded_compatible_commit_mapping_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (public_cells local_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (commit_bounds public_bounds local_bounds: list array_bounds)
    (source_view after: PolyLang.t) : Prop := {
  cpdbccmvvc_base :
    copy_protocol_commit_mapping_bounded_value_view_contract
      value input_view output_view expected_commit_targets commit_bounds
      mapping trace value_trace source_view after;
  cpdbccmvvc_mapping_declared :
    copy_mapping_declaration_obligations
      mapping public_cells local_cells;
  cpdbccmvvc_storage_compatible :
    storage_compatibility_obligations
      mapping public_specs local_specs;
  cpdbccmvvc_public_bounds :
    storage_bounds_obligations public_bounds public_cells;
  cpdbccmvvc_local_bounds :
    storage_bounds_obligations local_bounds local_cells;
}.

Definition copy_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_copy_protocol_view_correct :
  forall input_view output_view trace before source_view after ok,
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_view_contract
      input_view output_view trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view trace before source_view after ok
         Hret Hok Hprotocol Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_mapping_view_correct :
  forall input_view output_view mapping trace before source_view after ok,
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_mappingb mapping trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_mapping_view_contract
      input_view output_view mapping trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping trace before source_view after ok
         Hret Hok Hprotocol Hmapping Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_mappingb_sound mapping trace Hmapping)
    as Hcopy_mapping.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view trace value_trace
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_value_view_contract
      value input_view output_view trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view trace value_trace
         before source_view after ok Hvalue_eqb Hret Hok
         Hprotocol Hvalue Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_mapping_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping trace value_trace
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_mapping_value_view_contract
      value input_view output_view mapping trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping trace value_trace
         before source_view after ok Hvalue_eqb Hret Hok
         Hprotocol Hmapping Hvalue Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_mappingb_sound mapping trace Hmapping)
    as Hcopy_mapping.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_commit_mapping_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view expected_commit_targets
         mapping trace value_trace before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_commit_coverb expected_commit_targets trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view expected_commit_targets
         mapping trace value_trace before source_view after ok
         Hvalue_eqb Hret Hok Hprotocol Hcommit Hmapping Hvalue
         Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_commit_coverb_obligations_sound
       expected_commit_targets trace Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_copy_mappingb_sound mapping trace Hmapping)
    as Hcopy_mapping.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_commit_mapping_bounded_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view expected_commit_targets commit_bounds
         mapping trace value_trace before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_commit_coverb expected_commit_targets trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_storage_boundsb commit_bounds expected_commit_targets = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_commit_mapping_bounded_value_view_contract
      value input_view output_view expected_commit_targets commit_bounds
      mapping trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view expected_commit_targets
         commit_bounds mapping trace value_trace before source_view after ok
         Hvalue_eqb Hret Hok Hprotocol Hcommit Hmapping Hvalue Hbounds
         Hcopy_semantics.
  pose proof
    (checked_copy_protocol_commit_mapping_value_view_correct
       value value_eqb input_view output_view expected_commit_targets
       mapping trace value_trace before source_view after ok
       Hvalue_eqb Hret Hok Hprotocol Hcommit Hmapping Hvalue
       Hcopy_semantics)
    as [Hbase Hview].
  pose proof
    (check_storage_boundsb_sound
       commit_bounds expected_commit_targets Hbounds)
    as Hbounds_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view expected_commit_targets
         mapping trace value_trace
         public_cells local_cells public_specs local_specs
         commit_bounds public_bounds local_bounds
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_commit_coverb expected_commit_targets trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_mapping_declarationb
      mapping public_cells local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_storage_compatibilityb
      mapping public_specs local_specs = true ->
    check_storage_boundsb commit_bounds expected_commit_targets = true ->
    check_storage_boundsb public_bounds public_cells = true ->
    check_storage_boundsb local_bounds local_cells = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_declared_bounded_compatible_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace public_cells local_cells
      public_specs local_specs commit_bounds public_bounds local_bounds
      source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         before source_view after ok Hvalue_eqb Hret Hok Hprotocol
         Hcommit Hmapping Hdeclared Hvalue Hcompatible Hcommit_bounds
         Hpublic_bounds Hlocal_bounds Hcopy_semantics.
  pose proof
    (checked_copy_protocol_commit_mapping_bounded_value_view_correct
       value value_eqb input_view output_view expected_commit_targets
       commit_bounds mapping trace value_trace before source_view after ok
       Hvalue_eqb Hret Hok Hprotocol Hcommit Hmapping Hvalue
       Hcommit_bounds Hcopy_semantics)
    as [Hbase Hview].
  pose proof
    (check_copy_mapping_declarationb_sound
       mapping public_cells local_cells Hdeclared)
    as Hdeclared_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping public_specs local_specs Hcompatible)
    as Hcompatible_obligations.
  pose proof
    (check_storage_boundsb_sound
       public_bounds public_cells Hpublic_bounds)
    as Hpublic_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       local_bounds local_cells Hlocal_bounds)
    as Hlocal_bounds_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view expected_commit_targets
         mapping trace value_trace
         public_cells local_cells public_specs local_specs
         commit_bounds public_bounds local_bounds
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_commit_coverb expected_commit_targets trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_mapping_declarationb
      mapping public_cells local_cells = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_storage_compatibilityb
      mapping public_specs local_specs = true ->
    check_storage_boundsb commit_bounds expected_commit_targets = true ->
    check_storage_boundsb public_bounds public_cells = true ->
    check_storage_boundsb local_bounds local_cells = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         before source_view after ok Hvalue_eqb Hret Hok Hprotocol
         Hcommit Hmapping Hdeclared Hvalue Hcompatible Hcommit_bounds
         Hpublic_bounds Hlocal_bounds Hcopy_semantics.
  pose proof
    (checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_view_correct
       value value_eqb input_view output_view expected_commit_targets
       mapping trace value_trace public_cells local_cells
       public_specs local_specs commit_bounds public_bounds local_bounds
       before source_view after ok Hvalue_eqb Hret Hok Hprotocol
       Hcommit Hmapping Hdeclared Hvalue Hcompatible Hcommit_bounds
       Hpublic_bounds Hlocal_bounds Hcopy_semantics)
    as [_ Hview].
  exact Hview.
Qed.

Record copy_protocol_declared_bounded_compatible_commit_mapping_value_params
    (value: Type) := {
  cpdbccmvp_input_view : View.view;
  cpdbccmvp_output_view : View.view;
  cpdbccmvp_expected_commit_targets : list MemCell;
  cpdbccmvp_mapping : copy_cell_mapping;
  cpdbccmvp_trace : list copy_event;
  cpdbccmvp_value_trace : copy_value_trace value;
  cpdbccmvp_public_cells : list MemCell;
  cpdbccmvp_local_cells : list MemCell;
  cpdbccmvp_public_specs : list storage_spec;
  cpdbccmvp_local_specs : list storage_spec;
  cpdbccmvp_commit_bounds : list array_bounds;
  cpdbccmvp_public_bounds : list array_bounds;
  cpdbccmvp_local_bounds : list array_bounds;
  cpdbccmvp_source_view : PolyLang.t;
}.

Definition copy_protocol_declared_bounded_compatible_commit_mapping_value_input_view
    {value: Type}
    (params:
      copy_protocol_declared_bounded_compatible_commit_mapping_value_params
        value) : View.view :=
  cpdbccmvp_input_view value params.

Definition copy_protocol_declared_bounded_compatible_commit_mapping_value_output_view
    {value: Type}
    (params:
      copy_protocol_declared_bounded_compatible_commit_mapping_value_params
        value) : View.view :=
  copy_pipeline_final_view (cpdbccmvp_output_view value params).

Definition copy_protocol_declared_bounded_compatible_commit_mapping_value_check
    {value: Type}
    (params:
      copy_protocol_declared_bounded_compatible_commit_mapping_value_params
        value)
    (before after: PolyLang.t) : imp bool :=
  check_copy_source_view before (cpdbccmvp_source_view value params).

Definition copy_protocol_declared_bounded_compatible_commit_mapping_value_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params:
      copy_protocol_declared_bounded_compatible_commit_mapping_value_params
        value)
    (before after: PolyLang.t) : Prop :=
  check_copy_protocol_wfb
    (cpdbccmvp_trace value params) = true /\
  check_copy_commit_coverb
    (cpdbccmvp_expected_commit_targets value params)
    (cpdbccmvp_trace value params) = true /\
  check_copy_mappingb
    (cpdbccmvp_mapping value params)
    (cpdbccmvp_trace value params) = true /\
  check_copy_mapping_declarationb
    (cpdbccmvp_mapping value params)
    (cpdbccmvp_public_cells value params)
    (cpdbccmvp_local_cells value params) = true /\
  check_copy_value_traceb
    value_eqb
    (cpdbccmvp_value_trace value params) = true /\
  check_storage_compatibilityb
    (cpdbccmvp_mapping value params)
    (cpdbccmvp_public_specs value params)
    (cpdbccmvp_local_specs value params) = true /\
  check_storage_boundsb
    (cpdbccmvp_commit_bounds value params)
    (cpdbccmvp_expected_commit_targets value params) = true /\
  check_storage_boundsb
    (cpdbccmvp_public_bounds value params)
    (cpdbccmvp_public_cells value params) = true /\
  check_storage_boundsb
    (cpdbccmvp_local_bounds value params)
    (cpdbccmvp_local_cells value params) = true /\
  copy_source_view_refines_view
    (cpdbccmvp_input_view value params)
    (cpdbccmvp_output_view value params)
    (cpdbccmvp_source_view value params)
    after.

Theorem copy_protocol_declared_bounded_compatible_commit_mapping_value_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (copy_protocol_declared_bounded_compatible_commit_mapping_value_check
        params before after)
      ok ->
    ok = true ->
    copy_protocol_declared_bounded_compatible_commit_mapping_value_side_condition
      value_eqb params before after ->
    View.view_refinement
      (copy_protocol_declared_bounded_compatible_commit_mapping_value_input_view
        params)
      (copy_protocol_declared_bounded_compatible_commit_mapping_value_output_view
        params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view expected_commit_targets mapping trace value_trace
     public_cells local_cells public_specs local_specs
     commit_bounds public_bounds local_bounds source_view].
  simpl in *.
  destruct Hside as
    [Hprotocol
     [Hcommit
      [Hmapping
       [Hdeclared
        [Hvalue
         [Hcompatible
          [Hcommit_bounds
           [Hpublic_bounds [Hlocal_bounds Hsemantics]]]]]]]]].
  eapply
    checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_public_refinement;
    eauto.
Qed.

Definition copy_protocol_declared_bounded_compatible_commit_mapping_value_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (copy_protocol_declared_bounded_compatible_commit_mapping_value_params
          value) := {|
  generic_cpvtf_input_view :=
    copy_protocol_declared_bounded_compatible_commit_mapping_value_input_view;
  generic_cpvtf_output_view :=
    copy_protocol_declared_bounded_compatible_commit_mapping_value_output_view;
  generic_cpvtf_check :=
    copy_protocol_declared_bounded_compatible_commit_mapping_value_check;
  generic_cpvtf_side_condition :=
    copy_protocol_declared_bounded_compatible_commit_mapping_value_side_condition
      value_eqb;
  generic_cpvtf_check_sound :=
    copy_protocol_declared_bounded_compatible_commit_mapping_value_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem copy_protocol_expected_commit_target_within_bounds :
  forall (value: Type) input_view output_view
         expected_commit_targets commit_bounds mapping trace value_trace
         source_view after cell,
    copy_protocol_commit_mapping_bounded_value_view_contract
      value input_view output_view expected_commit_targets commit_bounds
      mapping trace value_trace source_view after ->
    In cell expected_commit_targets ->
    cell_within_declared_bounds commit_bounds cell.
Proof.
  intros value input_view output_view
         expected_commit_targets commit_bounds mapping trace value_trace
         source_view after cell Hcontract Hin.
  destruct Hcontract as [_ Hbounds].
  eapply storage_bounds_cell_within; eauto.
Qed.

Theorem copy_protocol_committed_target_within_bounds :
  forall (value: Type) input_view output_view
         expected_commit_targets commit_bounds mapping trace value_trace
         source_view after cell,
    copy_protocol_commit_mapping_bounded_value_view_contract
      value input_view output_view expected_commit_targets commit_bounds
      mapping trace value_trace source_view after ->
    In cell (copy_protocol_committed_targets trace) ->
    cell_within_declared_bounds commit_bounds cell.
Proof.
  intros value input_view output_view
         expected_commit_targets commit_bounds mapping trace value_trace
         source_view after cell Hcontract Hcommitted.
  destruct Hcontract as [Hbase Hbounds].
  destruct Hbase as [_ Hcommit _ _ _].
  destruct Hcommit as [[_ Hcover]].
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - apply (proj2 (Hcover cell)).
    exact Hcommitted.
Qed.

Theorem copy_protocol_mapping_public_within_bounds :
  forall (value: Type) input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after cell,
    copy_protocol_declared_bounded_compatible_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace public_cells local_cells
      public_specs local_specs commit_bounds public_bounds local_bounds
      source_view after ->
    In cell (copy_mapping_publics mapping) ->
    cell_within_declared_bounds public_bounds cell.
Proof.
  intros value input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after cell Hcontract Hpublic.
  destruct Hcontract as [_ Hdeclared _ Hpublic_bounds _].
  eapply storage_bounds_cell_within.
  - exact Hpublic_bounds.
  - eapply cmd_mapping_publics_declared; eauto.
Qed.

Theorem copy_protocol_mapping_local_within_bounds :
  forall (value: Type) input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after cell,
    copy_protocol_declared_bounded_compatible_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace public_cells local_cells
      public_specs local_specs commit_bounds public_bounds local_bounds
      source_view after ->
    In cell (copy_mapping_locals mapping) ->
    cell_within_declared_bounds local_bounds cell.
Proof.
  intros value input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after cell Hcontract Hlocal.
  destruct Hcontract as [_ Hdeclared _ _ Hlocal_bounds].
  eapply storage_bounds_cell_within.
  - exact Hlocal_bounds.
  - eapply cmd_mapping_locals_declared; eauto.
Qed.

Theorem copy_protocol_mapping_pair_within_bounds :
  forall (value: Type) input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after public_cell local_cell,
    copy_protocol_declared_bounded_compatible_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace public_cells local_cells
      public_specs local_specs commit_bounds public_bounds local_bounds
      source_view after ->
    copy_mapping_pair mapping public_cell local_cell ->
    cell_within_declared_bounds public_bounds public_cell /\
    cell_within_declared_bounds local_bounds local_cell.
Proof.
  intros value input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after public_cell local_cell Hcontract Hpair.
  destruct Hcontract as [_ Hdeclared _ Hpublic_bounds Hlocal_bounds].
  pose proof
    (copy_mapping_declaration_pair_declared
       mapping public_cells local_cells public_cell local_cell
       Hdeclared Hpair)
    as [Hpublic Hlocal].
  split.
  - eapply storage_bounds_cell_within; eauto.
  - eapply storage_bounds_cell_within; eauto.
Qed.

Theorem copy_protocol_mapping_pair_compatible_specs :
  forall (value: Type) input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after public_cell local_cell,
    copy_protocol_declared_bounded_compatible_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace public_cells local_cells
      public_specs local_specs commit_bounds public_bounds local_bounds
      source_view after ->
    copy_mapping_pair mapping public_cell local_cell ->
    exists public_spec local_spec,
      In public_spec public_specs /\
      In local_spec local_specs /\
      storage_spec_cell public_spec = public_cell /\
      storage_spec_cell local_spec = local_cell /\
      storage_specs_compatible public_spec local_spec.
Proof.
  intros value input_view output_view expected_commit_targets
         mapping trace value_trace public_cells local_cells
         public_specs local_specs commit_bounds public_bounds local_bounds
         source_view after public_cell local_cell Hcontract Hpair.
  destruct Hcontract as [_ _ Hcompatible _ _].
  pose proof
    (storage_compatibility_mapping_entry_specs
       mapping public_specs local_specs
       (public_cell, local_cell) Hcompatible Hpair)
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

Theorem copy_protocol_value_event_entry :
  forall (value: Type) input_view output_view expected_commit_targets
         mapping trace value_trace source_view after copy_event',
    copy_protocol_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace source_view after ->
    In copy_event' (copy_value_trace_events value_trace) ->
    exists value_event,
      In (copy_event', value_event) value_trace /\
      copy_value_event_kind_matches copy_event' value_event /\
      copy_value_event_values_match value_event.
Proof.
  intros value input_view output_view expected_commit_targets
         mapping trace value_trace source_view after copy_event'
         Hcontract Hin.
  destruct Hcontract as [_ _ _ Hvalue _].
  eapply copy_value_obligation_event_entry; eauto.
Qed.

Theorem copy_protocol_trace_value_event_entry :
  forall (value: Type) input_view output_view expected_commit_targets
         mapping trace value_trace source_view after copy_event',
    copy_protocol_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace source_view after ->
    copy_value_trace_events value_trace = trace ->
    In copy_event' trace ->
    exists value_event,
      In (copy_event', value_event) value_trace /\
      copy_value_event_kind_matches copy_event' value_event /\
      copy_value_event_values_match value_event.
Proof.
  intros value input_view output_view expected_commit_targets
         mapping trace value_trace source_view after copy_event'
         Hcontract Hevents Hin.
  destruct Hcontract as [_ _ _ Hvalue _].
  eapply copy_value_obligation_trace_event_entry; eauto.
Qed.

Theorem checked_copy_protocol_commits_nodup :
  forall trace,
    check_copy_protocol_wfb trace = true ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  apply check_copy_protocol_wfb_commits_nodup.
Qed.

End CopyProtocolValidator.
