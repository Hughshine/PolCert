Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import FramePreservationWitness.
Require Import FrameValueWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** View-level wrapper for contextual frame preservation.

    The finite frame witness says that the transformed fragment writes only
    allowed cells, and those allowed cells are disjoint from the surrounding
    context frame.  This validator layer packages that side condition with the
    standard source-view pipeline theorem.  It does not change the output view;
    it records the context-safety obligation that should be composed with a
    feature-specific storage view. *)

Module FramePreservationValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_frame_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_frame_source_view_correct :
  forall before source_view ok,
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition frame_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record frame_preservation_view_contract
    (input_view output_view: View.view)
    (frame_cells write_cells allowed_write_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  fpvc_frame :
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells;
  fpvc_writes_disjoint :
    writes_disjoint_from_frame write_cells frame_cells;
  fpvc_semantic_refinement :
    frame_source_view_refines_view
      input_view output_view source_view after;
}.

Record frame_preservation_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (frame_cells write_cells allowed_write_cells: list MemCell)
    (frame_entries: list (frame_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  fpvvc_frame_contract :
    frame_preservation_view_contract
      input_view output_view frame_cells write_cells allowed_write_cells
      source_view after;
  fpvvc_frame_values :
    frame_value_obligations value frame_cells frame_entries;
}.

Record frame_preservation_bounded_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (frame_cells write_cells allowed_write_cells: list MemCell)
    (frame_entries: list (frame_value_entry value))
    (allowed_write_bounds frame_bounds: list array_bounds)
    (source_view after: PolyLang.t) : Prop := {
  fpbvvc_base :
    frame_preservation_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      source_view after;
  fpbvvc_allowed_write_bounds :
    storage_bounds_obligations allowed_write_bounds allowed_write_cells;
  fpbvvc_frame_bounds :
    storage_bounds_obligations frame_bounds frame_cells;
}.

Definition frame_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_frame_preservation_view_correct :
  forall input_view output_view frame_cells write_cells allowed_write_cells
         before source_view after ok,
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    check_frame_preservationb
      frame_cells write_cells allowed_write_cells = true ->
    frame_source_view_refines_view
      input_view output_view source_view after ->
    frame_preservation_view_contract
      input_view output_view frame_cells write_cells allowed_write_cells
      source_view after /\
    View.view_refinement
      input_view
      (frame_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view frame_cells write_cells allowed_write_cells
         before source_view after ok Hret Hok Hframe Hsemantics.
  pose proof
    (check_frame_preservationb_sound
       frame_cells write_cells allowed_write_cells Hframe)
    as Hframe_obligations.
  pose proof
    (frame_preservation_writes_disjoint
       frame_cells write_cells allowed_write_cells Hframe_obligations)
    as Hwrites_disjoint.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_frame_preservation_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view frame_cells write_cells allowed_write_cells
         frame_entries before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    check_frame_preservationb
      frame_cells write_cells allowed_write_cells = true ->
    check_frame_valueb value value_eqb frame_cells frame_entries = true ->
    frame_source_view_refines_view
      input_view output_view source_view after ->
    frame_preservation_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      source_view after /\
    View.view_refinement
      input_view
      (frame_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view frame_cells write_cells
         allowed_write_cells frame_entries before source_view after ok
         Hvalue_eqb Hret Hok Hframe Hvalues Hsemantics.
  pose proof
    (checked_frame_preservation_view_correct
       input_view output_view frame_cells write_cells allowed_write_cells
       before source_view after ok Hret Hok Hframe Hsemantics)
    as [Hframe_contract Hrefinement].
  pose proof
    (check_frame_valueb_sound
       value value_eqb Hvalue_eqb frame_cells frame_entries Hvalues)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - exact Hrefinement.
Qed.

Theorem checked_frame_preservation_bounded_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view frame_cells write_cells allowed_write_cells
         frame_entries allowed_write_bounds frame_bounds
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    check_frame_preservationb
      frame_cells write_cells allowed_write_cells = true ->
    check_frame_valueb value value_eqb frame_cells frame_entries = true ->
    check_storage_boundsb allowed_write_bounds allowed_write_cells = true ->
    check_storage_boundsb frame_bounds frame_cells = true ->
    frame_source_view_refines_view
      input_view output_view source_view after ->
    frame_preservation_bounded_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      allowed_write_bounds frame_bounds source_view after /\
    View.view_refinement
      input_view
      (frame_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view frame_cells write_cells
         allowed_write_cells frame_entries allowed_write_bounds frame_bounds
         before source_view after ok
         Hvalue_eqb Hret Hok Hframe Hvalues Hallowed_bounds Hframe_bounds
         Hsemantics.
  pose proof
    (checked_frame_preservation_value_view_correct
       value value_eqb input_view output_view
       frame_cells write_cells allowed_write_cells frame_entries
       before source_view after ok
       Hvalue_eqb Hret Hok Hframe Hvalues Hsemantics)
    as [Hbase Hview].
  pose proof
    (check_storage_boundsb_sound
       allowed_write_bounds allowed_write_cells Hallowed_bounds)
    as Hallowed_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       frame_bounds frame_cells Hframe_bounds)
    as Hframe_bounds_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_frame_preservation_bounded_value_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view frame_cells write_cells allowed_write_cells
         frame_entries allowed_write_bounds frame_bounds
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    check_frame_preservationb
      frame_cells write_cells allowed_write_cells = true ->
    check_frame_valueb value value_eqb frame_cells frame_entries = true ->
    check_storage_boundsb allowed_write_bounds allowed_write_cells = true ->
    check_storage_boundsb frame_bounds frame_cells = true ->
    frame_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (frame_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         frame_cells write_cells allowed_write_cells
         frame_entries allowed_write_bounds frame_bounds
         before source_view after ok Hvalue_eqb Hret Hok Hframe Hvalues
         Hallowed_bounds Hframe_bounds Hsemantics.
  pose proof
    (checked_frame_preservation_bounded_value_view_correct
       value value_eqb input_view output_view
       frame_cells write_cells allowed_write_cells frame_entries
       allowed_write_bounds frame_bounds before source_view after ok
       Hvalue_eqb Hret Hok Hframe Hvalues Hallowed_bounds
       Hframe_bounds Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record frame_preservation_bounded_value_params (value: Type) := {
  fpbvp_input_view : View.view;
  fpbvp_output_view : View.view;
  fpbvp_frame_cells : list MemCell;
  fpbvp_write_cells : list MemCell;
  fpbvp_allowed_write_cells : list MemCell;
  fpbvp_frame_entries : list (frame_value_entry value);
  fpbvp_allowed_write_bounds : list array_bounds;
  fpbvp_frame_bounds : list array_bounds;
  fpbvp_source_view : PolyLang.t;
}.

Definition frame_preservation_bounded_value_input_view
    {value: Type}
    (params: frame_preservation_bounded_value_params value)
    : View.view :=
  fpbvp_input_view value params.

Definition frame_preservation_bounded_value_output_view
    {value: Type}
    (params: frame_preservation_bounded_value_params value)
    : View.view :=
  frame_pipeline_final_view (fpbvp_output_view value params).

Definition frame_preservation_bounded_value_check
    {value: Type}
    (params: frame_preservation_bounded_value_params value)
    (before after: PolyLang.t) : imp bool :=
  check_frame_source_view before (fpbvp_source_view value params).

Definition frame_preservation_bounded_value_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params: frame_preservation_bounded_value_params value)
    (before after: PolyLang.t) : Prop :=
  check_frame_preservationb
    (fpbvp_frame_cells value params)
    (fpbvp_write_cells value params)
    (fpbvp_allowed_write_cells value params) = true /\
  check_frame_valueb
    value value_eqb
    (fpbvp_frame_cells value params)
    (fpbvp_frame_entries value params) = true /\
  check_storage_boundsb
    (fpbvp_allowed_write_bounds value params)
    (fpbvp_allowed_write_cells value params) = true /\
  check_storage_boundsb
    (fpbvp_frame_bounds value params)
    (fpbvp_frame_cells value params) = true /\
  frame_source_view_refines_view
    (fpbvp_input_view value params)
    (fpbvp_output_view value params)
    (fpbvp_source_view value params)
    after.

Theorem frame_preservation_bounded_value_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (frame_preservation_bounded_value_check params before after)
      ok ->
    ok = true ->
    frame_preservation_bounded_value_side_condition
      value_eqb params before after ->
    View.view_refinement
      (frame_preservation_bounded_value_input_view params)
      (frame_preservation_bounded_value_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view frame_cells write_cells allowed_write_cells
     frame_entries allowed_write_bounds frame_bounds source_view].
  simpl in *.
  destruct Hside as
    [Hframe [Hvalues [Hallowed_bounds [Hframe_bounds Hsemantics]]]].
  eapply checked_frame_preservation_bounded_value_public_refinement; eauto.
Qed.

Definition frame_preservation_bounded_value_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (frame_preservation_bounded_value_params value) := {|
  generic_cpvtf_input_view :=
    frame_preservation_bounded_value_input_view;
  generic_cpvtf_output_view :=
    frame_preservation_bounded_value_output_view;
  generic_cpvtf_check :=
    frame_preservation_bounded_value_check;
  generic_cpvtf_side_condition :=
    frame_preservation_bounded_value_side_condition value_eqb;
  generic_cpvtf_check_sound :=
    frame_preservation_bounded_value_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem frame_preservation_frame_cell_value_preserved :
  forall (value: Type) input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         source_view after cell,
    frame_preservation_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      source_view after ->
    In cell frame_cells ->
    exists entry,
      In entry frame_entries /\
      fve_frame_cell entry = cell /\
      fve_before_value entry = fve_after_value entry.
Proof.
  intros value input_view output_view frame_cells write_cells
         allowed_write_cells frame_entries source_view after cell
         Hcontract Hin.
  destruct Hcontract as [_ Hvalues].
  eapply frame_value_cell_preserved; eauto.
Qed.

Theorem frame_preservation_allowed_write_within_bounds :
  forall (value: Type) input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         allowed_write_bounds frame_bounds source_view after cell,
    frame_preservation_bounded_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      allowed_write_bounds frame_bounds source_view after ->
    In cell allowed_write_cells ->
    cell_within_declared_bounds allowed_write_bounds cell.
Proof.
  intros value input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         allowed_write_bounds frame_bounds source_view after cell
         Hcontract Hin.
  destruct Hcontract as [_ Hallowed_bounds _].
  eapply storage_bounds_cell_within; eauto.
Qed.

Theorem frame_preservation_write_within_allowed_bounds :
  forall (value: Type) input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         allowed_write_bounds frame_bounds source_view after cell,
    frame_preservation_bounded_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      allowed_write_bounds frame_bounds source_view after ->
    In cell write_cells ->
    cell_within_declared_bounds allowed_write_bounds cell.
Proof.
  intros value input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         allowed_write_bounds frame_bounds source_view after cell
         Hcontract Hwrite.
  destruct Hcontract as [Hbase Hallowed_bounds _].
  destruct Hbase as [Hframe_contract _].
  destruct Hframe_contract as [Hframe _ _].
  destruct Hframe as [_ Hwrites_allowed _].
  eapply storage_bounds_cell_within.
  - exact Hallowed_bounds.
  - apply Hwrites_allowed.
    exact Hwrite.
Qed.

Theorem frame_preservation_frame_cell_within_bounds :
  forall (value: Type) input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         allowed_write_bounds frame_bounds source_view after cell,
    frame_preservation_bounded_value_view_contract
      value input_view output_view
      frame_cells write_cells allowed_write_cells frame_entries
      allowed_write_bounds frame_bounds source_view after ->
    In cell frame_cells ->
    cell_within_declared_bounds frame_bounds cell.
Proof.
  intros value input_view output_view
         frame_cells write_cells allowed_write_cells frame_entries
         allowed_write_bounds frame_bounds source_view after cell
         Hcontract Hin.
  destruct Hcontract as [_ _ Hframe_bounds].
  eapply storage_bounds_cell_within; eauto.
Qed.

End FramePreservationValidator.
