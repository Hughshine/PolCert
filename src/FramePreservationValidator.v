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

End FramePreservationValidator.
