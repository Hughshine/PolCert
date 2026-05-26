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
Require Import ScalarPromotionWitness.
Require Import ScalarPromotionValueWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** View-level wrapper for scalar promotion / register replacement.

    The finite witness checks the local protocol around a promoted source cell:
    load before scalar use, no interfering source write, and store-back when
    the source cell is live out.  The promoted scalar is also checked as
    private target storage.  The actual value simulation between the source
    memory events and the scalar events remains an explicit semantic
    refinement obligation. *)

Module ScalarPromotionValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_promotion_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_promotion_source_view_correct :
  forall before source_view ok,
    mayReturn (check_promotion_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition promotion_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record scalar_promotion_view_contract
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (value_trace: scalar_promotion_value_trace value)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spvvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spvvc_value_simulation :
    scalar_value_simulation_obligations value value_trace;
  spvvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spvvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_compatible_view_contract
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (logical_specs scalar_specs: list storage_spec)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spcvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spcvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spcvc_storage_compatible :
    storage_compatibility_obligations
      [(source_cell, scalar_cell)] logical_specs scalar_specs;
  spcvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (value_trace: scalar_promotion_value_trace value)
    (logical_specs scalar_specs: list storage_spec)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spcvvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spcvvc_value_simulation :
    scalar_value_simulation_obligations value value_trace;
  spcvvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spcvvc_storage_compatible :
    storage_compatibility_obligations
      [(source_cell, scalar_cell)] logical_specs scalar_specs;
  spcvvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_bounded_compatible_non_escape_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (value_trace: scalar_promotion_value_trace value)
    (logical_specs scalar_specs: list storage_spec)
    (source_bounds scalar_bounds: list array_bounds)
    (escaped_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spbcnev_base :
    scalar_promotion_compatible_value_view_contract
      value input_view output_view
      source_cell scalar_cell source_liveout trace value_trace
      logical_specs scalar_specs public_cells frame_cells source_view after;
  spbcnev_source_bounds :
    storage_bounds_obligations source_bounds [source_cell];
  spbcnev_scalar_bounds :
    storage_bounds_obligations scalar_bounds [scalar_cell];
  spbcnev_scalar_non_escape :
    private_non_escape_obligations [scalar_cell] escaped_cells;
}.

Definition promotion_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_scalar_promotion_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout trace
         public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_view_contract
      input_view output_view source_cell scalar_cell source_liveout trace
      public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout trace
         public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_scalar_promotion_compatible_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_compatible_view_contract
      input_view output_view source_cell scalar_cell source_liveout trace
      logical_specs scalar_specs public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Hcompat Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       [(source_cell, scalar_cell)] logical_specs scalar_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  pose proof
    (checked_scalar_promotion_view_correct
       input_view output_view source_cell scalar_cell source_liveout trace
       public_cells frame_cells before source_view after ok
       Hret Hok Hpromotion Hseparation Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scalar_promotion_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_scalar_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace public_cells frame_cells
      source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         public_cells frame_cells
         before source_view after ok
         Hvalue_eqb Hret Hok Hpromotion Hvalue Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_scalar_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_scalar_promotion_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_scalar_value_traceb value_eqb value_trace = true ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_compatible_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace logical_specs scalar_specs
      public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok
         Hvalue_eqb Hret Hok Hpromotion Hvalue Hcompat
         Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_scalar_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       [(source_cell, scalar_cell)] logical_specs scalar_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  pose proof
    (checked_scalar_promotion_value_view_correct
       value value_eqb input_view output_view
       source_cell scalar_cell source_liveout trace value_trace
       public_cells frame_cells before source_view after ok
       Hvalue_eqb Hret Hok Hpromotion Hvalue Hseparation Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scalar_promotion_bounded_compatible_non_escape_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_scalar_value_traceb value_eqb value_trace = true ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_storage_boundsb source_bounds [source_cell] = true ->
    check_storage_boundsb scalar_bounds [scalar_cell] = true ->
    check_private_non_escapeb [scalar_cell] escaped_cells = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace logical_specs scalar_specs
      source_bounds scalar_bounds escaped_cells public_cells frame_cells
      source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok
         Hvalue_eqb Hret Hok Hpromotion Hvalue Hcompat
         Hsource_bounds Hscalar_bounds Hnon_escape Hseparation Hsemantics.
  pose proof
    (check_storage_boundsb_sound
       source_bounds [source_cell] Hsource_bounds)
    as Hsource_bounds_obligations.
  pose proof
    (check_storage_boundsb_sound
       scalar_bounds [scalar_cell] Hscalar_bounds)
    as Hscalar_bounds_obligations.
  pose proof
    (check_private_non_escapeb_sound
       [scalar_cell] escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (checked_scalar_promotion_compatible_value_view_correct
       value value_eqb input_view output_view
       source_cell scalar_cell source_liveout trace value_trace
       logical_specs scalar_specs public_cells frame_cells
       before source_view after ok
       Hvalue_eqb Hret Hok Hpromotion Hvalue Hcompat
       Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scalar_promotion_bounded_compatible_non_escape_value_public_refinement :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_scalar_value_traceb value_eqb value_trace = true ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_storage_boundsb source_bounds [source_cell] = true ->
    check_storage_boundsb scalar_bounds [scalar_cell] = true ->
    check_private_non_escapeb [scalar_cell] escaped_cells = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         before source_view after ok
         Hvalue_eqb Hret Hok Hpromotion Hvalue Hcompat
         Hsource_bounds Hscalar_bounds Hnon_escape Hseparation Hsemantics.
  pose proof
    (checked_scalar_promotion_bounded_compatible_non_escape_value_view_correct
       value value_eqb input_view output_view
       source_cell scalar_cell source_liveout trace value_trace
       logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
       public_cells frame_cells before source_view after ok
       Hvalue_eqb Hret Hok Hpromotion Hvalue Hcompat
       Hsource_bounds Hscalar_bounds Hnon_escape Hseparation Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record scalar_promotion_bounded_compatible_non_escape_value_params
    (value: Type) := {
  spbcnevp_input_view : View.view;
  spbcnevp_output_view : View.view;
  spbcnevp_source_cell : MemCell;
  spbcnevp_scalar_cell : MemCell;
  spbcnevp_source_liveout : bool;
  spbcnevp_trace : list scalar_promotion_event;
  spbcnevp_value_trace : scalar_promotion_value_trace value;
  spbcnevp_logical_specs : list storage_spec;
  spbcnevp_scalar_specs : list storage_spec;
  spbcnevp_source_bounds : list array_bounds;
  spbcnevp_scalar_bounds : list array_bounds;
  spbcnevp_escaped_cells : list MemCell;
  spbcnevp_public_cells : list MemCell;
  spbcnevp_frame_cells : list MemCell;
  spbcnevp_source_view : PolyLang.t;
}.

Definition scalar_promotion_bounded_compatible_non_escape_value_input_view
    {value: Type}
    (params:
      scalar_promotion_bounded_compatible_non_escape_value_params value)
    : View.view :=
  spbcnevp_input_view value params.

Definition scalar_promotion_bounded_compatible_non_escape_value_output_view
    {value: Type}
    (params:
      scalar_promotion_bounded_compatible_non_escape_value_params value)
    : View.view :=
  promotion_pipeline_final_view (spbcnevp_output_view value params).

Definition scalar_promotion_bounded_compatible_non_escape_value_check
    {value: Type}
    (params:
      scalar_promotion_bounded_compatible_non_escape_value_params value)
    (before after: PolyLang.t) : imp bool :=
  check_promotion_source_view before (spbcnevp_source_view value params).

Definition scalar_promotion_bounded_compatible_non_escape_value_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params:
      scalar_promotion_bounded_compatible_non_escape_value_params value)
    (before after: PolyLang.t) : Prop :=
  check_scalar_promotionb
    (spbcnevp_source_cell value params)
    (spbcnevp_scalar_cell value params)
    (spbcnevp_source_liveout value params)
    (spbcnevp_trace value params) = true /\
  check_scalar_value_traceb
    value_eqb
    (spbcnevp_value_trace value params) = true /\
  check_storage_compatibilityb
    [(spbcnevp_source_cell value params,
      spbcnevp_scalar_cell value params)]
    (spbcnevp_logical_specs value params)
    (spbcnevp_scalar_specs value params) = true /\
  check_storage_boundsb
    (spbcnevp_source_bounds value params)
    [spbcnevp_source_cell value params] = true /\
  check_storage_boundsb
    (spbcnevp_scalar_bounds value params)
    [spbcnevp_scalar_cell value params] = true /\
  check_private_non_escapeb
    [spbcnevp_scalar_cell value params]
    (spbcnevp_escaped_cells value params) = true /\
  check_private_separationb
    [spbcnevp_scalar_cell value params]
    (spbcnevp_public_cells value params)
    (spbcnevp_frame_cells value params) = true /\
  promotion_source_view_refines_view
    (spbcnevp_input_view value params)
    (spbcnevp_output_view value params)
    (spbcnevp_source_view value params)
    after.

Theorem scalar_promotion_bounded_compatible_non_escape_value_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (scalar_promotion_bounded_compatible_non_escape_value_check
        params before after)
      ok ->
    ok = true ->
    scalar_promotion_bounded_compatible_non_escape_value_side_condition
      value_eqb params before after ->
    View.view_refinement
      (scalar_promotion_bounded_compatible_non_escape_value_input_view params)
      (scalar_promotion_bounded_compatible_non_escape_value_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view source_cell scalar_cell source_liveout trace
     value_trace logical_specs scalar_specs source_bounds scalar_bounds
     escaped_cells public_cells frame_cells source_view].
  simpl in *.
  destruct Hside as [Hpromotion Hside].
  destruct Hside as [Hvalue Hside].
  destruct Hside as [Hcompat Hside].
  destruct Hside as [Hsource_bounds Hside].
  destruct Hside as [Hscalar_bounds Hside].
  destruct Hside as [Hnon_escape Hside].
  destruct Hside as [Hseparation Hsemantics].
  eapply checked_scalar_promotion_bounded_compatible_non_escape_value_public_refinement;
    eauto.
Qed.

Definition scalar_promotion_bounded_compatible_non_escape_value_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (scalar_promotion_bounded_compatible_non_escape_value_params value) := {|
  generic_cpvtf_input_view :=
    scalar_promotion_bounded_compatible_non_escape_value_input_view;
  generic_cpvtf_output_view :=
    scalar_promotion_bounded_compatible_non_escape_value_output_view;
  generic_cpvtf_check :=
    scalar_promotion_bounded_compatible_non_escape_value_check;
  generic_cpvtf_side_condition :=
    scalar_promotion_bounded_compatible_non_escape_value_side_condition
      value_eqb;
  generic_cpvtf_check_sound :=
    scalar_promotion_bounded_compatible_non_escape_value_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem scalar_promotion_source_cell_within_bounds :
  forall (value: Type)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         source_view after,
    scalar_promotion_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace logical_specs scalar_specs
      source_bounds scalar_bounds escaped_cells public_cells frame_cells
      source_view after ->
    cell_within_declared_bounds source_bounds source_cell.
Proof.
  intros value input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells source_view after Hcontract.
  destruct Hcontract as [_ Hsource_bounds _ _].
  eapply storage_bounds_cell_within.
  - exact Hsource_bounds.
  - simpl; auto.
Qed.

Theorem scalar_promotion_scalar_cell_within_bounds :
  forall (value: Type)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         source_view after,
    scalar_promotion_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace logical_specs scalar_specs
      source_bounds scalar_bounds escaped_cells public_cells frame_cells
      source_view after ->
    cell_within_declared_bounds scalar_bounds scalar_cell.
Proof.
  intros value input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells source_view after Hcontract.
  destruct Hcontract as [_ _ Hscalar_bounds _].
  eapply storage_bounds_cell_within.
  - exact Hscalar_bounds.
  - simpl; auto.
Qed.

Theorem scalar_promotion_scalar_cell_not_escaped :
  forall (value: Type)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells
         source_view after,
    scalar_promotion_bounded_compatible_non_escape_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace logical_specs scalar_specs
      source_bounds scalar_bounds escaped_cells public_cells frame_cells
      source_view after ->
    ~ In scalar_cell escaped_cells.
Proof.
  intros value input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs source_bounds scalar_bounds escaped_cells
         public_cells frame_cells source_view after Hcontract.
  destruct Hcontract as [_ _ _ Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  simpl; auto.
Qed.

End ScalarPromotionValidator.
