Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import StorageWitness.
Require Import StateObservation.
Require Import PrivateStorageWitness.
Require Import PrivateBoundaryWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** Feature target: private storage / scalar expansion / local temporaries.

    This module covers the theorem shape for transformations that introduce
    target-only storage, such as scalar privatization, scalar expansion, or
    tile-local temporaries.  The public cells are described by an
    [Observation.cell_view]; private target cells are required to be outside the
    public target-to-source relation and are therefore erased by the endpoint
    view.

    The transformation-specific proof obligation remains semantic for now:
    [private_source_view_refines_view] states that the privatized target refines
    the logical source-view program when both endpoints are observed through
    the same public view.  Later syntactic validators can discharge this
    obligation with use-def, freshness, copy-in, and copy-out checks. *)

Module PrivateStorageValidator
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Witness := PrivateStorageWitness PolIRs Observer.
Module Observation := Witness.Observation.
Module View := Pipeline.View.
Module Transform := Pipeline.Transform.

Definition private_erasure_view
    (public_view: Observation.cell_view) : View.view :=
  Observation.cell_view_state_view public_view.

Definition private_pipeline_final_view
    (public_view: Observation.cell_view) : View.view :=
  View.compose_view (private_erasure_view public_view) View.identity_view.

Definition check_private_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_private_source_view_correct :
  forall before source_view ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition private_source_view_refines_view
    (public_view: Observation.cell_view)
    (source_view after: PolyLang.t) : Prop :=
  View.view_refinement
    (private_erasure_view public_view)
    (private_erasure_view public_view)
    source_view after.

Fixpoint private_boundary_storage_mapping
    (pairs: list private_boundary_pair) : list (MemCell * MemCell) :=
  match pairs with
  | [] => []
  | boundary :: tail =>
      (private_boundary_public boundary, private_boundary_private boundary) ::
      private_boundary_storage_mapping tail
  end.

Record private_expansion_view_contract
    (public_view: Observation.cell_view)
    (private_target_cell: MemCell -> Prop)
    (source_view after: PolyLang.t) : Prop := {
  pevc_private_unobservable :
    forall target_cell source_cell,
      private_target_cell target_cell ->
      ~ Observation.cv_cell_relation
          public_view target_cell source_cell;
  pevc_semantic_refinement :
    private_source_view_refines_view
      public_view source_view after;
}.

Record private_boundary_view_contract
    (public_view: Observation.cell_view)
    (hidden_cells private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbvc_local :
    Witness.private_local_obligations hidden_cells private_cells trace;
  pbvc_boundary :
    private_boundary_obligations
      private_cells public_liveins public_liveouts copyins copyouts;
  pbvc_semantic_refinement :
    private_source_view_refines_view
      public_view source_view after;
}.

Record private_boundary_value_view_contract
    (value: Type)
    (public_view: Observation.cell_view)
    (hidden_cells private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value))
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbvvc_local :
    Witness.private_local_obligations hidden_cells private_cells trace;
  pbvvc_boundary :
    private_boundary_obligations
      private_cells public_liveins public_liveouts copyins copyouts;
  pbvvc_boundary_values :
    private_boundary_value_obligations
      value copyins copyouts copyin_values copyout_values;
  pbvvc_semantic_refinement :
    private_source_view_refines_view
      public_view source_view after;
}.

Record private_boundary_unique_view_contract
    (public_view: Observation.cell_view)
    (hidden_cells private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbuvc_base :
    private_boundary_view_contract
      public_view hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts trace source_view after;
  pbuvc_private_unique :
    private_boundary_private_unique_obligations copyins copyouts;
}.

Record private_boundary_unique_value_view_contract
    (value: Type)
    (public_view: Observation.cell_view)
    (hidden_cells private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value))
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbuvvc_value_base :
    private_boundary_value_view_contract
      value public_view
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      trace source_view after;
  pbuvvc_private_unique :
    private_boundary_private_unique_obligations copyins copyouts;
}.

Record private_boundary_unique_compatible_value_view_contract
    (value: Type)
    (public_view: Observation.cell_view)
    (hidden_cells private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value))
    (public_specs private_specs: list storage_spec)
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbucvvc_value_base :
    private_boundary_unique_value_view_contract
      value public_view
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      trace source_view after;
  pbucvvc_copyins_compatible :
    storage_compatibility_obligations
      (private_boundary_storage_mapping copyins)
      public_specs private_specs;
  pbucvvc_copyouts_compatible :
    storage_compatibility_obligations
      (private_boundary_storage_mapping copyouts)
      public_specs private_specs;
}.

Record private_boundary_unique_compatible_non_escape_value_view_contract
    (value: Type)
    (public_view: Observation.cell_view)
    (hidden_cells private_cells escaped_cells
       public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value))
    (public_specs private_specs: list storage_spec)
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbucnevvc_compatible_base :
    private_boundary_unique_compatible_value_view_contract
      value public_view
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs trace source_view after;
  pbucnevvc_non_escape :
    private_non_escape_obligations private_cells escaped_cells;
}.

Record private_declared_boundary_unique_compatible_non_escape_value_view_contract
    (value: Type)
    (public_view: Observation.cell_view)
    (hidden_cells private_cells escaped_cells
       public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value))
    (public_specs private_specs: list storage_spec)
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pdbucnevvc_base :
    private_boundary_unique_compatible_non_escape_value_view_contract
      value public_view
      hidden_cells private_cells escaped_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs trace source_view after;
  pdbucnevvc_declared_local :
    Witness.private_declared_local_obligations
      hidden_cells private_cells trace;
}.

Record private_bounded_declared_boundary_unique_compatible_non_escape_value_view_contract
    (value: Type)
    (public_view: Observation.cell_view)
    (hidden_cells private_cells escaped_cells
       public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value))
    (public_specs private_specs: list storage_spec)
    (bounds: list array_bounds)
    (trace: list private_event)
    (source_view after: PolyLang.t) : Prop := {
  pbdbucnevvc_declared_base :
    private_declared_boundary_unique_compatible_non_escape_value_view_contract
      value public_view
      hidden_cells private_cells escaped_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs trace source_view after;
  pbdbucnevvc_private_bounds :
    storage_bounds_obligations bounds private_cells;
}.

Record private_access_declared_local_view_contract
    (public_view: Observation.cell_view)
    (hidden_cells private_cells: list MemCell)
    (points: list DomIndex)
    (access_trace: list private_access_event)
    (source_view after: PolyLang.t) : Prop := {
  padlvc_local :
    Witness.private_access_local_obligations
      hidden_cells private_cells access_trace;
  padlvc_declared_instances :
    private_access_instances_declared_obligations
      private_cells points access_trace;
  padlvc_semantic_refinement :
    private_source_view_refines_view public_view source_view after;
}.

Record private_access_bounded_declared_local_view_contract
    (public_view: Observation.cell_view)
    (hidden_cells private_cells: list MemCell)
    (points: list DomIndex)
    (bounds: list array_bounds)
    (access_trace: list private_access_event)
    (source_view after: PolyLang.t) : Prop := {
  pabdlvc_declared_base :
    private_access_declared_local_view_contract
      public_view hidden_cells private_cells points access_trace
      source_view after;
  pabdlvc_private_bounds :
    storage_bounds_obligations bounds private_cells;
}.

Theorem checked_private_expansion_view_correct :
  forall public_view private_target_cell before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    private_expansion_view_contract
      public_view private_target_cell source_view after ->
    View.view_refinement
      (private_erasure_view public_view)
      (private_pipeline_final_view public_view)
      before after.
Proof.
  intros public_view private_target_cell before source_view after ok
         Hret Hok Hcontract.
  destruct Hcontract as [_ Hprivate].
  apply
    (Pipeline.compose_checked_source_view
       (private_erasure_view public_view)
       (private_erasure_view public_view)
       before source_view after ok);
    assumption.
Qed.

Theorem checked_hidden_private_expansion_view_correct :
  forall hidden_cells private_cells before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    mem_cells_subsetb private_cells hidden_cells = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells before source_view after ok
         Hret Hok Hsubset Hprivate.
  eapply checked_private_expansion_view_correct.
  - exact Hret.
  - exact Hok.
  - constructor.
    + intros target_cell source_cell Hprivate_cell.
      eapply Witness.private_cells_hidden_unobservable.
      * apply Witness.private_cells_hidden_sound.
        exact Hsubset.
      * exact Hprivate_cell.
    + exact Hprivate.
Qed.

Theorem checked_local_private_expansion_view_correct :
  forall hidden_cells private_cells trace before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Witness.private_local_obligations
      hidden_cells private_cells trace /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells trace before source_view after ok
         Hret Hok Hlocal Hprivate.
  pose proof
    (Witness.check_private_local_obligationsb_sound
       hidden_cells private_cells trace Hlocal)
    as Hobligations.
  destruct Hobligations as [Hhidden Hnodup Husedef].
  split.
  - constructor; assumption.
  - eapply checked_private_expansion_view_correct.
    + exact Hret.
    + exact Hok.
    + constructor.
      * intros target_cell source_cell Hprivate_cell.
        eapply Witness.private_cells_hidden_unobservable.
        -- exact Hhidden.
        -- exact Hprivate_cell.
      * exact Hprivate.
Qed.

Theorem checked_boundary_private_expansion_view_correct :
  forall hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts trace before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_boundary_view_contract
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts trace before source_view after ok
         Hret Hok Hlocal Hboundary Hprivate.
  pose proof
    (Witness.check_private_local_obligationsb_sound
       hidden_cells private_cells trace Hlocal)
    as Hlocal_obligations.
  pose proof
    (check_private_boundaryb_sound
       private_cells public_liveins public_liveouts
       copyins copyouts Hboundary)
    as Hboundary_obligations.
  split.
  - constructor; assumption.
  - eapply checked_local_private_expansion_view_correct.
    + exact Hret.
    + exact Hok.
    + exact Hlocal.
    + exact Hprivate.
Qed.

Theorem checked_boundary_private_unique_expansion_view_correct :
  forall hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts trace before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_boundary_unique_view_contract
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts trace before source_view after ok
         Hret Hok Hlocal Hboundary Hunique Hprivate.
  pose proof
    (check_private_boundary_private_uniqueb_sound
       copyins copyouts Hunique)
    as Hunique_obligations.
  pose proof
    (checked_boundary_private_expansion_view_correct
       hidden_cells private_cells public_liveins public_liveouts
       copyins copyouts trace before source_view after ok
       Hret Hok Hlocal Hboundary Hprivate)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_boundary_private_value_expansion_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_boundary_value_view_contract
      value
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros value value_eqb
         hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         trace before source_view after ok
         Hvalue_eqb Hret Hok Hlocal Hboundary Hboundary_values Hprivate.
  pose proof
    (Witness.check_private_local_obligationsb_sound
       hidden_cells private_cells trace Hlocal)
    as Hlocal_obligations.
  pose proof
    (check_private_boundaryb_sound
       private_cells public_liveins public_liveouts
       copyins copyouts Hboundary)
    as Hboundary_obligations.
  pose proof
    (check_private_boundary_valueb_sound
       value value_eqb Hvalue_eqb
       copyins copyouts copyin_values copyout_values Hboundary_values)
    as Hboundary_value_obligations.
  split.
  - constructor; assumption.
  - eapply checked_boundary_private_expansion_view_correct.
    + exact Hret.
    + exact Hok.
    + exact Hlocal.
    + exact Hboundary.
    + exact Hprivate.
Qed.

Theorem checked_boundary_private_unique_value_expansion_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_boundary_unique_value_view_contract
      value
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros value value_eqb
         hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         trace before source_view after ok
         Hvalue_eqb Hret Hok Hlocal Hboundary Hunique
         Hboundary_values Hprivate.
  pose proof
    (check_private_boundary_private_uniqueb_sound
       copyins copyouts Hunique)
    as Hunique_obligations.
  pose proof
    (checked_boundary_private_value_expansion_view_correct
       value value_eqb hidden_cells private_cells
       public_liveins public_liveouts copyins copyouts
       copyin_values copyout_values trace before source_view after ok
       Hvalue_eqb Hret Hok Hlocal Hboundary Hboundary_values Hprivate)
    as [Hvalue_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_boundary_private_unique_compatible_value_expansion_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs
         trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyins)
      public_specs private_specs = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyouts)
      public_specs private_specs = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_boundary_unique_compatible_value_view_contract
      value
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros value value_eqb
         hidden_cells private_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs
         trace before source_view after ok
         Hvalue_eqb Hret Hok Hlocal Hboundary Hunique
         Hboundary_values Hcopyins_storage Hcopyouts_storage Hprivate.
  pose proof
    (check_storage_compatibilityb_sound
       (private_boundary_storage_mapping copyins)
       public_specs private_specs Hcopyins_storage)
    as Hcopyins_compatible.
  pose proof
    (check_storage_compatibilityb_sound
       (private_boundary_storage_mapping copyouts)
       public_specs private_specs Hcopyouts_storage)
    as Hcopyouts_compatible.
  pose proof
    (checked_boundary_private_unique_value_expansion_view_correct
       value value_eqb hidden_cells private_cells
       public_liveins public_liveouts copyins copyouts
       copyin_values copyout_values trace before source_view after ok
       Hvalue_eqb Hret Hok Hlocal Hboundary Hunique
       Hboundary_values Hprivate)
    as [Hvalue_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_boundary_private_unique_compatible_non_escape_value_expansion_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs
         trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyins)
      public_specs private_specs = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyouts)
      public_specs private_specs = true ->
    check_private_non_escapeb private_cells escaped_cells = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_boundary_unique_compatible_non_escape_value_view_contract
      value
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells escaped_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros value value_eqb
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs
         trace before source_view after ok
         Hvalue_eqb Hret Hok Hlocal Hboundary Hunique
         Hboundary_values Hcopyins_storage Hcopyouts_storage
         Hnon_escape Hprivate.
  pose proof
    (check_private_non_escapeb_sound
       private_cells escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (checked_boundary_private_unique_compatible_value_expansion_view_correct
       value value_eqb hidden_cells private_cells
       public_liveins public_liveouts copyins copyouts
       copyin_values copyout_values public_specs private_specs
       trace before source_view after ok
       Hvalue_eqb Hret Hok Hlocal Hboundary Hunique
       Hboundary_values Hcopyins_storage Hcopyouts_storage Hprivate)
    as [Hcompatible_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_declared_boundary_private_unique_compatible_non_escape_value_expansion_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs
         trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_declared_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyins)
      public_specs private_specs = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyouts)
      public_specs private_specs = true ->
    check_private_non_escapeb private_cells escaped_cells = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_declared_boundary_unique_compatible_non_escape_value_view_contract
      value
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells escaped_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros value value_eqb
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs
         trace before source_view after ok
         Hvalue_eqb Hret Hok Hdeclared_local Hboundary Hunique
         Hboundary_values Hcopyins_storage Hcopyouts_storage
         Hnon_escape Hprivate.
  pose proof
    (Witness.check_private_declared_local_obligationsb_sound
       hidden_cells private_cells trace Hdeclared_local)
    as Hdeclared_local_obligations.
  unfold Witness.check_private_declared_local_obligationsb
    in Hdeclared_local.
  apply andb_true_iff in Hdeclared_local.
  destruct Hdeclared_local as [Hlocal _].
  pose proof
    (checked_boundary_private_unique_compatible_non_escape_value_expansion_view_correct
       value value_eqb hidden_cells private_cells escaped_cells
       public_liveins public_liveouts copyins copyouts
       copyin_values copyout_values public_specs private_specs
       trace before source_view after ok
       Hvalue_eqb Hret Hok Hlocal Hboundary Hunique
       Hboundary_values Hcopyins_storage Hcopyouts_storage
       Hnon_escape Hprivate)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_bounded_declared_boundary_private_unique_compatible_non_escape_value_expansion_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs bounds
         trace before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_declared_local_obligationsb
      hidden_cells private_cells trace = true ->
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyins)
      public_specs private_specs = true ->
    check_storage_compatibilityb
      (private_boundary_storage_mapping copyouts)
      public_specs private_specs = true ->
    check_private_non_escapeb private_cells escaped_cells = true ->
    check_storage_boundsb bounds private_cells = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_bounded_declared_boundary_unique_compatible_non_escape_value_view_contract
      value
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells escaped_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs bounds trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros value value_eqb
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs bounds
         trace before source_view after ok
         Hvalue_eqb Hret Hok Hdeclared_local Hboundary Hunique
         Hboundary_values Hcopyins_storage Hcopyouts_storage
         Hnon_escape Hbounds Hprivate.
  pose proof
    (check_storage_boundsb_sound bounds private_cells Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_declared_boundary_private_unique_compatible_non_escape_value_expansion_view_correct
       value value_eqb hidden_cells private_cells escaped_cells
       public_liveins public_liveouts copyins copyouts
       copyin_values copyout_values public_specs private_specs
       trace before source_view after ok
       Hvalue_eqb Hret Hok Hdeclared_local Hboundary Hunique
       Hboundary_values Hcopyins_storage Hcopyouts_storage
       Hnon_escape Hprivate)
    as [Hdeclared_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem private_declared_trace_cell_within_bounds :
  forall (value: Type)
         public_view
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs bounds trace source_view after cell,
    private_bounded_declared_boundary_unique_compatible_non_escape_value_view_contract
      value public_view
      hidden_cells private_cells escaped_cells public_liveins public_liveouts
      copyins copyouts copyin_values copyout_values
      public_specs private_specs bounds trace source_view after ->
    In cell (private_trace_cells trace) ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros value public_view
         hidden_cells private_cells escaped_cells public_liveins public_liveouts
         copyins copyouts copyin_values copyout_values
         public_specs private_specs bounds trace source_view after cell
         Hcontract Htrace_cell.
  destruct Hcontract as [Hdeclared Hbounds].
  destruct Hdeclared as [_ Hdeclared_local].
  destruct Hdeclared_local as [_ Htrace_declared].
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - eapply private_trace_cells_declared_in; eauto.
Qed.

Theorem checked_access_local_private_expansion_view_correct :
  forall hidden_cells private_cells access_trace before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_access_local_obligationsb
      hidden_cells private_cells access_trace = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    Witness.private_access_local_obligations
      hidden_cells private_cells access_trace /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells access_trace before source_view after ok
         Hret Hok Hlocal Hprivate.
  pose proof
    (Witness.check_private_access_local_obligationsb_sound
       hidden_cells private_cells access_trace Hlocal)
    as Hobligations.
  destruct Hobligations as
    [Hhidden Hnodup Haccess_use_def Hinstantiated_use_def].
  split.
  - constructor; assumption.
  - eapply checked_private_expansion_view_correct.
    + exact Hret.
    + exact Hok.
    + constructor.
      * intros target_cell source_cell Hprivate_cell.
        eapply Witness.private_cells_hidden_unobservable.
        -- exact Hhidden.
        -- exact Hprivate_cell.
      * exact Hprivate.
Qed.

Theorem checked_access_declared_local_private_expansion_view_correct :
  forall hidden_cells private_cells points access_trace
         before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_access_local_obligationsb
      hidden_cells private_cells access_trace = true ->
    check_private_access_instances_declaredb
      private_cells points access_trace = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_access_declared_local_view_contract
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells points access_trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells points access_trace
         before source_view after ok Hret Hok Hlocal Hdeclared Hprivate.
  pose proof
    (check_private_access_instances_declaredb_sound
       private_cells points access_trace Hdeclared)
    as Hdeclared_obligations.
  pose proof
    (checked_access_local_private_expansion_view_correct
       hidden_cells private_cells access_trace before source_view after ok
       Hret Hok Hlocal Hprivate)
    as [Hlocal_obligations Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_access_bounded_declared_local_private_expansion_view_correct :
  forall hidden_cells private_cells points bounds access_trace
         before source_view after ok,
    mayReturn (check_private_source_view before source_view) ok ->
    ok = true ->
    Witness.check_private_access_local_obligationsb
      hidden_cells private_cells access_trace = true ->
    check_private_access_instances_declaredb
      private_cells points access_trace = true ->
    check_storage_boundsb bounds private_cells = true ->
    private_source_view_refines_view
      (Witness.hidden_identity_cell_view hidden_cells)
      source_view after ->
    private_access_bounded_declared_local_view_contract
      (Witness.hidden_identity_cell_view hidden_cells)
      hidden_cells private_cells points bounds access_trace source_view after /\
    View.view_refinement
      (private_erasure_view
         (Witness.hidden_identity_cell_view hidden_cells))
      (private_pipeline_final_view
         (Witness.hidden_identity_cell_view hidden_cells))
      before after.
Proof.
  intros hidden_cells private_cells points bounds access_trace
         before source_view after ok Hret Hok Hlocal Hdeclared Hbounds Hprivate.
  pose proof
    (check_storage_boundsb_sound bounds private_cells Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_access_declared_local_private_expansion_view_correct
       hidden_cells private_cells points access_trace before source_view after ok
       Hret Hok Hlocal Hdeclared Hprivate)
    as [Hdeclared_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem private_access_instantiated_trace_cell_declared :
  forall public_view hidden_cells private_cells points access_trace
         source_view after p cell,
    private_access_declared_local_view_contract
      public_view hidden_cells private_cells points access_trace
      source_view after ->
    In p points ->
    In cell (private_access_trace_cells_at p access_trace) ->
    In cell private_cells.
Proof.
  intros public_view hidden_cells private_cells points access_trace
         source_view after p cell Hcontract Hin_point Hin_cell.
  destruct Hcontract as [_ Hdeclared _].
  eapply private_access_instances_declared_cell; eauto.
Qed.

Theorem private_access_instantiated_trace_cell_within_bounds :
  forall public_view hidden_cells private_cells points bounds access_trace
         source_view after p cell,
    private_access_bounded_declared_local_view_contract
      public_view hidden_cells private_cells points bounds access_trace
      source_view after ->
    In p points ->
    In cell (private_access_trace_cells_at p access_trace) ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros public_view hidden_cells private_cells points bounds access_trace
         source_view after p cell Hcontract Hin_point Hin_cell.
  destruct Hcontract as [Hdeclared Hbounds].
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - eapply private_access_instantiated_trace_cell_declared; eauto.
Qed.

End PrivateStorageValidator.
