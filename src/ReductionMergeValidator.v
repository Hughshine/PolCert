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
Require Import PrivateStorageWitness.
Require Import ReductionMergeWitness.
Require Import ReductionMergeValueWitness.
Require Import ReductionAlgebraWitness.
Require Import StorageCompatibilityWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** View-level wrapper for reduction privatization and merge.

    The finite witness checks reduction-domain partitioning and private
    accumulator/merge coverage.  The algebraic law required to replace the
    source reduction order by private partials plus a merge is not a boolean
    syntactic fact; it remains an explicit proposition in the contract. *)

Module ReductionMergeValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_reduction_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_reduction_source_view_correct :
  forall before source_view ok,
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition reduction_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Fixpoint reduction_accumulator_storage_mapping
    (public_accumulator: MemCell)
    (partial_accumulators: list MemCell) : list (MemCell * MemCell) :=
  match partial_accumulators with
  | [] => []
  | partial_accumulator :: tail =>
      (public_accumulator, partial_accumulator) ::
      reduction_accumulator_storage_mapping public_accumulator tail
  end.

Lemma reduction_accumulator_storage_mapping_pair :
  forall public_accumulator partial_accumulators partial_accumulator,
    In partial_accumulator partial_accumulators ->
    In (public_accumulator, partial_accumulator)
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators).
Proof.
  intros public_accumulator partial_accumulators.
  induction partial_accumulators
    as [|head_accumulator tail_accumulators IH];
    intros partial_accumulator Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      left. reflexivity.
    + right.
      apply IH.
      exact Hin_tail.
Qed.

Record reduction_merge_view_contract
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (merge_law: Prop)
    (source_view after: PolyLang.t) : Prop := {
  rmvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmvc_merge_law :
    merge_law;
  rmvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (merge_law: Prop)
    (source_view after: PolyLang.t) : Prop := {
  rmvvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmvvc_value_merge :
    reduction_value_merge_obligations
      value merge_op initial_value final_value
      merge_order accumulator_values;
  rmvvc_merge_law :
    merge_law;
  rmvvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_associative_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmavc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmavc_algebra :
    reduction_associative_obligations
      value merge_op identity carrier;
  rmavc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_commutative_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmcvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmcvc_algebra :
    reduction_commutative_obligations
      value merge_op identity carrier;
  rmcvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_associative_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmavvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmavvc_value_merge :
    reduction_value_merge_obligations
      value merge_op initial_value final_value
      merge_order accumulator_values;
  rmavvc_algebra :
    reduction_associative_obligations
      value merge_op identity carrier;
  rmavvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_commutative_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmcsvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmcsvc_value_merge :
    reduction_value_merge_obligations
      value merge_op initial_value final_value
      merge_order accumulator_values;
  rmcsvc_algebra :
    reduction_commutative_obligations
      value merge_op identity carrier;
  rmcsvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_commutative_compatible_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (public_accumulator: MemCell)
    (public_specs accumulator_specs: list storage_spec)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmccsvc_value_base :
    reduction_merge_commutative_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values carrier source_view after;
  rmccsvc_storage_compatible :
    storage_compatibility_obligations
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs;
}.

Record reduction_merge_commutative_compatible_non_escape_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (public_accumulator: MemCell)
    (public_specs accumulator_specs: list storage_spec)
    (escaped_cells: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmccnesvc_compatible_base :
    reduction_merge_commutative_compatible_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs
      initial_value final_value accumulator_values carrier source_view after;
  rmccnesvc_non_escape :
    private_non_escape_obligations partial_accumulators escaped_cells;
}.

Record reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (public_accumulator: MemCell)
    (public_specs accumulator_specs: list storage_spec)
    (accumulator_bounds: list array_bounds)
    (escaped_cells: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmcbccnesvc_non_escape_base :
    reduction_merge_commutative_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs escaped_cells
      initial_value final_value accumulator_values carrier source_view after;
  rmcbccnesvc_accumulator_bounds :
    storage_bounds_obligations accumulator_bounds partial_accumulators;
}.

Definition reduction_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_reduction_merge_view_correct :
  forall input_view output_view
         source_domain chunks partial_accumulators merge_order
         (merge_law: Prop)
         before source_view after ok,
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    merge_law ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_view_contract
      input_view output_view source_domain chunks
      partial_accumulators merge_order merge_law source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain chunks partial_accumulators merge_order merge_law
         before source_view after ok Hret Hok Hmerge Hlaw Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_associative_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_associative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_associative_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok Hvalue_eqb Hret Hok Hmerge
         Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_associative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_commutative_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok Hvalue_eqb Hret Hok Hmerge
         Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_commutative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values
         (merge_law: Prop)
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    merge_law ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_value_view_contract
      value merge_op input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values merge_law source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values merge_law
         before source_view after ok Hvalue_eqb Hret Hok Hmerge
         Hvalue Hlaw Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_value_mergeb_sound
       value value_eqb merge_op Hvalue_eqb
       initial_value final_value merge_order accumulator_values Hvalue)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_associative_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_associative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_associative_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_value_mergeb_sound
       value value_eqb merge_op Hvalue_eqb
       initial_value final_value merge_order accumulator_values Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_reduction_associative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_commutative_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_value_mergeb_sound
       value value_eqb merge_op Hvalue_eqb
       initial_value final_value merge_order accumulator_values Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_reduction_commutative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_commutative_compatible_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    check_storage_compatibilityb
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_compatible_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs
      initial_value final_value accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage Hsemantics.
  pose proof
    (check_storage_compatibilityb_sound
       (reduction_accumulator_storage_mapping
          public_accumulator partial_accumulators)
       public_specs accumulator_specs Hstorage)
    as Hstorage_obligations.
  pose proof
    (checked_reduction_merge_commutative_value_view_correct
       value value_eqb merge_op identity input_view output_view
       source_domain chunks partial_accumulators merge_order
       initial_value final_value accumulator_values carrier
       before source_view after ok
       Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hsemantics)
    as [Hvalue_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_reduction_merge_commutative_compatible_non_escape_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs escaped_cells
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    check_storage_compatibilityb
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs = true ->
    check_private_non_escapeb partial_accumulators escaped_cells = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs escaped_cells
      initial_value final_value accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs escaped_cells
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage
         Hnon_escape Hsemantics.
  pose proof
    (check_private_non_escapeb_sound
       partial_accumulators escaped_cells Hnon_escape)
    as Hnon_escape_obligations.
  pose proof
    (checked_reduction_merge_commutative_compatible_value_view_correct
       value value_eqb merge_op identity input_view output_view
       source_domain chunks partial_accumulators merge_order
       public_accumulator public_specs accumulator_specs
       initial_value final_value accumulator_values carrier
       before source_view after ok
       Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage Hsemantics)
    as [Hcompatible_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_reduction_merge_commutative_bounded_compatible_non_escape_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    check_storage_compatibilityb
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs = true ->
    check_storage_boundsb accumulator_bounds partial_accumulators = true ->
    check_private_non_escapeb partial_accumulators escaped_cells = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage
         Hbounds Hnon_escape Hsemantics.
  pose proof
    (check_storage_boundsb_sound
       accumulator_bounds partial_accumulators Hbounds)
    as Hbounds_obligations.
  pose proof
    (checked_reduction_merge_commutative_compatible_non_escape_value_view_correct
       value value_eqb merge_op identity input_view output_view
       source_domain chunks partial_accumulators merge_order
       public_accumulator public_specs accumulator_specs escaped_cells
       initial_value final_value accumulator_values carrier
       before source_view after ok
       Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage
       Hnon_escape Hsemantics)
    as [Hnon_escape_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_reduction_merge_commutative_bounded_compatible_non_escape_value_public_refinement :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    check_storage_compatibilityb
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs = true ->
    check_storage_boundsb accumulator_bounds partial_accumulators = true ->
    check_private_non_escapeb partial_accumulators escaped_cells = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage
         Hbounds Hnon_escape Hsemantics.
  pose proof
    (checked_reduction_merge_commutative_bounded_compatible_non_escape_value_view_correct
       value value_eqb merge_op identity input_view output_view
       source_domain chunks partial_accumulators merge_order
       public_accumulator public_specs accumulator_specs
       accumulator_bounds escaped_cells
       initial_value final_value accumulator_values carrier
       before source_view after ok
       Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage
       Hbounds Hnon_escape Hsemantics)
    as [_ Hview].
  exact Hview.
Qed.

Record reduction_merge_commutative_bounded_non_escape_params (value: Type) := {
  rmcbnep_input_view : View.view;
  rmcbnep_output_view : View.view;
  rmcbnep_source_domain : list logical_instance;
  rmcbnep_chunks : reduction_chunks;
  rmcbnep_partial_accumulators : list MemCell;
  rmcbnep_merge_order : list MemCell;
  rmcbnep_public_accumulator : MemCell;
  rmcbnep_public_specs : list storage_spec;
  rmcbnep_accumulator_specs : list storage_spec;
  rmcbnep_accumulator_bounds : list array_bounds;
  rmcbnep_escaped_cells : list MemCell;
  rmcbnep_merge_op : value -> value -> value;
  rmcbnep_identity : value;
  rmcbnep_initial_value : value;
  rmcbnep_final_value : value;
  rmcbnep_accumulator_values : list (reduction_accumulator_value value);
  rmcbnep_carrier : list value;
  rmcbnep_source_view : PolyLang.t;
}.

Definition reduction_merge_commutative_bounded_non_escape_input_view
    {value: Type}
    (params: reduction_merge_commutative_bounded_non_escape_params value)
    : View.view :=
  rmcbnep_input_view value params.

Definition reduction_merge_commutative_bounded_non_escape_output_view
    {value: Type}
    (params: reduction_merge_commutative_bounded_non_escape_params value)
    : View.view :=
  reduction_pipeline_final_view (rmcbnep_output_view value params).

Definition reduction_merge_commutative_bounded_non_escape_check
    {value: Type}
    (params: reduction_merge_commutative_bounded_non_escape_params value)
    (before after: PolyLang.t) : imp bool :=
  check_reduction_source_view before (rmcbnep_source_view value params).

Definition reduction_merge_commutative_bounded_non_escape_side_condition
    {value: Type} (value_eqb: value -> value -> bool)
    (params: reduction_merge_commutative_bounded_non_escape_params value)
    (before after: PolyLang.t) : Prop :=
  check_reduction_mergeb
    (rmcbnep_source_domain value params)
    (rmcbnep_chunks value params)
    (rmcbnep_partial_accumulators value params)
    (rmcbnep_merge_order value params) = true /\
  @check_reduction_value_mergeb
    value value_eqb
    (rmcbnep_merge_op value params)
    (rmcbnep_initial_value value params)
    (rmcbnep_final_value value params)
    (rmcbnep_merge_order value params)
    (rmcbnep_accumulator_values value params) = true /\
  @check_reduction_commutative_lawb
    value value_eqb
    (rmcbnep_merge_op value params)
    (rmcbnep_identity value params)
    (rmcbnep_carrier value params) = true /\
  check_storage_compatibilityb
    (reduction_accumulator_storage_mapping
      (rmcbnep_public_accumulator value params)
      (rmcbnep_partial_accumulators value params))
    (rmcbnep_public_specs value params)
    (rmcbnep_accumulator_specs value params) = true /\
  check_storage_boundsb
    (rmcbnep_accumulator_bounds value params)
    (rmcbnep_partial_accumulators value params) = true /\
  check_private_non_escapeb
    (rmcbnep_partial_accumulators value params)
    (rmcbnep_escaped_cells value params) = true /\
  reduction_source_view_refines_view
    (rmcbnep_input_view value params)
    (rmcbnep_output_view value params)
    (rmcbnep_source_view value params)
    after.

Theorem reduction_merge_commutative_bounded_non_escape_family_sound :
  forall (value: Type) (value_eqb: value -> value -> bool)
         (value_eqb_sound:
           forall left right,
             value_eqb left right = true ->
             left = right)
         params before after ok,
    mayReturn
      (reduction_merge_commutative_bounded_non_escape_check
        params before after)
      ok ->
    ok = true ->
    reduction_merge_commutative_bounded_non_escape_side_condition
      value_eqb params before after ->
    View.view_refinement
      (reduction_merge_commutative_bounded_non_escape_input_view params)
      (reduction_merge_commutative_bounded_non_escape_output_view params)
      before after.
Proof.
  intros value value_eqb value_eqb_sound params before after ok
         Hret Hok Hside.
  destruct params as
    [input_view output_view source_domain chunks partial_accumulators merge_order
     public_accumulator public_specs accumulator_specs accumulator_bounds
     escaped_cells merge_op identity initial_value final_value
     accumulator_values carrier source_view].
  simpl in *.
  destruct Hside as
    [Hmerge
     [Hvalue
      [Halgebra
       [Hstorage
        [Hbounds [Hnon_escape Hsemantics]]]]]].
  eapply
    checked_reduction_merge_commutative_bounded_compatible_non_escape_value_public_refinement;
    eauto.
Qed.

Definition reduction_merge_commutative_bounded_non_escape_family
    (value: Type) (value_eqb: value -> value -> bool)
    (value_eqb_sound:
      forall left right,
        value_eqb left right = true ->
        left = right)
    : View.checked_parameterized_view_transform_family
        (reduction_merge_commutative_bounded_non_escape_params value) := {|
  generic_cpvtf_input_view :=
    reduction_merge_commutative_bounded_non_escape_input_view;
  generic_cpvtf_output_view :=
    reduction_merge_commutative_bounded_non_escape_output_view;
  generic_cpvtf_check :=
    reduction_merge_commutative_bounded_non_escape_check;
  generic_cpvtf_side_condition :=
    reduction_merge_commutative_bounded_non_escape_side_condition value_eqb;
  generic_cpvtf_check_sound :=
    reduction_merge_commutative_bounded_non_escape_family_sound
      value value_eqb value_eqb_sound;
|}.

Theorem reduction_private_accumulator_within_bounds :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc,
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after ->
    In acc partial_accumulators ->
    cell_within_declared_bounds accumulator_bounds acc.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc Hcontract Hin.
  destruct Hcontract as [_ Hbounds].
  eapply storage_bounds_cell_within; eauto.
Qed.

Theorem reduction_merged_accumulator_within_bounds :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc,
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after ->
    In acc merge_order ->
    cell_within_declared_bounds accumulator_bounds acc.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc Hcontract Hin.
  destruct Hcontract as [Hbase Hbounds].
  eapply storage_bounds_cell_within
    with (cells := partial_accumulators); eauto.
  destruct Hbase as [Hcompatible _].
  destruct Hcompatible as [Hvalue _].
  destruct Hvalue as [Hmerge _ _ _].
  eapply reduction_merged_accumulator_private; eauto.
Qed.

Theorem reduction_private_accumulator_not_escaped :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc,
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after ->
    In acc partial_accumulators ->
    ~ In acc escaped_cells.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc Hcontract Hin.
  destruct Hcontract as [Hbase _].
  destruct Hbase as [_ Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint; eauto.
Qed.

Theorem reduction_merged_accumulator_not_escaped :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc,
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after ->
    In acc merge_order ->
    ~ In acc escaped_cells.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc Hcontract Hin.
  destruct Hcontract as [Hbase _].
  destruct Hbase as [Hcompatible Hnon_escape].
  destruct Hnon_escape as [Hdisjoint].
  eapply Hdisjoint.
  destruct Hcompatible as [Hvalue _].
  destruct Hvalue as [Hmerge _ _ _].
  eapply reduction_merged_accumulator_private; eauto.
Qed.

Theorem reduction_value_entry_in_merge_order :
  forall (value: Type)
         (merge_op: value -> value -> value)
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values
         (merge_law: Prop)
         source_view after acc acc_value,
    reduction_merge_value_view_contract
      value merge_op input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values merge_law source_view after ->
    In (acc, acc_value) accumulator_values ->
    In acc merge_order.
Proof.
  intros value merge_op input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values merge_law
         source_view after acc acc_value Hcontract Hin.
  destruct Hcontract as [_ Hvalues _ _].
  eapply reduction_accumulator_value_entry_in_merge_order; eauto.
Qed.

Theorem reduction_value_entry_private_accumulator :
  forall (value: Type)
         (merge_op: value -> value -> value)
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values
         (merge_law: Prop)
         source_view after acc acc_value,
    reduction_merge_value_view_contract
      value merge_op input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values merge_law source_view after ->
    In (acc, acc_value) accumulator_values ->
    In acc partial_accumulators.
Proof.
  intros value merge_op input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values merge_law
         source_view after acc acc_value Hcontract Hin.
  destruct Hcontract as [Hmerge Hvalues Hlaw Hsemantics].
  pose proof
    (reduction_accumulator_value_entry_in_merge_order
       value merge_op initial_value final_value merge_order
       accumulator_values acc acc_value Hvalues Hin)
    as Hmerge_order.
  eapply reduction_merged_accumulator_private; eauto.
Qed.

Theorem reduction_value_entry_compatible_specs :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         initial_value final_value accumulator_values carrier
         source_view after acc acc_value,
    reduction_merge_commutative_compatible_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs
      initial_value final_value accumulator_values carrier source_view after ->
    In (acc, acc_value) accumulator_values ->
    exists public_spec accumulator_spec,
      In public_spec public_specs /\
      In accumulator_spec accumulator_specs /\
      storage_spec_cell public_spec = public_accumulator /\
      storage_spec_cell accumulator_spec = acc /\
      storage_specs_compatible public_spec accumulator_spec.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         initial_value final_value accumulator_values carrier
         source_view after acc acc_value Hcontract Hin.
  destruct Hcontract as [Hbase Hcompatible].
  destruct Hbase as [Hmerge Hvalues _ _].
  pose proof
    (reduction_accumulator_value_entry_in_merge_order
       value merge_op initial_value final_value merge_order
       accumulator_values acc acc_value Hvalues Hin)
    as Hmerge_order.
  pose proof
    (reduction_merged_accumulator_private
       source_domain chunks partial_accumulators merge_order acc
       Hmerge Hmerge_order)
    as Hprivate.
  pose proof
    (reduction_accumulator_storage_mapping_pair
       public_accumulator partial_accumulators acc Hprivate)
    as Hmapping.
  eapply storage_compatibility_mapping_pair_specs; eauto.
Qed.

Theorem reduction_value_entry_within_bounds :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc acc_value,
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after ->
    In (acc, acc_value) accumulator_values ->
    cell_within_declared_bounds accumulator_bounds acc.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc acc_value Hcontract Hin.
  assert (Hmerge_order: In acc merge_order).
  {
    destruct Hcontract as [Hbase _].
    destruct Hbase as [Hcompatible _].
    destruct Hcompatible as [Hvalue _].
    destruct Hvalue as [_ Hvalues _ _].
    eapply reduction_accumulator_value_entry_in_merge_order; eauto.
  }
  eapply reduction_merged_accumulator_within_bounds; eauto.
Qed.

Theorem reduction_value_entry_not_escaped :
  forall (value: Type)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc acc_value,
    reduction_merge_commutative_bounded_compatible_non_escape_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs accumulator_bounds escaped_cells
      initial_value final_value accumulator_values carrier source_view after ->
    In (acc, acc_value) accumulator_values ->
    ~ In acc escaped_cells.
Proof.
  intros value merge_op identity input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         accumulator_bounds escaped_cells
         initial_value final_value accumulator_values carrier
         source_view after acc acc_value Hcontract Hin.
  assert (Hmerge_order: In acc merge_order).
  {
    destruct Hcontract as [Hbase _].
    destruct Hbase as [Hcompatible _].
    destruct Hcompatible as [Hvalue _].
    destruct Hvalue as [_ Hvalues _ _].
    eapply reduction_accumulator_value_entry_in_merge_order; eauto.
  }
  eapply reduction_merged_accumulator_not_escaped; eauto.
Qed.

End ReductionMergeValidator.
