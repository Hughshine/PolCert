Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Value witness for reduction privatization and merge.

    [ReductionMergeWitness] checks chunk coverage, private accumulator
    uniqueness, and merge-order coverage.  This module checks a narrower value
    layer: the merge order is paired with values for the corresponding private
    accumulators, and folding those values with a supplied merge operator
    yields the claimed final value.

    This does not prove that the transformation is allowed to reassociate or
    reorder the source reduction.  The algebraic law remains an explicit
    semantic assumption in [ReductionMergeValidator]. *)

Definition reduction_accumulator_value (value: Type) :=
  (MemCell * value)%type.

Fixpoint reduction_value_cells {value: Type}
    (values: list (reduction_accumulator_value value)) : list MemCell :=
  match values with
  | [] => []
  | (cell, _) :: tail =>
      cell :: reduction_value_cells tail
  end.

Fixpoint reduction_value_lookup {value: Type}
    (cell: MemCell)
    (values: list (reduction_accumulator_value value)) : option value :=
  match values with
  | [] => None
  | (value_cell, value') :: tail =>
      if mem_cell_strict_eqb cell value_cell
      then Some value'
      else reduction_value_lookup cell tail
  end.

Fixpoint reduction_merge_values_for_order {value: Type}
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : option (list value) :=
  match merge_order with
  | [] => Some []
  | cell :: tail =>
      match reduction_value_lookup cell values,
            reduction_merge_values_for_order tail values with
      | Some value', Some tail_values =>
          Some (value' :: tail_values)
      | _, _ => None
      end
  end.

Fixpoint fold_reduction_values {value: Type}
    (merge_op: value -> value -> value)
    (acc: value)
    (values: list value) : value :=
  match values with
  | [] => acc
  | value' :: tail =>
      fold_reduction_values merge_op (merge_op acc value') tail
  end.

Definition reduction_value_merge_result {value: Type}
    (merge_op: value -> value -> value)
    (initial_value final_value: value)
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : Prop :=
  exists ordered_values,
    reduction_merge_values_for_order merge_order values =
      Some ordered_values /\
    fold_reduction_values merge_op initial_value ordered_values =
      final_value.

Definition reduction_accumulator_values_exact_cover {value: Type}
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : Prop :=
  NoDup (reduction_value_cells values) /\
  (forall cell,
     In cell merge_order <-> In cell (reduction_value_cells values)).

Definition check_reduction_accumulator_values_exact_coverb {value: Type}
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : bool :=
  mem_cells_nodupb (reduction_value_cells values) &&
  mem_cells_subsetb merge_order (reduction_value_cells values) &&
  mem_cells_subsetb (reduction_value_cells values) merge_order.

Lemma check_reduction_accumulator_values_exact_coverb_sound :
  forall (value: Type)
         merge_order
         (values: list (reduction_accumulator_value value)),
    check_reduction_accumulator_values_exact_coverb merge_order values = true ->
    reduction_accumulator_values_exact_cover merge_order values.
Proof.
  intros value merge_order values Hcheck.
  unfold check_reduction_accumulator_values_exact_coverb in Hcheck.
  unfold reduction_accumulator_values_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hmerge_subset) & Hvalue_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - intro cell.
    split.
    + intro Hin_merge.
      eapply mem_cells_subsetb_sound; eauto.
    + intro Hin_value.
      eapply mem_cells_subsetb_sound; eauto.
Qed.

Lemma reduction_value_lookup_in_cells :
  forall (value: Type)
         cell
         (values: list (reduction_accumulator_value value)),
    In cell (reduction_value_cells values) ->
    exists value',
      reduction_value_lookup cell values = Some value'.
Proof.
  intros value cell values.
  induction values as [|[head_cell head_value] tail IH];
    intros Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      rewrite mem_cell_strict_eq_eqb by reflexivity.
      exists head_value.
      reflexivity.
    + destruct (mem_cell_strict_eqb cell head_cell) eqn:Heq.
      * exists head_value.
        reflexivity.
      * apply IH.
        exact Hin_tail.
Qed.

Definition check_reduction_value_mergeb {value: Type}
    (value_eqb: value -> value -> bool)
    (merge_op: value -> value -> value)
    (initial_value final_value: value)
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : bool :=
  check_reduction_accumulator_values_exact_coverb merge_order values &&
  match reduction_merge_values_for_order merge_order values with
  | Some ordered_values =>
      value_eqb
        (fold_reduction_values merge_op initial_value ordered_values)
        final_value
  | None => false
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Variable merge_op: value -> value -> value.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_reduction_value_mergeb_result_sound :
  forall initial_value final_value merge_order values,
    check_reduction_value_mergeb
      value_eqb merge_op initial_value final_value
      merge_order values = true ->
    reduction_value_merge_result
      merge_op initial_value final_value merge_order values.
Proof.
  intros initial_value final_value merge_order values Hcheck.
  unfold check_reduction_value_mergeb in Hcheck.
  rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hcheck].
  destruct (reduction_merge_values_for_order merge_order values)
    as [ordered_values |] eqn:Hordered; try discriminate.
  apply value_eqb_sound in Hcheck.
  exists ordered_values.
  split.
  - exact Hordered.
  - exact Hcheck.
Qed.

Record reduction_value_merge_obligations
    (initial_value final_value: value)
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : Prop := {
  rvmo_values_exact_cover :
    reduction_accumulator_values_exact_cover merge_order values;
  rvmo_merge_result :
    reduction_value_merge_result
      merge_op initial_value final_value merge_order values;
}.

Lemma check_reduction_value_mergeb_sound :
  forall initial_value final_value merge_order values,
    check_reduction_value_mergeb
      value_eqb merge_op initial_value final_value
      merge_order values = true ->
    reduction_value_merge_obligations
      initial_value final_value merge_order values.
Proof.
  intros initial_value final_value merge_order values Hcheck.
  constructor.
  - unfold check_reduction_value_mergeb in Hcheck.
    rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [Hcover _].
    apply check_reduction_accumulator_values_exact_coverb_sound.
    exact Hcover.
  - apply check_reduction_value_mergeb_result_sound.
    exact Hcheck.
Qed.

Theorem reduction_accumulator_value_cells_nodup :
  forall initial_value final_value merge_order values,
    reduction_value_merge_obligations
      initial_value final_value merge_order values ->
    NoDup (reduction_value_cells values).
Proof.
  intros initial_value final_value merge_order values Hobligations.
  destruct Hobligations as [Hcover _].
  destruct Hcover as [Hnodup _].
  exact Hnodup.
Qed.

Theorem reduction_merged_accumulator_has_value :
  forall initial_value final_value merge_order values cell,
    reduction_value_merge_obligations
      initial_value final_value merge_order values ->
    In cell merge_order ->
    exists value',
      reduction_value_lookup cell values = Some value'.
Proof.
  intros initial_value final_value merge_order values cell
         Hobligations Hin_merge.
  destruct Hobligations as [Hcover _].
  destruct Hcover as [_ Hexact_cover].
  apply reduction_value_lookup_in_cells.
  apply Hexact_cover.
  exact Hin_merge.
Qed.

Theorem reduction_value_cell_in_merge_order :
  forall initial_value final_value merge_order values cell,
    reduction_value_merge_obligations
      initial_value final_value merge_order values ->
    In cell (reduction_value_cells values) ->
    In cell merge_order.
Proof.
  intros initial_value final_value merge_order values cell
         Hobligations Hin_value.
  destruct Hobligations as [Hcover _].
  destruct Hcover as [_ Hexact_cover].
  apply Hexact_cover.
  exact Hin_value.
Qed.

End Soundness.
