Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import InstanceProjectionWitness.
Require Import ScalarExpansionWitness.

Import ListNotations.

(** Value-flow witness for scalar privatization / expansion.

    [ScalarExpansionWitness] checks the storage bookkeeping: dynamic
    [(source instance, source scalar cell)] keys choose private cells, events
    use those choices consistently, and private reads have earlier writes.
    This module adds a finite value-flow layer over the same event stream.

    The witness is still independent of C expressions.  A later
    instruction-level proof should produce this trace from source and target
    expression evaluation.  Once supplied, the checker states the important
    local semantic fact: each private write stores the source logical value it
    replaces, and each private read observes the current private value that
    corresponds to the source logical read. *)

Inductive scalar_expansion_value_event (value: Type) :=
| ExpansionValueWrite (source_value private_value: value)
| ExpansionValueRead (source_value private_value: value).

Arguments ExpansionValueWrite {value} _ _.
Arguments ExpansionValueRead {value} _ _.

Definition scalar_expansion_value_trace (value: Type) :=
  list (scalar_expansion_event * scalar_expansion_value_event value).

Definition scalar_expansion_event_kind_eqb
    (left right: scalar_expansion_event_kind) : bool :=
  match left, right with
  | ExpansionWrite, ExpansionWrite => true
  | ExpansionRead, ExpansionRead => true
  | _, _ => false
  end.

Lemma scalar_expansion_event_kind_eqb_eq :
  forall left right,
    scalar_expansion_event_kind_eqb left right = true ->
    left = right.
Proof.
  intros left right Hcheck.
  destruct left; destruct right; simpl in Hcheck; try discriminate;
    reflexivity.
Qed.

Definition scalar_expansion_event_eqb
    (left right: scalar_expansion_event) : bool :=
  scalar_expansion_event_kind_eqb
    (expansion_event_kind left)
    (expansion_event_kind right) &&
  logical_instance_eqb
    (expansion_event_instance left)
    (expansion_event_instance right) &&
  mem_cell_strict_eqb
    (expansion_event_source_cell left)
    (expansion_event_source_cell right) &&
  mem_cell_strict_eqb
    (expansion_event_private_cell left)
    (expansion_event_private_cell right).

Lemma scalar_expansion_event_eqb_eq :
  forall left right,
    scalar_expansion_event_eqb left right = true ->
    left = right.
Proof.
  intros [left_kind left_instance left_source left_private]
         [right_kind right_instance right_source right_private] Hcheck.
  unfold scalar_expansion_event_eqb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hkind & Hinstance) & Hsource) & Hprivate).
  apply scalar_expansion_event_kind_eqb_eq in Hkind.
  apply logical_instance_eqb_eq in Hinstance.
  apply mem_cell_strict_eqb_eq in Hsource.
  apply mem_cell_strict_eqb_eq in Hprivate.
  subst. reflexivity.
Qed.

Fixpoint scalar_expansion_events_eqb
    (left right: list scalar_expansion_event) : bool :=
  match left, right with
  | [], [] => true
  | left_event :: left_tail, right_event :: right_tail =>
      scalar_expansion_event_eqb left_event right_event &&
      scalar_expansion_events_eqb left_tail right_tail
  | _, _ => false
  end.

Lemma scalar_expansion_events_eqb_eq :
  forall left right,
    scalar_expansion_events_eqb left right = true ->
    left = right.
Proof.
  induction left as [|left_event left_tail IH];
    intros right Hcheck;
    destruct right as [|right_event right_tail];
    simpl in Hcheck; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hevent Htail].
    apply scalar_expansion_event_eqb_eq in Hevent.
    apply IH in Htail.
    subst. reflexivity.
Qed.

Fixpoint lookup_expanded_value {value: Type}
    (private_cell: MemCell)
    (values: list (MemCell * value)) : option value :=
  match values with
  | [] => None
  | (cell, current_value) :: tail =>
      if mem_cell_strict_eqb private_cell cell
      then Some current_value
      else lookup_expanded_value private_cell tail
  end.

Fixpoint update_expanded_value {value: Type}
    (private_cell: MemCell)
    (new_value: value)
    (values: list (MemCell * value)) : list (MemCell * value) :=
  match values with
  | [] => [(private_cell, new_value)]
  | (cell, old_value) :: tail =>
      if mem_cell_strict_eqb private_cell cell
      then (cell, new_value) :: tail
      else (cell, old_value) ::
           update_expanded_value private_cell new_value tail
  end.

Definition scalar_expansion_value_event_kind_matches
    {value: Type}
    (storage_event: scalar_expansion_event)
    (value_event: scalar_expansion_value_event value) : Prop :=
  match expansion_event_kind storage_event, value_event with
  | ExpansionWrite, ExpansionValueWrite _ _ => True
  | ExpansionRead, ExpansionValueRead _ _ => True
  | _, _ => False
  end.

Fixpoint scalar_expansion_value_trace_simulates_from {value: Type}
    (expanded_values: list (MemCell * value))
    (trace: scalar_expansion_value_trace value) : Prop :=
  match trace with
  | [] => True
  | (storage_event, ExpansionValueWrite source_value private_value) :: tail =>
      expansion_event_kind storage_event = ExpansionWrite /\
      source_value = private_value /\
      scalar_expansion_value_trace_simulates_from
        (update_expanded_value
           (expansion_event_private_cell storage_event)
           private_value expanded_values)
        tail
  | (storage_event, ExpansionValueRead source_value private_value) :: tail =>
      expansion_event_kind storage_event = ExpansionRead /\
      match lookup_expanded_value
              (expansion_event_private_cell storage_event)
              expanded_values with
      | Some current_value =>
          source_value = current_value /\
          private_value = current_value /\
          scalar_expansion_value_trace_simulates_from expanded_values tail
      | None => False
      end
  end.

Definition scalar_expansion_value_trace_simulates {value: Type}
    (trace: scalar_expansion_value_trace value) : Prop :=
  scalar_expansion_value_trace_simulates_from [] trace.

Fixpoint check_scalar_expansion_value_trace_fromb {value: Type}
    (value_eqb: value -> value -> bool)
    (expanded_values: list (MemCell * value))
    (trace: scalar_expansion_value_trace value) : bool :=
  match trace with
  | [] => true
  | (storage_event, ExpansionValueWrite source_value private_value) :: tail =>
      match expansion_event_kind storage_event with
      | ExpansionWrite =>
          value_eqb source_value private_value &&
          check_scalar_expansion_value_trace_fromb
            value_eqb
            (update_expanded_value
               (expansion_event_private_cell storage_event)
               private_value expanded_values)
            tail
      | ExpansionRead => false
      end
  | (storage_event, ExpansionValueRead source_value private_value) :: tail =>
      match expansion_event_kind storage_event with
      | ExpansionWrite => false
      | ExpansionRead =>
          match lookup_expanded_value
                  (expansion_event_private_cell storage_event)
                  expanded_values with
          | Some current_value =>
              value_eqb source_value current_value &&
              value_eqb private_value current_value &&
              check_scalar_expansion_value_trace_fromb
                value_eqb expanded_values tail
          | None => false
          end
      end
  end.

Definition check_scalar_expansion_value_traceb {value: Type}
    (value_eqb: value -> value -> bool)
    (trace: scalar_expansion_value_trace value) : bool :=
  check_scalar_expansion_value_trace_fromb value_eqb [] trace.

Fixpoint scalar_expansion_value_trace_events {value: Type}
    (trace: scalar_expansion_value_trace value)
    : list scalar_expansion_event :=
  match trace with
  | [] => []
  | (storage_event, _) :: tail =>
      storage_event :: scalar_expansion_value_trace_events tail
  end.

Fixpoint scalar_expansion_value_trace_values {value: Type}
    (trace: scalar_expansion_value_trace value)
    : list (scalar_expansion_value_event value) :=
  match trace with
  | [] => []
  | (_, value_event) :: tail =>
      value_event :: scalar_expansion_value_trace_values tail
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_scalar_expansion_value_trace_fromb_sound :
  forall trace expanded_values,
    check_scalar_expansion_value_trace_fromb
      value_eqb expanded_values trace = true ->
    scalar_expansion_value_trace_simulates_from expanded_values trace.
Proof.
  induction trace as [|[storage_event value_event] tail IH];
    intros expanded_values Hcheck; simpl in Hcheck.
  - exact I.
  - destruct value_event as [source_value private_value
                            | source_value private_value];
      destruct (expansion_event_kind storage_event) eqn:Hkind;
      simpl in Hcheck; try discriminate.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hkind.
      * split.
        -- exact Hvalue.
        -- apply IH.
           exact Htail.
    + destruct (lookup_expanded_value
                  (expansion_event_private_cell storage_event)
                  expanded_values) as [current_value |] eqn:Hlookup;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hsource & Hprivate) & Htail).
      apply value_eqb_sound in Hsource.
      apply value_eqb_sound in Hprivate.
      split.
      * exact Hkind.
      * rewrite Hlookup.
        split.
        -- exact Hsource.
        -- split.
           ++ exact Hprivate.
           ++ apply IH.
              exact Htail.
Qed.

Record scalar_expansion_value_obligations
    (trace: scalar_expansion_value_trace value) : Prop := {
  sevo_trace_simulates :
    scalar_expansion_value_trace_simulates trace;
}.

Lemma check_scalar_expansion_value_traceb_sound :
  forall trace,
    check_scalar_expansion_value_traceb value_eqb trace = true ->
    scalar_expansion_value_obligations trace.
Proof.
  unfold check_scalar_expansion_value_traceb.
  intros trace Hcheck.
  constructor.
  apply check_scalar_expansion_value_trace_fromb_sound.
  exact Hcheck.
Qed.

End Soundness.
