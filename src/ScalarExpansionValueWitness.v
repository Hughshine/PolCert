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

Definition scalar_expansion_value_event_values_match
    {value: Type}
    (value_event: scalar_expansion_value_event value) : Prop :=
  match value_event with
  | ExpansionValueWrite source_value private_value =>
      source_value = private_value
  | ExpansionValueRead source_value private_value =>
      source_value = private_value
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

Lemma scalar_expansion_value_trace_pair_event_in_events :
  forall (value: Type)
         (trace: scalar_expansion_value_trace value)
         storage_event value_event,
    In (storage_event, value_event) trace ->
    In storage_event (scalar_expansion_value_trace_events trace).
Proof.
  intros value trace.
  induction trace as [|[head_storage head_value] tail IH];
    intros storage_event value_event Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + inversion Hhead; subst.
      left. reflexivity.
    + right.
      eapply IH.
      exact Htail.
Qed.

Fixpoint scalar_expansion_value_trace_values {value: Type}
    (trace: scalar_expansion_value_trace value)
    : list (scalar_expansion_value_event value) :=
  match trace with
  | [] => []
  | (_, value_event) :: tail =>
      value_event :: scalar_expansion_value_trace_values tail
  end.

Definition expanded_values_defined_by {value: Type}
    (expanded_values: list (MemCell * value))
    (defined_cells: list MemCell) : Prop :=
  forall cell current_value,
    lookup_expanded_value cell expanded_values = Some current_value ->
    In cell defined_cells.

Lemma expanded_values_defined_by_nil :
  forall (value: Type) defined_cells,
    @expanded_values_defined_by value [] defined_cells.
Proof.
  intros value defined_cells cell current_value Hlookup.
  simpl in Hlookup.
  discriminate.
Qed.

Lemma expanded_values_defined_by_update :
  forall (value: Type) expanded_values defined_cells write_cell write_value,
    @expanded_values_defined_by value expanded_values defined_cells ->
    @expanded_values_defined_by value
      (update_expanded_value write_cell write_value expanded_values)
      (write_cell :: defined_cells).
Proof.
  induction expanded_values as [|[cell old_value] tail IH];
    intros defined_cells write_cell write_value Hdefined
           query_cell query_value Hlookup; simpl in Hlookup.
  - destruct (mem_cell_strict_eqb query_cell write_cell) eqn:Heq.
    + apply mem_cell_strict_eqb_eq in Heq.
      subst. left. reflexivity.
    + discriminate.
  - destruct (mem_cell_strict_eqb write_cell cell) eqn:Hwrite.
    + simpl in Hlookup.
      destruct (mem_cell_strict_eqb query_cell cell) eqn:Hquery.
      * apply mem_cell_strict_eqb_eq in Hquery.
        apply mem_cell_strict_eqb_eq in Hwrite.
        subst. left. reflexivity.
      * right.
        eapply Hdefined.
        simpl.
        rewrite Hquery.
        exact Hlookup.
    + simpl in Hlookup.
      destruct (mem_cell_strict_eqb query_cell cell) eqn:Hquery.
      * inversion Hlookup; subst.
        right.
        eapply Hdefined.
        simpl.
        rewrite Hquery.
        reflexivity.
      * eapply IH.
        -- intros old_query old_current Hold.
           destruct (mem_cell_strict_eqb old_query cell) eqn:Hold_query.
           ++ apply mem_cell_strict_eqb_eq in Hold_query.
              subst.
              eapply Hdefined.
              simpl.
              rewrite mem_cell_strict_eq_eqb with (c2 := cell).
              ** reflexivity.
              ** reflexivity.
           ++ eapply Hdefined.
              simpl.
              rewrite Hold_query.
              exact Hold.
        -- exact Hlookup.
Qed.

Theorem scalar_expansion_value_trace_private_use_def_from :
  forall (value: Type) trace expanded_values defined_cells,
    scalar_expansion_value_trace_simulates_from
      expanded_values trace ->
    @expanded_values_defined_by value expanded_values defined_cells ->
    private_reads_defined
      defined_cells
      (scalar_expansion_private_trace
         (scalar_expansion_value_trace_events trace)).
Proof.
  induction trace as [|[storage_event value_event] tail IH];
    intros expanded_values defined_cells Hsim Hdefined; simpl in Hsim.
  - exact I.
  - destruct value_event as [source_value private_value
                            | source_value private_value].
    + destruct Hsim as [Hkind [_ Htail]].
      destruct storage_event as [event_kind event_instance
                                 event_source event_private].
      simpl in *.
      destruct event_kind; try discriminate.
      eapply IH.
      * exact Htail.
      * apply expanded_values_defined_by_update.
        exact Hdefined.
    + destruct Hsim as [Hkind Hread].
      destruct (lookup_expanded_value
                  (expansion_event_private_cell storage_event)
                  expanded_values) as [current_value |] eqn:Hlookup;
        try contradiction.
      destruct Hread as [_ [_ Htail]].
      destruct storage_event as [event_kind event_instance
                                 event_source event_private].
      simpl in *.
      destruct event_kind; try discriminate.
      split.
      * eapply Hdefined.
        exact Hlookup.
      * eapply IH; eauto.
Qed.

Theorem scalar_expansion_value_trace_private_use_def :
  forall (value: Type) (trace: scalar_expansion_value_trace value),
    scalar_expansion_value_trace_simulates trace ->
    private_use_def_trace
      (scalar_expansion_private_trace
         (scalar_expansion_value_trace_events trace)).
Proof.
  intros value trace Hsim.
  unfold scalar_expansion_value_trace_simulates,
         private_use_def_trace in *.
  eapply scalar_expansion_value_trace_private_use_def_from.
  - exact Hsim.
  - apply expanded_values_defined_by_nil.
Qed.

Theorem scalar_expansion_value_trace_simulates_from_event_matched :
  forall (value: Type)
         (trace: scalar_expansion_value_trace value)
         expanded_values storage_event value_event,
    scalar_expansion_value_trace_simulates_from
      expanded_values trace ->
    In (storage_event, value_event) trace ->
    scalar_expansion_value_event_kind_matches
      storage_event value_event /\
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros value trace.
  induction trace as [|[head_storage head_value] tail IH];
    intros expanded_values storage_event value_event Hsim Hin;
    simpl in Hin.
  - contradiction.
  - destruct Hin as [Hhead | Htail_in].
    + inversion Hhead; subst head_storage head_value.
      destruct value_event as [source_value private_value
                              | source_value private_value];
        simpl in Hsim.
      * destruct Hsim as [Hkind [Hvalue _]].
        split.
        -- unfold scalar_expansion_value_event_kind_matches.
           rewrite Hkind.
           exact I.
        -- unfold scalar_expansion_value_event_values_match.
           exact Hvalue.
      * destruct Hsim as [Hkind Hread].
        destruct
          (lookup_expanded_value
             (expansion_event_private_cell storage_event)
             expanded_values) as [current_value |] eqn:Hlookup;
          try contradiction.
        destruct Hread as [Hsource [Hprivate _]].
        split.
        -- unfold scalar_expansion_value_event_kind_matches.
           rewrite Hkind.
           exact I.
        -- unfold scalar_expansion_value_event_values_match.
           transitivity current_value.
           ++ exact Hsource.
           ++ symmetry. exact Hprivate.
    + destruct head_value as [head_source head_private
                            | head_source head_private];
        simpl in Hsim.
      * destruct Hsim as [_ [_ Htail]].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
      * destruct Hsim as [_ Hread].
        destruct
          (lookup_expanded_value
             (expansion_event_private_cell head_storage)
             expanded_values) as [current_value |] eqn:Hlookup;
          try contradiction.
        destruct Hread as [_ [_ Htail]].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
Qed.

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

Theorem scalar_expansion_value_obligations_private_use_def :
  forall (value: Type) (trace: scalar_expansion_value_trace value),
    scalar_expansion_value_obligations value trace ->
    private_use_def_trace
      (scalar_expansion_private_trace
         (scalar_expansion_value_trace_events trace)).
Proof.
  intros value trace Hobligations.
  destruct Hobligations as [Hsimulates].
  apply scalar_expansion_value_trace_private_use_def.
  exact Hsimulates.
Qed.

Theorem scalar_expansion_value_obligations_events_private_use_def :
  forall (value: Type)
         (value_trace: scalar_expansion_value_trace value)
         events,
    scalar_expansion_value_obligations value value_trace ->
    scalar_expansion_value_trace_events value_trace = events ->
    private_use_def_trace (scalar_expansion_private_trace events).
Proof.
  intros value value_trace events Hobligations Hevents.
  subst events.
  apply scalar_expansion_value_obligations_private_use_def.
  exact Hobligations.
Qed.

Theorem scalar_expansion_value_obligation_event_matched :
  forall (value: Type)
         (value_trace: scalar_expansion_value_trace value)
         storage_event value_event,
    scalar_expansion_value_obligations value value_trace ->
    In (storage_event, value_event) value_trace ->
    scalar_expansion_value_event_kind_matches
      storage_event value_event /\
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros value value_trace storage_event value_event
         Hobligations Hin.
  destruct Hobligations as [Hsimulates].
  unfold scalar_expansion_value_trace_simulates in Hsimulates.
  eapply scalar_expansion_value_trace_simulates_from_event_matched.
  - exact Hsimulates.
  - exact Hin.
Qed.

Theorem scalar_expansion_value_obligation_write_values_equal :
  forall (value: Type)
         (value_trace: scalar_expansion_value_trace value)
         storage_event source_value private_value,
    scalar_expansion_value_obligations value value_trace ->
    In (storage_event, ExpansionValueWrite source_value private_value)
      value_trace ->
    source_value = private_value.
Proof.
  intros value value_trace storage_event source_value private_value
         Hobligations Hin.
  pose proof
    (scalar_expansion_value_obligation_event_matched
       value value_trace storage_event
       (ExpansionValueWrite source_value private_value)
       Hobligations Hin)
    as [_ Hvalues].
  simpl in Hvalues.
  exact Hvalues.
Qed.

Theorem scalar_expansion_value_obligation_read_values_equal :
  forall (value: Type)
         (value_trace: scalar_expansion_value_trace value)
         storage_event source_value private_value,
    scalar_expansion_value_obligations value value_trace ->
    In (storage_event, ExpansionValueRead source_value private_value)
      value_trace ->
    source_value = private_value.
Proof.
  intros value value_trace storage_event source_value private_value
         Hobligations Hin.
  pose proof
    (scalar_expansion_value_obligation_event_matched
       value value_trace storage_event
       (ExpansionValueRead source_value private_value)
       Hobligations Hin)
    as [_ Hvalues].
  simpl in Hvalues.
  exact Hvalues.
Qed.
