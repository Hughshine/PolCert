Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import CopyProtocolWitness.

Import ListNotations.

(** Value-flow witness for copy-mediated local storage.

    [CopyProtocolWitness] proves that local reads and copy-outs are defined and
    commits are unique.  This module adds a value-flow layer: copy-in transfers
    the source value to the local cell, local writes update the local value,
    local reads observe the current local value, and copy-out commits the
    current local value to the target. *)

Inductive copy_value_event (value: Type) :=
| CopyValueIn (source_value local_value: value)
| CopyValueRead (read_value: value)
| CopyValueWrite (new_local_value: value)
| CopyValueOut (local_value target_value: value).

Arguments CopyValueIn {value} _ _.
Arguments CopyValueRead {value} _.
Arguments CopyValueWrite {value} _.
Arguments CopyValueOut {value} _ _.

Definition copy_value_trace (value: Type) :=
  list (copy_event * copy_value_event value).

Definition copy_value_event_kind_matches {value: Type}
    (event: copy_event)
    (value_event: copy_value_event value) : Prop :=
  match event, value_event with
  | CopyIn _ _, CopyValueIn _ _ => True
  | LocalRead _, CopyValueRead _ => True
  | LocalWrite _, CopyValueWrite _ => True
  | CopyOut _ _, CopyValueOut _ _ => True
  | _, _ => False
  end.

Definition copy_value_event_values_match {value: Type}
    (value_event: copy_value_event value) : Prop :=
  match value_event with
  | CopyValueIn source_value local_value =>
      source_value = local_value
  | CopyValueRead _ => True
  | CopyValueWrite _ => True
  | CopyValueOut local_value target_value =>
      local_value = target_value
  end.

Fixpoint lookup_local_value {value: Type}
    (local_cell: MemCell)
    (locals: list (MemCell * value)) : option value :=
  match locals with
  | [] => None
  | (cell, local_value) :: tail =>
      if mem_cell_strict_eqb local_cell cell
      then Some local_value
      else lookup_local_value local_cell tail
  end.

Fixpoint update_local_value {value: Type}
    (local_cell: MemCell)
    (local_value: value)
    (locals: list (MemCell * value)) : list (MemCell * value) :=
  match locals with
  | [] => [(local_cell, local_value)]
  | (cell, old_value) :: tail =>
      if mem_cell_strict_eqb local_cell cell
      then (cell, local_value) :: tail
      else (cell, old_value) ::
           update_local_value local_cell local_value tail
  end.

Fixpoint copy_value_trace_simulates_from {value: Type}
    (locals: list (MemCell * value))
    (trace: copy_value_trace value) : Prop :=
  match trace with
  | [] => True
  | (CopyIn _ local_cell, CopyValueIn source_value local_value)
      :: tail =>
      source_value = local_value /\
      copy_value_trace_simulates_from
        (update_local_value local_cell local_value locals) tail
  | (LocalRead local_cell, CopyValueRead read_value) :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          read_value = current_value /\
          copy_value_trace_simulates_from locals tail
      | None => False
      end
  | (LocalWrite local_cell, CopyValueWrite new_local_value) :: tail =>
      copy_value_trace_simulates_from
        (update_local_value local_cell new_local_value locals) tail
  | (CopyOut local_cell _, CopyValueOut local_value target_value)
      :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          local_value = current_value /\
          target_value = current_value /\
          copy_value_trace_simulates_from locals tail
      | None => False
      end
  | _ :: _ => False
  end.

Definition copy_value_trace_simulates {value: Type}
    (trace: copy_value_trace value) : Prop :=
  copy_value_trace_simulates_from [] trace.

Fixpoint check_copy_value_trace_fromb {value: Type}
    (value_eqb: value -> value -> bool)
    (locals: list (MemCell * value))
    (trace: copy_value_trace value) : bool :=
  match trace with
  | [] => true
  | (CopyIn _ local_cell, CopyValueIn source_value local_value)
      :: tail =>
      value_eqb source_value local_value &&
      check_copy_value_trace_fromb
        value_eqb
        (update_local_value local_cell local_value locals)
        tail
  | (LocalRead local_cell, CopyValueRead read_value) :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          value_eqb read_value current_value &&
          check_copy_value_trace_fromb value_eqb locals tail
      | None => false
      end
  | (LocalWrite local_cell, CopyValueWrite new_local_value) :: tail =>
      check_copy_value_trace_fromb
        value_eqb
        (update_local_value local_cell new_local_value locals)
        tail
  | (CopyOut local_cell _, CopyValueOut local_value target_value)
      :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          value_eqb local_value current_value &&
          value_eqb target_value current_value &&
          check_copy_value_trace_fromb value_eqb locals tail
      | None => false
      end
  | _ :: _ => false
  end.

Definition check_copy_value_traceb {value: Type}
    (value_eqb: value -> value -> bool)
    (trace: copy_value_trace value) : bool :=
  check_copy_value_trace_fromb value_eqb [] trace.

Fixpoint copy_value_trace_events {value: Type}
    (trace: copy_value_trace value) : list copy_event :=
  match trace with
  | [] => []
  | (copy_event', _) :: tail =>
      copy_event' :: copy_value_trace_events tail
  end.

Lemma copy_value_trace_pair_event_in_events :
  forall (value: Type)
         (trace: copy_value_trace value)
         copy_event' value_event,
    In (copy_event', value_event) trace ->
    In copy_event' (copy_value_trace_events trace).
Proof.
  intros value trace.
  induction trace as [|[head_event head_value] tail IH];
    intros copy_event' value_event Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + inversion Hhead; subst.
      left. reflexivity.
    + right.
      eapply IH.
      exact Htail.
Qed.

Lemma copy_value_trace_event_in_trace :
  forall (value: Type)
         (trace: copy_value_trace value)
         copy_event',
    In copy_event' (copy_value_trace_events trace) ->
    exists value_event,
      In (copy_event', value_event) trace.
Proof.
  intros value trace.
  induction trace as [|[head_event head_value] tail IH];
    intros copy_event' Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + subst copy_event'.
      exists head_value.
      simpl. left. reflexivity.
    + pose proof (IH copy_event' Htail)
        as (value_event & Hin_trace).
      exists value_event.
      simpl. right. exact Hin_trace.
Qed.

Fixpoint copy_value_trace_values {value: Type}
    (trace: copy_value_trace value) : list (copy_value_event value) :=
  match trace with
  | [] => []
  | (_, value_event) :: tail =>
      value_event :: copy_value_trace_values tail
  end.

Lemma copy_value_trace_value_in_trace :
  forall (value: Type)
         (trace: copy_value_trace value)
         value_event,
    In value_event (copy_value_trace_values trace) ->
    exists copy_event',
      In (copy_event', value_event) trace.
Proof.
  intros value trace.
  induction trace as [|[head_event head_value] tail IH];
    intros value_event Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + subst value_event.
      exists head_event.
      simpl. left. reflexivity.
    + pose proof (IH value_event Htail)
        as (copy_event' & Hin_trace).
      exists copy_event'.
      simpl. right. exact Hin_trace.
Qed.

Fixpoint copy_local_use_def_from
    (defined_locals: list MemCell)
    (trace: list copy_event) : Prop :=
  match trace with
  | [] => True
  | CopyIn _ local_cell :: tail =>
      copy_local_use_def_from (local_cell :: defined_locals) tail
  | LocalRead local_cell :: tail =>
      In local_cell defined_locals /\
      copy_local_use_def_from defined_locals tail
  | LocalWrite local_cell :: tail =>
      copy_local_use_def_from (local_cell :: defined_locals) tail
  | CopyOut local_cell _ :: tail =>
      In local_cell defined_locals /\
      copy_local_use_def_from defined_locals tail
  end.

Definition copy_local_use_def_trace (trace: list copy_event) : Prop :=
  copy_local_use_def_from [] trace.

Definition local_values_defined_by {value: Type}
    (locals: list (MemCell * value))
    (defined_locals: list MemCell) : Prop :=
  forall cell current_value,
    lookup_local_value cell locals = Some current_value ->
    In cell defined_locals.

Lemma local_values_defined_by_nil :
  forall (value: Type) defined_locals,
    @local_values_defined_by value [] defined_locals.
Proof.
  intros value defined_locals cell current_value Hlookup.
  simpl in Hlookup.
  discriminate.
Qed.

Lemma local_values_defined_by_update :
  forall (value: Type) locals defined_locals local_cell local_value,
    @local_values_defined_by value locals defined_locals ->
    @local_values_defined_by value
      (update_local_value local_cell local_value locals)
      (local_cell :: defined_locals).
Proof.
  induction locals as [|[cell old_value] tail IH];
    intros defined_locals local_cell local_value Hdefined
           query_cell query_value Hlookup; simpl in Hlookup.
  - destruct (mem_cell_strict_eqb query_cell local_cell) eqn:Heq.
    + apply mem_cell_strict_eqb_eq in Heq.
      subst. left. reflexivity.
    + discriminate.
  - destruct (mem_cell_strict_eqb local_cell cell) eqn:Hwrite.
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

Theorem copy_value_trace_local_use_def_from :
  forall (value: Type) trace locals defined_locals,
    copy_value_trace_simulates_from locals trace ->
    @local_values_defined_by value locals defined_locals ->
    copy_local_use_def_from
      defined_locals
      (copy_value_trace_events trace).
Proof.
  induction trace as [|[copy_event' value_event] tail IH];
    intros locals defined_locals Hsim Hdefined; simpl in Hsim.
  - exact I.
  - destruct copy_event' as [source_cell local_cell
                            | local_cell
                            | local_cell
                            | local_cell target_cell];
      destruct value_event as [source_value local_value
                              | read_value
                              | new_local_value
                              | out_local_value out_target_value];
      simpl in Hsim; try contradiction; simpl.
    + destruct Hsim as [_ Htail].
      eapply IH.
      * exact Htail.
      * apply local_values_defined_by_update.
        exact Hdefined.
    + destruct (lookup_local_value local_cell locals)
        as [current_value |] eqn:Hlookup; try contradiction.
      destruct Hsim as [_ Htail].
      split.
      * eapply Hdefined.
        exact Hlookup.
      * eapply IH; eauto.
    + eapply IH.
      * exact Hsim.
      * apply local_values_defined_by_update.
        exact Hdefined.
    + destruct (lookup_local_value local_cell locals)
        as [current_value |] eqn:Hlookup; try contradiction.
      destruct Hsim as [_ [_ Htail]].
      split.
      * eapply Hdefined.
        exact Hlookup.
      * eapply IH; eauto.
Qed.

Theorem copy_value_trace_local_use_def :
  forall (value: Type) (trace: copy_value_trace value),
    copy_value_trace_simulates trace ->
    copy_local_use_def_trace (copy_value_trace_events trace).
Proof.
  intros value trace Hsim.
  unfold copy_value_trace_simulates, copy_local_use_def_trace in *.
  eapply copy_value_trace_local_use_def_from.
  - exact Hsim.
  - apply local_values_defined_by_nil.
Qed.

Theorem copy_value_trace_simulates_from_event_matched :
  forall (value: Type)
         (trace: copy_value_trace value)
         locals copy_event' value_event,
    copy_value_trace_simulates_from locals trace ->
    In (copy_event', value_event) trace ->
    copy_value_event_kind_matches copy_event' value_event /\
    copy_value_event_values_match value_event.
Proof.
  intros value trace.
  induction trace as [|[head_event head_value] tail IH];
    intros locals copy_event' value_event Hsim Hin;
    simpl in Hin.
  - contradiction.
  - destruct Hin as [Hhead | Htail_in].
    + inversion Hhead; subst head_event head_value.
      destruct copy_event' as [source_cell local_cell
                              | local_cell
                              | local_cell
                              | local_cell target_cell];
        destruct value_event as [source_value local_value
                                | read_value
                                | new_local_value
                                | out_local_value out_target_value];
        simpl in Hsim; try contradiction.
      * destruct Hsim as [Hvalue _].
        split.
        -- simpl. exact I.
        -- simpl. exact Hvalue.
      * destruct
          (lookup_local_value local_cell locals)
          as [current_value |] eqn:Hlookup;
          try contradiction.
        destruct Hsim as [_ _].
        split; simpl; exact I.
      * split; simpl; exact I.
      * destruct
          (lookup_local_value local_cell locals)
          as [current_value |] eqn:Hlookup;
          try contradiction.
        destruct Hsim as [Hlocal [Htarget _]].
        split.
        -- simpl. exact I.
        -- simpl.
           transitivity current_value.
           ++ exact Hlocal.
           ++ symmetry. exact Htarget.
    + destruct head_event as [source_cell local_cell
                             | local_cell
                             | local_cell
                             | local_cell target_cell];
        destruct head_value as [source_value local_value
                               | read_value
                               | new_local_value
                               | out_local_value out_target_value];
        simpl in Hsim; try contradiction.
      * destruct Hsim as [_ Htail].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
      * destruct
          (lookup_local_value local_cell locals)
          as [current_value |] eqn:Hlookup;
          try contradiction.
        destruct Hsim as [_ Htail].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
      * eapply IH.
        -- exact Hsim.
        -- exact Htail_in.
      * destruct
          (lookup_local_value local_cell locals)
          as [current_value |] eqn:Hlookup;
          try contradiction.
        destruct Hsim as [_ [_ Htail]].
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

Lemma check_copy_value_trace_fromb_sound :
  forall trace locals,
    check_copy_value_trace_fromb
      value_eqb locals trace = true ->
    copy_value_trace_simulates_from locals trace.
Proof.
  induction trace as [|[copy_event' value_event] tail IH];
    intros locals Hcheck; simpl in Hcheck.
  - exact I.
  - destruct copy_event' as [source_cell local_cell
                            | local_cell
                            | local_cell
                            | local_cell target_cell];
      destruct value_event as [source_value local_value
                              | read_value
                              | new_local_value
                              | out_local_value out_target_value];
      simpl in Hcheck; try discriminate.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
    + cbn.
      destruct (lookup_local_value local_cell locals) as
        [current_value |] eqn:Hlookup; cbn in Hcheck; try discriminate.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
    + apply IH.
      exact Hcheck.
    + cbn.
      destruct (lookup_local_value local_cell locals) as
        [current_value |] eqn:Hlookup; cbn in Hcheck; try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hlocal & Htarget) & Htail).
      apply value_eqb_sound in Hlocal.
      apply value_eqb_sound in Htarget.
      split.
      * exact Hlocal.
      * split.
        -- exact Htarget.
        -- apply IH.
           exact Htail.
Qed.

Record copy_value_simulation_obligations
    (trace: copy_value_trace value) : Prop := {
  cvso_trace_simulates :
    copy_value_trace_simulates trace;
}.

Lemma check_copy_value_traceb_sound :
  forall trace,
    check_copy_value_traceb value_eqb trace = true ->
    copy_value_simulation_obligations trace.
Proof.
  unfold check_copy_value_traceb.
  intros trace Hcheck.
  constructor.
  apply check_copy_value_trace_fromb_sound.
  exact Hcheck.
Qed.

End Soundness.

Theorem copy_value_obligations_local_use_def :
  forall (value: Type) (trace: copy_value_trace value),
    copy_value_simulation_obligations value trace ->
    copy_local_use_def_trace (copy_value_trace_events trace).
Proof.
  intros value trace Hobligations.
  destruct Hobligations as [Hsimulates].
  apply copy_value_trace_local_use_def.
  exact Hsimulates.
Qed.

Theorem copy_value_obligations_events_local_use_def :
  forall (value: Type)
         (value_trace: copy_value_trace value)
         events,
    copy_value_simulation_obligations value value_trace ->
    copy_value_trace_events value_trace = events ->
    copy_local_use_def_trace events.
Proof.
  intros value value_trace events Hobligations Hevents.
  subst events.
  apply copy_value_obligations_local_use_def.
  exact Hobligations.
Qed.

Theorem copy_value_obligation_event_matched :
  forall (value: Type)
         (value_trace: copy_value_trace value)
         copy_event' value_event,
    copy_value_simulation_obligations value value_trace ->
    In (copy_event', value_event) value_trace ->
    copy_value_event_kind_matches copy_event' value_event /\
    copy_value_event_values_match value_event.
Proof.
  intros value value_trace copy_event' value_event
         Hobligations Hin.
  destruct Hobligations as [Hsimulates].
  unfold copy_value_trace_simulates in Hsimulates.
  eapply copy_value_trace_simulates_from_event_matched.
  - exact Hsimulates.
  - exact Hin.
Qed.

Theorem copy_value_obligation_event_entry :
  forall (value: Type)
         (value_trace: copy_value_trace value)
         copy_event',
    copy_value_simulation_obligations value value_trace ->
    In copy_event' (copy_value_trace_events value_trace) ->
    exists value_event,
      In (copy_event', value_event) value_trace /\
      copy_value_event_kind_matches copy_event' value_event /\
      copy_value_event_values_match value_event.
Proof.
  intros value value_trace copy_event' Hobligations Hin.
  pose proof
    (copy_value_trace_event_in_trace
       value value_trace copy_event' Hin)
    as (value_event & Hentry_in).
  pose proof
    (copy_value_obligation_event_matched
       value value_trace copy_event' value_event
       Hobligations Hentry_in)
    as [Hkind Hvalues].
  exists value_event.
  split.
  - exact Hentry_in.
  - split; assumption.
Qed.

Theorem copy_value_obligation_trace_event_entry :
  forall (value: Type)
         (value_trace: copy_value_trace value)
         events copy_event',
    copy_value_simulation_obligations value value_trace ->
    copy_value_trace_events value_trace = events ->
    In copy_event' events ->
    exists value_event,
      In (copy_event', value_event) value_trace /\
      copy_value_event_kind_matches copy_event' value_event /\
      copy_value_event_values_match value_event.
Proof.
  intros value value_trace events copy_event'
         Hobligations Hevents Hin.
  subst events.
  eapply copy_value_obligation_event_entry; eauto.
Qed.
