Require Import Bool.
Require Import List.

Require Import ScalarPromotionWitness.

Import ListNotations.

(** Value-flow witness for scalar promotion.

    [ScalarPromotionWitness] checks the storage protocol: load before use, no
    bypassing write to the promoted cell, and live-out store-back.  This module
    adds a small value-flow layer over the same event stream.  It does not know
    about C expressions; instead, it checks that the value attached to each
    scalar event is consistent with the current promoted scalar value.  A later
    instruction-level proof can discharge the remaining obligation by producing
    this value trace from expression semantics. *)

Inductive scalar_promotion_value_event (value: Type) :=
| PromotionValueLoad (source_value scalar_value: value)
| PromotionValueRead (read_value: value)
| PromotionValueWrite (new_scalar_value: value)
| PromotionValueStore (scalar_value source_value: value)
| PromotionValueGlobalWrite.

Arguments PromotionValueLoad {value} _ _.
Arguments PromotionValueRead {value} _.
Arguments PromotionValueWrite {value} _.
Arguments PromotionValueStore {value} _ _.
Arguments PromotionValueGlobalWrite {value}.

Definition scalar_promotion_value_trace (value: Type) :=
  list (scalar_promotion_event * scalar_promotion_value_event value).

Definition scalar_promotion_value_event_kind_matches {value: Type}
    (event: scalar_promotion_event)
    (value_event: scalar_promotion_value_event value) : Prop :=
  match event, value_event with
  | PromotionLoad _ _, PromotionValueLoad _ _ => True
  | PromotionScalarRead _, PromotionValueRead _ => True
  | PromotionScalarWrite _, PromotionValueWrite _ => True
  | PromotionStore _ _, PromotionValueStore _ _ => True
  | PromotionGlobalWrite _, PromotionValueGlobalWrite => True
  | _, _ => False
  end.

Definition scalar_promotion_value_event_values_match {value: Type}
    (value_event: scalar_promotion_value_event value) : Prop :=
  match value_event with
  | PromotionValueLoad source_value scalar_value =>
      source_value = scalar_value
  | PromotionValueRead _ => True
  | PromotionValueWrite _ => True
  | PromotionValueStore scalar_value source_value =>
      scalar_value = source_value
  | PromotionValueGlobalWrite => True
  end.

Fixpoint scalar_promotion_value_trace_events {value: Type}
    (trace: scalar_promotion_value_trace value)
    : list scalar_promotion_event :=
  match trace with
  | [] => []
  | (storage_event, _) :: tail =>
      storage_event :: scalar_promotion_value_trace_events tail
  end.

Lemma scalar_promotion_value_trace_pair_event_in_events :
  forall (value: Type)
         (trace: scalar_promotion_value_trace value)
         storage_event value_event,
    In (storage_event, value_event) trace ->
    In storage_event (scalar_promotion_value_trace_events trace).
Proof.
  intros value trace.
  induction trace as [|[head_event head_value] tail IH];
    intros storage_event value_event Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + inversion Hhead; subst.
      left. reflexivity.
    + right.
      eapply IH.
      exact Htail.
Qed.

Fixpoint scalar_promotion_value_trace_values {value: Type}
    (trace: scalar_promotion_value_trace value)
    : list (scalar_promotion_value_event value) :=
  match trace with
  | [] => []
  | (_, value_event) :: tail =>
      value_event :: scalar_promotion_value_trace_values tail
  end.

Fixpoint scalar_value_trace_simulates_from {value: Type}
    (current_scalar: option value)
    (trace: scalar_promotion_value_trace value) : Prop :=
  match trace with
  | [] => True
  | (PromotionLoad _ _, PromotionValueLoad source_value scalar_value)
      :: tail =>
      source_value = scalar_value /\
      scalar_value_trace_simulates_from
        (Some scalar_value) tail
  | (PromotionScalarRead _, PromotionValueRead read_value) :: tail =>
      match current_scalar with
      | Some scalar_value =>
          read_value = scalar_value /\
          scalar_value_trace_simulates_from current_scalar tail
      | None => False
      end
  | (PromotionScalarWrite _, PromotionValueWrite new_scalar_value)
      :: tail =>
      match current_scalar with
      | Some _ =>
          scalar_value_trace_simulates_from
            (Some new_scalar_value) tail
      | None => False
      end
  | (PromotionStore _ _, PromotionValueStore scalar_value source_value)
      :: tail =>
      match current_scalar with
      | Some current_value =>
          scalar_value = current_value /\
          source_value = current_value /\
          scalar_value_trace_simulates_from current_scalar tail
      | None => False
      end
  | (PromotionGlobalWrite _, PromotionValueGlobalWrite) :: tail =>
      scalar_value_trace_simulates_from current_scalar tail
  | _ :: _ => False
  end.

Definition scalar_value_trace_simulates {value: Type}
    (trace: scalar_promotion_value_trace value) : Prop :=
  scalar_value_trace_simulates_from None trace.

Fixpoint check_scalar_value_trace_fromb {value: Type}
    (value_eqb: value -> value -> bool)
    (current_scalar: option value)
    (trace: scalar_promotion_value_trace value) : bool :=
  match trace with
  | [] => true
  | (PromotionLoad _ _, PromotionValueLoad source_value scalar_value)
      :: tail =>
      value_eqb source_value scalar_value &&
      check_scalar_value_trace_fromb
        value_eqb (Some scalar_value) tail
  | (PromotionScalarRead _, PromotionValueRead read_value) :: tail =>
      match current_scalar with
      | Some scalar_value =>
          value_eqb read_value scalar_value &&
          check_scalar_value_trace_fromb
            value_eqb current_scalar tail
      | None => false
      end
  | (PromotionScalarWrite _, PromotionValueWrite new_scalar_value)
      :: tail =>
      match current_scalar with
      | Some _ =>
          check_scalar_value_trace_fromb
            value_eqb (Some new_scalar_value) tail
      | None => false
      end
  | (PromotionStore _ _, PromotionValueStore scalar_value source_value)
      :: tail =>
      match current_scalar with
      | Some current_value =>
          value_eqb scalar_value current_value &&
          value_eqb source_value current_value &&
          check_scalar_value_trace_fromb
            value_eqb current_scalar tail
      | None => false
      end
  | (PromotionGlobalWrite _, PromotionValueGlobalWrite) :: tail =>
      check_scalar_value_trace_fromb value_eqb current_scalar tail
  | _ :: _ => false
  end.

Definition check_scalar_value_traceb {value: Type}
    (value_eqb: value -> value -> bool)
    (trace: scalar_promotion_value_trace value) : bool :=
  check_scalar_value_trace_fromb value_eqb None trace.

Fixpoint scalar_value_use_def_from
    (loaded: bool)
    (trace: list scalar_promotion_event) : Prop :=
  match trace with
  | [] => True
  | PromotionLoad _ _ :: tail =>
      scalar_value_use_def_from true tail
  | PromotionScalarRead _ :: tail =>
      loaded = true /\
      scalar_value_use_def_from loaded tail
  | PromotionScalarWrite _ :: tail =>
      loaded = true /\
      scalar_value_use_def_from loaded tail
  | PromotionStore _ _ :: tail =>
      loaded = true /\
      scalar_value_use_def_from loaded tail
  | PromotionGlobalWrite _ :: tail =>
      scalar_value_use_def_from loaded tail
  end.

Definition scalar_value_use_def_trace
    (trace: list scalar_promotion_event) : Prop :=
  scalar_value_use_def_from false trace.

Definition scalar_current_loaded {value: Type}
    (current_scalar: option value)
    (loaded: bool) : Prop :=
  match current_scalar with
  | Some _ => loaded = true
  | None => True
  end.

Theorem scalar_value_trace_use_def_from :
  forall (value: Type)
         (trace: scalar_promotion_value_trace value)
         current_scalar loaded,
    scalar_value_trace_simulates_from current_scalar trace ->
    scalar_current_loaded current_scalar loaded ->
    scalar_value_use_def_from
      loaded
      (scalar_promotion_value_trace_events trace).
Proof.
  induction trace as [|[storage_event value_event] tail IH];
    intros current_scalar loaded Hsim Hloaded; simpl in Hsim.
  - exact I.
  - destruct storage_event as [source_cell scalar_cell
                              | scalar_cell
                              | scalar_cell
                              | scalar_cell source_cell
                              | cell];
      destruct value_event as [source_value scalar_value
                              | read_value
                              | new_scalar_value
                              | store_scalar_value store_source_value
                              | ];
      simpl in Hsim; try contradiction; simpl.
    + destruct Hsim as [_ Htail].
      eapply IH.
      * exact Htail.
      * simpl. reflexivity.
    + destruct current_scalar as [current_value |]; try contradiction.
      destruct Hsim as [_ Htail].
      split.
      * exact Hloaded.
      * eapply IH; eauto.
    + destruct current_scalar as [current_value |]; try contradiction.
      split.
      * exact Hloaded.
      * eapply IH.
        -- exact Hsim.
        -- exact Hloaded.
    + destruct current_scalar as [current_value |]; try contradiction.
      destruct Hsim as [_ [_ Htail]].
      split.
      * exact Hloaded.
      * eapply IH; eauto.
    + eapply IH; eauto.
Qed.

Theorem scalar_value_trace_use_def :
  forall (value: Type) (trace: scalar_promotion_value_trace value),
    scalar_value_trace_simulates trace ->
    scalar_value_use_def_trace
      (scalar_promotion_value_trace_events trace).
Proof.
  intros value trace Hsim.
  unfold scalar_value_trace_simulates, scalar_value_use_def_trace in *.
  eapply scalar_value_trace_use_def_from.
  - exact Hsim.
  - exact I.
Qed.

Theorem scalar_value_trace_simulates_from_event_matched :
  forall (value: Type)
         (trace: scalar_promotion_value_trace value)
         current_scalar storage_event value_event,
    scalar_value_trace_simulates_from current_scalar trace ->
    In (storage_event, value_event) trace ->
    scalar_promotion_value_event_kind_matches storage_event value_event /\
    scalar_promotion_value_event_values_match value_event.
Proof.
  intros value trace.
  induction trace as [|[head_event head_value] tail IH];
    intros current_scalar storage_event value_event Hsim Hin;
    simpl in Hin.
  - contradiction.
  - destruct Hin as [Hhead | Htail_in].
    + inversion Hhead; subst head_event head_value.
      destruct storage_event as [source_cell scalar_cell
                                | scalar_cell
                                | scalar_cell
                                | scalar_cell source_cell
                                | cell];
        destruct value_event as [source_value scalar_value
                                | read_value
                                | new_scalar_value
                                | store_scalar_value store_source_value
                                | ];
        simpl in Hsim; try contradiction.
      * destruct Hsim as [Hvalue _].
        split.
        -- simpl. exact I.
        -- simpl. exact Hvalue.
      * destruct current_scalar as [current_value |]; try contradiction.
        destruct Hsim as [_ _].
        split; simpl; exact I.
      * destruct current_scalar as [current_value |]; try contradiction.
        split; simpl; exact I.
      * destruct current_scalar as [current_value |]; try contradiction.
        destruct Hsim as [Hscalar [Hsource _]].
        split.
        -- simpl. exact I.
        -- simpl.
           transitivity current_value.
           ++ exact Hscalar.
           ++ symmetry. exact Hsource.
      * split; simpl; exact I.
    + destruct head_event as [source_cell scalar_cell
                             | scalar_cell
                             | scalar_cell
                             | scalar_cell source_cell
                             | cell];
        destruct head_value as [source_value scalar_value
                               | read_value
                               | new_scalar_value
                               | store_scalar_value store_source_value
                               | ];
        simpl in Hsim; try contradiction.
      * destruct Hsim as [_ Htail].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
      * destruct current_scalar as [current_value |]; try contradiction.
        destruct Hsim as [_ Htail].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
      * destruct current_scalar as [current_value |]; try contradiction.
        eapply IH.
        -- exact Hsim.
        -- exact Htail_in.
      * destruct current_scalar as [current_value |]; try contradiction.
        destruct Hsim as [_ [_ Htail]].
        eapply IH.
        -- exact Htail.
        -- exact Htail_in.
      * eapply IH.
        -- exact Hsim.
        -- exact Htail_in.
Qed.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_scalar_value_trace_fromb_sound :
  forall trace current_scalar,
    check_scalar_value_trace_fromb
      value_eqb current_scalar trace = true ->
    scalar_value_trace_simulates_from current_scalar trace.
Proof.
  induction trace as [|[storage_event value_event] tail IH];
    intros current_scalar Hcheck; simpl in Hcheck.
  - exact I.
  - destruct storage_event as [source_cell scalar_cell
                              | scalar_cell
                              | scalar_cell
                              | scalar_cell source_cell
                              | cell];
      destruct value_event as [source_value scalar_value
                              | read_value
                              | new_scalar_value
                              | store_scalar_value store_source_value
                              | ];
      simpl in Hcheck; try discriminate.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
    + destruct current_scalar as [current_value |]; try discriminate.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
    + destruct current_scalar as [current_value |]; try discriminate.
      apply IH.
      exact Hcheck.
    + destruct current_scalar as [current_value |]; try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hscalar & Hsource) & Htail).
      apply value_eqb_sound in Hscalar.
      apply value_eqb_sound in Hsource.
      split.
      * exact Hscalar.
      * split.
        -- exact Hsource.
        -- apply IH.
           exact Htail.
    + apply IH.
      exact Hcheck.
Qed.

Record scalar_value_simulation_obligations
    (trace: scalar_promotion_value_trace value) : Prop := {
  svso_trace_simulates :
    scalar_value_trace_simulates trace;
}.

Lemma check_scalar_value_traceb_sound :
  forall trace,
    check_scalar_value_traceb value_eqb trace = true ->
    scalar_value_simulation_obligations trace.
Proof.
  unfold check_scalar_value_traceb.
  intros trace Hcheck.
  constructor.
  apply check_scalar_value_trace_fromb_sound.
  exact Hcheck.
Qed.

End Soundness.

Theorem scalar_value_obligations_use_def :
  forall (value: Type) (trace: scalar_promotion_value_trace value),
    scalar_value_simulation_obligations value trace ->
    scalar_value_use_def_trace
      (scalar_promotion_value_trace_events trace).
Proof.
  intros value trace Hobligations.
  destruct Hobligations as [Hsimulates].
  apply scalar_value_trace_use_def.
  exact Hsimulates.
Qed.

Theorem scalar_value_obligations_events_use_def :
  forall (value: Type)
         (value_trace: scalar_promotion_value_trace value)
         events,
    scalar_value_simulation_obligations value value_trace ->
    scalar_promotion_value_trace_events value_trace = events ->
    scalar_value_use_def_trace events.
Proof.
  intros value value_trace events Hobligations Hevents.
  subst events.
  apply scalar_value_obligations_use_def.
  exact Hobligations.
Qed.

Theorem scalar_value_obligation_event_matched :
  forall (value: Type)
         (value_trace: scalar_promotion_value_trace value)
         storage_event value_event,
    scalar_value_simulation_obligations value value_trace ->
    In (storage_event, value_event) value_trace ->
    scalar_promotion_value_event_kind_matches storage_event value_event /\
    scalar_promotion_value_event_values_match value_event.
Proof.
  intros value value_trace storage_event value_event
         Hobligations Hin.
  destruct Hobligations as [Hsimulates].
  unfold scalar_value_trace_simulates in Hsimulates.
  eapply scalar_value_trace_simulates_from_event_matched.
  - exact Hsimulates.
  - exact Hin.
Qed.

Theorem scalar_value_obligation_load_values_equal :
  forall (value: Type)
         (value_trace: scalar_promotion_value_trace value)
         source_cell scalar_cell source_value scalar_value,
    scalar_value_simulation_obligations value value_trace ->
    In (PromotionLoad source_cell scalar_cell,
        PromotionValueLoad source_value scalar_value) value_trace ->
    source_value = scalar_value.
Proof.
  intros value value_trace source_cell scalar_cell source_value scalar_value
         Hobligations Hin.
  pose proof
    (scalar_value_obligation_event_matched
       value value_trace
       (PromotionLoad source_cell scalar_cell)
       (PromotionValueLoad source_value scalar_value)
       Hobligations Hin)
    as [_ Hvalues].
  simpl in Hvalues.
  exact Hvalues.
Qed.

Theorem scalar_value_obligation_store_values_equal :
  forall (value: Type)
         (value_trace: scalar_promotion_value_trace value)
         scalar_cell source_cell scalar_value source_value,
    scalar_value_simulation_obligations value value_trace ->
    In (PromotionStore scalar_cell source_cell,
        PromotionValueStore scalar_value source_value) value_trace ->
    scalar_value = source_value.
Proof.
  intros value value_trace scalar_cell source_cell scalar_value source_value
         Hobligations Hin.
  pose proof
    (scalar_value_obligation_event_matched
       value value_trace
       (PromotionStore scalar_cell source_cell)
       (PromotionValueStore scalar_value source_value)
       Hobligations Hin)
    as [_ Hvalues].
  simpl in Hvalues.
  exact Hvalues.
Qed.
