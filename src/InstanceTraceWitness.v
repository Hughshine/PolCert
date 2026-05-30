Require Import Bool.
Require Import List.

Require Import InstanceProjectionWitness.

Import ListNotations.

(** Generic finite witness for target-instance trace roles.

    [InstanceProjectionWitness] states which target instances are internal
    helper computations and which ones commit source-observable results.  This
    module factors out the reusable trace alignment pattern: a concrete event
    trace is accepted when each projected target instance has the role expected
    by the event at the same position. *)

Definition trace_instance_role_eqb
    (left right: instance_role) : bool :=
  match left, right with
  | Internal, Internal => true
  | Commit, Commit => true
  | _, _ => false
  end.

Lemma trace_instance_role_eqb_eq :
  forall left right,
    trace_instance_role_eqb left right = true ->
    left = right.
Proof.
  intros [] []; simpl; auto; discriminate.
Qed.

Section EventTrace.

Variable event: Type.
Variable event_projected_role: event -> instance_role.

Fixpoint instance_trace_matches
    (targets: list projected_instance)
    (trace: list event) : Prop :=
  match targets, trace with
  | [], [] => True
  | target :: targets_tail, event_head :: trace_tail =>
      projected_role target = event_projected_role event_head /\
      instance_trace_matches targets_tail trace_tail
  | _, _ => False
  end.

Fixpoint check_instance_traceb
    (targets: list projected_instance)
    (trace: list event) : bool :=
  match targets, trace with
  | [], [] => true
  | target :: targets_tail, event_head :: trace_tail =>
      trace_instance_role_eqb
        (projected_role target)
        (event_projected_role event_head) &&
      check_instance_traceb targets_tail trace_tail
  | _, _ => false
  end.

Lemma check_instance_traceb_sound :
  forall targets trace,
    check_instance_traceb targets trace = true ->
    instance_trace_matches targets trace.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace Hcheck; destruct trace as [|event_head trace_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hrole Htail].
    apply trace_instance_role_eqb_eq in Hrole.
    split.
    + exact Hrole.
    + apply IH.
      exact Htail.
Qed.

Record instance_trace_obligations
    (targets: list projected_instance)
    (trace: list event) : Prop := {
  ito_trace_matches :
    instance_trace_matches targets trace;
}.

Theorem check_instance_traceb_obligations_sound :
  forall targets trace,
    check_instance_traceb targets trace = true ->
    instance_trace_obligations targets trace.
Proof.
  intros targets trace Hcheck.
  constructor.
  apply check_instance_traceb_sound.
  exact Hcheck.
Qed.

Lemma instance_trace_matches_length :
  forall targets trace,
    instance_trace_matches targets trace ->
    length targets = length trace.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace Hmatch;
    destruct trace as [|event_head trace_tail];
    simpl in Hmatch |- *; try contradiction.
  - reflexivity.
  - destruct Hmatch as [_ Htail].
    simpl.
    f_equal.
    apply IH.
    exact Htail.
Qed.

Lemma instance_trace_matches_target_event :
  forall targets trace target,
    instance_trace_matches targets trace ->
    In target targets ->
    exists event_head,
      In event_head trace /\
      projected_role target = event_projected_role event_head.
Proof.
  induction targets as [|head_target targets_tail IH];
    intros trace target Hmatch Hin;
    destruct trace as [|event_head trace_tail];
    simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [Hrole Htail].
  destruct Hin as [Heq | Hin_tail].
  - subst target.
    exists event_head.
    split.
    + simpl. left. reflexivity.
    + exact Hrole.
  - pose proof
      (IH trace_tail target Htail Hin_tail)
      as (tail_event & Hevent_in & Hrole_tail).
    exists tail_event.
    split.
    + simpl. right. exact Hevent_in.
    + exact Hrole_tail.
Qed.

Lemma instance_trace_matches_event_target :
  forall targets trace event_head,
    instance_trace_matches targets trace ->
    In event_head trace ->
    exists target,
      In target targets /\
      projected_role target = event_projected_role event_head.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace event_head Hmatch Hin;
    destruct trace as [|head_event trace_tail];
    simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [Hrole Htail].
  destruct Hin as [Heq | Hin_tail].
  - subst event_head.
    exists target.
    split.
    + simpl. left. reflexivity.
    + exact Hrole.
  - pose proof
      (IH trace_tail event_head Htail Hin_tail)
      as (tail_target & Htarget_in & Hrole_tail).
    exists tail_target.
    split.
    + simpl. right. exact Htarget_in.
    + exact Hrole_tail.
Qed.

Theorem instance_trace_obligations_length_match :
  forall targets trace,
    instance_trace_obligations targets trace ->
    length targets = length trace.
Proof.
  intros targets trace Hobligations.
  destruct Hobligations as [Hmatch].
  eapply instance_trace_matches_length; eauto.
Qed.

Theorem instance_trace_obligation_target_event :
  forall targets trace target,
    instance_trace_obligations targets trace ->
    In target targets ->
    exists event_head,
      In event_head trace /\
      projected_role target = event_projected_role event_head.
Proof.
  intros targets trace target Hobligations Hin.
  destruct Hobligations as [Hmatch].
  eapply instance_trace_matches_target_event; eauto.
Qed.

Theorem instance_trace_obligation_event_target :
  forall targets trace event_head,
    instance_trace_obligations targets trace ->
    In event_head trace ->
    exists target,
      In target targets /\
      projected_role target = event_projected_role event_head.
Proof.
  intros targets trace event_head Hobligations Hin.
  destruct Hobligations as [Hmatch].
  eapply instance_trace_matches_event_target; eauto.
Qed.

Theorem check_instance_traceb_length_match :
  forall targets trace,
    check_instance_traceb targets trace = true ->
    length targets = length trace.
Proof.
  intros targets trace Hcheck.
  eapply instance_trace_obligations_length_match.
  apply check_instance_traceb_obligations_sound.
  exact Hcheck.
Qed.

Theorem check_instance_traceb_target_event :
  forall targets trace target,
    check_instance_traceb targets trace = true ->
    In target targets ->
    exists event_head,
      In event_head trace /\
      projected_role target = event_projected_role event_head.
Proof.
  intros targets trace target Hcheck Hin.
  eapply instance_trace_obligation_target_event; eauto.
  apply check_instance_traceb_obligations_sound.
  exact Hcheck.
Qed.

Theorem check_instance_traceb_event_target :
  forall targets trace event_head,
    check_instance_traceb targets trace = true ->
    In event_head trace ->
    exists target,
      In target targets /\
      projected_role target = event_projected_role event_head.
Proof.
  intros targets trace event_head Hcheck Hin.
  eapply instance_trace_obligation_event_target; eauto.
  apply check_instance_traceb_obligations_sound.
  exact Hcheck.
Qed.

End EventTrace.
