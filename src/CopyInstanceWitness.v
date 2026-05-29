Require Import Bool.
Require Import List.

Require Import CopyProtocolWitness.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** Instance-role alignment for copy-mediated helper events.

    [CopyProtocolWitness] checks an ordered copy/local/commit trace.
    [InstanceProjectionWitness] checks that projected target instances are
    internal or commit-role instances and that commits exact-cover source
    live-outs.  This file connects the two finite witnesses: a copy-out helper
    event must be a commit-role projected instance, while copy-in/local helper
    events must be internal. *)

Definition instance_role_eqb (left right: instance_role) : bool :=
  match left, right with
  | Internal, Internal => true
  | Commit, Commit => true
  | _, _ => false
  end.

Lemma instance_role_eqb_eq :
  forall left right,
    instance_role_eqb left right = true ->
    left = right.
Proof.
  intros [] []; simpl; auto; discriminate.
Qed.

Definition copy_event_projected_role (event: copy_event) : instance_role :=
  match event with
  | CopyIn _ _ => Internal
  | LocalRead _ => Internal
  | LocalWrite _ => Internal
  | CopyOut _ _ => Commit
  end.

Fixpoint copy_instance_trace_matches
    (targets: list projected_instance)
    (trace: list copy_event) : Prop :=
  match targets, trace with
  | [], [] => True
  | target :: targets_tail, event :: trace_tail =>
      projected_role target = copy_event_projected_role event /\
      copy_instance_trace_matches targets_tail trace_tail
  | _, _ => False
  end.

Fixpoint check_copy_instance_traceb
    (targets: list projected_instance)
    (trace: list copy_event) : bool :=
  match targets, trace with
  | [], [] => true
  | target :: targets_tail, event :: trace_tail =>
      instance_role_eqb
        (projected_role target)
        (copy_event_projected_role event) &&
      check_copy_instance_traceb targets_tail trace_tail
  | _, _ => false
  end.

Lemma check_copy_instance_traceb_sound :
  forall targets trace,
    check_copy_instance_traceb targets trace = true ->
    copy_instance_trace_matches targets trace.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace Hcheck; destruct trace as [|event trace_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hrole Htail].
    apply instance_role_eqb_eq in Hrole.
    split.
    + exact Hrole.
    + apply IH.
      exact Htail.
Qed.

Record copy_instance_trace_obligations
    (targets: list projected_instance)
    (trace: list copy_event) : Prop := {
  cito_trace_matches :
    copy_instance_trace_matches targets trace;
}.

Lemma check_copy_instance_traceb_obligations_sound :
  forall targets trace,
    check_copy_instance_traceb targets trace = true ->
    copy_instance_trace_obligations targets trace.
Proof.
  intros targets trace Hcheck.
  constructor.
  apply check_copy_instance_traceb_sound.
  exact Hcheck.
Qed.

Lemma copy_instance_trace_matches_length :
  forall targets trace,
    copy_instance_trace_matches targets trace ->
    length targets = length trace.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace Hmatch;
    destruct trace as [|event trace_tail];
    simpl in Hmatch |- *; try contradiction.
  - reflexivity.
  - destruct Hmatch as [_ Htail].
    simpl.
    f_equal.
    apply IH.
    exact Htail.
Qed.

Lemma copy_instance_trace_matches_target_event :
  forall targets trace target,
    copy_instance_trace_matches targets trace ->
    In target targets ->
    exists event,
      In event trace /\
      projected_role target = copy_event_projected_role event.
Proof.
  induction targets as [|head_target targets_tail IH];
    intros trace target Hmatch Hin;
    destruct trace as [|event trace_tail];
    simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [Hrole Htail].
  destruct Hin as [Heq | Hin_tail].
  - subst target.
    exists event.
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

Lemma copy_instance_trace_matches_event_target :
  forall targets trace event,
    copy_instance_trace_matches targets trace ->
    In event trace ->
    exists target,
      In target targets /\
      projected_role target = copy_event_projected_role event.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace event Hmatch Hin;
    destruct trace as [|head_event trace_tail];
    simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [Hrole Htail].
  destruct Hin as [Heq | Hin_tail].
  - subst event.
    exists target.
    split.
    + simpl. left. reflexivity.
    + exact Hrole.
  - pose proof
      (IH trace_tail event Htail Hin_tail)
      as (tail_target & Htarget_in & Hrole_tail).
    exists tail_target.
    split.
    + simpl. right. exact Htarget_in.
    + exact Hrole_tail.
Qed.

Theorem copy_instance_trace_obligations_length_match :
  forall targets trace,
    copy_instance_trace_obligations targets trace ->
    length targets = length trace.
Proof.
  intros targets trace Hobligations.
  destruct Hobligations as [Hmatch].
  eapply copy_instance_trace_matches_length; eauto.
Qed.

Theorem copy_instance_trace_obligation_target_event :
  forall targets trace target,
    copy_instance_trace_obligations targets trace ->
    In target targets ->
    exists event,
      In event trace /\
      projected_role target = copy_event_projected_role event.
Proof.
  intros targets trace target Hobligations Hin.
  destruct Hobligations as [Hmatch].
  eapply copy_instance_trace_matches_target_event; eauto.
Qed.

Theorem copy_instance_trace_obligation_event_target :
  forall targets trace event,
    copy_instance_trace_obligations targets trace ->
    In event trace ->
    exists target,
      In target targets /\
      projected_role target = copy_event_projected_role event.
Proof.
  intros targets trace event Hobligations Hin.
  destruct Hobligations as [Hmatch].
  eapply copy_instance_trace_matches_event_target; eauto.
Qed.
