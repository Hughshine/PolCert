Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import CopyProtocolWitness.
Require Import ReuseConflictWitness.

Import ListNotations.

(** Exact copy-out commit cover for copy-mediated local storage.

    [CopyProtocolWitness] checks that every copy-out reads a defined local cell
    and that committed public targets are duplicate-free.  For update-style
    scratchpad transformations, the validator also needs to know that the
    copy-out targets exactly cover the source-observable outputs.  This witness
    checks that finite boundary set. *)

Definition copy_commit_exact_cover
    (expected_targets: list MemCell)
    (trace: list copy_event) : Prop :=
  let committed_targets := copy_protocol_committed_targets trace in
  NoDup committed_targets /\
  (forall expected_target,
     In expected_target expected_targets <->
     In expected_target committed_targets).

Definition check_copy_commit_coverb
    (expected_targets: list MemCell)
    (trace: list copy_event) : bool :=
  let committed_targets := copy_protocol_committed_targets trace in
  mem_cells_nodupb committed_targets &&
  mem_cells_subsetb expected_targets committed_targets &&
  mem_cells_subsetb committed_targets expected_targets.

Lemma check_copy_commit_coverb_sound :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    copy_commit_exact_cover expected_targets trace.
Proof.
  intros expected_targets trace Hcheck.
  unfold check_copy_commit_coverb in Hcheck.
  unfold copy_commit_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hexpected_subset) & Hcommitted_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - intro expected_target_cell.
    split.
    + intro Hin_expected.
      eapply mem_cells_subsetb_sound; eauto.
    + intro Hin_committed.
      eapply mem_cells_subsetb_sound; eauto.
Qed.

Record copy_commit_obligations
    (expected_targets: list MemCell)
    (trace: list copy_event) : Prop := {
  cco_exact_cover :
    copy_commit_exact_cover expected_targets trace;
}.

Lemma check_copy_commit_coverb_obligations_sound :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    copy_commit_obligations expected_targets trace.
Proof.
  intros expected_targets trace Hcheck.
  constructor.
  apply check_copy_commit_coverb_sound.
  exact Hcheck.
Qed.

Fixpoint copy_commit_identity_mapping
    (cells: list MemCell) : reuse_mapping :=
  match cells with
  | [] => []
  | cell :: tail =>
      (cell, cell) :: copy_commit_identity_mapping tail
  end.

Lemma copy_commit_identity_lookup :
  forall cells cell,
    In cell cells ->
    reuse_lookup cell (copy_commit_identity_mapping cells) = Some cell.
Proof.
  induction cells as [|head tail IH]; intros cell Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      rewrite mem_cell_strict_eq_eqb with (c2 := cell).
      * reflexivity.
      * reflexivity.
    + destruct (mem_cell_strict_eqb cell head) eqn:Heq_head.
      * apply mem_cell_strict_eqb_eq in Heq_head.
        subst.
        reflexivity.
      * apply IH.
        exact Hin_tail.
Qed.

Theorem copy_commit_committed_targets_nodup :
  forall expected_targets trace,
    copy_commit_obligations expected_targets trace ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  intros expected_targets trace Hobligations.
  destruct Hobligations as [Hcover].
  destruct Hcover as [Hnodup _].
  exact Hnodup.
Qed.

Theorem copy_commit_committed_targets_covered :
  forall expected_targets trace,
    copy_commit_obligations expected_targets trace ->
    reuse_mapping_covers_sources
      (copy_commit_identity_mapping
         (copy_protocol_committed_targets trace))
      (copy_protocol_committed_targets trace).
Proof.
  unfold reuse_mapping_covers_sources, reuse_source_covered.
  intros expected_targets trace _ source_cell Hin_source.
  exists source_cell.
  unfold reuse_cell_relation.
  apply copy_commit_identity_lookup.
  exact Hin_source.
Qed.

Theorem copy_commit_boundary_obligations :
  forall expected_targets trace,
    copy_commit_obligations expected_targets trace ->
    reuse_boundary_obligations
      (copy_commit_identity_mapping
         (copy_protocol_committed_targets trace))
      (copy_protocol_committed_targets trace).
Proof.
  intros expected_targets trace Hobligations.
  constructor.
  - eapply copy_commit_committed_targets_nodup; eauto.
  - eapply copy_commit_committed_targets_covered; eauto.
Qed.

Theorem check_copy_commit_coverb_committed_targets_nodup :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  intros expected_targets trace Hcheck.
  eapply copy_commit_committed_targets_nodup.
  apply check_copy_commit_coverb_obligations_sound.
  exact Hcheck.
Qed.

Theorem check_copy_commit_coverb_committed_targets_covered :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    reuse_mapping_covers_sources
      (copy_commit_identity_mapping
         (copy_protocol_committed_targets trace))
      (copy_protocol_committed_targets trace).
Proof.
  intros expected_targets trace Hcheck.
  eapply copy_commit_committed_targets_covered.
  apply check_copy_commit_coverb_obligations_sound.
  exact Hcheck.
Qed.

Theorem check_copy_commit_coverb_boundary_obligations :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    reuse_boundary_obligations
      (copy_commit_identity_mapping
         (copy_protocol_committed_targets trace))
      (copy_protocol_committed_targets trace).
Proof.
  intros expected_targets trace Hcheck.
  eapply copy_commit_boundary_obligations.
  apply check_copy_commit_coverb_obligations_sound.
  exact Hcheck.
Qed.
