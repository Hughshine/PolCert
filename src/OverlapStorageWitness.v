Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import InstanceProjectionWitness.
Require Import OverlapValueWitness.

Import ListNotations.

(** Finite write-storage witness for overlapped recomputation.

    [InstanceProjectionWitness] separates target instances into [Internal] and
    [Commit] roles.  For storage-aware overlap this role split must also be
    reflected in the cells written by the target program: internal halo/local
    recomputations should write tile-private cells, while commit instances
    write public commit cells.  This witness checks that finite role-to-cell
    bookkeeping fact. *)

Record overlap_write := {
  overlap_write_target : projected_instance;
  overlap_write_cell : MemCell;
}.

Definition overlap_write_role_cell_ok
    (private_cells commit_cells: list MemCell)
    (write: overlap_write) : Prop :=
  match projected_role (overlap_write_target write) with
  | Internal => In (overlap_write_cell write) private_cells
  | Commit => In (overlap_write_cell write) commit_cells
  end.

Definition check_overlap_write_role_cellb
    (private_cells commit_cells: list MemCell)
    (write: overlap_write) : bool :=
  match projected_role (overlap_write_target write) with
  | Internal => mem_cell_inb (overlap_write_cell write) private_cells
  | Commit => mem_cell_inb (overlap_write_cell write) commit_cells
  end.

Lemma check_overlap_write_role_cellb_sound :
  forall private_cells commit_cells write,
    check_overlap_write_role_cellb private_cells commit_cells write = true ->
    overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells [target cell] Hcheck.
  unfold check_overlap_write_role_cellb,
         overlap_write_role_cell_ok in Hcheck |- *.
  simpl in Hcheck |- *.
  destruct (projected_role target).
  - apply mem_cell_inb_sound. exact Hcheck.
  - apply mem_cell_inb_sound. exact Hcheck.
Qed.

Fixpoint overlap_write_entries_match
    (private_cells commit_cells: list MemCell)
    (targets: list projected_instance)
    (writes: list overlap_write) : Prop :=
  match targets, writes with
  | [], [] => True
  | target :: target_tail, write :: write_tail =>
      target = overlap_write_target write /\
      overlap_write_role_cell_ok private_cells commit_cells write /\
      overlap_write_entries_match
        private_cells commit_cells target_tail write_tail
  | _, _ => False
  end.

Fixpoint check_overlap_write_entriesb
    (private_cells commit_cells: list MemCell)
    (targets: list projected_instance)
    (writes: list overlap_write) : bool :=
  match targets, writes with
  | [], [] => true
  | target :: target_tail, write :: write_tail =>
      projected_instance_eqb target (overlap_write_target write) &&
      check_overlap_write_role_cellb private_cells commit_cells write &&
      check_overlap_write_entriesb
        private_cells commit_cells target_tail write_tail
  | _, _ => false
  end.

Lemma check_overlap_write_entriesb_sound :
  forall private_cells commit_cells targets writes,
    check_overlap_write_entriesb
      private_cells commit_cells targets writes = true ->
    overlap_write_entries_match
      private_cells commit_cells targets writes.
Proof.
  intros private_cells commit_cells targets.
  induction targets as [|target target_tail IH];
    intros writes Hcheck;
    destruct writes as [|write write_tail]; simpl in Hcheck; try discriminate.
  - exact I.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as ((Htarget & Hcell) & Htail).
    split.
    + apply projected_instance_eqb_eq.
      exact Htarget.
    + split.
      * apply check_overlap_write_role_cellb_sound.
        exact Hcell.
      * apply IH.
        exact Htail.
Qed.

Fixpoint overlap_commit_write_cells
    (writes: list overlap_write) : list MemCell :=
  match writes with
  | [] => []
  | write :: tail =>
      match projected_role (overlap_write_target write) with
      | Internal => overlap_commit_write_cells tail
      | Commit => overlap_write_cell write :: overlap_commit_write_cells tail
      end
  end.

Record overlap_storage_obligations
    (private_cells commit_cells: list MemCell)
    (targets: list projected_instance)
    (writes: list overlap_write) : Prop := {
  oso_entries_match :
    overlap_write_entries_match private_cells commit_cells targets writes;
  oso_commit_cells_nodup :
    NoDup (overlap_commit_write_cells writes);
}.

Definition check_overlap_storageb
    (private_cells commit_cells: list MemCell)
    (targets: list projected_instance)
    (writes: list overlap_write) : bool :=
  check_overlap_write_entriesb private_cells commit_cells targets writes &&
  mem_cells_nodupb (overlap_commit_write_cells writes).

Lemma check_overlap_storageb_sound :
  forall private_cells commit_cells targets writes,
    check_overlap_storageb private_cells commit_cells targets writes = true ->
    overlap_storage_obligations
      private_cells commit_cells targets writes.
Proof.
  intros private_cells commit_cells targets writes Hcheck.
  unfold check_overlap_storageb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hentries Hnodup].
  constructor.
  - apply check_overlap_write_entriesb_sound.
    exact Hentries.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
Qed.

Lemma overlap_write_entries_match_role_cell_ok :
  forall private_cells commit_cells targets writes write,
    overlap_write_entries_match
      private_cells commit_cells targets writes ->
    In write writes ->
    overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets.
  induction targets as [|target target_tail IH];
    intros writes write Hmatch Hin;
    destruct writes as [|head tail]; simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [_ [Hhead Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst. exact Hhead.
  - eapply IH; eauto.
Qed.

Lemma overlap_write_entries_match_length :
  forall private_cells commit_cells targets writes,
    overlap_write_entries_match
      private_cells commit_cells targets writes ->
    length targets = length writes.
Proof.
  intros private_cells commit_cells targets.
  induction targets as [|target target_tail IH];
    intros writes Hmatch;
    destruct writes as [|write write_tail];
    simpl in Hmatch |- *; try contradiction.
  - reflexivity.
  - destruct Hmatch as [_ [_ Htail]].
    simpl.
    f_equal.
    eapply IH; eauto.
Qed.

Lemma overlap_write_entries_match_target_write :
  forall private_cells commit_cells targets writes target,
    overlap_write_entries_match
      private_cells commit_cells targets writes ->
    In target targets ->
    exists write,
      In write writes /\
      target = overlap_write_target write /\
      overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets.
  induction targets as [|head_target target_tail IH];
    intros writes target Hmatch Hin;
    destruct writes as [|write write_tail];
    simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [Htarget [Hcell Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst target.
    exists write.
    split.
    + simpl. left. reflexivity.
    + split.
      * exact Htarget.
      * exact Hcell.
  - pose proof
      (IH write_tail target Htail Hin_tail)
      as (tail_write & Hwrite_in & Htarget_match & Hcell_ok).
    exists tail_write.
    split.
    + simpl. right. exact Hwrite_in.
    + split; assumption.
Qed.

Lemma overlap_write_entries_match_write_target :
  forall private_cells commit_cells targets writes write,
    overlap_write_entries_match
      private_cells commit_cells targets writes ->
    In write writes ->
    In (overlap_write_target write) targets /\
    overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets.
  induction targets as [|target target_tail IH];
    intros writes write Hmatch Hin;
    destruct writes as [|head_write write_tail];
    simpl in Hmatch, Hin; try contradiction.
  destruct Hmatch as [Htarget [Hcell Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst write.
    split.
    + simpl. left. exact Htarget.
    + exact Hcell.
  - pose proof (IH write_tail write Htail Hin_tail)
      as [Htarget_in Hcell_ok].
    split.
    + simpl. right. exact Htarget_in.
    + exact Hcell_ok.
Qed.

Theorem overlap_storage_entries_length_match :
  forall private_cells commit_cells targets writes,
    overlap_storage_obligations
      private_cells commit_cells targets writes ->
    length targets = length writes.
Proof.
  intros private_cells commit_cells targets writes Hobligations.
  destruct Hobligations as [Hmatch _].
  eapply overlap_write_entries_match_length; eauto.
Qed.

Theorem overlap_storage_target_write_entry :
  forall private_cells commit_cells targets writes target,
    overlap_storage_obligations
      private_cells commit_cells targets writes ->
    In target targets ->
    exists write,
      In write writes /\
      target = overlap_write_target write /\
      overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets writes target Hobligations Hin.
  destruct Hobligations as [Hmatch _].
  eapply overlap_write_entries_match_target_write; eauto.
Qed.

Theorem overlap_storage_write_target_in_targets :
  forall private_cells commit_cells targets writes write,
    overlap_storage_obligations
      private_cells commit_cells targets writes ->
    In write writes ->
    In (overlap_write_target write) targets /\
    overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets writes write Hobligations Hin.
  destruct Hobligations as [Hmatch _].
  eapply overlap_write_entries_match_write_target; eauto.
Qed.

Theorem overlap_storage_internal_write_private :
  forall private_cells commit_cells targets writes write,
    overlap_storage_obligations
      private_cells commit_cells targets writes ->
    In write writes ->
    projected_role (overlap_write_target write) = Internal ->
    In (overlap_write_cell write) private_cells.
Proof.
  intros private_cells commit_cells targets writes write
         Hobligations Hin Hrole.
  destruct Hobligations as [Hmatch _].
  pose proof
    (overlap_write_entries_match_role_cell_ok
       private_cells commit_cells targets writes write Hmatch Hin)
    as Hok.
  unfold overlap_write_role_cell_ok in Hok.
  rewrite Hrole in Hok.
  exact Hok.
Qed.

Theorem overlap_storage_commit_write_public :
  forall private_cells commit_cells targets writes write,
    overlap_storage_obligations
      private_cells commit_cells targets writes ->
    In write writes ->
    projected_role (overlap_write_target write) = Commit ->
    In (overlap_write_cell write) commit_cells.
Proof.
  intros private_cells commit_cells targets writes write
         Hobligations Hin Hrole.
  destruct Hobligations as [Hmatch _].
  pose proof
    (overlap_write_entries_match_role_cell_ok
       private_cells commit_cells targets writes write Hmatch Hin)
    as Hok.
  unfold overlap_write_role_cell_ok in Hok.
  rewrite Hrole in Hok.
  exact Hok.
Qed.

Theorem overlap_storage_commit_cells_nodup :
  forall private_cells commit_cells targets writes,
    overlap_storage_obligations
      private_cells commit_cells targets writes ->
    NoDup (overlap_commit_write_cells writes).
Proof.
  intros private_cells commit_cells targets writes Hobligations.
  destruct Hobligations as [_ Hnodup].
  exact Hnodup.
Qed.

Theorem check_overlap_storageb_entries_length_match :
  forall private_cells commit_cells targets writes,
    check_overlap_storageb
      private_cells commit_cells targets writes = true ->
    length targets = length writes.
Proof.
  intros private_cells commit_cells targets writes Hcheck.
  eapply overlap_storage_entries_length_match.
  apply check_overlap_storageb_sound.
  exact Hcheck.
Qed.

Theorem check_overlap_storageb_target_write_entry :
  forall private_cells commit_cells targets writes target,
    check_overlap_storageb
      private_cells commit_cells targets writes = true ->
    In target targets ->
    exists write,
      In write writes /\
      target = overlap_write_target write /\
      overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets writes target Hcheck Hin.
  eapply overlap_storage_target_write_entry; eauto.
  apply check_overlap_storageb_sound.
  exact Hcheck.
Qed.

Theorem check_overlap_storageb_write_target_in_targets :
  forall private_cells commit_cells targets writes write,
    check_overlap_storageb
      private_cells commit_cells targets writes = true ->
    In write writes ->
    In (overlap_write_target write) targets /\
    overlap_write_role_cell_ok private_cells commit_cells write.
Proof.
  intros private_cells commit_cells targets writes write Hcheck Hin.
  eapply overlap_storage_write_target_in_targets; eauto.
  apply check_overlap_storageb_sound.
  exact Hcheck.
Qed.

Theorem check_overlap_storageb_internal_write_private :
  forall private_cells commit_cells targets writes write,
    check_overlap_storageb
      private_cells commit_cells targets writes = true ->
    In write writes ->
    projected_role (overlap_write_target write) = Internal ->
    In (overlap_write_cell write) private_cells.
Proof.
  intros private_cells commit_cells targets writes write
         Hcheck Hin Hrole.
  eapply overlap_storage_internal_write_private; eauto.
  apply check_overlap_storageb_sound.
  exact Hcheck.
Qed.

Theorem check_overlap_storageb_commit_write_public :
  forall private_cells commit_cells targets writes write,
    check_overlap_storageb
      private_cells commit_cells targets writes = true ->
    In write writes ->
    projected_role (overlap_write_target write) = Commit ->
    In (overlap_write_cell write) commit_cells.
Proof.
  intros private_cells commit_cells targets writes write
         Hcheck Hin Hrole.
  eapply overlap_storage_commit_write_public; eauto.
  apply check_overlap_storageb_sound.
  exact Hcheck.
Qed.

Theorem check_overlap_storageb_commit_cells_nodup :
  forall private_cells commit_cells targets writes,
    check_overlap_storageb
      private_cells commit_cells targets writes = true ->
    NoDup (overlap_commit_write_cells writes).
Proof.
  intros private_cells commit_cells targets writes Hcheck.
  eapply overlap_storage_commit_cells_nodup.
  apply check_overlap_storageb_sound.
  exact Hcheck.
Qed.
