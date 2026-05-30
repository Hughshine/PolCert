Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Boundary value witness for contextual frame preservation.

    [FramePreservationWitness] checks the set-level condition: transformed
    fragments write only allowed cells, and those allowed cells are disjoint
    from the context frame.  For contextual composition we also need a value
    layer saying that the finite frame snapshot observed before the fragment is
    preserved after the fragment.  This module checks that value evidence while
    keeping derivation of the frame snapshot from concrete semantics explicit. *)

Record frame_value_entry (value: Type) := {
  fve_frame_cell : MemCell;
  fve_before_value : value;
  fve_after_value : value;
}.

Arguments fve_frame_cell {value} _.
Arguments fve_before_value {value} _.
Arguments fve_after_value {value} _.

Definition frame_value_entry_cell_match {value: Type}
    (cell: MemCell)
    (entry: frame_value_entry value) : Prop :=
  cell = fve_frame_cell entry.

Definition frame_value_entry_preserved {value: Type}
    (entry: frame_value_entry value) : Prop :=
  fve_before_value entry = fve_after_value entry.

Fixpoint frame_value_entries_preserve {value: Type}
    (frame_cells: list MemCell)
    (entries: list (frame_value_entry value)) : Prop :=
  match frame_cells, entries with
  | [], [] => True
  | cell :: frame_tail, entry :: entry_tail =>
      frame_value_entry_cell_match cell entry /\
      frame_value_entry_preserved entry /\
      frame_value_entries_preserve frame_tail entry_tail
  | _, _ => False
  end.

Definition check_frame_value_entryb {value: Type}
    (value_eqb: value -> value -> bool)
    (cell: MemCell)
    (entry: frame_value_entry value) : bool :=
  mem_cell_strict_eqb cell (fve_frame_cell entry) &&
  value_eqb (fve_before_value entry) (fve_after_value entry).

Fixpoint check_frame_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (frame_cells: list MemCell)
    (entries: list (frame_value_entry value)) : bool :=
  match frame_cells, entries with
  | [], [] => true
  | cell :: frame_tail, entry :: entry_tail =>
      check_frame_value_entryb value_eqb cell entry &&
      check_frame_value_entriesb value_eqb frame_tail entry_tail
  | _, _ => false
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_frame_value_entryb_sound :
  forall cell entry,
    check_frame_value_entryb value_eqb cell entry = true ->
    frame_value_entry_cell_match cell entry /\
    frame_value_entry_preserved entry.
Proof.
  intros cell entry Hcheck.
  unfold check_frame_value_entryb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcell Hvalue].
  apply mem_cell_strict_eqb_eq in Hcell.
  apply value_eqb_sound in Hvalue.
  split.
  - unfold frame_value_entry_cell_match.
    exact Hcell.
  - unfold frame_value_entry_preserved.
    exact Hvalue.
Qed.

Lemma check_frame_value_entriesb_sound :
  forall frame_cells entries,
    check_frame_value_entriesb
      value_eqb frame_cells entries = true ->
    frame_value_entries_preserve frame_cells entries.
Proof.
  induction frame_cells as [|cell frame_tail IH];
    intros entries Hcheck; destruct entries as [|entry entry_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    pose proof
      (check_frame_value_entryb_sound cell entry Hhead)
      as [Hcell Hvalue].
    split.
    + exact Hcell.
    + split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Lemma frame_value_entries_preserve_length :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value)),
    frame_value_entries_preserve frame_cells entries ->
    length frame_cells = length entries.
Proof.
  induction frame_cells as [|cell frame_tail IH];
    intros entries Hpreserve;
    destruct entries as [|entry entry_tail];
    simpl in Hpreserve; try contradiction.
  - reflexivity.
  - simpl.
    destruct Hpreserve as [_ [_ Htail]].
    f_equal.
    apply IH.
    exact Htail.
Qed.

Record frame_value_obligations
    (frame_cells: list MemCell)
    (entries: list (frame_value_entry value)) : Prop := {
  fvo_entries_preserve :
    frame_value_entries_preserve frame_cells entries;
}.

Definition check_frame_valueb
    (frame_cells: list MemCell)
    (entries: list (frame_value_entry value)) : bool :=
  check_frame_value_entriesb value_eqb frame_cells entries.

Lemma check_frame_valueb_sound :
  forall frame_cells entries,
    check_frame_valueb frame_cells entries = true ->
    frame_value_obligations frame_cells entries.
Proof.
  unfold check_frame_valueb.
  intros frame_cells entries Hcheck.
  constructor.
  apply check_frame_value_entriesb_sound.
  exact Hcheck.
Qed.

Theorem frame_value_obligation_length_match :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value)),
    frame_value_obligations frame_cells entries ->
    length frame_cells = length entries.
Proof.
  intros frame_cells entries Hobligations.
  destruct Hobligations as [Hpreserve].
  eapply frame_value_entries_preserve_length; eauto.
Qed.

Lemma frame_value_entries_preserve_cell :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (cell: MemCell),
    frame_value_entries_preserve frame_cells entries ->
    In cell frame_cells ->
    exists entry,
      In entry entries /\
      fve_frame_cell entry = cell /\
      fve_before_value entry = fve_after_value entry.
Proof.
  induction frame_cells as [|head frame_tail IH];
    intros entries cell Hpreserve Hin;
    destruct entries as [|entry entry_tail]; simpl in Hpreserve, Hin;
    try contradiction.
  destruct Hpreserve as [Hcell [Hvalue Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst.
    exists entry.
    split.
    + simpl. left. reflexivity.
    + split.
      * unfold frame_value_entry_cell_match in Hcell.
        symmetry.
        exact Hcell.
      * unfold frame_value_entry_preserved in Hvalue.
        exact Hvalue.
  - pose proof (IH entry_tail cell Htail Hin_tail)
      as (tail_entry & Htail_in & Htail_cell & Htail_value).
    exists tail_entry.
    split.
    + simpl. right. exact Htail_in.
    + split; assumption.
Qed.

Theorem frame_value_cell_preserved :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (cell: MemCell),
    frame_value_obligations frame_cells entries ->
    In cell frame_cells ->
    exists entry,
      In entry entries /\
      fve_frame_cell entry = cell /\
      fve_before_value entry = fve_after_value entry.
Proof.
  intros frame_cells entries cell Hobligations Hin.
  destruct Hobligations as [Hpreserve].
  eapply frame_value_entries_preserve_cell; eauto.
Qed.

Lemma frame_value_entries_preserve_entry :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (entry: frame_value_entry value),
    frame_value_entries_preserve frame_cells entries ->
    In entry entries ->
    In (fve_frame_cell entry) frame_cells /\
    fve_before_value entry = fve_after_value entry.
Proof.
  induction frame_cells as [|head frame_tail IH];
    intros entries entry Hpreserve Hin;
    destruct entries as [|head_entry entry_tail];
    simpl in Hpreserve, Hin; try contradiction.
  destruct Hpreserve as [Hcell [Hvalue Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst head_entry.
    split.
    + simpl. left.
      unfold frame_value_entry_cell_match in Hcell.
      exact Hcell.
    + unfold frame_value_entry_preserved in Hvalue.
      exact Hvalue.
  - pose proof (IH entry_tail entry Htail Hin_tail)
      as [Hframe Hpreserved].
    split.
    + simpl. right. exact Hframe.
    + exact Hpreserved.
Qed.

Theorem frame_value_entry_in_frame_cells :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (entry: frame_value_entry value),
    frame_value_obligations frame_cells entries ->
    In entry entries ->
    In (fve_frame_cell entry) frame_cells /\
    fve_before_value entry = fve_after_value entry.
Proof.
  intros frame_cells entries entry Hobligations Hin.
  destruct Hobligations as [Hpreserve].
  eapply frame_value_entries_preserve_entry; eauto.
Qed.

Theorem frame_value_entry_preserved_from_obligation :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (entry: frame_value_entry value),
    frame_value_obligations frame_cells entries ->
    In entry entries ->
    fve_before_value entry = fve_after_value entry.
Proof.
  intros frame_cells entries entry Hobligations Hin.
  pose proof
    (frame_value_entry_in_frame_cells
       frame_cells entries entry Hobligations Hin)
    as [_ Hpreserved].
  exact Hpreserved.
Qed.

Theorem check_frame_valueb_length_match :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value)),
    check_frame_valueb frame_cells entries = true ->
    length frame_cells = length entries.
Proof.
  intros frame_cells entries Hcheck.
  eapply frame_value_obligation_length_match.
  apply check_frame_valueb_sound.
  exact Hcheck.
Qed.

Theorem check_frame_valueb_cell_preserved :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (cell: MemCell),
    check_frame_valueb frame_cells entries = true ->
    In cell frame_cells ->
    exists entry,
      In entry entries /\
      fve_frame_cell entry = cell /\
      fve_before_value entry = fve_after_value entry.
Proof.
  intros frame_cells entries cell Hcheck Hin.
  eapply frame_value_cell_preserved; eauto.
  apply check_frame_valueb_sound.
  exact Hcheck.
Qed.

Theorem check_frame_valueb_entry_in_frame_cells :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (entry: frame_value_entry value),
    check_frame_valueb frame_cells entries = true ->
    In entry entries ->
    In (fve_frame_cell entry) frame_cells /\
    fve_before_value entry = fve_after_value entry.
Proof.
  intros frame_cells entries entry Hcheck Hin.
  eapply frame_value_entry_in_frame_cells; eauto.
  apply check_frame_valueb_sound.
  exact Hcheck.
Qed.

Theorem check_frame_valueb_entry_preserved :
  forall (frame_cells: list MemCell)
         (entries: list (frame_value_entry value))
         (entry: frame_value_entry value),
    check_frame_valueb frame_cells entries = true ->
    In entry entries ->
    fve_before_value entry = fve_after_value entry.
Proof.
  intros frame_cells entries entry Hcheck Hin.
  eapply frame_value_entry_preserved_from_obligation; eauto.
  apply check_frame_valueb_sound.
  exact Hcheck.
Qed.

End Soundness.
