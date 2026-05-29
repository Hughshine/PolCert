Require Import Bool.
Require Import List.
Require Import ZArith.

Require Import AST.
Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.
Open Scope Z_scope.

(** Finite in-bounds witness for storage-changing transformations.

    Layout rewrites, padding, scratch buffers, contraction, and versioned
    storage all introduce physical cells whose address legality is not implied
    by schedule legality.  This witness records a small, reusable fact: every
    represented physical cell lies within a declared array extent.  It is still
    finite and boundary-oriented; deriving these extents from C declarations is
    a later front-end/CompCert obligation. *)

Fixpoint ident_inb (id: ident) (ids: list ident) : bool :=
  match ids with
  | [] => false
  | id' :: tail =>
      Pos.eqb id id' || ident_inb id tail
  end.

Lemma ident_inb_sound :
  forall id ids,
    ident_inb id ids = true ->
    In id ids.
Proof.
  induction ids as [|id' tail IH]; intros Hcheck; simpl in Hcheck.
  - discriminate.
  - apply orb_true_iff in Hcheck.
    destruct Hcheck as [Heq | Hin_tail].
    + apply Pos.eqb_eq in Heq.
      subst. left. reflexivity.
    + right. apply IH. exact Hin_tail.
Qed.

Lemma ident_inb_complete :
  forall id ids,
    In id ids ->
    ident_inb id ids = true.
Proof.
  induction ids as [|id' tail IH]; intros Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst. rewrite Pos.eqb_refl. reflexivity.
    + rewrite IH; auto.
      destruct (Pos.eqb id id'); reflexivity.
Qed.

Fixpoint idents_nodupb (ids: list ident) : bool :=
  match ids with
  | [] => true
  | id :: tail =>
      negb (ident_inb id tail) && idents_nodupb tail
  end.

Lemma idents_nodupb_sound :
  forall ids,
    idents_nodupb ids = true ->
    NoDup ids.
Proof.
  induction ids as [|id tail IH]; intros Hcheck; simpl in Hcheck.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    apply negb_true_iff in Hnotin.
    constructor.
    + intro Hin.
      apply ident_inb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + apply IH. exact Htail.
Qed.

Definition z_index_within_bound (index extent: Z) : Prop :=
  0 <= index < extent.

Definition check_z_index_within_boundb
    (index extent: Z) : bool :=
  Z.leb 0 index && Z.ltb index extent.

Lemma check_z_index_within_boundb_sound :
  forall index extent,
    check_z_index_within_boundb index extent = true ->
    z_index_within_bound index extent.
Proof.
  intros index extent Hcheck.
  unfold check_z_index_within_boundb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hlower Hupper].
  apply Z.leb_le in Hlower.
  apply Z.ltb_lt in Hupper.
  unfold z_index_within_bound.
  split; assumption.
Qed.

Fixpoint indices_within_bounds
    (indices extents: list Z) : Prop :=
  match indices, extents with
  | [], [] => True
  | index :: indices_tail, extent :: extents_tail =>
      z_index_within_bound index extent /\
      indices_within_bounds indices_tail extents_tail
  | _, _ => False
  end.

Fixpoint check_indices_within_boundsb
    (indices extents: list Z) : bool :=
  match indices, extents with
  | [], [] => true
  | index :: indices_tail, extent :: extents_tail =>
      check_z_index_within_boundb index extent &&
      check_indices_within_boundsb indices_tail extents_tail
  | _, _ => false
  end.

Lemma check_indices_within_boundsb_sound :
  forall indices extents,
    check_indices_within_boundsb indices extents = true ->
    indices_within_bounds indices extents.
Proof.
  induction indices as [|index indices_tail IH];
    intros extents Hcheck;
    destruct extents as [|extent extents_tail];
    simpl in Hcheck |- *; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    split.
    + apply check_z_index_within_boundb_sound.
      exact Hhead.
    + apply IH. exact Htail.
Qed.

Fixpoint positive_extents (extents: list Z) : Prop :=
  match extents with
  | [] => True
  | extent :: tail =>
      0 < extent /\ positive_extents tail
  end.

Fixpoint check_positive_extentsb (extents: list Z) : bool :=
  match extents with
  | [] => true
  | extent :: tail =>
      Z.ltb 0 extent && check_positive_extentsb tail
  end.

Lemma check_positive_extentsb_sound :
  forall extents,
    check_positive_extentsb extents = true ->
    positive_extents extents.
Proof.
  induction extents as [|extent tail IH]; intros Hcheck;
    simpl in Hcheck |- *.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hextent Htail].
    split.
    + apply Z.ltb_lt. exact Hextent.
    + apply IH. exact Htail.
Qed.

Record array_bounds := {
  array_bounds_id : ident;
  array_bounds_extents : list Z;
}.

Fixpoint array_bounds_ids
    (bounds: list array_bounds) : list ident :=
  match bounds with
  | [] => []
  | bound :: tail =>
      array_bounds_id bound :: array_bounds_ids tail
  end.

Fixpoint array_bounds_lookup
    (id: ident)
    (bounds: list array_bounds) : option array_bounds :=
  match bounds with
  | [] => None
  | bound :: tail =>
      if Pos.eqb id (array_bounds_id bound)
      then Some bound
      else array_bounds_lookup id tail
  end.

Definition array_bounds_wf (bound: array_bounds) : Prop :=
  positive_extents (array_bounds_extents bound).

Definition check_array_bounds_wfb (bound: array_bounds) : bool :=
  check_positive_extentsb (array_bounds_extents bound).

Lemma check_array_bounds_wfb_sound :
  forall bound,
    check_array_bounds_wfb bound = true ->
    array_bounds_wf bound.
Proof.
  unfold check_array_bounds_wfb, array_bounds_wf.
  intros bound Hcheck.
  apply check_positive_extentsb_sound.
  exact Hcheck.
Qed.

Definition array_bounds_list_wf
    (bounds: list array_bounds) : Prop :=
  NoDup (array_bounds_ids bounds) /\
  forall bound,
    In bound bounds ->
    array_bounds_wf bound.

Definition check_array_bounds_list_wfb
    (bounds: list array_bounds) : bool :=
  idents_nodupb (array_bounds_ids bounds) &&
  forallb check_array_bounds_wfb bounds.

Lemma check_array_bounds_list_wfb_sound :
  forall bounds,
    check_array_bounds_list_wfb bounds = true ->
    array_bounds_list_wf bounds.
Proof.
  intros bounds Hcheck.
  unfold check_array_bounds_list_wfb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hnodup Hwf].
  unfold array_bounds_list_wf.
  split.
  - apply idents_nodupb_sound.
    exact Hnodup.
  - intros bound Hin.
    apply forallb_forall with (x := bound) in Hwf; auto.
    apply check_array_bounds_wfb_sound.
    exact Hwf.
Qed.

Lemma array_bounds_lookup_sound :
  forall bounds id bound,
    array_bounds_lookup id bounds = Some bound ->
    In bound bounds /\ array_bounds_id bound = id.
Proof.
  induction bounds as [|head tail IH];
    intros id bound Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (Pos.eqb id (array_bounds_id head)) eqn:Heq.
    + inversion Hlookup; subst.
      apply Pos.eqb_eq in Heq.
      split.
      * left. reflexivity.
      * symmetry. exact Heq.
    + destruct (IH id bound Hlookup) as [Hin Hid].
      split.
      * right. exact Hin.
      * exact Hid.
Qed.

Definition cell_within_array_bounds
    (cell: MemCell) (bound: array_bounds) : Prop :=
  array_bounds_id bound = arr_id cell /\
  indices_within_bounds
    (arr_index cell)
    (array_bounds_extents bound).

Definition cell_within_declared_bounds
    (bounds: list array_bounds) (cell: MemCell) : Prop :=
  exists bound,
    In bound bounds /\
    cell_within_array_bounds cell bound.

Definition check_cell_within_declared_boundsb
    (bounds: list array_bounds) (cell: MemCell) : bool :=
  match array_bounds_lookup (arr_id cell) bounds with
  | Some bound =>
      check_indices_within_boundsb
        (arr_index cell)
        (array_bounds_extents bound)
  | None => false
  end.

Lemma check_cell_within_declared_boundsb_sound :
  forall bounds cell,
    check_cell_within_declared_boundsb bounds cell = true ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros bounds cell Hcheck.
  unfold check_cell_within_declared_boundsb in Hcheck.
  destruct (array_bounds_lookup (arr_id cell) bounds)
    as [bound|] eqn:Hlookup; try discriminate.
  destruct (array_bounds_lookup_sound bounds (arr_id cell) bound Hlookup)
    as [Hin Hid].
  exists bound.
  split.
  - exact Hin.
  - unfold cell_within_array_bounds.
    split.
    + exact Hid.
    + apply check_indices_within_boundsb_sound.
      exact Hcheck.
Qed.

Definition cells_within_declared_bounds
    (bounds: list array_bounds) (cells: list MemCell) : Prop :=
  forall cell,
    In cell cells ->
    cell_within_declared_bounds bounds cell.

Fixpoint check_cells_within_declared_boundsb
    (bounds: list array_bounds) (cells: list MemCell) : bool :=
  match cells with
  | [] => true
  | cell :: tail =>
      check_cell_within_declared_boundsb bounds cell &&
      check_cells_within_declared_boundsb bounds tail
  end.

Lemma check_cells_within_declared_boundsb_sound :
  forall bounds cells,
    check_cells_within_declared_boundsb bounds cells = true ->
    cells_within_declared_bounds bounds cells.
Proof.
  induction cells as [|cell tail IH]; intros Hcheck cell' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply check_cell_within_declared_boundsb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Record storage_bounds_obligations
    (bounds: list array_bounds)
    (cells: list MemCell) : Prop := {
  sbo_bounds_wf :
    array_bounds_list_wf bounds;
  sbo_cells_within_bounds :
    cells_within_declared_bounds bounds cells;
}.

Definition check_storage_boundsb
    (bounds: list array_bounds)
    (cells: list MemCell) : bool :=
  check_array_bounds_list_wfb bounds &&
  check_cells_within_declared_boundsb bounds cells.

Lemma check_storage_boundsb_sound :
  forall bounds cells,
    check_storage_boundsb bounds cells = true ->
    storage_bounds_obligations bounds cells.
Proof.
  intros bounds cells Hcheck.
  unfold check_storage_boundsb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hbounds Hcells].
  constructor.
  - apply check_array_bounds_list_wfb_sound.
    exact Hbounds.
  - apply check_cells_within_declared_boundsb_sound.
    exact Hcells.
Qed.

Theorem storage_bounds_cell_within :
  forall bounds cells cell,
    storage_bounds_obligations bounds cells ->
    In cell cells ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros bounds cells cell Hobligations Hin.
  destruct Hobligations as [_ Hcells].
  eapply Hcells; eauto.
Qed.

Theorem cell_within_declared_bounds_entry :
  forall bounds cell,
    cell_within_declared_bounds bounds cell ->
    exists bound,
      In bound bounds /\
      array_bounds_id bound = arr_id cell /\
      indices_within_bounds
        (arr_index cell)
        (array_bounds_extents bound).
Proof.
  intros bounds cell Hwithin.
  destruct Hwithin as (bound & Hin & Harray).
  unfold cell_within_array_bounds in Harray.
  destruct Harray as [Hid Hindices].
  exists bound.
  repeat split; assumption.
Qed.

Theorem check_cell_within_declared_boundsb_entry :
  forall bounds cell,
    check_cell_within_declared_boundsb bounds cell = true ->
    exists bound,
      In bound bounds /\
      array_bounds_id bound = arr_id cell /\
      indices_within_bounds
        (arr_index cell)
        (array_bounds_extents bound).
Proof.
  intros bounds cell Hcheck.
  apply cell_within_declared_bounds_entry.
  apply check_cell_within_declared_boundsb_sound.
  exact Hcheck.
Qed.

Theorem storage_bounds_cell_bound_entry :
  forall bounds cells cell,
    storage_bounds_obligations bounds cells ->
    In cell cells ->
    exists bound,
      In bound bounds /\
      array_bounds_id bound = arr_id cell /\
      indices_within_bounds
        (arr_index cell)
        (array_bounds_extents bound).
Proof.
  intros bounds cells cell Hobligations Hin.
  apply cell_within_declared_bounds_entry.
  eapply storage_bounds_cell_within; eauto.
Qed.

Theorem check_storage_boundsb_cell_bound_entry :
  forall bounds cells cell,
    check_storage_boundsb bounds cells = true ->
    In cell cells ->
    exists bound,
      In bound bounds /\
      array_bounds_id bound = arr_id cell /\
      indices_within_bounds
        (arr_index cell)
        (array_bounds_extents bound).
Proof.
  intros bounds cells cell Hcheck Hin.
  apply storage_bounds_cell_bound_entry with (cells := cells).
  - apply check_storage_boundsb_sound.
    exact Hcheck.
  - exact Hin.
Qed.
