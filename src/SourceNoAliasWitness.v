Require Import Bool.
Require Import List.

Require Import Coqlib.
Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import StorageBoundsWitness.

Import ListNotations.

(** Finite witness for source no-alias abstraction.

    This is a boundary precondition, not a transformation.  It records a finite
    footprint for each logical source object and checks that different logical
    objects have disjoint concrete cells. *)

Definition source_object := positive.
Definition source_footprint := (source_object * list MemCell)%type.
Definition source_access_footprint := (source_object * list MemCell)%type.

Definition source_object_eqb
    (left right: source_object) : bool :=
  Pos.eqb left right.

Fixpoint source_footprint_cells
    (footprints: list source_footprint) : list MemCell :=
  match footprints with
  | [] => []
  | (_, cells) :: tail =>
      cells ++ source_footprint_cells tail
  end.

Lemma source_object_eqb_eq :
  forall left right,
    source_object_eqb left right = true ->
    left = right.
Proof.
  unfold source_object_eqb.
  intros left right Hcheck.
  apply Pos.eqb_eq.
  exact Hcheck.
Qed.

Definition source_object_inb
    (object: source_object)
    (objects: list source_object) : bool :=
  existsb (source_object_eqb object) objects.

Lemma source_object_inb_sound :
  forall object objects,
    source_object_inb object objects = true ->
    In object objects.
Proof.
  unfold source_object_inb.
  intros object objects Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (object' & Hin & Heq).
  apply source_object_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma source_object_inb_complete :
  forall object objects,
    In object objects ->
    source_object_inb object objects = true.
Proof.
  unfold source_object_inb, source_object_eqb.
  intros object objects Hin.
  apply existsb_exists.
  exists object.
  split.
  - exact Hin.
  - apply Pos.eqb_refl.
Qed.

Fixpoint source_objects_nodupb
    (objects: list source_object) : bool :=
  match objects with
  | [] => true
  | object :: tail =>
      negb (source_object_inb object tail) &&
      source_objects_nodupb tail
  end.

Lemma source_objects_nodupb_sound :
  forall objects,
    source_objects_nodupb objects = true ->
    NoDup objects.
Proof.
  induction objects as [|object tail IH]; intros Hcheck;
    simpl in Hcheck.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    apply negb_true_iff in Hnotin.
    constructor.
    + intro Hin.
      apply source_object_inb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + apply IH.
      exact Htail.
Qed.

Fixpoint source_footprint_objects
    (footprints: list source_footprint) : list source_object :=
  match footprints with
  | [] => []
  | (object, _) :: tail =>
      object :: source_footprint_objects tail
  end.

Fixpoint source_footprint_lookup
    (object: source_object)
    (footprints: list source_footprint) : option (list MemCell) :=
  match footprints with
  | [] => None
  | (object', cells) :: tail =>
      if source_object_eqb object object'
      then Some cells
      else source_footprint_lookup object tail
  end.

Lemma source_footprint_lookup_sound :
  forall object footprints cells,
    source_footprint_lookup object footprints = Some cells ->
    In (object, cells) footprints.
Proof.
  induction footprints as [|[object' cells'] tail IH];
    intros cells Hlookup; simpl in Hlookup; try discriminate.
  destruct (source_object_eqb object object') eqn:Hobject.
  - inversion Hlookup; subst.
    apply source_object_eqb_eq in Hobject.
    subst.
    simpl. left. reflexivity.
  - simpl. right.
    eapply IH.
    exact Hlookup.
Qed.

Lemma source_footprint_cell_in_cells :
  forall footprints object cells cell,
    In (object, cells) footprints ->
    In cell cells ->
    In cell (source_footprint_cells footprints).
Proof.
  induction footprints as [|[object' cells'] tail IH];
    intros object cells cell Hfootprint Hcell;
    simpl in Hfootprint |- *; try contradiction.
  destruct Hfootprint as [Heq | Htail].
  - inversion Heq; subst.
    apply in_or_app.
    left. exact Hcell.
  - apply in_or_app.
    right.
    eapply IH; eauto.
Qed.

Fixpoint source_footprints_nodupb
    (footprints: list source_footprint) : bool :=
  match footprints with
  | [] => true
  | (_, cells) :: tail =>
      mem_cells_nodupb cells &&
      source_footprints_nodupb tail
  end.

Fixpoint source_footprints_nodup
    (footprints: list source_footprint) : Prop :=
  match footprints with
  | [] => True
  | (_, cells) :: tail =>
      NoDup cells /\ source_footprints_nodup tail
  end.

Lemma source_footprints_nodupb_sound :
  forall footprints,
    source_footprints_nodupb footprints = true ->
    source_footprints_nodup footprints.
Proof.
  induction footprints as [|[object cells] tail IH]; intros Hcheck;
    simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hcells Htail].
    split.
    + apply mem_cells_nodupb_sound.
      exact Hcells.
    + apply IH.
      exact Htail.
Qed.

Definition footprint_disjoint_from
    (cells: list MemCell)
    (footprints: list source_footprint) : Prop :=
  forall object cells',
    In (object, cells') footprints ->
    mem_cells_disjoint cells cells'.

Fixpoint check_footprint_disjoint_fromb
    (cells: list MemCell)
    (footprints: list source_footprint) : bool :=
  match footprints with
  | [] => true
  | (_, cells') :: tail =>
      mem_cells_disjointb cells cells' &&
      check_footprint_disjoint_fromb cells tail
  end.

Lemma check_footprint_disjoint_fromb_sound :
  forall cells footprints,
    check_footprint_disjoint_fromb cells footprints = true ->
    footprint_disjoint_from cells footprints.
Proof.
  induction footprints as [|[object cells'] tail IH];
    intros Hcheck object' cells'' Hin; simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      apply mem_cells_disjointb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Fixpoint source_footprints_pairwise_disjoint
    (footprints: list source_footprint) : Prop :=
  match footprints with
  | [] => True
  | (_, cells) :: tail =>
      footprint_disjoint_from cells tail /\
      source_footprints_pairwise_disjoint tail
  end.

Fixpoint check_source_footprints_pairwise_disjointb
    (footprints: list source_footprint) : bool :=
  match footprints with
  | [] => true
  | (_, cells) :: tail =>
      check_footprint_disjoint_fromb cells tail &&
      check_source_footprints_pairwise_disjointb tail
  end.

Lemma check_source_footprints_pairwise_disjointb_sound :
  forall footprints,
    check_source_footprints_pairwise_disjointb footprints = true ->
    source_footprints_pairwise_disjoint footprints.
Proof.
  induction footprints as [|[object cells] tail IH]; intros Hcheck;
    simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    split.
    + apply check_footprint_disjoint_fromb_sound.
      exact Hhead.
    + apply IH.
      exact Htail.
Qed.

Record source_no_alias_obligations
    (footprints: list source_footprint) : Prop := {
  sna_objects_nodup :
    NoDup (source_footprint_objects footprints);
  sna_footprints_nodup :
    source_footprints_nodup footprints;
  sna_pairwise_disjoint :
    source_footprints_pairwise_disjoint footprints;
}.

Definition check_source_no_aliasb
    (footprints: list source_footprint) : bool :=
  source_objects_nodupb (source_footprint_objects footprints) &&
  source_footprints_nodupb footprints &&
  check_source_footprints_pairwise_disjointb footprints.

Lemma check_source_no_aliasb_sound :
  forall footprints,
    check_source_no_aliasb footprints = true ->
    source_no_alias_obligations footprints.
Proof.
  intros footprints Hcheck.
  unfold check_source_no_aliasb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hobjects & Hfootprints) & Hdisjoint).
  constructor.
  - apply source_objects_nodupb_sound.
    exact Hobjects.
  - apply source_footprints_nodupb_sound.
    exact Hfootprints.
  - apply check_source_footprints_pairwise_disjointb_sound.
    exact Hdisjoint.
Qed.

(** Access-footprint coverage.

    No-alias disjointness is sound only if the finite footprints actually
    over-approximate the cells read or written by the source abstraction.  The
    following checker records that side condition over a finite list of
    per-object access cells. *)

Definition source_accesses_covered
    (footprints: list source_footprint)
    (accesses: list source_access_footprint) : Prop :=
  forall object access_cells cell,
    In (object, access_cells) accesses ->
    In cell access_cells ->
    exists footprint_cells,
      In (object, footprint_cells) footprints /\
      In cell footprint_cells.

Fixpoint check_source_accesses_coveredb
    (footprints: list source_footprint)
    (accesses: list source_access_footprint) : bool :=
  match accesses with
  | [] => true
  | (object, access_cells) :: tail =>
      match source_footprint_lookup object footprints with
      | Some footprint_cells =>
          mem_cells_subsetb access_cells footprint_cells &&
          check_source_accesses_coveredb footprints tail
      | None => false
      end
  end.

Lemma check_source_accesses_coveredb_sound :
  forall footprints accesses,
    check_source_accesses_coveredb footprints accesses = true ->
    source_accesses_covered footprints accesses.
Proof.
  unfold source_accesses_covered.
  intros footprints accesses.
  induction accesses as [|[object access_cells] tail IH];
    intros Hcheck query_object query_cells cell Haccess Hcell;
    simpl in Hcheck, Haccess.
  - contradiction.
  - destruct (source_footprint_lookup object footprints)
      as [footprint_cells|] eqn:Hlookup; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hcovered Htail].
    destruct Haccess as [Heq | Htail_access].
    + inversion Heq; subst.
      exists footprint_cells.
      split.
      * eapply source_footprint_lookup_sound.
        exact Hlookup.
      * eapply mem_cells_subsetb_sound; eauto.
    + eapply IH; eauto.
Qed.

Record source_no_alias_access_obligations
    (footprints: list source_footprint)
    (accesses: list source_access_footprint) : Prop := {
  snaa_no_alias :
    source_no_alias_obligations footprints;
  snaa_accesses_covered :
    source_accesses_covered footprints accesses;
}.

Record source_no_alias_access_bounded_obligations
    (footprints: list source_footprint)
    (accesses: list source_access_footprint)
    (bounds: list array_bounds) : Prop := {
  snaab_base :
    source_no_alias_access_obligations footprints accesses;
  snaab_footprint_bounds :
    storage_bounds_obligations bounds (source_footprint_cells footprints);
}.

Definition check_source_no_alias_accessb
    (footprints: list source_footprint)
    (accesses: list source_access_footprint) : bool :=
  check_source_no_aliasb footprints &&
  check_source_accesses_coveredb footprints accesses.

Definition check_source_no_alias_access_boundedb
    (footprints: list source_footprint)
    (accesses: list source_access_footprint)
    (bounds: list array_bounds) : bool :=
  check_source_no_alias_accessb footprints accesses &&
  check_storage_boundsb bounds (source_footprint_cells footprints).

Lemma check_source_no_alias_accessb_sound :
  forall footprints accesses,
    check_source_no_alias_accessb footprints accesses = true ->
    source_no_alias_access_obligations footprints accesses.
Proof.
  intros footprints accesses Hcheck.
  unfold check_source_no_alias_accessb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hno_alias Hcovered].
  constructor.
  - apply check_source_no_aliasb_sound.
    exact Hno_alias.
  - apply check_source_accesses_coveredb_sound.
    exact Hcovered.
Qed.

Lemma check_source_no_alias_access_boundedb_sound :
  forall footprints accesses bounds,
    check_source_no_alias_access_boundedb
      footprints accesses bounds = true ->
    source_no_alias_access_bounded_obligations
      footprints accesses bounds.
Proof.
  intros footprints accesses bounds Hcheck.
  unfold check_source_no_alias_access_boundedb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hbase Hbounds].
  constructor.
  - apply check_source_no_alias_accessb_sound.
    exact Hbase.
  - apply check_storage_boundsb_sound.
    exact Hbounds.
Qed.

Theorem source_access_cell_covered :
  forall footprints accesses object access_cells cell,
    source_no_alias_access_obligations footprints accesses ->
    In (object, access_cells) accesses ->
    In cell access_cells ->
    exists footprint_cells,
      In (object, footprint_cells) footprints /\
      In cell footprint_cells.
Proof.
  intros footprints accesses object access_cells cell Hobligations
         Haccess Hcell.
  destruct Hobligations as [_ Hcovered].
  eapply Hcovered; eauto.
Qed.

Theorem source_footprint_cell_within_bounds :
  forall footprints accesses bounds object footprint_cells cell,
    source_no_alias_access_bounded_obligations
      footprints accesses bounds ->
    In (object, footprint_cells) footprints ->
    In cell footprint_cells ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros footprints accesses bounds object footprint_cells cell
         Hobligations Hfootprint Hcell.
  destruct Hobligations as [_ Hbounds].
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - eapply source_footprint_cell_in_cells; eauto.
Qed.

Theorem source_access_cell_within_bounds :
  forall footprints accesses bounds object access_cells cell,
    source_no_alias_access_bounded_obligations
      footprints accesses bounds ->
    In (object, access_cells) accesses ->
    In cell access_cells ->
    cell_within_declared_bounds bounds cell.
Proof.
  intros footprints accesses bounds object access_cells cell
         Hobligations Haccess Hcell.
  destruct Hobligations as [Hbase Hbounds].
  pose proof
    (source_access_cell_covered
       footprints accesses object access_cells cell Hbase Haccess Hcell)
    as (footprint_cells & Hfootprint & Hfootprint_cell).
  eapply storage_bounds_cell_within.
  - exact Hbounds.
  - eapply source_footprint_cell_in_cells; eauto.
Qed.
