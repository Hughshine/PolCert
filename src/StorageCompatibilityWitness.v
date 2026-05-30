Require Import Arith.
Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import ReuseConflictWitness.

Import ListNotations.

(** Finite storage-compatibility witness.

    Storage-changing transformations often need a side condition that is not
    purely about aliasing or live ranges: the physical cell that represents a
    logical cell must be compatible with the logical value's storage class.
    Examples include inter-array reuse, contraction into a rolling buffer,
    scratchpad packing, and scalar/private expansion.

    This witness intentionally models only a small boundary fact: each
    logical-to-physical mapping entry has finite storage specs on both sides,
    and the specs agree on size and alignment.  A future C/CompCert integration
    should derive these specs from actual types, object bounds, and alignment
    rules. *)

Record storage_spec := {
  storage_spec_cell : MemCell;
  storage_spec_size : nat;
  storage_spec_align : nat;
}.

Fixpoint storage_spec_lookup
    (cell: MemCell)
    (specs: list storage_spec) : option storage_spec :=
  match specs with
  | [] => None
  | spec :: tail =>
      if mem_cell_strict_eqb cell (storage_spec_cell spec)
      then Some spec
      else storage_spec_lookup cell tail
  end.

Lemma storage_spec_lookup_entry :
  forall cell specs spec,
    storage_spec_lookup cell specs = Some spec ->
    In spec specs /\ storage_spec_cell spec = cell.
Proof.
  intros cell specs.
  induction specs as [|head tail IH];
    intros spec Hlookup; simpl in Hlookup; try discriminate.
  destruct (mem_cell_strict_eqb cell (storage_spec_cell head))
    eqn:Hcell.
  - inversion Hlookup; subst spec.
    apply mem_cell_strict_eqb_eq in Hcell.
    split.
    + simpl. left. reflexivity.
    + symmetry. exact Hcell.
  - pose proof (IH spec Hlookup) as [Hin Hcell_spec].
    split.
    + simpl. right. exact Hin.
    + exact Hcell_spec.
Qed.

Fixpoint storage_spec_cells
    (specs: list storage_spec) : list MemCell :=
  match specs with
  | [] => []
  | spec :: tail =>
      storage_spec_cell spec :: storage_spec_cells tail
  end.

Definition storage_specs_nodup
    (specs: list storage_spec) : Prop :=
  NoDup (storage_spec_cells specs).

Definition check_storage_specs_nodupb
    (specs: list storage_spec) : bool :=
  mem_cells_nodupb (storage_spec_cells specs).

Lemma check_storage_specs_nodupb_sound :
  forall specs,
    check_storage_specs_nodupb specs = true ->
    storage_specs_nodup specs.
Proof.
  unfold check_storage_specs_nodupb, storage_specs_nodup.
  intros specs Hcheck.
  apply mem_cells_nodupb_sound.
  exact Hcheck.
Qed.

Definition storage_specs_compatible
    (logical_spec physical_spec: storage_spec) : Prop :=
  storage_spec_size logical_spec = storage_spec_size physical_spec /\
  storage_spec_align logical_spec = storage_spec_align physical_spec.

Definition check_storage_specs_compatibleb
    (logical_spec physical_spec: storage_spec) : bool :=
  Nat.eqb
    (storage_spec_size logical_spec)
    (storage_spec_size physical_spec) &&
  Nat.eqb
    (storage_spec_align logical_spec)
    (storage_spec_align physical_spec).

Lemma check_storage_specs_compatibleb_sound :
  forall logical_spec physical_spec,
    check_storage_specs_compatibleb logical_spec physical_spec = true ->
    storage_specs_compatible logical_spec physical_spec.
Proof.
  intros logical_spec physical_spec Hcheck.
  unfold check_storage_specs_compatibleb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hsize Halign].
  apply Nat.eqb_eq in Hsize.
  apply Nat.eqb_eq in Halign.
  unfold storage_specs_compatible.
  split; assumption.
Qed.

Definition storage_mapping_entry_compatible
    (logical_specs physical_specs: list storage_spec)
    (mapping_entry: MemCell * MemCell) : Prop :=
  exists logical_spec physical_spec,
    storage_spec_lookup (fst mapping_entry) logical_specs =
      Some logical_spec /\
    storage_spec_lookup (snd mapping_entry) physical_specs =
      Some physical_spec /\
    storage_specs_compatible logical_spec physical_spec.

Definition check_storage_mapping_entry_compatibleb
    (logical_specs physical_specs: list storage_spec)
    (mapping_entry: MemCell * MemCell) : bool :=
  match storage_spec_lookup (fst mapping_entry) logical_specs,
        storage_spec_lookup (snd mapping_entry) physical_specs with
  | Some logical_spec, Some physical_spec =>
      check_storage_specs_compatibleb logical_spec physical_spec
  | _, _ => false
  end.

Lemma check_storage_mapping_entry_compatibleb_sound :
  forall logical_specs physical_specs mapping_entry,
    check_storage_mapping_entry_compatibleb
      logical_specs physical_specs mapping_entry = true ->
    storage_mapping_entry_compatible
      logical_specs physical_specs mapping_entry.
Proof.
  intros logical_specs physical_specs [logical_cell physical_cell] Hcheck.
  unfold check_storage_mapping_entry_compatibleb in Hcheck.
  unfold storage_mapping_entry_compatible.
  simpl in Hcheck.
  destruct (storage_spec_lookup logical_cell logical_specs)
    as [logical_spec|] eqn:Hlogical; try discriminate.
  destruct (storage_spec_lookup physical_cell physical_specs)
    as [physical_spec|] eqn:Hphysical; try discriminate.
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical.
  - split.
    + exact Hphysical.
    + apply check_storage_specs_compatibleb_sound.
      exact Hcheck.
Qed.

Theorem storage_mapping_entry_compatible_specs :
  forall logical_specs physical_specs mapping_entry,
    storage_mapping_entry_compatible
      logical_specs physical_specs mapping_entry ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = fst mapping_entry /\
      storage_spec_cell physical_spec = snd mapping_entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros logical_specs physical_specs
         [logical_cell physical_cell] Hcompatible.
  unfold storage_mapping_entry_compatible in Hcompatible.
  simpl in Hcompatible |- *.
  destruct Hcompatible as
    (logical_spec & physical_spec & Hlogical & Hphysical & Hspecs).
  pose proof
    (storage_spec_lookup_entry
       logical_cell logical_specs logical_spec Hlogical)
    as [Hlogical_in Hlogical_cell].
  pose proof
    (storage_spec_lookup_entry
       physical_cell physical_specs physical_spec Hphysical)
    as [Hphysical_in Hphysical_cell].
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical_in.
  - split.
    + exact Hphysical_in.
    + split.
      * exact Hlogical_cell.
      * split.
        -- exact Hphysical_cell.
        -- exact Hspecs.
Qed.

Theorem check_storage_mapping_entry_compatibleb_specs :
  forall logical_specs physical_specs mapping_entry,
    check_storage_mapping_entry_compatibleb
      logical_specs physical_specs mapping_entry = true ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = fst mapping_entry /\
      storage_spec_cell physical_spec = snd mapping_entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros logical_specs physical_specs mapping_entry Hcheck.
  apply storage_mapping_entry_compatible_specs.
  apply check_storage_mapping_entry_compatibleb_sound.
  exact Hcheck.
Qed.

Fixpoint check_storage_mapping_compatibleb
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec) : bool :=
  match mapping with
  | [] => true
  | mapping_entry :: tail =>
      check_storage_mapping_entry_compatibleb
        logical_specs physical_specs mapping_entry &&
      check_storage_mapping_compatibleb
        tail logical_specs physical_specs
  end.

Definition storage_mapping_compatible
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec) : Prop :=
  forall mapping_entry,
    In mapping_entry mapping ->
    storage_mapping_entry_compatible
      logical_specs physical_specs mapping_entry.

Lemma check_storage_mapping_compatibleb_sound :
  forall mapping logical_specs physical_specs,
    check_storage_mapping_compatibleb
      mapping logical_specs physical_specs = true ->
    storage_mapping_compatible
      mapping logical_specs physical_specs.
Proof.
  induction mapping as [|mapping_entry mapping_tail IH];
    intros logical_specs physical_specs Hcheck entry Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply check_storage_mapping_entry_compatibleb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Record storage_compatibility_obligations
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec) : Prop := {
  sco_logical_specs_nodup :
    storage_specs_nodup logical_specs;
  sco_physical_specs_nodup :
    storage_specs_nodup physical_specs;
  sco_mapping_compatible :
    storage_mapping_compatible mapping logical_specs physical_specs;
}.

Definition check_storage_compatibilityb
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec) : bool :=
  check_storage_specs_nodupb logical_specs &&
  check_storage_specs_nodupb physical_specs &&
  check_storage_mapping_compatibleb mapping logical_specs physical_specs.

Lemma check_storage_compatibilityb_sound :
  forall mapping logical_specs physical_specs,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    storage_compatibility_obligations
      mapping logical_specs physical_specs.
Proof.
  intros mapping logical_specs physical_specs Hcheck.
  unfold check_storage_compatibilityb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hlogical & Hphysical) & Hcompatible).
  constructor.
  - apply check_storage_specs_nodupb_sound.
    exact Hlogical.
  - apply check_storage_specs_nodupb_sound.
    exact Hphysical.
  - apply check_storage_mapping_compatibleb_sound.
    exact Hcompatible.
Qed.

Theorem check_storage_compatibilityb_logical_specs_nodup :
  forall mapping logical_specs physical_specs,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    storage_specs_nodup logical_specs.
Proof.
  intros mapping logical_specs physical_specs Hcheck.
  destruct
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcheck)
    as [Hlogical _ _].
  exact Hlogical.
Qed.

Theorem check_storage_compatibilityb_physical_specs_nodup :
  forall mapping logical_specs physical_specs,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    storage_specs_nodup physical_specs.
Proof.
  intros mapping logical_specs physical_specs Hcheck.
  destruct
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcheck)
    as [_ Hphysical _].
  exact Hphysical.
Qed.

Theorem check_storage_compatibilityb_mapping_compatible :
  forall mapping logical_specs physical_specs,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    storage_mapping_compatible mapping logical_specs physical_specs.
Proof.
  intros mapping logical_specs physical_specs Hcheck.
  destruct
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcheck)
    as [_ _ Hcompatible].
  exact Hcompatible.
Qed.

Theorem check_storage_compatibilityb_mapping_entry_compatible :
  forall mapping logical_specs physical_specs mapping_entry,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    In mapping_entry mapping ->
    storage_mapping_entry_compatible
      logical_specs physical_specs mapping_entry.
Proof.
  intros mapping logical_specs physical_specs mapping_entry Hcheck Hin.
  apply
    (check_storage_compatibilityb_mapping_compatible
       mapping logical_specs physical_specs Hcheck).
  exact Hin.
Qed.

Theorem storage_compatibility_mapping_entry_specs :
  forall mapping logical_specs physical_specs mapping_entry,
    storage_compatibility_obligations
      mapping logical_specs physical_specs ->
    In mapping_entry mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = fst mapping_entry /\
      storage_spec_cell physical_spec = snd mapping_entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping logical_specs physical_specs mapping_entry
         Hobligations Hin.
  destruct Hobligations as [_ _ Hcompatible].
  apply storage_mapping_entry_compatible_specs.
  apply Hcompatible.
  exact Hin.
Qed.

Theorem check_storage_compatibilityb_mapping_entry_specs :
  forall mapping logical_specs physical_specs mapping_entry,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    In mapping_entry mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = fst mapping_entry /\
      storage_spec_cell physical_spec = snd mapping_entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping logical_specs physical_specs mapping_entry Hcheck Hin.
  eapply storage_compatibility_mapping_entry_specs.
  - apply check_storage_compatibilityb_sound.
    exact Hcheck.
  - exact Hin.
Qed.

Theorem storage_compatibility_mapping_pair_specs :
  forall mapping logical_specs physical_specs logical_cell physical_cell,
    storage_compatibility_obligations
      mapping logical_specs physical_specs ->
    In (logical_cell, physical_cell) mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping logical_specs physical_specs logical_cell physical_cell
         Hobligations Hin.
  destruct
    (storage_compatibility_mapping_entry_specs
       mapping logical_specs physical_specs
       (logical_cell, physical_cell) Hobligations Hin)
    as (logical_spec & physical_spec &
        Hlogical_in & Hphysical_in & Hlogical_cell &
        Hphysical_cell & Hcompatible).
  simpl in Hlogical_cell, Hphysical_cell.
  exists logical_spec, physical_spec.
  split.
  - exact Hlogical_in.
  - split.
    + exact Hphysical_in.
    + split.
      * exact Hlogical_cell.
      * split.
        -- exact Hphysical_cell.
        -- exact Hcompatible.
Qed.

Theorem storage_compatibility_lookup_specs :
  forall mapping logical_specs physical_specs logical_cell physical_cell,
    storage_compatibility_obligations
      mapping logical_specs physical_specs ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping logical_specs physical_specs logical_cell physical_cell
         Hobligations Hlookup.
  assert (In (logical_cell, physical_cell) mapping) as Hin.
  {
    destruct
      (reuse_lookup_sound logical_cell physical_cell mapping Hlookup)
      as [Hin | (logical_cell' & Hin & Hlogical_eq)].
    - exact Hin.
    - rewrite <- Hlogical_eq in Hin.
      exact Hin.
  }
  eapply storage_compatibility_mapping_pair_specs; eauto.
Qed.

Theorem check_storage_compatibilityb_mapping_pair_specs :
  forall mapping logical_specs physical_specs logical_cell physical_cell,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    In (logical_cell, physical_cell) mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping logical_specs physical_specs logical_cell physical_cell
         Hcheck Hin.
  eapply storage_compatibility_mapping_pair_specs.
  - apply check_storage_compatibilityb_sound.
    exact Hcheck.
  - exact Hin.
Qed.

Theorem check_storage_compatibilityb_lookup_specs :
  forall mapping logical_specs physical_specs logical_cell physical_cell,
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping logical_specs physical_specs logical_cell physical_cell
         Hcheck Hlookup.
  eapply storage_compatibility_lookup_specs.
  - apply check_storage_compatibilityb_sound.
    exact Hcheck.
  - exact Hlookup.
Qed.
