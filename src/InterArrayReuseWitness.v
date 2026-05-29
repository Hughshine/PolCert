Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import ReuseConflictWitness.
Require Import LifetimeConflictWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** Finite facade for inter-array storage reuse.

    Inter-array reuse is not a new safety principle.  It combines three
    existing witnesses:

    - supplied live intervals cover every overlap conflict;
    - the logical-to-physical reuse map separates every listed conflict; and
    - every logical cell mapped to shared storage is size/alignment compatible
      with its physical representative.

    This file packages that combination under a named obligation because the
    transformation is user-visible: two different logical arrays may share one
    physical buffer when their live ranges do not overlap. *)

Record inter_array_reuse_obligations
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (logical_specs physical_specs: list storage_spec) : Prop := {
  iaro_live_conflicts :
    live_conflict_obligations intervals conflicts;
  iaro_conflict_safe_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  iaro_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
}.

Definition check_inter_array_reuseb
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (logical_specs physical_specs: list storage_spec) : bool :=
  check_live_conflictb intervals conflicts &&
  check_conflict_safe_reuseb mapping conflicts &&
  check_storage_compatibilityb mapping logical_specs physical_specs.

Lemma check_inter_array_reuseb_sound :
  forall mapping intervals conflicts logical_specs physical_specs,
    check_inter_array_reuseb
      mapping intervals conflicts logical_specs physical_specs = true ->
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs Hcheck.
  unfold check_inter_array_reuseb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hlive & Hreuse) & Hcompat).
  constructor.
  - apply check_live_conflictb_sound.
    exact Hlive.
  - apply check_conflict_safe_reuseb_sound.
    exact Hreuse.
  - apply check_storage_compatibilityb_sound.
    exact Hcompat.
Qed.

Theorem inter_array_reuse_sources_nodup :
  forall mapping intervals conflicts logical_specs physical_specs,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    NoDup (reuse_mapping_sources mapping).
Proof.
  intros mapping intervals conflicts logical_specs physical_specs Hobligations.
  destruct Hobligations as [_ Hreuse _].
  destruct Hreuse as [Hnodup _].
  exact Hnodup.
Qed.

Theorem inter_array_storage_mapping_compatible :
  forall mapping intervals conflicts logical_specs physical_specs,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    storage_mapping_compatible mapping logical_specs physical_specs.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs Hobligations.
  destruct Hobligations as [_ _ Hcompat].
  destruct Hcompat as [_ _ Hmapping_compatible].
  exact Hmapping_compatible.
Qed.

Theorem inter_array_reuse_boundary_obligations :
  forall mapping intervals conflicts logical_specs physical_specs,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    reuse_boundary_obligations mapping (reuse_mapping_sources mapping).
Proof.
  intros mapping intervals conflicts logical_specs physical_specs Hobligations.
  destruct Hobligations as [_ Hreuse _].
  eapply conflict_safe_reuse_boundary_obligations.
  exact Hreuse.
Qed.

Theorem inter_array_mapping_pair_cell_relation :
  forall mapping intervals conflicts logical_specs physical_specs
         logical_cell physical_cell,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    In (logical_cell, physical_cell) mapping ->
    reuse_cell_relation mapping physical_cell logical_cell.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs
         logical_cell physical_cell Hobligations Hin.
  unfold reuse_cell_relation.
  eapply reuse_lookup_complete_nodup.
  - eapply inter_array_reuse_sources_nodup; eauto.
  - exact Hin.
Qed.

Theorem inter_array_mapping_entry_compatible_specs :
  forall mapping intervals conflicts logical_specs physical_specs mapping_entry,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    In mapping_entry mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = fst mapping_entry /\
      storage_spec_cell physical_spec = snd mapping_entry /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs mapping_entry
         Hobligations Hin.
  destruct Hobligations as [_ _ Hcompatible].
  eapply storage_compatibility_mapping_entry_specs; eauto.
Qed.

Theorem inter_array_mapping_pair_compatible_specs :
  forall mapping intervals conflicts logical_specs physical_specs
         logical_cell physical_cell,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    In (logical_cell, physical_cell) mapping ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs
         logical_cell physical_cell Hobligations Hin.
  pose proof
    (inter_array_mapping_entry_compatible_specs
       mapping intervals conflicts logical_specs physical_specs
       (logical_cell, physical_cell) Hobligations Hin)
    as (logical_spec & physical_spec & Hlogical_in & Hphysical_in &
        Hlogical_cell & Hphysical_cell & Hspecs).
  exists logical_spec, physical_spec.
  simpl in Hlogical_cell, Hphysical_cell.
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

Theorem inter_array_lookup_compatible_specs :
  forall mapping intervals conflicts logical_specs physical_specs
         logical_cell physical_cell,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    reuse_lookup logical_cell mapping = Some physical_cell ->
    exists logical_spec physical_spec,
      In logical_spec logical_specs /\
      In physical_spec physical_specs /\
      storage_spec_cell logical_spec = logical_cell /\
      storage_spec_cell physical_spec = physical_cell /\
      storage_specs_compatible logical_spec physical_spec.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs
         logical_cell physical_cell Hobligations Hlookup.
  pose proof
    (reuse_lookup_sound logical_cell physical_cell mapping Hlookup)
    as [Hin | (logical_cell' & Hin & Heq)].
  - eapply inter_array_mapping_pair_compatible_specs; eauto.
  - subst logical_cell'.
    eapply inter_array_mapping_pair_compatible_specs; eauto.
Qed.

Theorem inter_array_live_overlaps_reuse_separated :
  forall mapping intervals conflicts logical_specs physical_specs,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    live_overlaps_reuse_separated mapping intervals.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs Hobligations.
  destruct Hobligations as [Hlive Hreuse _].
  eapply live_conflict_and_conflict_safe_reuse_sound; eauto.
Qed.

Theorem inter_array_overlap_mapped_distinct :
  forall mapping intervals conflicts logical_specs physical_specs
         left right physical_left physical_right,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    In left intervals ->
    In right intervals ->
    li_cell left <> li_cell right ->
    live_interval_overlap left right ->
    reuse_lookup (li_cell left) mapping = Some physical_left ->
    reuse_lookup (li_cell right) mapping = Some physical_right ->
    physical_left <> physical_right.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs
         left right physical_left physical_right
         Hobligations Hin_left Hin_right Hcells_distinct Hoverlap
         Hlookup_left Hlookup_right.
  pose proof
    (inter_array_live_overlaps_reuse_separated
       mapping intervals conflicts logical_specs physical_specs Hobligations)
    as Hseparated.
  specialize
    (Hseparated left right
       Hin_left Hin_right Hcells_distinct Hoverlap).
  destruct Hseparated
    as (mapped_left & mapped_right &
        Hmapped_left & Hmapped_right & Hmapped_distinct).
  rewrite Hlookup_left in Hmapped_left.
  inversion Hmapped_left; subst.
  rewrite Hlookup_right in Hmapped_right.
  inversion Hmapped_right; subst.
  exact Hmapped_distinct.
Qed.

Theorem inter_array_same_physical_not_live_overlap :
  forall mapping intervals conflicts logical_specs physical_specs
         left right physical_cell,
    inter_array_reuse_obligations
      mapping intervals conflicts logical_specs physical_specs ->
    In left intervals ->
    In right intervals ->
    li_cell left <> li_cell right ->
    reuse_lookup (li_cell left) mapping = Some physical_cell ->
    reuse_lookup (li_cell right) mapping = Some physical_cell ->
    ~ live_interval_overlap left right.
Proof.
  intros mapping intervals conflicts logical_specs physical_specs
         left right physical_cell Hobligations Hin_left Hin_right
         Hcells_distinct Hlookup_left Hlookup_right Hoverlap.
  pose proof
    (inter_array_overlap_mapped_distinct
       mapping intervals conflicts logical_specs physical_specs
       left right physical_cell physical_cell
       Hobligations Hin_left Hin_right Hcells_distinct Hoverlap
       Hlookup_left Hlookup_right)
    as Hdistinct.
  contradiction Hdistinct.
  reflexivity.
Qed.
