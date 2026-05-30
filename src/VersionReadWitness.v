Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** Finite read-selection witness for versioned storage.

    [VersionCommitWitness] checks which target versions are committed at the
    fragment boundary.  Array expansion/versioning also has an internal
    obligation: each target read must select the version produced by the source
    write that the corresponding source read should observe.

    Dynamic producer/read identities are represented as [logical_instance]s,
    while the selected target storage is a [MemCell].  This keeps repeated
    writes to the same logical cell at different dynamic instances distinct,
    without changing the endpoint [State.eq] pipeline. *)

Definition produced_version_mapping := list (logical_instance * MemCell).

Definition version_read_producer
    (entry: logical_instance * MemCell) : logical_instance :=
  fst entry.

Definition version_read_version
    (entry: logical_instance * MemCell) : MemCell :=
  snd entry.

Fixpoint produced_version_versions
    (produced_versions: produced_version_mapping) : list MemCell :=
  match produced_versions with
  | [] => []
  | entry :: tail =>
      version_read_version entry ::
      produced_version_versions tail
  end.

Record version_read_entry := {
  vre_read_instance : logical_instance;
  vre_expected_producer : logical_instance;
  vre_selected_version : MemCell;
}.

Definition produced_version_pair_eqb
    (left right: logical_instance * MemCell) : bool :=
  logical_instance_eqb (version_read_producer left)
    (version_read_producer right) &&
  mem_cell_strict_eqb (version_read_version left)
    (version_read_version right).

Lemma produced_version_pair_eqb_eq :
  forall left right,
    produced_version_pair_eqb left right = true ->
    left = right.
Proof.
  intros [left_producer left_version] [right_producer right_version] Hcheck.
  unfold produced_version_pair_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hproducer Hversion].
  apply logical_instance_eqb_eq in Hproducer.
  apply mem_cell_strict_eqb_eq in Hversion.
  subst. reflexivity.
Qed.

Definition produced_version_pair_inb
    (entry: logical_instance * MemCell)
    (produced_versions: produced_version_mapping) : bool :=
  existsb (produced_version_pair_eqb entry) produced_versions.

Lemma produced_version_pair_inb_sound :
  forall entry produced_versions,
    produced_version_pair_inb entry produced_versions = true ->
    In entry produced_versions.
Proof.
  unfold produced_version_pair_inb.
  intros entry produced_versions Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (entry' & Hin & Heq).
  apply produced_version_pair_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma produced_version_pair_version_in_versions :
  forall produced_versions producer version,
    In (producer, version) produced_versions ->
    In version (produced_version_versions produced_versions).
Proof.
  induction produced_versions as [|entry tail IH];
    intros producer version Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst. left. reflexivity.
    + right. eapply IH; eauto.
Qed.

Definition version_read_entry_eqb
    (left right: version_read_entry) : bool :=
  logical_instance_eqb
    (vre_read_instance left)
    (vre_read_instance right) &&
  logical_instance_eqb
    (vre_expected_producer left)
    (vre_expected_producer right) &&
  mem_cell_strict_eqb
    (vre_selected_version left)
    (vre_selected_version right).

Lemma version_read_entry_eqb_eq :
  forall left right,
    version_read_entry_eqb left right = true ->
    left = right.
Proof.
  intros [left_read left_producer left_version]
         [right_read right_producer right_version] Hcheck.
  unfold version_read_entry_eqb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hread & Hproducer) & Hversion).
  apply logical_instance_eqb_eq in Hread.
  apply logical_instance_eqb_eq in Hproducer.
  apply mem_cell_strict_eqb_eq in Hversion.
  subst. reflexivity.
Qed.

Fixpoint version_read_entries_cover
    (expected_reads: list logical_instance)
    (entries: list version_read_entry) : Prop :=
  match expected_reads, entries with
  | [], [] => True
  | expected_read :: expected_tail, entry :: entry_tail =>
      expected_read = vre_read_instance entry /\
      version_read_entries_cover expected_tail entry_tail
  | _, _ => False
  end.

Fixpoint check_version_read_entries_coverb
    (expected_reads: list logical_instance)
    (entries: list version_read_entry) : bool :=
  match expected_reads, entries with
  | [], [] => true
  | expected_read :: expected_tail, entry :: entry_tail =>
      logical_instance_eqb expected_read (vre_read_instance entry) &&
      check_version_read_entries_coverb expected_tail entry_tail
  | _, _ => false
  end.

Fixpoint version_read_entries_select_producers
    (produced_versions: produced_version_mapping)
    (entries: list version_read_entry) : Prop :=
  match entries with
  | [] => True
  | entry :: tail =>
      In (vre_expected_producer entry, vre_selected_version entry)
        produced_versions /\
      version_read_entries_select_producers produced_versions tail
  end.

Fixpoint check_version_read_entries_select_producersb
    (produced_versions: produced_version_mapping)
    (entries: list version_read_entry) : bool :=
  match entries with
  | [] => true
  | entry :: tail =>
      produced_version_pair_inb
        (vre_expected_producer entry, vre_selected_version entry)
        produced_versions &&
      check_version_read_entries_select_producersb produced_versions tail
  end.

Record version_read_selection_obligations
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (entries: list version_read_entry) : Prop := {
  vrso_reads_covered :
    version_read_entries_cover expected_reads entries;
  vrso_selected_versions_produced :
    version_read_entries_select_producers produced_versions entries;
}.

Lemma check_version_read_entries_coverb_sound :
  forall expected_reads entries,
    check_version_read_entries_coverb expected_reads entries = true ->
    version_read_entries_cover expected_reads entries.
Proof.
  induction expected_reads as [|expected_read expected_tail IH];
    intros entries Hcheck;
    destruct entries as [|entry entry_tail]; simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hread Htail].
    split.
    + apply logical_instance_eqb_eq.
      exact Hread.
    + apply IH.
      exact Htail.
Qed.

Lemma check_version_read_entries_select_producersb_sound :
  forall produced_versions entries,
    check_version_read_entries_select_producersb
      produced_versions entries = true ->
    version_read_entries_select_producers produced_versions entries.
Proof.
  intros produced_versions entries.
  induction entries as [|entry tail IH]; intros Hcheck; simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    split.
    + apply produced_version_pair_inb_sound.
      exact Hhead.
    + apply IH.
      exact Htail.
Qed.

Lemma version_read_entries_cover_length :
  forall expected_reads entries,
    version_read_entries_cover expected_reads entries ->
    length expected_reads = length entries.
Proof.
  induction expected_reads as [|expected_read expected_tail IH];
    intros entries Hcover;
    destruct entries as [|entry entry_tail];
    simpl in Hcover |- *; try contradiction.
  - reflexivity.
  - destruct Hcover as [_ Htail].
    simpl.
    rewrite IH with (entries := entry_tail); auto.
Qed.

Lemma version_read_entries_cover_read_in_expected :
  forall expected_reads entries entry,
    version_read_entries_cover expected_reads entries ->
    In entry entries ->
    In (vre_read_instance entry) expected_reads.
Proof.
  induction expected_reads as [|expected_read expected_tail IH];
    intros entries entry Hcover Hin;
    destruct entries as [|entry_head entry_tail];
    simpl in Hcover, Hin |- *; try contradiction.
  destruct Hcover as [Hhead Htail].
  destruct Hin as [Heq | Hin_tail].
  - subst entry.
    left. exact Hhead.
  - right.
    eapply IH; eauto.
Qed.

Lemma version_read_entries_selected_pair_in_produced_versions :
  forall produced_versions entries entry,
    version_read_entries_select_producers produced_versions entries ->
    In entry entries ->
    In (vre_expected_producer entry, vre_selected_version entry)
      produced_versions.
Proof.
  intros produced_versions entries.
  induction entries as [|head tail IH];
    intros entry Hselect Hin;
    simpl in Hselect, Hin.
  - contradiction.
  - destruct Hselect as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma version_read_entries_selected_version_in_produced_versions :
  forall produced_versions entries entry,
    version_read_entries_select_producers produced_versions entries ->
    In entry entries ->
    In (vre_selected_version entry)
      (produced_version_versions produced_versions).
Proof.
  intros produced_versions entries.
  induction entries as [|head tail IH]; intros entry Hselect Hin;
    simpl in Hselect, Hin.
  - contradiction.
  - destruct Hselect as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      eapply produced_version_pair_version_in_versions; eauto.
    + eapply IH; eauto.
Qed.

Definition check_version_read_selectionb
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (entries: list version_read_entry) : bool :=
  check_version_read_entries_coverb expected_reads entries &&
  check_version_read_entries_select_producersb produced_versions entries.

Lemma check_version_read_selectionb_sound :
  forall expected_reads produced_versions entries,
    check_version_read_selectionb
      expected_reads produced_versions entries = true ->
    version_read_selection_obligations
      expected_reads produced_versions entries.
Proof.
  intros expected_reads produced_versions entries Hcheck.
  unfold check_version_read_selectionb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcover Hselect].
  constructor.
  - apply check_version_read_entries_coverb_sound.
    exact Hcover.
  - apply check_version_read_entries_select_producersb_sound.
    exact Hselect.
Qed.

Theorem version_read_selected_version_in_produced_versions :
  forall expected_reads produced_versions entries entry,
    version_read_selection_obligations
      expected_reads produced_versions entries ->
    In entry entries ->
    In (vre_selected_version entry)
      (produced_version_versions produced_versions).
Proof.
  intros expected_reads produced_versions entries entry Hobligations Hin.
  destruct Hobligations as [_ Hselect].
  eapply version_read_entries_selected_version_in_produced_versions; eauto.
Qed.

Theorem version_read_selection_obligation_length_match :
  forall expected_reads produced_versions entries,
    version_read_selection_obligations
      expected_reads produced_versions entries ->
    length expected_reads = length entries.
Proof.
  intros expected_reads produced_versions entries Hobligations.
  destruct Hobligations as [Hcover _].
  eapply version_read_entries_cover_length; eauto.
Qed.

Theorem version_read_selection_obligation_read_in_expected :
  forall expected_reads produced_versions entries entry,
    version_read_selection_obligations
      expected_reads produced_versions entries ->
    In entry entries ->
    In (vre_read_instance entry) expected_reads.
Proof.
  intros expected_reads produced_versions entries entry Hobligations Hin.
  destruct Hobligations as [Hcover _].
  eapply version_read_entries_cover_read_in_expected; eauto.
Qed.

Theorem version_read_selection_obligation_produced_pair :
  forall expected_reads produced_versions entries entry,
    version_read_selection_obligations
      expected_reads produced_versions entries ->
    In entry entries ->
    In (vre_expected_producer entry, vre_selected_version entry)
      produced_versions.
Proof.
  intros expected_reads produced_versions entries entry Hobligations Hin.
  destruct Hobligations as [_ Hselect].
  eapply version_read_entries_selected_pair_in_produced_versions; eauto.
Qed.

Theorem check_version_read_selectionb_selected_version_in_produced_versions :
  forall expected_reads produced_versions entries entry,
    check_version_read_selectionb
      expected_reads produced_versions entries = true ->
    In entry entries ->
    In (vre_selected_version entry)
      (produced_version_versions produced_versions).
Proof.
  intros expected_reads produced_versions entries entry Hcheck Hin.
  eapply version_read_selected_version_in_produced_versions; eauto.
  apply check_version_read_selectionb_sound.
  exact Hcheck.
Qed.

Theorem check_version_read_selectionb_length_match :
  forall expected_reads produced_versions entries,
    check_version_read_selectionb
      expected_reads produced_versions entries = true ->
    length expected_reads = length entries.
Proof.
  intros expected_reads produced_versions entries Hcheck.
  eapply version_read_selection_obligation_length_match.
  apply check_version_read_selectionb_sound.
  exact Hcheck.
Qed.

Theorem check_version_read_selectionb_read_in_expected :
  forall expected_reads produced_versions entries entry,
    check_version_read_selectionb
      expected_reads produced_versions entries = true ->
    In entry entries ->
    In (vre_read_instance entry) expected_reads.
Proof.
  intros expected_reads produced_versions entries entry Hcheck Hin.
  eapply version_read_selection_obligation_read_in_expected; eauto.
  apply check_version_read_selectionb_sound.
  exact Hcheck.
Qed.

Theorem check_version_read_selectionb_produced_pair :
  forall expected_reads produced_versions entries entry,
    check_version_read_selectionb
      expected_reads produced_versions entries = true ->
    In entry entries ->
    In (vre_expected_producer entry, vre_selected_version entry)
      produced_versions.
Proof.
  intros expected_reads produced_versions entries entry Hcheck Hin.
  eapply version_read_selection_obligation_produced_pair; eauto.
  apply check_version_read_selectionb_sound.
  exact Hcheck.
Qed.

Record version_read_value_entry (value: Type) := {
  vrve_read_entry : version_read_entry;
  vrve_source_value : value;
  vrve_version_value : value;
}.

Arguments vrve_read_entry {value} _.
Arguments vrve_source_value {value} _.
Arguments vrve_version_value {value} _.

Fixpoint version_read_value_entries_match {value: Type}
    (entries: list version_read_entry)
    (value_entries: list (version_read_value_entry value)) : Prop :=
  match entries, value_entries with
  | [], [] => True
  | entry :: entry_tail, value_entry :: value_tail =>
      entry = vrve_read_entry value_entry /\
      vrve_source_value value_entry =
        vrve_version_value value_entry /\
      version_read_value_entries_match entry_tail value_tail
  | _, _ => False
  end.

Fixpoint check_version_read_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (entries: list version_read_entry)
    (value_entries: list (version_read_value_entry value)) : bool :=
  match entries, value_entries with
  | [], [] => true
  | entry :: entry_tail, value_entry :: value_tail =>
      version_read_entry_eqb entry (vrve_read_entry value_entry) &&
      value_eqb
        (vrve_source_value value_entry)
        (vrve_version_value value_entry) &&
      check_version_read_value_entriesb value_eqb entry_tail value_tail
  | _, _ => false
  end.

Record version_read_value_obligations
    (value: Type)
    (entries: list version_read_entry)
    (value_entries: list (version_read_value_entry value)) : Prop := {
  vrvo_entries_match :
    version_read_value_entries_match entries value_entries;
}.

Lemma check_version_read_value_entriesb_sound :
  forall (value: Type) (value_eqb: value -> value -> bool),
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    forall entries value_entries,
      check_version_read_value_entriesb
        value_eqb entries value_entries = true ->
      version_read_value_entries_match entries value_entries.
Proof.
  intros value value_eqb Hvalue_eqb entries.
  induction entries as [|entry entry_tail IH];
    intros value_entries Hcheck;
    destruct value_entries as [|value_entry value_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as ((Hentry & Hvalue) & Htail).
    split.
    + apply version_read_entry_eqb_eq.
      exact Hentry.
    + split.
      * apply Hvalue_eqb.
        exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Definition check_version_read_valueb {value: Type}
    (value_eqb: value -> value -> bool)
    (entries: list version_read_entry)
    (value_entries: list (version_read_value_entry value)) : bool :=
  check_version_read_value_entriesb value_eqb entries value_entries.

Lemma check_version_read_valueb_sound :
  forall (value: Type) (value_eqb: value -> value -> bool),
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    forall entries value_entries,
      check_version_read_valueb value_eqb entries value_entries = true ->
      version_read_value_obligations value entries value_entries.
Proof.
  intros value value_eqb Hvalue_eqb entries value_entries Hcheck.
  constructor.
  apply check_version_read_value_entriesb_sound with (value_eqb := value_eqb).
  - exact Hvalue_eqb.
  - exact Hcheck.
Qed.

Lemma version_read_value_entries_match_length :
  forall (value: Type)
         (entries: list version_read_entry)
         (value_entries: list (version_read_value_entry value)),
    version_read_value_entries_match entries value_entries ->
    length entries = length value_entries.
Proof.
  intros value entries.
  induction entries as [|entry entry_tail IH];
    intros value_entries Hmatch;
    destruct value_entries as [|value_entry value_tail];
    simpl in Hmatch |- *; try contradiction.
  - reflexivity.
  - destruct Hmatch as [_ [_ Htail]].
    simpl.
    rewrite IH with (value_entries := value_tail); auto.
Qed.

Lemma version_read_value_entries_match_entry :
  forall (value: Type)
         (entries: list version_read_entry)
         (value_entries: list (version_read_value_entry value))
         entry,
    version_read_value_entries_match entries value_entries ->
    In entry entries ->
    exists value_entry,
      In value_entry value_entries /\
      vrve_read_entry value_entry = entry /\
      vrve_source_value value_entry =
        vrve_version_value value_entry.
Proof.
  intros value entries.
  induction entries as [|entry_head entry_tail IH];
    intros value_entries entry Hmatch Hin;
    destruct value_entries as [|value_entry value_tail];
    simpl in Hmatch, Hin |- *; try contradiction.
  destruct Hmatch as [Hentry [Hvalue Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst entry.
    exists value_entry.
    split.
    + left. reflexivity.
    + split.
      * exact (eq_sym Hentry).
      * exact Hvalue.
  - destruct
      (IH value_tail entry Htail Hin_tail)
      as (tail_value_entry & Hin_value & Hentry_eq & Hvalue_eq).
    exists tail_value_entry.
    split.
    + right. exact Hin_value.
    + split; assumption.
Qed.

Lemma version_read_value_entries_match_value_entry :
  forall (value: Type)
         (entries: list version_read_entry)
         (value_entries: list (version_read_value_entry value))
         value_entry,
    version_read_value_entries_match entries value_entries ->
    In value_entry value_entries ->
    In (vrve_read_entry value_entry) entries /\
    vrve_source_value value_entry =
      vrve_version_value value_entry.
Proof.
  intros value entries.
  induction entries as [|entry_head entry_tail IH];
    intros value_entries value_entry Hmatch Hin;
    destruct value_entries as [|value_head value_tail];
    simpl in Hmatch, Hin |- *; try contradiction.
  destruct Hmatch as [Hentry [Hvalue Htail]].
  destruct Hin as [Heq | Hin_tail].
  - subst value_head.
    split.
    + left. exact Hentry.
    + exact Hvalue.
  - destruct
      (IH value_tail value_entry Htail Hin_tail)
      as [Hentry_in Hvalue_eq].
    split.
    + right. exact Hentry_in.
    + exact Hvalue_eq.
Qed.

Theorem version_read_value_obligation_length_match :
  forall (value: Type)
         (entries: list version_read_entry)
         (value_entries: list (version_read_value_entry value)),
    version_read_value_obligations value entries value_entries ->
    length entries = length value_entries.
Proof.
  intros value entries value_entries Hobligations.
  destruct Hobligations as [Hmatch].
  eapply version_read_value_entries_match_length.
  exact Hmatch.
Qed.

Theorem version_read_value_obligation_entry_matched :
  forall (value: Type)
         (entries: list version_read_entry)
         (value_entries: list (version_read_value_entry value))
         entry,
    version_read_value_obligations value entries value_entries ->
    In entry entries ->
    exists value_entry,
      In value_entry value_entries /\
      vrve_read_entry value_entry = entry /\
      vrve_source_value value_entry =
        vrve_version_value value_entry.
Proof.
  intros value entries value_entries entry Hobligations Hin.
  destruct Hobligations as [Hmatch].
  eapply version_read_value_entries_match_entry; eauto.
Qed.

Theorem version_read_value_obligation_value_entry_matched :
  forall (value: Type)
         (entries: list version_read_entry)
         (value_entries: list (version_read_value_entry value))
         value_entry,
    version_read_value_obligations value entries value_entries ->
    In value_entry value_entries ->
    In (vrve_read_entry value_entry) entries /\
    vrve_source_value value_entry =
      vrve_version_value value_entry.
Proof.
  intros value entries value_entries value_entry Hobligations Hin.
  destruct Hobligations as [Hmatch].
  eapply version_read_value_entries_match_value_entry; eauto.
Qed.

Theorem check_version_read_valueb_length_match :
  forall (value: Type)
         (value_eqb: value -> value -> bool),
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    forall entries value_entries,
      check_version_read_valueb value_eqb entries value_entries = true ->
      length entries = length value_entries.
Proof.
  intros value value_eqb Hsound entries value_entries Hcheck.
  eapply version_read_value_obligation_length_match.
  eapply check_version_read_valueb_sound; eauto.
Qed.

Theorem check_version_read_valueb_entry_matched :
  forall (value: Type)
         (value_eqb: value -> value -> bool),
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    forall entries value_entries entry,
      check_version_read_valueb value_eqb entries value_entries = true ->
      In entry entries ->
      exists value_entry,
        In value_entry value_entries /\
        vrve_read_entry value_entry = entry /\
        vrve_source_value value_entry =
          vrve_version_value value_entry.
Proof.
  intros value value_eqb Hsound entries value_entries entry Hcheck Hin.
  eapply version_read_value_obligation_entry_matched; eauto.
  eapply check_version_read_valueb_sound; eauto.
Qed.

Theorem check_version_read_valueb_value_entry_matched :
  forall (value: Type)
         (value_eqb: value -> value -> bool),
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    forall entries value_entries value_entry,
      check_version_read_valueb value_eqb entries value_entries = true ->
      In value_entry value_entries ->
      In (vrve_read_entry value_entry) entries /\
      vrve_source_value value_entry =
        vrve_version_value value_entry.
Proof.
  intros value value_eqb Hsound entries value_entries value_entry
         Hcheck Hin.
  eapply version_read_value_obligation_value_entry_matched; eauto.
  eapply check_version_read_valueb_sound; eauto.
Qed.
