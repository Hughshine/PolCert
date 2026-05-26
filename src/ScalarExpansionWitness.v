Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** Finite witness for scalar privatization / scalar expansion.

    A source scalar cell may be reused by many dynamic instances.  Expansion
    rewrites each dynamic class, here represented by [(logical_instance,
    source_cell)], to a target-private cell.  This checker is deliberately
    local: it records consistency of that remapping, freshness of expanded
    cells, declaration coverage, and write-before-read on the target-private
    trace.  The expression-level proof that the private write computes the same
    value as the source scalar definition remains a separate semantic
    obligation. *)

Record scalar_expansion_entry := {
  expansion_instance : logical_instance;
  expansion_source_cell : MemCell;
  expansion_private_cell : MemCell;
}.

Definition scalar_expansion_key := (logical_instance * MemCell)%type.

Definition scalar_expansion_entry_key
    (entry: scalar_expansion_entry) : scalar_expansion_key :=
  (expansion_instance entry, expansion_source_cell entry).

Definition scalar_expansion_key_eqb
    (left right: scalar_expansion_key) : bool :=
  logical_instance_eqb (fst left) (fst right) &&
  mem_cell_strict_eqb (snd left) (snd right).

Lemma scalar_expansion_key_eqb_eq :
  forall left right,
    scalar_expansion_key_eqb left right = true ->
    left = right.
Proof.
  intros [left_instance left_cell] [right_instance right_cell] Hcheck.
  unfold scalar_expansion_key_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hinstance Hcell].
  apply logical_instance_eqb_eq in Hinstance.
  apply mem_cell_strict_eqb_eq in Hcell.
  subst. reflexivity.
Qed.

Lemma scalar_expansion_key_eq_eqb :
  forall left right,
    left = right ->
    scalar_expansion_key_eqb left right = true.
Proof.
  intros [left_instance left_cell] [right_instance right_cell] Heq.
  inversion Heq; subst.
  unfold scalar_expansion_key_eqb.
  simpl.
  rewrite logical_instance_eq_eqb with (i2 := right_instance).
  - rewrite mem_cell_strict_eq_eqb with (c2 := right_cell).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Definition scalar_expansion_key_inb
    (key: scalar_expansion_key)
    (keys: list scalar_expansion_key) : bool :=
  existsb (scalar_expansion_key_eqb key) keys.

Lemma scalar_expansion_key_inb_sound :
  forall key keys,
    scalar_expansion_key_inb key keys = true ->
    In key keys.
Proof.
  unfold scalar_expansion_key_inb.
  intros key keys Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (key' & Hin & Heq).
  apply scalar_expansion_key_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma scalar_expansion_key_inb_complete :
  forall key keys,
    In key keys ->
    scalar_expansion_key_inb key keys = true.
Proof.
  unfold scalar_expansion_key_inb.
  intros key keys Hin.
  apply existsb_exists.
  exists key.
  split.
  - exact Hin.
  - apply scalar_expansion_key_eq_eqb.
    reflexivity.
Qed.

Fixpoint scalar_expansion_keys_nodupb
    (keys: list scalar_expansion_key) : bool :=
  match keys with
  | [] => true
  | key :: tail =>
      negb (scalar_expansion_key_inb key tail) &&
      scalar_expansion_keys_nodupb tail
  end.

Lemma scalar_expansion_keys_nodupb_sound :
  forall keys,
    scalar_expansion_keys_nodupb keys = true ->
    NoDup keys.
Proof.
  induction keys as [|key tail IH]; intros Hcheck; simpl in Hcheck.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    apply negb_true_iff in Hnotin.
    constructor.
    + intro Hin.
      apply scalar_expansion_key_inb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + apply IH.
      exact Htail.
Qed.

Fixpoint scalar_expansion_lookup
    (instance: logical_instance)
    (source_cell: MemCell)
    (entries: list scalar_expansion_entry) : option MemCell :=
  match entries with
  | [] => None
  | entry :: tail =>
      if scalar_expansion_key_eqb
           (instance, source_cell)
           (scalar_expansion_entry_key entry)
      then Some (expansion_private_cell entry)
      else scalar_expansion_lookup instance source_cell tail
  end.

Lemma scalar_expansion_lookup_sound :
  forall entries instance source_cell private_cell,
    scalar_expansion_lookup
      instance source_cell entries = Some private_cell ->
    exists entry,
      In entry entries /\
      expansion_instance entry = instance /\
      expansion_source_cell entry = source_cell /\
      expansion_private_cell entry = private_cell.
Proof.
  induction entries as [|entry tail IH];
    intros instance source_cell private_cell Hlookup;
    simpl in Hlookup; try discriminate.
  destruct (scalar_expansion_key_eqb
              (instance, source_cell)
              (scalar_expansion_entry_key entry)) eqn:Hkey.
  - inversion Hlookup; subst.
    apply scalar_expansion_key_eqb_eq in Hkey.
    unfold scalar_expansion_entry_key in Hkey.
    destruct entry as [entry_instance entry_source entry_private].
    simpl in *.
    inversion Hkey; subst.
    exists {|
      expansion_instance := entry_instance;
      expansion_source_cell := entry_source;
      expansion_private_cell := entry_private;
    |}.
    simpl.
    repeat split; try reflexivity.
    left. reflexivity.
  - pose proof (IH instance source_cell private_cell Hlookup)
      as (found & Hin & Hinstance & Hsource & Hprivate).
    exists found.
    repeat split; auto.
    simpl. right. exact Hin.
Qed.

Fixpoint scalar_expansion_entry_keys
    (entries: list scalar_expansion_entry)
    : list scalar_expansion_key :=
  match entries with
  | [] => []
  | entry :: tail =>
      scalar_expansion_entry_key entry ::
      scalar_expansion_entry_keys tail
  end.

Fixpoint scalar_expansion_instances
    (entries: list scalar_expansion_entry)
    : list logical_instance :=
  match entries with
  | [] => []
  | entry :: tail =>
      expansion_instance entry :: scalar_expansion_instances tail
  end.

Fixpoint scalar_expansion_source_cells
    (entries: list scalar_expansion_entry)
    : list MemCell :=
  match entries with
  | [] => []
  | entry :: tail =>
      expansion_source_cell entry :: scalar_expansion_source_cells tail
  end.

Fixpoint scalar_expansion_private_cells
    (entries: list scalar_expansion_entry)
    : list MemCell :=
  match entries with
  | [] => []
  | entry :: tail =>
      expansion_private_cell entry :: scalar_expansion_private_cells tail
  end.

Inductive scalar_expansion_event_kind :=
| ExpansionWrite
| ExpansionRead.

Record scalar_expansion_event := {
  expansion_event_kind : scalar_expansion_event_kind;
  expansion_event_instance : logical_instance;
  expansion_event_source_cell : MemCell;
  expansion_event_private_cell : MemCell;
}.

Definition scalar_expansion_event_private_event
    (event: scalar_expansion_event) : private_event :=
  match expansion_event_kind event with
  | ExpansionWrite => PrivateWrite (expansion_event_private_cell event)
  | ExpansionRead => PrivateRead (expansion_event_private_cell event)
  end.

Fixpoint scalar_expansion_private_trace
    (events: list scalar_expansion_event) : list private_event :=
  match events with
  | [] => []
  | event :: tail =>
      scalar_expansion_event_private_event event ::
      scalar_expansion_private_trace tail
  end.

Definition scalar_expansion_event_mapped
    (entries: list scalar_expansion_entry)
    (event: scalar_expansion_event) : Prop :=
  scalar_expansion_lookup
    (expansion_event_instance event)
    (expansion_event_source_cell event)
    entries =
  Some (expansion_event_private_cell event).

Definition check_scalar_expansion_event_mappedb
    (entries: list scalar_expansion_entry)
    (event: scalar_expansion_event) : bool :=
  match scalar_expansion_lookup
          (expansion_event_instance event)
          (expansion_event_source_cell event)
          entries with
  | Some private_cell =>
      mem_cell_strict_eqb
        private_cell (expansion_event_private_cell event)
  | None => false
  end.

Lemma check_scalar_expansion_event_mappedb_sound :
  forall entries event,
    check_scalar_expansion_event_mappedb entries event = true ->
    scalar_expansion_event_mapped entries event.
Proof.
  intros entries event Hcheck.
  unfold check_scalar_expansion_event_mappedb in Hcheck.
  unfold scalar_expansion_event_mapped.
  destruct (scalar_expansion_lookup
              (expansion_event_instance event)
              (expansion_event_source_cell event)
              entries) as [private_cell|] eqn:Hlookup;
    try discriminate.
  apply mem_cell_strict_eqb_eq in Hcheck.
  subst. reflexivity.
Qed.

Fixpoint check_scalar_expansion_events_mappedb
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event) : bool :=
  match events with
  | [] => true
  | event :: tail =>
      check_scalar_expansion_event_mappedb entries event &&
      check_scalar_expansion_events_mappedb entries tail
  end.

Definition scalar_expansion_events_mapped
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event) : Prop :=
  forall event,
    In event events ->
    scalar_expansion_event_mapped entries event.

Lemma check_scalar_expansion_events_mappedb_sound :
  forall entries events,
    check_scalar_expansion_events_mappedb entries events = true ->
    scalar_expansion_events_mapped entries events.
Proof.
  unfold scalar_expansion_events_mapped.
  intros entries events.
  induction events as [|event tail IH]; intros Hcheck query_event Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply check_scalar_expansion_event_mappedb_sound.
      exact Hhead.
    + apply IH; auto.
Qed.

Record scalar_expansion_obligations
    (source_domain: list logical_instance)
    (source_cells private_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event) : Prop := {
  seo_instances_in_domain :
    forall instance,
      In instance (scalar_expansion_instances entries) ->
      In instance source_domain;
  seo_source_cells_declared :
    forall source_cell,
      In source_cell (scalar_expansion_source_cells entries) ->
      In source_cell source_cells;
  seo_private_cells_declared :
    forall private_cell,
      In private_cell (scalar_expansion_private_cells entries) ->
      In private_cell private_cells;
  seo_entry_keys_unique :
    NoDup (scalar_expansion_entry_keys entries);
  seo_private_cells_unique :
    NoDup (scalar_expansion_private_cells entries);
  seo_events_mapped :
    scalar_expansion_events_mapped entries events;
  seo_private_use_def :
    private_use_def_trace (scalar_expansion_private_trace events);
}.

Definition check_scalar_expansionb
    (source_domain: list logical_instance)
    (source_cells private_cells: list MemCell)
    (entries: list scalar_expansion_entry)
    (events: list scalar_expansion_event) : bool :=
  logical_instances_subsetb
    (scalar_expansion_instances entries) source_domain &&
  mem_cells_subsetb
    (scalar_expansion_source_cells entries) source_cells &&
  mem_cells_subsetb
    (scalar_expansion_private_cells entries) private_cells &&
  scalar_expansion_keys_nodupb
    (scalar_expansion_entry_keys entries) &&
  mem_cells_nodupb
    (scalar_expansion_private_cells entries) &&
  check_scalar_expansion_events_mappedb entries events &&
  check_private_use_def_traceb (scalar_expansion_private_trace events).

Lemma check_scalar_expansionb_sound :
  forall source_domain source_cells private_cells entries events,
    check_scalar_expansionb
      source_domain source_cells private_cells entries events = true ->
    scalar_expansion_obligations
      source_domain source_cells private_cells entries events.
Proof.
  intros source_domain source_cells private_cells entries events Hcheck.
  unfold check_scalar_expansionb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((((Hinstances & Hsources) & Hprivates) & Hkeys) & Hprivate_unique)
       & Hevents) & Husedef).
  constructor.
  - intros instance Hin.
    eapply logical_instances_subsetb_sound; eauto.
  - intros source_cell Hin.
    eapply mem_cells_subsetb_sound; eauto.
  - intros private_cell Hin.
    eapply mem_cells_subsetb_sound; eauto.
  - apply scalar_expansion_keys_nodupb_sound.
    exact Hkeys.
  - apply mem_cells_nodupb_sound.
    exact Hprivate_unique.
  - apply check_scalar_expansion_events_mappedb_sound.
    exact Hevents.
  - apply check_private_use_def_traceb_sound.
    exact Husedef.
Qed.

Lemma scalar_expansion_entry_private_cell_in :
  forall entries entry,
    In entry entries ->
    In (expansion_private_cell entry)
       (scalar_expansion_private_cells entries).
Proof.
  induction entries as [|head tail IH]; intros entry Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst. left. reflexivity.
    + right. apply IH. exact Hin_tail.
Qed.

Theorem scalar_expansion_event_uses_declared_private :
  forall source_domain source_cells private_cells entries events event,
    scalar_expansion_obligations
      source_domain source_cells private_cells entries events ->
    In event events ->
    In (expansion_event_private_cell event) private_cells.
Proof.
  intros source_domain source_cells private_cells entries events event
         Hobligations Hin_event.
  destruct Hobligations as
    [_ _ Hprivate_declared _ _ Hevents _].
  unfold scalar_expansion_events_mapped in Hevents.
  unfold scalar_expansion_event_mapped in Hevents.
  pose proof (Hevents event Hin_event) as Hlookup.
  apply scalar_expansion_lookup_sound in Hlookup.
  destruct Hlookup as
    (entry & Hin_entry & _ & _ & Hprivate).
  rewrite <- Hprivate.
  apply Hprivate_declared.
  eapply scalar_expansion_entry_private_cell_in.
  exact Hin_entry.
Qed.

Theorem scalar_expansion_events_same_key_same_private :
  forall source_domain source_cells private_cells entries events left right,
    scalar_expansion_obligations
      source_domain source_cells private_cells entries events ->
    In left events ->
    In right events ->
    expansion_event_instance left = expansion_event_instance right ->
    expansion_event_source_cell left = expansion_event_source_cell right ->
    expansion_event_private_cell left = expansion_event_private_cell right.
Proof.
  intros source_domain source_cells private_cells entries events left right
         Hobligations Hin_left Hin_right Hinstance Hsource.
  destruct Hobligations as
    [_ _ _ _ _ Hevents _].
  unfold scalar_expansion_events_mapped in Hevents.
  unfold scalar_expansion_event_mapped in Hevents.
  pose proof (Hevents left Hin_left) as Hleft.
  pose proof (Hevents right Hin_right) as Hright.
  rewrite <- Hinstance in Hright.
  rewrite <- Hsource in Hright.
  rewrite Hleft in Hright.
  inversion Hright.
  reflexivity.
Qed.
