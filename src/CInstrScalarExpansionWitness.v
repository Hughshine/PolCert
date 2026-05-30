Require Import List.
Require Import ZArith.

Require Import CInstr.
Require Import InstanceProjectionWitness.
Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import ScalarExpansionWitness.
Require Import ScalarExpansionValueWitness.
Require Import Values.

Import ListNotations.

(** CInstr-facing scalar expansion event witnesses.

    [ScalarExpansionWitness] and [ScalarExpansionValueWitness] are finite,
    storage-oriented witnesses.  This file starts connecting them to concrete
    instruction semantics without pretending that C expression equivalence is
    already solved.

    The layer is intentionally local.  It says how a pair of source/target
    [Iassign] semantic steps can justify one expansion write event, and how a
    pair of source/target scalar reads can justify one expansion read event.
    A later pass-level proof still has to derive such local witnesses for all
    relevant instructions in schedule order. *)

Definition cscalar_expansion_write_event
    (instance: logical_instance)
    (source_cell private_cell: MemCell) : scalar_expansion_event := {|
  expansion_event_kind := ExpansionWrite;
  expansion_event_instance := instance;
  expansion_event_source_cell := source_cell;
  expansion_event_private_cell := private_cell;
|}.

Definition cscalar_expansion_read_event
    (instance: logical_instance)
    (source_cell private_cell: MemCell) : scalar_expansion_event := {|
  expansion_event_kind := ExpansionRead;
  expansion_event_instance := instance;
  expansion_event_source_cell := source_cell;
  expansion_event_private_cell := private_cell;
|}.

Inductive cassign_scalar_expansion_write_value_event
    (entries: list scalar_expansion_entry)
    (instance: logical_instance)
    (envv: list Z)
    (source_before source_after private_before private_after: CInstr.State.t)
    (source_instr private_instr: CInstr.t)
    : scalar_expansion_event ->
      scalar_expansion_value_event Values.val -> Prop :=
| CAssignScalarExpansionWriteValueEvent :
    forall source_access source_expr private_access private_expr
           source_cell private_cell source_rcells private_rcells
           source_value private_value,
      source_instr = CInstr.Iassign source_access source_expr ->
      private_instr = CInstr.Iassign private_access private_expr ->
      CInstr.access_cell source_access envv source_cell ->
      CInstr.access_cell private_access envv private_cell ->
      CInstr.eval_expr
        source_expr envv source_rcells source_before source_value ->
      CInstr.eval_expr
        private_expr envv private_rcells private_before private_value ->
      CInstr.State.write_cell
        source_cell (CInstr.typeof_access source_access)
        source_value source_before source_after ->
      CInstr.State.write_cell
        private_cell (CInstr.typeof_access private_access)
        private_value private_before private_after ->
      scalar_expansion_lookup instance source_cell entries =
        Some private_cell ->
      source_value = private_value ->
      cassign_scalar_expansion_write_value_event
        entries instance envv source_before source_after
        private_before private_after source_instr private_instr
        (cscalar_expansion_write_event instance source_cell private_cell)
        (ExpansionValueWrite source_value private_value).

Theorem cassign_scalar_expansion_write_event_mapped :
  forall entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event,
    cassign_scalar_expansion_write_value_event
      entries instance envv source_before source_after
      private_before private_after source_instr private_instr
      event value_event ->
    scalar_expansion_event_mapped entries event.
Proof.
  intros entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event Hwrite.
  inversion Hwrite; subst.
  unfold scalar_expansion_event_mapped.
  simpl.
  exact H7.
Qed.

Theorem cassign_scalar_expansion_write_value_kind :
  forall entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event,
    cassign_scalar_expansion_write_value_event
      entries instance envv source_before source_after
      private_before private_after source_instr private_instr
      event value_event ->
    scalar_expansion_value_event_kind_matches event value_event.
Proof.
  intros entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event Hwrite.
  inversion Hwrite; subst.
  simpl. exact I.
Qed.

Theorem cassign_scalar_expansion_write_has_cinstr_semantics :
  forall entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event,
    cassign_scalar_expansion_write_value_event
      entries instance envv source_before source_after
      private_before private_after source_instr private_instr
      event value_event ->
    exists source_cell private_cell source_rcells private_rcells,
      CInstr.semantics
        source_instr envv [source_cell] source_rcells
        source_before source_after /\
      CInstr.semantics
        private_instr envv [private_cell] private_rcells
        private_before private_after /\
      event =
        cscalar_expansion_write_event instance source_cell private_cell.
Proof.
  intros entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event Hwrite.
  inversion Hwrite; subst.
  exists source_cell, private_cell, source_rcells, private_rcells.
  repeat split; try reflexivity.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Theorem cassign_scalar_expansion_write_singleton_value_flow_from :
  forall entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event current_values,
    cassign_scalar_expansion_write_value_event
      entries instance envv source_before source_after
      private_before private_after source_instr private_instr
      event value_event ->
    scalar_expansion_value_trace_simulates_from
      current_values [(event, value_event)].
Proof.
  intros entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event current_values Hwrite.
  inversion Hwrite; subst.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exact I.
Qed.

Theorem cassign_scalar_expansion_write_singleton_value_flow :
  forall entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event,
    cassign_scalar_expansion_write_value_event
      entries instance envv source_before source_after
      private_before private_after source_instr private_instr
      event value_event ->
    scalar_expansion_value_trace_simulates
      [(event, value_event)].
Proof.
  intros entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event value_event Hwrite.
  apply cassign_scalar_expansion_write_singleton_value_flow_from
    with (current_values := []) in Hwrite.
  exact Hwrite.
Qed.

Inductive caccess_scalar_expansion_read_value_event
    (entries: list scalar_expansion_entry)
    (instance: logical_instance)
    (envv: list Z)
    (source_state private_state: CInstr.State.t)
    (source_access private_access: CInstr.arr_access)
    (ty: CInstr.Ty.basetype)
    : scalar_expansion_event ->
      scalar_expansion_value_event Values.val -> Prop :=
| CAccessScalarExpansionReadValueEvent :
    forall source_cell private_cell source_value private_value,
      CInstr.eval_expr
        (CInstr.Eaccess source_access ty)
        envv [source_cell] source_state source_value ->
      CInstr.eval_expr
        (CInstr.Eaccess private_access ty)
        envv [private_cell] private_state private_value ->
      scalar_expansion_lookup instance source_cell entries =
        Some private_cell ->
      source_value = private_value ->
      caccess_scalar_expansion_read_value_event
        entries instance envv source_state private_state
        source_access private_access ty
        (cscalar_expansion_read_event instance source_cell private_cell)
        (ExpansionValueRead source_value private_value).

Theorem caccess_scalar_expansion_read_event_mapped :
  forall entries instance envv source_state private_state
         source_access private_access ty event value_event,
    caccess_scalar_expansion_read_value_event
      entries instance envv source_state private_state
      source_access private_access ty event value_event ->
    scalar_expansion_event_mapped entries event.
Proof.
  intros entries instance envv source_state private_state
         source_access private_access ty event value_event Hread.
  inversion Hread; subst.
  unfold scalar_expansion_event_mapped.
  simpl.
  exact H1.
Qed.

Theorem caccess_scalar_expansion_read_value_kind :
  forall entries instance envv source_state private_state
         source_access private_access ty event value_event,
    caccess_scalar_expansion_read_value_event
      entries instance envv source_state private_state
      source_access private_access ty event value_event ->
    scalar_expansion_value_event_kind_matches event value_event.
Proof.
  intros entries instance envv source_state private_state
         source_access private_access ty event value_event Hread.
  inversion Hread; subst.
  simpl. exact I.
Qed.

Theorem caccess_scalar_expansion_read_singleton_value_flow_from :
  forall entries instance envv source_state private_state
         source_access private_access ty event value_event
         current_values current_value,
    caccess_scalar_expansion_read_value_event
      entries instance envv source_state private_state
      source_access private_access ty event value_event ->
    lookup_expanded_value
      (expansion_event_private_cell event) current_values =
      Some current_value ->
    value_event = ExpansionValueRead current_value current_value ->
    scalar_expansion_value_trace_simulates_from
      current_values [(event, value_event)].
Proof.
  intros entries instance envv source_state private_state
         source_access private_access ty event value_event
         current_values current_value Hread Hlookup Hvalue_event.
  inversion Hvalue_event; subst.
  inversion Hread; subst.
  simpl in Hlookup.
  simpl.
  rewrite Hlookup.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * exact I.
Qed.

Theorem caccess_scalar_expansion_read_singleton_value_flow_from_current :
  forall entries instance envv source_state private_state
         source_access private_access ty event value_event current_value,
    caccess_scalar_expansion_read_value_event
      entries instance envv source_state private_state
      source_access private_access ty event value_event ->
    value_event = ExpansionValueRead current_value current_value ->
    scalar_expansion_value_trace_simulates_from
      [(expansion_event_private_cell event, current_value)]
      [(event, value_event)].
Proof.
  intros entries instance envv source_state private_state
         source_access private_access ty event value_event current_value
         Hread Hvalue_event.
  eapply caccess_scalar_expansion_read_singleton_value_flow_from.
  - exact Hread.
  - simpl.
    rewrite mem_cell_strict_eq_eqb
      with (c2 := expansion_event_private_cell event).
    + reflexivity.
    + reflexivity.
  - exact Hvalue_event.
Qed.

(** Event-level CInstr provenance.

    The ordered trace below is the object consumed by the generic scalar
    expansion value-flow validator.  This predicate exposes what each trace
    event came from without forcing later proofs to re-induct over the trace
    structure. *)
Inductive cscalar_expansion_value_event_cinstr_semantics
    (entries: list scalar_expansion_entry)
    : scalar_expansion_event ->
      scalar_expansion_value_event Values.val -> Prop :=
| CScalarExpansionWriteEventCInstrSemantics :
    forall instance envv source_before source_after
           private_before private_after source_instr private_instr
           event value_event,
      cassign_scalar_expansion_write_value_event
        entries instance envv source_before source_after
        private_before private_after source_instr private_instr
        event value_event ->
      cscalar_expansion_value_event_cinstr_semantics
        entries event value_event
| CScalarExpansionReadEventCInstrSemantics :
    forall instance envv source_state private_state
           source_access private_access ty event value_event,
      caccess_scalar_expansion_read_value_event
        entries instance envv source_state private_state
        source_access private_access ty event value_event ->
      cscalar_expansion_value_event_cinstr_semantics
        entries event value_event.

Theorem cscalar_expansion_value_event_cinstr_mapped :
  forall entries event value_event,
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event ->
    scalar_expansion_event_mapped entries event.
Proof.
  intros entries event value_event Hsem.
  inversion Hsem; subst.
  - eapply cassign_scalar_expansion_write_event_mapped.
    exact H.
  - eapply caccess_scalar_expansion_read_event_mapped.
    exact H.
Qed.

Theorem cscalar_expansion_value_event_cinstr_kind :
  forall entries event value_event,
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event ->
    scalar_expansion_value_event_kind_matches event value_event.
Proof.
  intros entries event value_event Hsem.
  inversion Hsem; subst.
  - eapply cassign_scalar_expansion_write_value_kind.
    exact H.
  - eapply caccess_scalar_expansion_read_value_kind.
    exact H.
Qed.

Theorem cscalar_expansion_value_event_cinstr_values_match :
  forall entries event value_event,
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event ->
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros entries event value_event Hsem.
  inversion Hsem; subst.
  - inversion H; subst.
    simpl.
    reflexivity.
  - inversion H; subst.
    simpl.
    reflexivity.
Qed.

Theorem cscalar_expansion_value_event_cinstr_mapped_and_matched :
  forall entries event value_event,
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event ->
    scalar_expansion_event_mapped entries event /\
    scalar_expansion_value_event_kind_matches event value_event /\
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros entries event value_event Hsem.
  split.
  - eapply cscalar_expansion_value_event_cinstr_mapped.
    exact Hsem.
  - split.
    + eapply cscalar_expansion_value_event_cinstr_kind.
      exact Hsem.
    + eapply cscalar_expansion_value_event_cinstr_values_match.
      exact Hsem.
Qed.

Theorem cscalar_expansion_value_event_cinstr_write_values_equal :
  forall entries event source_value private_value,
    cscalar_expansion_value_event_cinstr_semantics
      entries event (ExpansionValueWrite source_value private_value) ->
    source_value = private_value.
Proof.
  intros entries event source_value private_value Hsem.
  pose proof
    (cscalar_expansion_value_event_cinstr_values_match
       entries event (ExpansionValueWrite source_value private_value)
       Hsem)
    as Hvalues.
  simpl in Hvalues.
  exact Hvalues.
Qed.

Theorem cscalar_expansion_value_event_cinstr_read_values_equal :
  forall entries event source_value private_value,
    cscalar_expansion_value_event_cinstr_semantics
      entries event (ExpansionValueRead source_value private_value) ->
    source_value = private_value.
Proof.
  intros entries event source_value private_value Hsem.
  pose proof
    (cscalar_expansion_value_event_cinstr_values_match
       entries event (ExpansionValueRead source_value private_value)
       Hsem)
    as Hvalues.
  simpl in Hvalues.
  exact Hvalues.
Qed.

(** Ordered trace layer.

    The singleton lemmas above justify one CInstr read or write event.  The
    pass-level scalar-privatization proof will need to thread the current
    private values through many such events in schedule order.  The following
    witness is still local to CInstr, but it is no longer a one-step fact: it
    records an ordered list of CInstr-derived scalar expansion events and
    proves that the list discharges the generic value-flow obligation. *)

Inductive cscalar_expansion_value_trace
    (entries: list scalar_expansion_entry)
    : list (MemCell * Values.val) ->
      scalar_expansion_value_trace Values.val -> Prop :=
| CScalarExpansionValueTraceNil :
    forall current_values,
      cscalar_expansion_value_trace entries current_values []
| CScalarExpansionValueTraceWrite :
    forall current_values tail
           instance envv source_before source_after
           private_before private_after source_instr private_instr
           event source_value private_value,
      cassign_scalar_expansion_write_value_event
        entries instance envv source_before source_after
        private_before private_after source_instr private_instr
        event (ExpansionValueWrite source_value private_value) ->
      cscalar_expansion_value_trace
        entries
        (update_expanded_value
           (expansion_event_private_cell event)
           private_value current_values)
        tail ->
      cscalar_expansion_value_trace
        entries current_values
        ((event, ExpansionValueWrite source_value private_value) :: tail)
| CScalarExpansionValueTraceRead :
    forall current_values tail current_value
           instance envv source_state private_state
           source_access private_access ty event,
      caccess_scalar_expansion_read_value_event
        entries instance envv source_state private_state
        source_access private_access ty
        event (ExpansionValueRead current_value current_value) ->
      lookup_expanded_value
        (expansion_event_private_cell event) current_values =
        Some current_value ->
      cscalar_expansion_value_trace entries current_values tail ->
      cscalar_expansion_value_trace
        entries current_values
        ((event, ExpansionValueRead current_value current_value) :: tail).

Theorem cscalar_expansion_value_trace_sound_from :
  forall entries current_values trace,
    cscalar_expansion_value_trace entries current_values trace ->
    scalar_expansion_value_trace_simulates_from current_values trace.
Proof.
  intros entries current_values trace Htrace.
  induction Htrace.
  - exact I.
  - pose proof
      (cassign_scalar_expansion_write_singleton_value_flow_from
         entries instance envv source_before source_after
         private_before private_after source_instr private_instr
         event (ExpansionValueWrite source_value private_value)
         current_values H)
      as Hsingle.
    simpl in Hsingle.
    destruct Hsingle as [Hkind [Hvalue _]].
    simpl.
    split.
    + exact Hkind.
    + split.
      * exact Hvalue.
      * exact IHHtrace.
  - pose proof
      (caccess_scalar_expansion_read_singleton_value_flow_from
         entries instance envv source_state private_state
         source_access private_access ty
         event (ExpansionValueRead current_value current_value)
         current_values current_value H H0 eq_refl)
      as Hsingle.
    simpl in Hsingle.
    destruct Hsingle as [Hkind _].
    simpl.
    split.
    + exact Hkind.
    + rewrite H0.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- exact IHHtrace.
Qed.

Theorem cscalar_expansion_value_trace_event_cinstr_semantics :
  forall entries current_values trace event value_event,
    cscalar_expansion_value_trace entries current_values trace ->
    In (event, value_event) trace ->
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event.
Proof.
  intros entries current_values trace event value_event Htrace Hin.
  induction Htrace.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      econstructor.
      exact H.
    + apply IHHtrace.
      exact Hin_tail.
  - simpl in Hin.
    destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      econstructor 2.
      exact H.
    + apply IHHtrace.
      exact Hin_tail.
Qed.

Definition cscalar_expansion_value_trace_simulates
    (entries: list scalar_expansion_entry)
    (trace: scalar_expansion_value_trace Values.val) : Prop :=
  cscalar_expansion_value_trace entries [] trace.

Theorem cscalar_expansion_value_trace_sound :
  forall entries trace,
    cscalar_expansion_value_trace_simulates entries trace ->
    scalar_expansion_value_trace_simulates trace.
Proof.
  intros entries trace Htrace.
  unfold cscalar_expansion_value_trace_simulates in Htrace.
  unfold scalar_expansion_value_trace_simulates.
  eapply cscalar_expansion_value_trace_sound_from.
  exact Htrace.
Qed.

Theorem cscalar_expansion_value_trace_obligations :
  forall entries trace,
    cscalar_expansion_value_trace_simulates entries trace ->
    scalar_expansion_value_obligations Values.val trace.
Proof.
  intros entries trace Htrace.
  constructor.
  apply (cscalar_expansion_value_trace_sound entries).
  exact Htrace.
Qed.

Theorem cscalar_expansion_value_trace_events_mapped :
  forall entries current_values trace,
    cscalar_expansion_value_trace entries current_values trace ->
    scalar_expansion_events_mapped
      entries (scalar_expansion_value_trace_events trace).
Proof.
  intros entries current_values trace Htrace.
  induction Htrace.
  - unfold scalar_expansion_events_mapped.
    intros event Hin.
    simpl in Hin. contradiction.
  - unfold scalar_expansion_events_mapped in *.
    intros query_event Hin.
    simpl in Hin.
    destruct Hin as [Heq | Hin_tail].
    + subst.
      eapply cassign_scalar_expansion_write_event_mapped.
      exact H.
    + apply IHHtrace.
      exact Hin_tail.
  - unfold scalar_expansion_events_mapped in *.
    intros query_event Hin.
    simpl in Hin.
    destruct Hin as [Heq | Hin_tail].
    + subst.
      eapply caccess_scalar_expansion_read_event_mapped.
      exact H.
    + apply IHHtrace.
      exact Hin_tail.
Qed.

Theorem cscalar_expansion_value_trace_sound_and_mapped :
  forall entries trace,
    cscalar_expansion_value_trace_simulates entries trace ->
    scalar_expansion_value_obligations Values.val trace /\
    scalar_expansion_events_mapped
      entries (scalar_expansion_value_trace_events trace).
Proof.
  intros entries trace Htrace.
  split.
  - apply (cscalar_expansion_value_trace_obligations entries).
    exact Htrace.
  - unfold cscalar_expansion_value_trace_simulates in Htrace.
    eapply cscalar_expansion_value_trace_events_mapped.
    exact Htrace.
Qed.

Theorem cscalar_expansion_value_trace_private_use_def :
  forall entries trace,
    cscalar_expansion_value_trace_simulates entries trace ->
    private_use_def_trace
      (scalar_expansion_private_trace
         (scalar_expansion_value_trace_events trace)).
Proof.
  intros entries trace Htrace.
  apply scalar_expansion_value_trace_private_use_def
    with (value := Values.val).
  apply cscalar_expansion_value_trace_sound
    with (entries := entries).
  exact Htrace.
Qed.

Theorem cscalar_expansion_value_trace_sound_mapped_and_usedef :
  forall entries trace,
    cscalar_expansion_value_trace_simulates entries trace ->
    scalar_expansion_value_obligations Values.val trace /\
    scalar_expansion_events_mapped
      entries (scalar_expansion_value_trace_events trace) /\
    private_use_def_trace
      (scalar_expansion_private_trace
         (scalar_expansion_value_trace_events trace)).
Proof.
  intros entries trace Htrace.
  split.
  - apply (cscalar_expansion_value_trace_obligations entries).
    exact Htrace.
  - split.
    + unfold cscalar_expansion_value_trace_simulates in Htrace.
      eapply cscalar_expansion_value_trace_events_mapped.
      exact Htrace.
    + eapply cscalar_expansion_value_trace_private_use_def.
      exact Htrace.
Qed.

Theorem cscalar_expansion_value_trace_event_mapped_and_matched :
  forall entries current_values trace event value_event,
    cscalar_expansion_value_trace entries current_values trace ->
    In (event, value_event) trace ->
    scalar_expansion_event_mapped entries event /\
    scalar_expansion_value_event_kind_matches event value_event /\
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros entries current_values trace event value_event Htrace Hin.
  pose proof
    (cscalar_expansion_value_trace_events_mapped
       entries current_values trace Htrace)
    as Hmapped.
  pose proof
    (cscalar_expansion_value_trace_sound_from
       entries current_values trace Htrace)
    as Hsimulates.
  pose proof
    (scalar_expansion_value_trace_pair_event_in_events
       Values.val trace event value_event Hin)
    as Hin_event.
  pose proof
    (scalar_expansion_value_trace_simulates_from_event_matched
       Values.val trace current_values event value_event
       Hsimulates Hin)
    as [Hkind Hvalues].
  split.
  - unfold scalar_expansion_events_mapped in Hmapped.
    exact (Hmapped event Hin_event).
  - split; assumption.
Qed.

Theorem cscalar_expansion_value_trace_event_cinstr_and_matched :
  forall entries current_values trace event value_event,
    cscalar_expansion_value_trace entries current_values trace ->
    In (event, value_event) trace ->
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event /\
    scalar_expansion_event_mapped entries event /\
    scalar_expansion_value_event_kind_matches event value_event /\
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros entries current_values trace event value_event Htrace Hin.
  pose proof
    (cscalar_expansion_value_trace_event_cinstr_semantics
       entries current_values trace event value_event Htrace Hin)
    as Hcinstr.
  pose proof
    (cscalar_expansion_value_event_cinstr_mapped_and_matched
       entries event value_event Hcinstr)
    as [Hmapped [Hkind Hvalues]].
  repeat split; assumption.
Qed.

Theorem cscalar_expansion_value_trace_event_write_values_equal :
  forall entries current_values trace event source_value private_value,
    cscalar_expansion_value_trace entries current_values trace ->
    In (event, ExpansionValueWrite source_value private_value) trace ->
    source_value = private_value.
Proof.
  intros entries current_values trace event source_value private_value
         Htrace Hin.
  pose proof
    (cscalar_expansion_value_trace_event_cinstr_and_matched
       entries current_values trace event
       (ExpansionValueWrite source_value private_value)
       Htrace Hin)
    as [_ [_ [_ Hvalues]]].
  simpl in Hvalues.
  exact Hvalues.
Qed.

Theorem cscalar_expansion_value_trace_event_read_values_equal :
  forall entries current_values trace event source_value private_value,
    cscalar_expansion_value_trace entries current_values trace ->
    In (event, ExpansionValueRead source_value private_value) trace ->
    source_value = private_value.
Proof.
  intros entries current_values trace event source_value private_value
         Htrace Hin.
  pose proof
    (cscalar_expansion_value_trace_event_cinstr_and_matched
       entries current_values trace event
       (ExpansionValueRead source_value private_value)
       Htrace Hin)
    as [_ [_ [_ Hvalues]]].
  simpl in Hvalues.
  exact Hvalues.
Qed.

Theorem cscalar_expansion_value_trace_simulates_event_cinstr_and_matched :
  forall entries trace event value_event,
    cscalar_expansion_value_trace_simulates entries trace ->
    In (event, value_event) trace ->
    cscalar_expansion_value_event_cinstr_semantics
      entries event value_event /\
    scalar_expansion_event_mapped entries event /\
    scalar_expansion_value_event_kind_matches event value_event /\
    scalar_expansion_value_event_values_match value_event.
Proof.
  intros entries trace event value_event Htrace Hin.
  unfold cscalar_expansion_value_trace_simulates in Htrace.
  eapply cscalar_expansion_value_trace_event_cinstr_and_matched; eauto.
Qed.

Theorem cscalar_expansion_value_trace_simulates_event_write_values_equal :
  forall entries trace event source_value private_value,
    cscalar_expansion_value_trace_simulates entries trace ->
    In (event, ExpansionValueWrite source_value private_value) trace ->
    source_value = private_value.
Proof.
  intros entries trace event source_value private_value Htrace Hin.
  unfold cscalar_expansion_value_trace_simulates in Htrace.
  eapply cscalar_expansion_value_trace_event_write_values_equal; eauto.
Qed.

Theorem cscalar_expansion_value_trace_simulates_event_read_values_equal :
  forall entries trace event source_value private_value,
    cscalar_expansion_value_trace_simulates entries trace ->
    In (event, ExpansionValueRead source_value private_value) trace ->
    source_value = private_value.
Proof.
  intros entries trace event source_value private_value Htrace Hin.
  unfold cscalar_expansion_value_trace_simulates in Htrace.
  eapply cscalar_expansion_value_trace_event_read_values_equal; eauto.
Qed.
