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
  inversion Hwrite; subst.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exact I.
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
  inversion Hvalue_event; subst.
  inversion Hread; subst.
  simpl.
  rewrite mem_cell_strict_eq_eqb with (c2 := private_cell).
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- exact I.
  - reflexivity.
Qed.
