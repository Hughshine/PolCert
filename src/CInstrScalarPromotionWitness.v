Require Import List.
Require Import ZArith.

Require Import CInstr.
Require Import PolyBase.
Require Import ScalarPromotionValueWitness.
Require Import ScalarPromotionWitness.
Require Import Values.

Import ListNotations.

(** CInstr-facing scalar promotion witnesses.

    [ScalarPromotionWitness] and [ScalarPromotionValueWitness] describe the
    storage protocol and value flow for scalar/register promotion abstractly.
    This file connects those events to concrete CInstr reads and writes.  The
    layer is intentionally still local: it proves that an ordered list of
    CInstr-derived load/read/write/store/global-write events discharges the
    generic scalar-promotion value-flow obligation. *)

Inductive cscalar_promotion_load_value_event
    (envv: list Z)
    (source_state target_before target_after: CInstr.State.t)
    (source_access scalar_access: CInstr.arr_access)
    (target_instr: CInstr.t)
    (target_expr: CInstr.expr)
    (ty: CInstr.Ty.basetype)
    : scalar_promotion_event ->
      scalar_promotion_value_event Values.val -> Prop :=
| CScalarPromotionLoadValueEvent :
    forall source_cell scalar_cell target_rcells source_value scalar_value,
      target_instr = CInstr.Iassign scalar_access target_expr ->
      CInstr.access_cell scalar_access envv scalar_cell ->
      CInstr.eval_expr
        (CInstr.Eaccess source_access ty)
        envv [source_cell] source_state source_value ->
      CInstr.eval_expr
        target_expr envv target_rcells target_before scalar_value ->
      CInstr.State.write_cell
        scalar_cell (CInstr.typeof_access scalar_access)
        scalar_value target_before target_after ->
      source_value = scalar_value ->
      cscalar_promotion_load_value_event
        envv source_state target_before target_after
        source_access scalar_access target_instr target_expr ty
        (PromotionLoad source_cell scalar_cell)
        (PromotionValueLoad source_value scalar_value).

Inductive cscalar_promotion_read_value_event
    (envv: list Z)
    (source_state target_state: CInstr.State.t)
    (source_access scalar_access: CInstr.arr_access)
    (ty: CInstr.Ty.basetype)
    : scalar_promotion_event ->
      scalar_promotion_value_event Values.val -> Prop :=
| CScalarPromotionReadValueEvent :
    forall source_cell scalar_cell source_value scalar_value,
      CInstr.eval_expr
        (CInstr.Eaccess source_access ty)
        envv [source_cell] source_state source_value ->
      CInstr.eval_expr
        (CInstr.Eaccess scalar_access ty)
        envv [scalar_cell] target_state scalar_value ->
      source_value = scalar_value ->
      cscalar_promotion_read_value_event
        envv source_state target_state source_access scalar_access ty
        (PromotionScalarRead scalar_cell)
        (PromotionValueRead scalar_value).

Inductive cscalar_promotion_write_value_event
    (envv: list Z)
    (source_before source_after target_before target_after: CInstr.State.t)
    (source_instr target_instr: CInstr.t)
    : scalar_promotion_event ->
      scalar_promotion_value_event Values.val -> Prop :=
| CScalarPromotionWriteValueEvent :
    forall source_access source_expr scalar_access target_expr
           source_cell scalar_cell source_rcells target_rcells
           source_value scalar_value,
      source_instr = CInstr.Iassign source_access source_expr ->
      target_instr = CInstr.Iassign scalar_access target_expr ->
      CInstr.access_cell source_access envv source_cell ->
      CInstr.access_cell scalar_access envv scalar_cell ->
      CInstr.eval_expr
        source_expr envv source_rcells source_before source_value ->
      CInstr.eval_expr
        target_expr envv target_rcells target_before scalar_value ->
      CInstr.State.write_cell
        source_cell (CInstr.typeof_access source_access)
        source_value source_before source_after ->
      CInstr.State.write_cell
        scalar_cell (CInstr.typeof_access scalar_access)
        scalar_value target_before target_after ->
      source_value = scalar_value ->
      cscalar_promotion_write_value_event
        envv source_before source_after target_before target_after
        source_instr target_instr
        (PromotionScalarWrite scalar_cell)
        (PromotionValueWrite scalar_value).

Inductive cscalar_promotion_store_value_event
    (envv: list Z)
    (target_before target_after: CInstr.State.t)
    (source_access scalar_access: CInstr.arr_access)
    (target_instr: CInstr.t)
    (store_expr: CInstr.expr)
    (ty: CInstr.Ty.basetype)
    : scalar_promotion_event ->
      scalar_promotion_value_event Values.val -> Prop :=
| CScalarPromotionStoreValueEvent :
    forall source_cell scalar_cell store_rcells scalar_value source_value,
      target_instr = CInstr.Iassign source_access store_expr ->
      CInstr.access_cell source_access envv source_cell ->
      CInstr.eval_expr
        (CInstr.Eaccess scalar_access ty)
        envv [scalar_cell] target_before scalar_value ->
      CInstr.eval_expr
        store_expr envv store_rcells target_before source_value ->
      CInstr.State.write_cell
        source_cell (CInstr.typeof_access source_access)
        source_value target_before target_after ->
      scalar_value = source_value ->
      cscalar_promotion_store_value_event
        envv target_before target_after source_access scalar_access
        target_instr store_expr ty
        (PromotionStore scalar_cell source_cell)
        (PromotionValueStore scalar_value source_value).

Inductive cscalar_promotion_global_write_value_event
    (envv: list Z)
    (before after: CInstr.State.t)
    (instr: CInstr.t)
    : scalar_promotion_event ->
      scalar_promotion_value_event Values.val -> Prop :=
| CScalarPromotionGlobalWriteValueEvent :
    forall access expr write_cell rcells value,
      instr = CInstr.Iassign access expr ->
      CInstr.access_cell access envv write_cell ->
      CInstr.eval_expr expr envv rcells before value ->
      CInstr.State.write_cell
        write_cell (CInstr.typeof_access access) value before after ->
      cscalar_promotion_global_write_value_event
        envv before after instr
        (PromotionGlobalWrite write_cell)
        PromotionValueGlobalWrite.

Theorem cscalar_promotion_load_singleton_value_flow_from :
  forall envv source_state target_before target_after
         source_access scalar_access target_instr target_expr ty
         event value_event current_scalar,
    cscalar_promotion_load_value_event
      envv source_state target_before target_after
      source_access scalar_access target_instr target_expr ty
      event value_event ->
    scalar_value_trace_simulates_from
      current_scalar [(event, value_event)].
Proof.
  intros envv source_state target_before target_after
         source_access scalar_access target_instr target_expr ty
         event value_event current_scalar Hload.
  inversion Hload; subst.
  simpl.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem cscalar_promotion_read_singleton_value_flow_from :
  forall envv source_state target_state source_access scalar_access ty
         event value_event current_value,
    cscalar_promotion_read_value_event
      envv source_state target_state source_access scalar_access ty
      event value_event ->
    value_event = PromotionValueRead current_value ->
    scalar_value_trace_simulates_from
      (Some current_value) [(event, value_event)].
Proof.
  intros envv source_state target_state source_access scalar_access ty
         event value_event current_value Hread Hvalue.
  inversion Hvalue; subst.
  inversion Hread; subst.
  simpl.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem cscalar_promotion_write_singleton_value_flow_from :
  forall envv source_before source_after target_before target_after
         source_instr target_instr event value_event current_value,
    cscalar_promotion_write_value_event
      envv source_before source_after target_before target_after
      source_instr target_instr event value_event ->
    scalar_value_trace_simulates_from
      (Some current_value) [(event, value_event)].
Proof.
  intros envv source_before source_after target_before target_after
         source_instr target_instr event value_event current_value Hwrite.
  inversion Hwrite; subst.
  simpl.
  exact I.
Qed.

Theorem cscalar_promotion_store_singleton_value_flow_from :
  forall envv target_before target_after source_access scalar_access
         target_instr store_expr ty event value_event current_value,
    cscalar_promotion_store_value_event
      envv target_before target_after source_access scalar_access
      target_instr store_expr ty event value_event ->
    value_event = PromotionValueStore current_value current_value ->
    scalar_value_trace_simulates_from
      (Some current_value) [(event, value_event)].
Proof.
  intros envv target_before target_after source_access scalar_access
         target_instr store_expr ty event value_event current_value
         Hstore Hvalue.
  inversion Hvalue; subst.
  inversion Hstore; subst.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exact I.
Qed.

Theorem cscalar_promotion_global_write_singleton_value_flow_from :
  forall envv before after instr event value_event current_scalar,
    cscalar_promotion_global_write_value_event
      envv before after instr event value_event ->
    scalar_value_trace_simulates_from
      current_scalar [(event, value_event)].
Proof.
  intros envv before after instr event value_event current_scalar Hglobal.
  inversion Hglobal; subst.
  simpl.
  exact I.
Qed.

Inductive cscalar_promotion_value_trace
    : option Values.val ->
      scalar_promotion_value_trace Values.val -> Prop :=
| CScalarPromotionValueTraceNil :
    forall current_scalar,
      cscalar_promotion_value_trace current_scalar []
| CScalarPromotionValueTraceLoad :
    forall current_scalar tail
           envv source_state target_before target_after
           source_access scalar_access target_instr target_expr ty
           event source_value scalar_value,
      cscalar_promotion_load_value_event
        envv source_state target_before target_after
        source_access scalar_access target_instr target_expr ty
        event (PromotionValueLoad source_value scalar_value) ->
      cscalar_promotion_value_trace (Some scalar_value) tail ->
      cscalar_promotion_value_trace
        current_scalar
        ((event, PromotionValueLoad source_value scalar_value) :: tail)
| CScalarPromotionValueTraceRead :
    forall current_value tail
           envv source_state target_state source_access scalar_access ty
           event,
      cscalar_promotion_read_value_event
        envv source_state target_state source_access scalar_access ty
        event (PromotionValueRead current_value) ->
      cscalar_promotion_value_trace (Some current_value) tail ->
      cscalar_promotion_value_trace
        (Some current_value)
        ((event, PromotionValueRead current_value) :: tail)
| CScalarPromotionValueTraceWrite :
    forall current_value tail
           envv source_before source_after target_before target_after
           source_instr target_instr event new_scalar_value,
      cscalar_promotion_write_value_event
        envv source_before source_after target_before target_after
        source_instr target_instr
        event (PromotionValueWrite new_scalar_value) ->
      cscalar_promotion_value_trace (Some new_scalar_value) tail ->
      cscalar_promotion_value_trace
        (Some current_value)
        ((event, PromotionValueWrite new_scalar_value) :: tail)
| CScalarPromotionValueTraceStore :
    forall current_value tail
           envv target_before target_after source_access scalar_access
           target_instr store_expr ty event,
      cscalar_promotion_store_value_event
        envv target_before target_after source_access scalar_access
        target_instr store_expr ty
        event (PromotionValueStore current_value current_value) ->
      cscalar_promotion_value_trace (Some current_value) tail ->
      cscalar_promotion_value_trace
        (Some current_value)
        ((event, PromotionValueStore current_value current_value) :: tail)
| CScalarPromotionValueTraceGlobalWrite :
    forall current_scalar tail envv before after instr event,
      cscalar_promotion_global_write_value_event
        envv before after instr event PromotionValueGlobalWrite ->
      cscalar_promotion_value_trace current_scalar tail ->
      cscalar_promotion_value_trace
        current_scalar
        ((event, PromotionValueGlobalWrite) :: tail).

Theorem cscalar_promotion_value_trace_sound_from :
  forall current_scalar trace,
    cscalar_promotion_value_trace current_scalar trace ->
    scalar_value_trace_simulates_from current_scalar trace.
Proof.
  intros current_scalar trace Htrace.
  induction Htrace.
  - exact I.
  - inversion H; subst.
    simpl.
    split.
    + auto.
    + exact IHHtrace.
  - inversion H; subst.
    simpl.
    split.
    + reflexivity.
    + exact IHHtrace.
  - inversion H; subst.
    simpl.
    exact IHHtrace.
  - inversion H; subst.
    simpl.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * exact IHHtrace.
  - inversion H; subst.
    simpl.
    exact IHHtrace.
Qed.

Definition cscalar_promotion_value_trace_simulates
    (trace: scalar_promotion_value_trace Values.val) : Prop :=
  cscalar_promotion_value_trace None trace.

Theorem cscalar_promotion_value_trace_sound :
  forall trace,
    cscalar_promotion_value_trace_simulates trace ->
    scalar_value_trace_simulates trace.
Proof.
  intros trace Htrace.
  unfold cscalar_promotion_value_trace_simulates in Htrace.
  unfold scalar_value_trace_simulates.
  eapply cscalar_promotion_value_trace_sound_from.
  exact Htrace.
Qed.

Theorem cscalar_promotion_value_trace_obligations :
  forall trace,
    cscalar_promotion_value_trace_simulates trace ->
    scalar_value_simulation_obligations Values.val trace.
Proof.
  intros trace Htrace.
  constructor.
  apply cscalar_promotion_value_trace_sound.
  exact Htrace.
Qed.
