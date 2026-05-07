Require Import SPolIRs.
Require Import LoopUnroll.

Module CoreUnroll := LoopUnroll SPolIRs.

Definition const_unroll : SPolIRs.Loop.t -> SPolIRs.Loop.t :=
  CoreUnroll.const_unroll.

Definition const_unroll_changed : SPolIRs.Loop.t -> bool :=
  CoreUnroll.const_unroll_changed.

Definition peel_unroll : nat -> SPolIRs.Loop.t -> SPolIRs.Loop.t :=
  CoreUnroll.peel_unroll.

Definition peel_unroll_changed : nat -> SPolIRs.Loop.t -> bool :=
  CoreUnroll.peel_unroll_changed.

Definition peel_plan : Type :=
  CoreUnroll.peel_plan.

Definition prefix_peel_plan : nat -> SPolIRs.Loop.expr -> peel_plan :=
  CoreUnroll.prefix_peel_plan.

Definition check_peel_plan : SPolIRs.Loop.expr -> SPolIRs.Loop.expr -> peel_plan -> bool :=
  CoreUnroll.check_peel_plan.

Definition checked_lower_peel_plan_stmt :
    peel_plan -> SPolIRs.Loop.expr -> SPolIRs.Loop.expr -> SPolIRs.Loop.stmt ->
    option SPolIRs.Loop.stmt :=
  CoreUnroll.checked_lower_peel_plan_stmt.
