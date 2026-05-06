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
