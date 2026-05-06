Require Import SPolIRs.
Require Import LoopUnroll.

Module CoreUnroll := LoopUnroll SPolIRs.

Definition const_unroll : SPolIRs.Loop.t -> SPolIRs.Loop.t :=
  CoreUnroll.const_unroll.

Definition const_unroll_changed : SPolIRs.Loop.t -> bool :=
  CoreUnroll.const_unroll_changed.
