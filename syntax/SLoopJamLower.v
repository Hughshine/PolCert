Require Import SPolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import LoopJamLower.

Module CoreLoopJamLower := LoopJamLower SPolIRs.

Definition try_jam_pair := CoreLoopJamLower.try_jam_pair.

Definition jam_stmt : SPolIRs.Loop.stmt -> SPolIRs.Loop.stmt :=
  CoreLoopJamLower.jam_stmt.

Definition jam_stmt_changed : SPolIRs.Loop.stmt -> bool :=
  CoreLoopJamLower.jam_stmt_changed.

Definition jam_loop : SPolIRs.Loop.t -> SPolIRs.Loop.t :=
  CoreLoopJamLower.jam_loop.

Definition jam_loop_changed : SPolIRs.Loop.t -> bool :=
  CoreLoopJamLower.jam_loop_changed.

Definition unrolljam_stmt : nat -> SPolIRs.Loop.stmt -> SPolIRs.Loop.stmt :=
  CoreLoopJamLower.unrolljam_stmt.

Definition unrolljam_loop : nat -> SPolIRs.Loop.t -> SPolIRs.Loop.t :=
  CoreLoopJamLower.unrolljam_loop.

Definition checked_unrolljam_loop :
  nat -> SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreLoopJamLower.checked_unrolljam_loop.
