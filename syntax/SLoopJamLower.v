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

Definition unrolljam_candidate : Type :=
  CoreLoopJamLower.unrolljam_candidate.

Definition make_unrolljam_candidate (depth : nat) : unrolljam_candidate :=
  CoreLoopJamLower.Build_unrolljam_candidate depth None.

Definition make_unrolljam_candidate_at_path
    (depth : nat) (path : list nat) : unrolljam_candidate :=
  CoreLoopJamLower.Build_unrolljam_candidate depth (Some path).

Definition unrolljam_all_depths_plan : nat -> list unrolljam_candidate :=
  CoreLoopJamLower.unrolljam_all_depths_plan.

Definition checked_unrolljam_loop_with_plan :
  list unrolljam_candidate -> nat -> SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreLoopJamLower.checked_unrolljam_loop_with_plan.

Definition checked_unrolljam_loop :
  nat -> SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreLoopJamLower.checked_unrolljam_loop.
