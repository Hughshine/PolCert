Require Import SPolIRs.
Require Import LoopJamValidator.

Module CoreLoopJamValidator := LoopJamValidator SPolIRs.

Definition checked_loop_jam_current :=
  CoreLoopJamValidator.checked_loop_jam_current.

Definition loop_jam_cert_sound :=
  CoreLoopJamValidator.loop_jam_cert_sound.
