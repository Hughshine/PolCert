Require Import SPolIRs.
Require Import JamValidator.

Module CoreJamValidator := JamValidator SPolIRs.

Definition checked_jam_current :=
  CoreJamValidator.checked_jam_current.

Definition adjacent_jam_plan_well_formedb :=
  CoreJamValidator.adjacent_jam_plan_well_formedb.

Definition check_pprog_adjacent_jamb :=
  CoreJamValidator.check_pprog_adjacent_jamb.
