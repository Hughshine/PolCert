Require Import SPolIRs.
Require Import TilingCanonicalScheduleValidator.
Require Import TilingWitness.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CanonicalSched := TilingCanonicalScheduleValidator SPolIRs.

Definition checked_tiling_schedule_canonical_validate :=
  CanonicalSched.checked_tiling_schedule_canonical_validate_poly.
