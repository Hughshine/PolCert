Require Import SPolIRs.
Require Import TilingBandScheduleValidator.
Require Import TilingWitness.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreBandSched := TilingBandScheduleValidator SPolIRs.

Definition check_pprog_permutable_tiling_bands :=
  CoreBandSched.check_pprog_permutable_tiling_bands_via_validate_tiling.

Definition checked_tiling_schedule_stripmined_validate_poly :=
  CoreBandSched.checked_tiling_schedule_stripmined_validate_poly.

Definition infer_pprog_tiling_bands :=
  CoreBandSched.infer_pprog_tiling_bands.

Definition outer_to_tiling_pprog :=
  CoreBandSched.Base.outer_to_tiling_pprog.
