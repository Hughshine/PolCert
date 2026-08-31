Require Import InstrTy.
Require Import PolyLang.
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import ISSWitness.
Require Import TilingWitness.

Module Type POLIRS.

Declare Module Instr : INSTR.
Module State := Instr.State.
Module Ty := Instr.Ty.
Module PolyLang := PolyLang Instr.
Module PolyLoop := PolyLoop Instr.
Module Loop := Loop Instr.

Parameter scheduler: PolyLang.t -> result PolyLang.t.
(** Clear alias: the legacy [scheduler] field is the affine-only scheduler
    contract used by the old validated pipeline. *)
Definition affine_scheduler := scheduler.

Parameter export_for_phase_scheduler: PolyLang.t -> option OpenScop.
(** Export a program to the OpenScop view consumed by the external two-stage
    Pluto phase pipeline (affine phase, then tiling phase). *)
Definition export_for_pluto_phase_pipeline := export_for_phase_scheduler.
(** Compatibility alias kept for the old, less descriptive name. *)
Definition to_phase_openscop := export_for_phase_scheduler.

Parameter phase_scop_scheduler: OpenScop -> result (OpenScop * OpenScop).
(** Clear alias: run the external two-stage Pluto phase pipeline and return the
    affine mid-point and the final tiled OpenScop. *)
Definition run_pluto_phase_pipeline := phase_scop_scheduler.

Parameter identity_tiling_phase_scop_scheduler:
  OpenScop -> result (OpenScop * OpenScop).
(** Variant of the phase pipeline for Pluto [--identity --tile].  The returned
    midpoint is the source OpenScop, while the final OpenScop is the tile-only
    Pluto output. *)
Definition run_pluto_identity_tiling_pipeline :=
  identity_tiling_phase_scop_scheduler.

Parameter phase_scop_scheduler_with_iss:
  OpenScop -> result (OpenScop * OpenScop).
(** Variant of the external Pluto phase pipeline that enables ISS before the
    affine scheduling and tiling stages. *)
Definition run_pluto_phase_pipeline_with_iss := phase_scop_scheduler_with_iss.

Parameter post_tiling_affine_phase_scop_scheduler:
  OpenScop -> result (OpenScop * (OpenScop * OpenScop)).
(** Variant of the external Pluto phase pipeline that exposes the post_tiling_affine
    midpoint, the post-tiling schedule, and the final rescheduled OpenScop.
    The nested product keeps the extraction ABI explicit. *)
Definition run_pluto_post_tiling_affine_phase_pipeline :=
  post_tiling_affine_phase_scop_scheduler.

Parameter post_tiling_affine_phase_scop_scheduler_with_iss:
  OpenScop -> result (OpenScop * (OpenScop * OpenScop)).
(** ISS-enabled variant of the post_tiling_affine phase pipeline.  The verified route
    still validates the ISS bridge and each affine/tiling boundary before using
    the oracle-produced OpenScop schedules. *)
Definition run_pluto_post_tiling_affine_phase_pipeline_with_iss :=
  post_tiling_affine_phase_scop_scheduler_with_iss.

Parameter infer_iss_from_source_scop:
  PolyLang.t -> OpenScop -> result (option (PolyLang.t * iss_witness)).

Parameter infer_tiling_witness_scops:
  OpenScop -> OpenScop -> result (list statement_tiling_witness).


End POLIRS.
