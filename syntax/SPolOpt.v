Require Import SPolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt SPolIRs.
Module Extractor := CoreOpt.Extractor.

Definition add_var_nodup := SPolIRs.add_var_nodup.
Definition export_pi_for_openscop := SPolIRs.export_pi_for_openscop.
Definition export_pprog_for_openscop := SPolIRs.export_pprog_for_openscop.
Definition to_source_openscop := SPolIRs.to_openscop_source.

Definition proved_opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreOpt.Opt.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  proved_opt loop.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  CoreOpt.phase_opt_prepared_from_poly (CoreOpt.Strengthen.strengthen_pprog pol).

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
