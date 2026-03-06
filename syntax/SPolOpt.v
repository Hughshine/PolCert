Require Import SPolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt SPolIRs.
Module SVal := CoreOpt.Validator.

Definition opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreOpt.Opt.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  BIND pol' <- CoreOpt.scheduler' pol -;
  CoreOpt.CodeGen.codegen pol'.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
