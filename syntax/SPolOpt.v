Require Import SPolIRs.
Require Import List.
Require Import Linalg.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import PolOptPrepared.
Require Import PrepareCodegen.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Local Open Scope string_scope.

Module CoreOpt := PolOpt SPolIRs.
Module PreparedOpt := PolOptPrepared SPolIRs.
Module Prepare := PrepareCodegen SPolIRs.
Module SVal := CoreOpt.Validator.
Module Extractor := CoreOpt.Extractor.

Definition opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  PreparedOpt.Opt.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  BIND pol' <- CoreOpt.scheduler' pol -;
  Prepare.prepared_codegen pol'.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
