Require Import TPolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt TPolIRs.
Module TVal := CoreOpt.Validator.

Definition opt : TPolIRs.Loop.t -> imp TPolIRs.Loop.t :=
  CoreOpt.Opt.

Definition opt_poly (pol: TPolIRs.PolyLang.t): imp TPolIRs.Loop.t :=
  BIND pol' <- CoreOpt.scheduler' pol -;
  CoreOpt.CodeGen.codegen pol'.

Definition opt_scop (scop: OpenScop): imp TPolIRs.Loop.t :=
  match TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm TPolIRs.Loop.dummy (Err msg)
  end.
