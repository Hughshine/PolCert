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

Definition proved_opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  PreparedOpt.Opt.

Definition validated_schedule (pol : SPolIRs.PolyLang.t) : imp SPolIRs.PolyLang.t :=
  match SPolIRs.PolyLang.to_openscop pol with
  | Some inscop =>
      match SPolIRs.scop_scheduler inscop with
      | Okk outscop =>
          BIND pol_validate_old <-
            res_to_alarm SPolIRs.PolyLang.dummy
              (SPolIRs.PolyLang.from_openscop_complete inscop) -;
          BIND pol_validate_new <-
            res_to_alarm SPolIRs.PolyLang.dummy
              (SPolIRs.PolyLang.from_openscop_complete outscop) -;
          BIND ok <- SVal.validate pol_validate_old pol_validate_new -;
          if ok
          then
            res_to_alarm SPolIRs.PolyLang.dummy
              (SPolIRs.PolyLang.from_openscop_like_source pol outscop)
          else
            res_to_alarm pol (Err "Scheduler validation failed.")
      | Err msg => res_to_alarm pol (Err msg)
      end
  | None => res_to_alarm pol (Err "Transform pol to openscop failed")
  end.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol <- res_to_alarm SPolIRs.PolyLang.dummy (Extractor.extractor loop) -;
  BIND pol' <- validated_schedule pol -;
  Prepare.prepared_codegen pol'.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  BIND pol' <- validated_schedule pol -;
  Prepare.prepared_codegen pol'.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
