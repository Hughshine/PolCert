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

Definition scheduler_normalized_validate
    (pol : SPolIRs.PolyLang.t) : imp SPolIRs.PolyLang.t :=
  match SPolIRs.PolyLang.to_openscop pol with
  | Some inscop =>
      match SPolIRs.scop_scheduler inscop with
      | Okk outscop =>
          match SPolIRs.PolyLang.from_openscop_complete inscop,
                SPolIRs.PolyLang.from_openscop_complete outscop,
                SPolIRs.PolyLang.from_openscop pol outscop with
          | Okk pol_before, Okk pol_after, Okk pol_sched =>
              BIND res <- SVal.validate pol_before pol_after -;
              if res then pure pol_sched
              else res_to_alarm pol (Err "Scheduler validation failed.")
          | _, _, Err msg => res_to_alarm pol (Err msg)
          | Err msg, _, _ => res_to_alarm pol (Err msg)
          | _, Err msg, _ => res_to_alarm pol (Err msg)
          end
      | Err msg => res_to_alarm pol (Err msg)
      end
  | None => res_to_alarm pol (Err "Transform pol to openscop failed")
  end.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol <- res_to_alarm SPolIRs.PolyLang.dummy (Extractor.extractor loop) -;
  BIND pol' <- scheduler_normalized_validate pol -;
  Prepare.prepared_codegen pol'.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  BIND pol' <- scheduler_normalized_validate pol -;
  Prepare.prepared_codegen pol'.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
