Require Import SPolIRs.
Require Import List.
Require Import Linalg.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt SPolIRs.
Module SVal := CoreOpt.Validator.

Definition codegen (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  let '(pis, varctxt, vars) := pol in
  let n :=
    fold_right Nat.max 0
      (map (fun pi => Linalg.poly_nrl pi.(SPolIRs.PolyLang.pi_poly)) pis) in
  BIND loop <- CoreOpt.CodeGen.complete_generate_many (length varctxt) n pis -;
  pure (loop, varctxt, vars).

Definition opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  fun loop =>
    BIND pol <- res_to_alarm SPolIRs.PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
    BIND pol' <- CoreOpt.scheduler' pol -;
    codegen pol'.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  BIND pol' <- CoreOpt.scheduler' pol -;
  codegen pol'.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
