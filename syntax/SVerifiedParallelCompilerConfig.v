Require Import String.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import Result.
Require Import SPolIRs.
Require Import SVerifiedCompilerConfig.
Require Import SParallelPolOpt.

Local Open Scope impure_scope.
Local Open Scope string_scope.

Module ParallelLoop := SParallelPolOpt.ParallelLoop.
Module ParallelCodegenCore := SParallelPolOpt.ParallelCodegenCore.

Inductive raw_config : Type :=
| RawSeq (cfg: SVerifiedCompilerConfig.raw_config)
| RawParallelCurrentIdentity (d: nat)
| RawParallelCurrentIdentityTiled (d: nat)
| RawParallelCurrentAffine (d: nat)
| RawParallelCurrentDefault (d: nat)
| RawParallelCurrentDiamond (d: nat)
| RawParallelCurrentDiamondISS (d: nat)
| RawParallelCurrentIdentityISS (d: nat)
| RawParallelCurrentAffineISS (d: nat)
| RawParallelCurrentDefaultISS (d: nat)
| RawParallelCurrentManyIdentity (dims: list nat)
| RawParallelCurrentManyIdentityTiled (dims: list nat)
| RawParallelCurrentManyAffine (dims: list nat)
| RawParallelCurrentManyDefault (dims: list nat)
| RawParallelCurrentManyDiamond (dims: list nat)
| RawParallelCurrentManyDiamondISS (dims: list nat)
| RawParallelCurrentManyIdentityISS (dims: list nat)
| RawParallelCurrentManyAffineISS (dims: list nat)
| RawParallelCurrentManyDefaultISS (dims: list nat)
| RawUnsupported.

Inductive verified_config : Type :=
| VSeq (cfg: SVerifiedCompilerConfig.verified_config)
| VParallelCurrentIdentity (d: nat)
| VParallelCurrentIdentityTiled (d: nat)
| VParallelCurrentAffine (d: nat)
| VParallelCurrentDefault (d: nat)
| VParallelCurrentDiamond (d: nat)
| VParallelCurrentDiamondISS (d: nat)
| VParallelCurrentIdentityISS (d: nat)
| VParallelCurrentAffineISS (d: nat)
| VParallelCurrentDefaultISS (d: nat)
| VParallelCurrentManyIdentity (dims: list nat)
| VParallelCurrentManyIdentityTiled (dims: list nat)
| VParallelCurrentManyAffine (dims: list nat)
| VParallelCurrentManyDefault (dims: list nat)
| VParallelCurrentManyDiamond (dims: list nat)
| VParallelCurrentManyDiamondISS (dims: list nat)
| VParallelCurrentManyIdentityISS (dims: list nat)
| VParallelCurrentManyAffineISS (dims: list nat)
| VParallelCurrentManyDefaultISS (dims: list nat).

Definition check_config (cfg: raw_config) : result verified_config :=
  match cfg with
  | RawSeq seq_cfg =>
      match SVerifiedCompilerConfig.check_config seq_cfg with
      | Okk vcfg => Okk (VSeq vcfg)
      | Err msg => Err msg
      end
  | RawParallelCurrentIdentity d => Okk (VParallelCurrentIdentity d)
  | RawParallelCurrentIdentityTiled d => Okk (VParallelCurrentIdentityTiled d)
  | RawParallelCurrentAffine d => Okk (VParallelCurrentAffine d)
  | RawParallelCurrentDefault d => Okk (VParallelCurrentDefault d)
  | RawParallelCurrentDiamond d => Okk (VParallelCurrentDiamond d)
  | RawParallelCurrentDiamondISS d => Okk (VParallelCurrentDiamondISS d)
  | RawParallelCurrentIdentityISS d => Okk (VParallelCurrentIdentityISS d)
  | RawParallelCurrentAffineISS d => Okk (VParallelCurrentAffineISS d)
  | RawParallelCurrentDefaultISS d => Okk (VParallelCurrentDefaultISS d)
  | RawParallelCurrentManyIdentity dims => Okk (VParallelCurrentManyIdentity dims)
  | RawParallelCurrentManyIdentityTiled dims => Okk (VParallelCurrentManyIdentityTiled dims)
  | RawParallelCurrentManyAffine dims => Okk (VParallelCurrentManyAffine dims)
  | RawParallelCurrentManyDefault dims => Okk (VParallelCurrentManyDefault dims)
  | RawParallelCurrentManyDiamond dims => Okk (VParallelCurrentManyDiamond dims)
  | RawParallelCurrentManyDiamondISS dims => Okk (VParallelCurrentManyDiamondISS dims)
  | RawParallelCurrentManyIdentityISS dims => Okk (VParallelCurrentManyIdentityISS dims)
  | RawParallelCurrentManyAffineISS dims => Okk (VParallelCurrentManyAffineISS dims)
  | RawParallelCurrentManyDefaultISS dims => Okk (VParallelCurrentManyDefaultISS dims)
  | RawUnsupported => Err "unsupported verified compiler configuration"
  end.

Definition checked_lift_sequential_loop
    (loop: SPolIRs.Loop.t)
  : imp ParallelLoop.t :=
  let pl := ParallelCodegenCore.tag_loop loop in
  if ParallelCodegenCore.all_es_safeb pl then
    pure pl
  else
    res_to_alarm
      SParallelPolOpt.parallel_dummy
      (Err "sequential route produced a non-affine ParallelLoop trace"%string).

Definition lift_sequential_compile
    (compile: imp SPolIRs.Loop.t)
  : imp ParallelLoop.t :=
  BIND loop <- compile -;
  checked_lift_sequential_loop loop.

Definition checked_sequential_current_annotated_codegen
    (pol: SPolIRs.PolyLang.t)
  : imp ParallelLoop.t :=
  BIND res <-
    ParallelCodegenCore.checked_annotated_codegen_many
      (SPolIRs.PolyLang.current_view_pprog pol)
      nil -;
  res_to_alarm SParallelPolOpt.parallel_dummy res.

Definition compile_seq_verified
    (cfg: SVerifiedCompilerConfig.verified_config)
    (loop: SPolIRs.Loop.t)
  : imp ParallelLoop.t :=
  BIND pol0 <-
    res_to_alarm
      SPolIRs.PolyLang.dummy
      (SParallelPolOpt.CoreOpt.Extractor.extractor loop) -;
  let pol := SParallelPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  match cfg with
  | SVerifiedCompilerConfig.VIdentity =>
      checked_sequential_current_annotated_codegen pol
  | SVerifiedCompilerConfig.VAffine =>
      BIND pol' <- SParallelPolOpt.CoreOpt.checked_affine_schedule pol -;
      checked_sequential_current_annotated_codegen pol'
  | SVerifiedCompilerConfig.VDefault =>
      BIND pol' <-
        SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SVerifiedCompilerConfig.VDefaultBand =>
      BIND pol' <-
        SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SVerifiedCompilerConfig.VIdentitySecondLevel =>
      lift_sequential_compile
        (SVerifiedCompilerConfig.compile_verified cfg loop)
  | SVerifiedCompilerConfig.VIdentitySecondLevelISS =>
      lift_sequential_compile
        (SVerifiedCompilerConfig.compile_verified cfg loop)
  | SVerifiedCompilerConfig.VIdentityBand =>
      BIND pol' <-
        SParallelPolOpt.identity_tiling_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SVerifiedCompilerConfig.VIdentityBandISS =>
      lift_sequential_compile
        (SVerifiedCompilerConfig.compile_verified cfg loop)
  | SVerifiedCompilerConfig.VISS =>
      BIND pol' <-
        SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SVerifiedCompilerConfig.VDiamond =>
      BIND pol' <-
        SParallelPolOpt.diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SVerifiedCompilerConfig.VDiamondISS =>
      BIND pol' <-
        SParallelPolOpt.diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  end.

(* This executable dispatcher deliberately exposes a single Loop -> ParallelLoop
   surface.  Sequential routes are checked-lifted into ParallelLoop; parallel
   routes keep their ParMode annotations and use the existing checked current
   dimension routes. *)
Definition compile_verified
    (cfg: verified_config) (loop: SPolIRs.Loop.t)
  : imp ParallelLoop.t :=
  match cfg with
  | VSeq seq_cfg =>
      compile_seq_verified seq_cfg loop
  | VParallelCurrentIdentity d =>
      SParallelPolOpt.opt_parallel_current_identity loop d
  | VParallelCurrentIdentityTiled d =>
      SParallelPolOpt.opt_parallel_current_identity_tiled loop d
  | VParallelCurrentAffine d =>
      SParallelPolOpt.opt_parallel_current_affine loop d
  | VParallelCurrentDefault d =>
      SParallelPolOpt.opt_parallel_current loop d
  | VParallelCurrentDiamond d =>
      SParallelPolOpt.opt_parallel_current_diamond loop d
  | VParallelCurrentDiamondISS d =>
      SParallelPolOpt.opt_parallel_current_diamond_with_iss loop d
  | VParallelCurrentIdentityISS d =>
      SParallelPolOpt.opt_parallel_current_identity_with_iss loop d
  | VParallelCurrentAffineISS d =>
      SParallelPolOpt.opt_parallel_current_affine_with_iss loop d
  | VParallelCurrentDefaultISS d =>
      SParallelPolOpt.opt_parallel_current_with_iss loop d
  | VParallelCurrentManyIdentity dims =>
      SParallelPolOpt.opt_parallel_current_many_identity loop dims
  | VParallelCurrentManyIdentityTiled dims =>
      SParallelPolOpt.opt_parallel_current_many_identity_tiled loop dims
  | VParallelCurrentManyAffine dims =>
      SParallelPolOpt.opt_parallel_current_many_affine loop dims
  | VParallelCurrentManyDefault dims =>
      SParallelPolOpt.opt_parallel_current_many loop dims
  | VParallelCurrentManyDiamond dims =>
      SParallelPolOpt.opt_parallel_current_many_diamond loop dims
  | VParallelCurrentManyDiamondISS dims =>
      SParallelPolOpt.opt_parallel_current_many_diamond_with_iss loop dims
  | VParallelCurrentManyIdentityISS dims =>
      SParallelPolOpt.opt_parallel_current_many_identity_with_iss loop dims
  | VParallelCurrentManyAffineISS dims =>
      SParallelPolOpt.opt_parallel_current_many_affine_with_iss loop dims
  | VParallelCurrentManyDefaultISS dims =>
      SParallelPolOpt.opt_parallel_current_many_with_iss loop dims
  end.

Definition compile (cfg: raw_config) (loop: SPolIRs.Loop.t)
  : imp ParallelLoop.t :=
  match check_config cfg with
  | Okk vcfg => compile_verified vcfg loop
  | Err msg => res_to_alarm SParallelPolOpt.parallel_dummy (Err msg)
  end.
