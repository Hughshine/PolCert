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

(** * Concrete extracted unified dispatcher

    This is the extraction-facing mirror of
    [VerifiedParallelCompilerConfig].  It returns [ParallelLoop.t] for every
    route: sequential results are checked-lifted, while parallel and vector
    routes keep their annotations.  The file intentionally carries no duplicate
    correctness proof.  The concrete endpoints are
    [ExtractedPipelineCorrect.extracted_parallel_compile_verified_correct] and
    [ExtractedPipelineCorrect.extracted_parallel_compile_correct]. *)

(** ** Concrete unified configurations *)

Inductive raw_config : Type :=
| RawSeq (cfg: SVerifiedCompilerConfig.raw_config)
| RawParallelCurrentIdentity (d: nat)
| RawParallelCurrentIdentityTiled (d: nat)
| RawParallelCurrentIdentityTiledISS (d: nat)
| RawParallelCurrentAffine (d: nat)
| RawParallelCurrentDefault (d: nat)
| RawParallelCurrentPostTilingAffine (d: nat)
| RawParallelCurrentPostTilingAffineISS (d: nat)
| RawParallelCurrentIdentityISS (d: nat)
| RawParallelCurrentAffineISS (d: nat)
| RawParallelCurrentDefaultISS (d: nat)
| RawVectorCurrentIdentity (d: nat)
| RawVectorCurrentIdentityTiled (d: nat)
| RawVectorCurrentIdentityTiledISS (d: nat)
| RawVectorCurrentAffine (d: nat)
| RawVectorCurrentDefault (d: nat)
| RawVectorCurrentPostTilingAffine (d: nat)
| RawVectorCurrentPostTilingAffineISS (d: nat)
| RawVectorCurrentIdentityISS (d: nat)
| RawVectorCurrentAffineISS (d: nat)
| RawVectorCurrentDefaultISS (d: nat)
| RawParallelCurrentManyIdentity (dims: list nat)
| RawParallelCurrentManyIdentityTiled (dims: list nat)
| RawParallelCurrentManyIdentityTiledISS (dims: list nat)
| RawParallelCurrentManyAffine (dims: list nat)
| RawParallelCurrentManyDefault (dims: list nat)
| RawParallelCurrentManyPostTilingAffine (dims: list nat)
| RawParallelCurrentManyPostTilingAffineISS (dims: list nat)
| RawParallelCurrentManyIdentityISS (dims: list nat)
| RawParallelCurrentManyAffineISS (dims: list nat)
| RawParallelCurrentManyDefaultISS (dims: list nat)
| RawUnsupported.

Inductive verified_config : Type :=
| VSeq (cfg: SVerifiedCompilerConfig.verified_config)
| VParallelCurrentIdentity (d: nat)
| VParallelCurrentIdentityTiled (d: nat)
| VParallelCurrentIdentityTiledISS (d: nat)
| VParallelCurrentAffine (d: nat)
| VParallelCurrentDefault (d: nat)
| VParallelCurrentPostTilingAffine (d: nat)
| VParallelCurrentPostTilingAffineISS (d: nat)
| VParallelCurrentIdentityISS (d: nat)
| VParallelCurrentAffineISS (d: nat)
| VParallelCurrentDefaultISS (d: nat)
| VVectorCurrentIdentity (d: nat)
| VVectorCurrentIdentityTiled (d: nat)
| VVectorCurrentIdentityTiledISS (d: nat)
| VVectorCurrentAffine (d: nat)
| VVectorCurrentDefault (d: nat)
| VVectorCurrentPostTilingAffine (d: nat)
| VVectorCurrentPostTilingAffineISS (d: nat)
| VVectorCurrentIdentityISS (d: nat)
| VVectorCurrentAffineISS (d: nat)
| VVectorCurrentDefaultISS (d: nat)
| VParallelCurrentManyIdentity (dims: list nat)
| VParallelCurrentManyIdentityTiled (dims: list nat)
| VParallelCurrentManyIdentityTiledISS (dims: list nat)
| VParallelCurrentManyAffine (dims: list nat)
| VParallelCurrentManyDefault (dims: list nat)
| VParallelCurrentManyPostTilingAffine (dims: list nat)
| VParallelCurrentManyPostTilingAffineISS (dims: list nat)
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
  | RawParallelCurrentIdentityTiledISS d =>
      Okk (VParallelCurrentIdentityTiledISS d)
  | RawParallelCurrentAffine d => Okk (VParallelCurrentAffine d)
  | RawParallelCurrentDefault d => Okk (VParallelCurrentDefault d)
  | RawParallelCurrentPostTilingAffine d => Okk (VParallelCurrentPostTilingAffine d)
  | RawParallelCurrentPostTilingAffineISS d => Okk (VParallelCurrentPostTilingAffineISS d)
  | RawParallelCurrentIdentityISS d => Okk (VParallelCurrentIdentityISS d)
  | RawParallelCurrentAffineISS d => Okk (VParallelCurrentAffineISS d)
  | RawParallelCurrentDefaultISS d => Okk (VParallelCurrentDefaultISS d)
  | RawVectorCurrentIdentity d => Okk (VVectorCurrentIdentity d)
  | RawVectorCurrentIdentityTiled d => Okk (VVectorCurrentIdentityTiled d)
  | RawVectorCurrentIdentityTiledISS d => Okk (VVectorCurrentIdentityTiledISS d)
  | RawVectorCurrentAffine d => Okk (VVectorCurrentAffine d)
  | RawVectorCurrentDefault d => Okk (VVectorCurrentDefault d)
  | RawVectorCurrentPostTilingAffine d => Okk (VVectorCurrentPostTilingAffine d)
  | RawVectorCurrentPostTilingAffineISS d => Okk (VVectorCurrentPostTilingAffineISS d)
  | RawVectorCurrentIdentityISS d => Okk (VVectorCurrentIdentityISS d)
  | RawVectorCurrentAffineISS d => Okk (VVectorCurrentAffineISS d)
  | RawVectorCurrentDefaultISS d => Okk (VVectorCurrentDefaultISS d)
  | RawParallelCurrentManyIdentity dims => Okk (VParallelCurrentManyIdentity dims)
  | RawParallelCurrentManyIdentityTiled dims => Okk (VParallelCurrentManyIdentityTiled dims)
  | RawParallelCurrentManyIdentityTiledISS dims =>
      Okk (VParallelCurrentManyIdentityTiledISS dims)
  | RawParallelCurrentManyAffine dims => Okk (VParallelCurrentManyAffine dims)
  | RawParallelCurrentManyDefault dims => Okk (VParallelCurrentManyDefault dims)
  | RawParallelCurrentManyPostTilingAffine dims => Okk (VParallelCurrentManyPostTilingAffine dims)
  | RawParallelCurrentManyPostTilingAffineISS dims => Okk (VParallelCurrentManyPostTilingAffineISS dims)
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
  lift_sequential_compile (SVerifiedCompilerConfig.compile_verified cfg loop).

(** ** Concrete verified and raw dispatchers

    The 31 constructors have the same grouping as the generic module: one
    wrapped sequential family, ten single-parallel, ten vector, and ten
    multi-parallel routes.  [compile_verified] assumes only that [check_config]
    accepted the outer configuration; route validators still run. *)
Definition compile_verified
    (cfg: verified_config) (loop: SPolIRs.Loop.t)
  : imp ParallelLoop.t :=
  match cfg with
  (** One wrapper for all 14 concrete sequential configurations. *)
  | VSeq seq_cfg =>
      compile_seq_verified seq_cfg loop
  (** Ten single-coordinate parallel routes. *)
  | VParallelCurrentIdentity d =>
      SParallelPolOpt.opt_parallel_current_identity loop d
  | VParallelCurrentIdentityTiled d =>
      SParallelPolOpt.opt_parallel_current_identity_tiled loop d
  | VParallelCurrentIdentityTiledISS d =>
      SParallelPolOpt.opt_parallel_current_identity_tiled_with_iss loop d
  | VParallelCurrentAffine d =>
      SParallelPolOpt.opt_parallel_current_affine loop d
  | VParallelCurrentDefault d =>
      SParallelPolOpt.opt_parallel_current loop d
  | VParallelCurrentPostTilingAffine d =>
      SParallelPolOpt.opt_parallel_current_post_tiling_affine loop d
  | VParallelCurrentPostTilingAffineISS d =>
      SParallelPolOpt.opt_parallel_current_post_tiling_affine_with_iss loop d
  | VParallelCurrentIdentityISS d =>
      SParallelPolOpt.opt_parallel_current_identity_with_iss loop d
  | VParallelCurrentAffineISS d =>
      SParallelPolOpt.opt_parallel_current_affine_with_iss loop d
  | VParallelCurrentDefaultISS d =>
      SParallelPolOpt.opt_parallel_current_with_iss loop d
  (** Ten single-coordinate vector routes. *)
  | VVectorCurrentIdentity d =>
      SParallelPolOpt.opt_vector_current_identity loop d
  | VVectorCurrentIdentityTiled d =>
      SParallelPolOpt.opt_vector_current_identity_tiled loop d
  | VVectorCurrentIdentityTiledISS d =>
      SParallelPolOpt.opt_vector_current_identity_tiled_with_iss loop d
  | VVectorCurrentAffine d =>
      SParallelPolOpt.opt_vector_current_affine loop d
  | VVectorCurrentDefault d =>
      SParallelPolOpt.opt_vector_current loop d
  | VVectorCurrentPostTilingAffine d =>
      SParallelPolOpt.opt_vector_current_post_tiling_affine loop d
  | VVectorCurrentPostTilingAffineISS d =>
      SParallelPolOpt.opt_vector_current_post_tiling_affine_with_iss loop d
  | VVectorCurrentIdentityISS d =>
      SParallelPolOpt.opt_vector_current_identity_with_iss loop d
  | VVectorCurrentAffineISS d =>
      SParallelPolOpt.opt_vector_current_affine_with_iss loop d
  | VVectorCurrentDefaultISS d =>
      SParallelPolOpt.opt_vector_current_with_iss loop d
  (** Ten multi-coordinate parallel routes. *)
  | VParallelCurrentManyIdentity dims =>
      SParallelPolOpt.opt_parallel_current_many_identity loop dims
  | VParallelCurrentManyIdentityTiled dims =>
      SParallelPolOpt.opt_parallel_current_many_identity_tiled loop dims
  | VParallelCurrentManyIdentityTiledISS dims =>
      SParallelPolOpt.opt_parallel_current_many_identity_tiled_with_iss loop dims
  | VParallelCurrentManyAffine dims =>
      SParallelPolOpt.opt_parallel_current_many_affine loop dims
  | VParallelCurrentManyDefault dims =>
      SParallelPolOpt.opt_parallel_current_many loop dims
  | VParallelCurrentManyPostTilingAffine dims =>
      SParallelPolOpt.opt_parallel_current_many_post_tiling_affine loop dims
  | VParallelCurrentManyPostTilingAffineISS dims =>
      SParallelPolOpt.opt_parallel_current_many_post_tiling_affine_with_iss loop dims
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

(** The concrete driver-facing composition for checked unroll-jam followed by
    fresh parallel validation on the transformed Loop IR. *)
Definition compile_parallel_after_unrolljam
    (seq_cfg : SVerifiedCompilerConfig.raw_config) (const_first : bool)
    (select : SPolIRs.Loop.t -> SLoopJamLower.unrolljam_plan)
    (factor d : nat) (loop : SPolIRs.Loop.t) : imp ParallelLoop.t :=
  BIND optimized <-
    SVerifiedCompilerConfig.compile_with_unrolljam
      seq_cfg const_first select factor loop -;
  compile (RawParallelCurrentIdentity d) optimized.

Definition compile_parallel_many_after_unrolljam
    (seq_cfg : SVerifiedCompilerConfig.raw_config) (const_first : bool)
    (select : SPolIRs.Loop.t -> SLoopJamLower.unrolljam_plan)
    (factor : nat) (dims : list nat) (loop : SPolIRs.Loop.t)
    : imp ParallelLoop.t :=
  BIND optimized <-
    SVerifiedCompilerConfig.compile_with_unrolljam
      seq_cfg const_first select factor loop -;
  compile (RawParallelCurrentManyIdentity dims) optimized.
