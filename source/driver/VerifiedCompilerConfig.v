Require Import String.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import PolOptCorrect.
Require Import PolOptBandTiling.
Require Import Result.
Require Import VerifiedLoopPostpass.
Require Import Vpl.Impure.

Local Open Scope impure_scope.
Local Open Scope string_scope.

Module VerifiedCompilerConfig (PolIRs: POLIRS).

Module Core := PolOpt.PolOpt PolIRs.
Module CoreCorrect := PolOptCorrect PolIRs Core.
Module BandCorrect := PolOptBandTiling PolIRs.
Module Postpass := VerifiedLoopPostpass PolIRs.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

(** * Generic sequential compiler endpoint

    This functor is the small, sequential endpoint.  Both its source and target
    use [LoopIR]; it contains no [ParMode] or [VecMode].  The 14 constructors of
    [verified_config] select identity, affine, tiling, ISS, and post_tiling_affine routes.

    The similarly named [VerifiedParallelCompilerConfig] is the larger unified
    endpoint: it embeds this sequential compiler into [ParallelLoop] and adds
    single-parallel, vector, and multi-parallel annotation families.

    [compile_verified] accepts a configuration that already passed
    [check_config].  It does not bypass the validators inside the selected
    optimization route.  [compile] is the raw-configuration wrapper, and
    [compile_correct] is the public theorem when starting from CLI-style
    configuration data. *)

(** ** Sequential configuration families *)

Inductive raw_config : Type :=
| RawIdentity
| RawAffine
| RawAffineISS
| RawDefault
| RawDefaultBand
| RawSecondLevel
| RawSecondLevelISS
| RawIdentitySecondLevel
| RawIdentitySecondLevelISS
| RawIdentityBand
| RawIdentityBandISS
| RawISS
| RawPostTilingAffine
| RawPostTilingAffineISS
| RawUnsupported.

Inductive verified_config : Type :=
| VIdentity
| VAffine
| VAffineISS
| VDefault
| VDefaultBand
| VSecondLevel
| VSecondLevelISS
| VIdentitySecondLevel
| VIdentitySecondLevelISS
| VIdentityBand
| VIdentityBandISS
| VISS
| VPostTilingAffine
| VPostTilingAffineISS.

Definition check_config (cfg: raw_config) : result verified_config :=
  match cfg with
  | RawIdentity => Okk VIdentity
  | RawAffine => Okk VAffine
  | RawAffineISS => Okk VAffineISS
  | RawDefault => Okk VDefault
  | RawDefaultBand => Okk VDefaultBand
  | RawSecondLevel => Okk VSecondLevel
  | RawSecondLevelISS => Okk VSecondLevelISS
  | RawIdentitySecondLevel => Okk VIdentitySecondLevel
  | RawIdentitySecondLevelISS => Okk VIdentitySecondLevelISS
  | RawIdentityBand => Okk VIdentityBand
  | RawIdentityBandISS => Okk VIdentityBandISS
  | RawISS => Okk VISS
  | RawPostTilingAffine => Okk VPostTilingAffine
  | RawPostTilingAffineISS => Okk VPostTilingAffineISS
  | RawUnsupported => Err "unsupported verified compiler configuration"
  end.

(** ** Verified sequential dispatcher

    This is intentionally enumerated so every accepted configuration is tied
    to one existing route theorem.  The concrete executable mirror is
    [SVerifiedCompilerConfig.compile_verified]; its correctness bridge is
    [ExtractedPipelineCorrect.extracted_sequential_compile_verified_correct].

    The word "verified" qualifies [cfg], not the input program and not the
    result.  The selected route still performs extraction, well-formedness, and
    transformation-specific validation.  Several external route names
    ([VDefault], [VDefaultBand], and [VSecondLevel]) deliberately converge on
    [Opt_band]; the earlier route selection changes how the candidate was
    produced, while this endpoint needs only the common checked theorem. *)
Definition compile_verified (cfg: verified_config) (loop: LoopIR.t)
    : imp LoopIR.t :=
  match cfg with
  | VIdentity => CoreCorrect.Core.identity_opt_prepared loop
  | VAffine => CoreCorrect.Core.affine_opt_prepared loop
  | VAffineISS => CoreCorrect.Core.Opt_with_iss loop
  | VDefault => BandCorrect.Opt_band loop
  | VDefaultBand => BandCorrect.Opt_band loop
  | VSecondLevel => BandCorrect.Opt_band loop
  | VSecondLevelISS => BandCorrect.Opt_band_with_iss loop
  | VIdentitySecondLevel =>
      BandCorrect.Opt_identity_tiled_band loop
  | VIdentitySecondLevelISS =>
      BandCorrect.Opt_identity_tiled_band_with_iss loop
  | VIdentityBand => BandCorrect.Opt_identity_tiled_band loop
  | VIdentityBandISS => BandCorrect.Opt_identity_tiled_band_with_iss loop
  | VISS => BandCorrect.Opt_band_with_iss loop
  | VPostTilingAffine => BandCorrect.Opt_post_tiling_affine_band loop
  | VPostTilingAffineISS => BandCorrect.Opt_post_tiling_affine_band_with_iss loop
  end.

Definition compile (cfg: raw_config) (loop: LoopIR.t) : imp LoopIR.t :=
  match check_config cfg with
  | Okk vcfg => compile_verified vcfg loop
  | Err msg => res_to_alarm loop (Err msg)
  end.

(** The postpass is orthogonal to the producer route.  Keeping it as a second
    argument avoids duplicating every affine, tiling, and ISS constructor. *)
Definition compile_with_postpass
    (cfg : raw_config) (postpass : loop_postpass_config) (loop : LoopIR.t)
    : imp LoopIR.t :=
  BIND optimized <- compile cfg loop -;
  Postpass.apply postpass optimized.

(** End-to-end checked unroll-jam endpoint.  The selector is deliberately a
    function of the producer result, so an untrusted profitability policy can
    inspect the actual optimized Loop IR without escaping the theorem. *)
Definition compile_with_unrolljam
    (cfg : raw_config) (const_first : bool)
    (select : LoopIR.t -> Postpass.JamLower.unrolljam_plan)
    (factor : nat) (loop : LoopIR.t) : imp LoopIR.t :=
  BIND optimized <- compile cfg loop -;
  Postpass.apply_checked_unrolljam
    const_first select factor optimized.

(** ** Generic sequential correctness endpoints

    [compile_verified_correct] assumes a [verified_config].
    [compile_correct] additionally discharges [check_config].  Their semantic
    conclusions are otherwise identical.  Cite [compile_correct] for a caller
    that supplies [raw_config]; cite [compile_verified_correct] only when the
    configuration-checking result is already in hand. *)

Theorem compile_verified_correct :
  forall cfg loop st st',
    WHEN loop' <- compile_verified cfg loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros cfg loop st st' loop' Hcompile Hsem.
  destruct cfg; simpl in Hcompile.
  - eapply CoreCorrect.Identity_opt_prepared_correct; eauto.
  - eapply CoreCorrect.Affine_opt_prepared_correct; eauto.
  - eapply CoreCorrect.Opt_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_band_correct; eauto.
  - eapply BandCorrect.Opt_band_correct; eauto.
  - eapply BandCorrect.Opt_band_correct; eauto.
  - eapply BandCorrect.Opt_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_post_tiling_affine_band_correct; eauto.
  - eapply BandCorrect.Opt_post_tiling_affine_band_with_iss_correct; eauto.
Qed.

(** Raw-config wrapper around [compile_verified_correct].  Rejection has no
    returned target; acceptance exposes a [verified_config] and immediately
    reuses the theorem above. *)
Theorem compile_correct :
  forall cfg loop st st',
    WHEN loop' <- compile cfg loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros cfg loop st st' loop' Hcompile Hsem.
  unfold compile in Hcompile.
  destruct (check_config cfg) as [vcfg|msg] eqn:Hcheck.
  - simpl in Hcompile.
    eapply compile_verified_correct; eauto.
  - simpl in Hcompile.
    apply mayReturn_alarm in Hcompile.
    tauto.
Qed.

Theorem compile_with_postpass_correct :
  forall cfg postpass loop st st',
    WHEN loop' <- compile_with_postpass cfg postpass loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros cfg postpass loop st st' loop' Hcompile Hsem.
  unfold compile_with_postpass in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hproducer Hpostpass]].
  destruct
    (Postpass.apply_correct
       postpass optimized loop' st st' Hpostpass Hsem)
    as [st_mid [Hsem_mid Heq_mid]].
  destruct
    (compile_correct cfg loop st st_mid optimized Hproducer Hsem_mid)
    as [st_src [Hsem_src Heq_src]].
  exists st_src.
  split; [exact Hsem_src|].
  eapply State.eq_trans; eauto.
Qed.

Theorem compile_with_unrolljam_correct :
  forall cfg const_first select factor loop st st',
    WHEN loop' <-
      compile_with_unrolljam cfg const_first select factor loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg const_first select factor loop st st' loop' Hcompile Hsem.
  unfold compile_with_unrolljam in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hproducer Hunrolljam]].
  destruct
    (Postpass.apply_checked_unrolljam_correct
       const_first select factor optimized loop' st st'
       Hunrolljam Hsem)
    as [st_mid [Hsem_mid Heq_mid]].
  destruct
    (compile_correct cfg loop st st_mid optimized Hproducer Hsem_mid)
    as [st_src [Hsem_src Heq_src]].
  exists st_src.
  split; [exact Hsem_src|].
  eapply State.eq_trans; eauto.
Qed.

Theorem compile_unsupported_no_result :
  forall loop out,
    ~ mayReturn (compile RawUnsupported loop) out.
Proof.
  intros loop out H.
  unfold compile, check_config, res_to_alarm in H.
  simpl in H.
  apply mayReturn_alarm in H.
  tauto.
Qed.

End VerifiedCompilerConfig.
