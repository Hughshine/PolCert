Require Import String.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import PolOptCorrect.
Require Import PolOptBandTiling.
Require Import Result.
Require Import Vpl.Impure.

Local Open Scope impure_scope.
Local Open Scope string_scope.

Module VerifiedCompilerConfig (PolIRs: POLIRS).

Module Core := PolOpt.PolOpt PolIRs.
Module CoreCorrect := PolOptCorrect PolIRs Core.
Module BandCorrect := PolOptBandTiling PolIRs.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

Inductive raw_config : Type :=
| RawIdentity
| RawAffine
| RawDefault
| RawDefaultBand
| RawSecondLevel
| RawSecondLevelISS
| RawIdentitySecondLevel
| RawIdentitySecondLevelISS
| RawIdentityBand
| RawIdentityBandISS
| RawISS
| RawDiamond
| RawDiamondISS
| RawUnsupported.

Inductive verified_config : Type :=
| VIdentity
| VAffine
| VDefault
| VDefaultBand
| VSecondLevel
| VSecondLevelISS
| VIdentitySecondLevel
| VIdentitySecondLevelISS
| VIdentityBand
| VIdentityBandISS
| VISS
| VDiamond
| VDiamondISS.

Definition check_config (cfg: raw_config) : result verified_config :=
  match cfg with
  | RawIdentity => Okk VIdentity
  | RawAffine => Okk VAffine
  | RawDefault => Okk VDefault
  | RawDefaultBand => Okk VDefaultBand
  | RawSecondLevel => Okk VSecondLevel
  | RawSecondLevelISS => Okk VSecondLevelISS
  | RawIdentitySecondLevel => Okk VIdentitySecondLevel
  | RawIdentitySecondLevelISS => Okk VIdentitySecondLevelISS
  | RawIdentityBand => Okk VIdentityBand
  | RawIdentityBandISS => Okk VIdentityBandISS
  | RawISS => Okk VISS
  | RawDiamond => Okk VDiamond
  | RawDiamondISS => Okk VDiamondISS
  | RawUnsupported => Err "unsupported verified compiler configuration"
  end.

(* This is intentionally enumerated for now, so every admitted CLI-facing route
   is tied to an existing top-level route theorem. A later version can replace
   [verified_config] with a compositional list of verified pass descriptors plus
   a generic pass-composition theorem, once the mixed LoopIR/ParallelLoop routes
   share a common output wrapper. *)
Definition compile_verified (cfg: verified_config) (loop: LoopIR.t)
    : imp LoopIR.t :=
  match cfg with
  | VIdentity => CoreCorrect.Core.identity_opt_prepared loop
  | VAffine => CoreCorrect.Core.affine_opt_prepared loop
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
  | VDiamond => BandCorrect.Opt_diamond_band loop
  | VDiamondISS => BandCorrect.Opt_diamond_band_with_iss loop
  end.

Definition compile (cfg: raw_config) (loop: LoopIR.t) : imp LoopIR.t :=
  match check_config cfg with
  | Okk vcfg => compile_verified vcfg loop
  | Err msg => res_to_alarm loop (Err msg)
  end.

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
  - eapply BandCorrect.Opt_band_correct; eauto.
  - eapply BandCorrect.Opt_band_correct; eauto.
  - eapply BandCorrect.Opt_band_correct; eauto.
  - eapply BandCorrect.Opt_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_correct; eauto.
  - eapply BandCorrect.Opt_identity_tiled_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_band_with_iss_correct; eauto.
  - eapply BandCorrect.Opt_diamond_band_correct; eauto.
  - eapply BandCorrect.Opt_diamond_band_with_iss_correct; eauto.
Qed.

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
