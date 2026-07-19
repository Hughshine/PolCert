Require Import ImpureAlarmConfig.
Require Import SPolIRs.
Require Import SPolOpt.
Require Import SPolOptShared.
Require Import PolOptCorrect.
Require Import SBandTilingOptShared.
Require Import SBandTilingOptBridge.
Require Import ParallelPolOptCorrect.
Require Import SParallelPolOptShared.
Require Import SParallelPolOptBridge.
Require Import SVerifiedCompilerConfig.
Require Import SVerifiedParallelCompilerConfig.
Require Import Vpl.Impure.

Local Open Scope impure_scope.

Module BandCorrect := SBandTilingOptShared.BandGeneric.
Module ParallelCorrect :=
  ParallelPolOptCorrect SPolIRs SParallelPolOptShared.Core.
Module CoreCorrect := PolOptCorrect SPolIRs SPolOptShared.Core.
Module ParallelCodegenCore :=
  SVerifiedParallelCompilerConfig.ParallelCodegenCore.
Module ParallelLoop := SVerifiedParallelCompilerConfig.ParallelLoop.

Theorem extracted_sequential_compile_verified_correct :
  forall cfg loop st st',
    WHEN loop' <- SVerifiedCompilerConfig.compile_verified cfg loop THEN
    SPolIRs.Loop.semantics loop' st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg loop st st' loop' Hcompile Hsem.
  destruct cfg; simpl in Hcompile.
  - eapply CoreCorrect.Identity_opt_prepared_correct; eauto.
  - eapply CoreCorrect.Affine_opt_prepared_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_with_iss_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_band_with_iss_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_identity_tiled_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_identity_tiled_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_identity_tiled_with_iss_impeq_generic
      in Hcompile.
    eapply BandCorrect.Opt_identity_tiled_band_with_iss_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_identity_tiled_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_identity_tiled_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_identity_tiled_with_iss_impeq_generic
      in Hcompile.
    eapply BandCorrect.Opt_identity_tiled_band_with_iss_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_with_iss_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_band_with_iss_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_diamond_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_diamond_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_diamond_with_iss_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_diamond_band_with_iss_correct; eauto.
Qed.

Theorem extracted_sequential_compile_correct :
  forall cfg loop st st',
    WHEN loop' <- SVerifiedCompilerConfig.compile cfg loop THEN
    SPolIRs.Loop.semantics loop' st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg loop st st' loop' Hcompile Hsem.
  unfold SVerifiedCompilerConfig.compile in Hcompile.
  destruct (SVerifiedCompilerConfig.check_config cfg) as [vcfg|msg].
  - eapply extracted_sequential_compile_verified_correct; eauto.
  - apply mayReturn_alarm in Hcompile. tauto.
Qed.

Lemma extracted_checked_lift_sequential_loop_correct :
  forall loop pl st st',
    mayReturn (SVerifiedParallelCompilerConfig.checked_lift_sequential_loop loop) pl ->
    SVerifiedParallelCompilerConfig.ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros loop pl st st' Hlift Hsem.
  unfold SVerifiedParallelCompilerConfig.checked_lift_sequential_loop in Hlift.
  destruct (ParallelCodegenCore.all_es_safeb
              (ParallelCodegenCore.tag_loop loop)) eqn:Hsafe.
  - apply mayReturn_pure in Hlift.
    subst pl.
    pose proof
      (ParallelCodegenCore.all_es_safeb_sound
         (ParallelCodegenCore.tag_loop loop) Hsafe)
      as Htrace_safe.
    pose proof
      (ParallelLoop.semantics_refines_erased
         (ParallelCodegenCore.tag_loop loop) st st' Htrace_safe Hsem)
      as [st'' [Herased Heq]].
    exists st''.
    split.
    + eapply ParallelCodegenCore.erase_to_loop_semantics in Herased.
      rewrite ParallelCodegenCore.erase_tag_loop_eq in Herased.
      exact Herased.
    + exact Heq.
  - apply mayReturn_alarm in Hlift.
    tauto.
Qed.

Lemma extracted_parallel_compile_seq_verified_correct :
  forall cfg loop pl st st',
    mayReturn (SVerifiedParallelCompilerConfig.compile_seq_verified cfg loop) pl ->
    SVerifiedParallelCompilerConfig.ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  unfold SVerifiedParallelCompilerConfig.compile_seq_verified,
    SVerifiedParallelCompilerConfig.lift_sequential_compile in Hcompile.
  bind_imp_destruct Hcompile loop' Hseq.
  destruct
    (extracted_checked_lift_sequential_loop_correct
       loop' pl st st' Hcompile Hsem)
    as [st_mid [Hmid_sem Heq_mid]].
  destruct
    (extracted_sequential_compile_verified_correct
       cfg loop st st_mid loop' Hseq Hmid_sem)
    as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; [exact Hsrc_sem|].
  eapply SPolIRs.State.eq_trans; eauto.
Qed.

Theorem extracted_parallel_compile_verified_correct :
  forall cfg loop pl st st',
    mayReturn (SVerifiedParallelCompilerConfig.compile_verified cfg loop) pl ->
    SVerifiedParallelCompilerConfig.ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  destruct cfg; simpl in Hcompile.
  - eapply extracted_parallel_compile_seq_verified_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_identity_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_identity_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_identity_tiled_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_identity_tiled_correct; eauto.
  - rewrite
      SParallelPolOptBridge.opt_parallel_current_identity_tiled_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_identity_tiled_with_iss_correct;
      eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_affine_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_affine_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_diamond_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_diamond_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_diamond_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_diamond_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_identity_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_identity_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_affine_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_with_iss_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_identity_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_identity_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_identity_tiled_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_identity_tiled_correct; eauto.
  - rewrite
      SParallelPolOptBridge.opt_vector_current_identity_tiled_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_identity_tiled_with_iss_correct;
      eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_affine_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_affine_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_diamond_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_diamond_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_diamond_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_diamond_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_identity_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_identity_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_affine_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_with_iss_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_identity_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_identity_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_identity_tiled_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_identity_tiled_correct;
      eauto.
  - rewrite
      SParallelPolOptBridge.opt_parallel_current_many_identity_tiled_with_iss_impeq
      in Hcompile.
    eapply
      ParallelCorrect.Opt_parallel_current_many_identity_tiled_with_iss_correct;
      eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_affine_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_affine_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_diamond_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_diamond_correct; eauto.
  - rewrite
      SParallelPolOptBridge.opt_parallel_current_many_diamond_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_diamond_with_iss_correct;
      eauto.
  - rewrite
      SParallelPolOptBridge.opt_parallel_current_many_identity_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_identity_with_iss_correct;
      eauto.
  - rewrite
      SParallelPolOptBridge.opt_parallel_current_many_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_affine_with_iss_correct;
      eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_with_iss_correct; eauto.
Qed.

Theorem extracted_parallel_compile_correct :
  forall cfg loop pl st st',
    mayReturn (SVerifiedParallelCompilerConfig.compile cfg loop) pl ->
    SVerifiedParallelCompilerConfig.ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  unfold SVerifiedParallelCompilerConfig.compile in Hcompile.
  destruct (SVerifiedParallelCompilerConfig.check_config cfg) as [vcfg|msg].
  - eapply extracted_parallel_compile_verified_correct; eauto.
  - apply mayReturn_alarm in Hcompile. tauto.
Qed.

Theorem extracted_sequential_unsupported_no_result :
  forall loop out,
    ~ mayReturn
        (SVerifiedCompilerConfig.compile
           SVerifiedCompilerConfig.RawUnsupported loop)
        out.
Proof.
  intros loop out Hcompile.
  unfold SVerifiedCompilerConfig.compile,
    SVerifiedCompilerConfig.check_config in Hcompile.
  simpl in Hcompile.
  apply mayReturn_alarm in Hcompile. tauto.
Qed.

Theorem extracted_parallel_unsupported_no_result :
  forall loop out,
    ~ mayReturn
        (SVerifiedParallelCompilerConfig.compile
           SVerifiedParallelCompilerConfig.RawUnsupported loop)
        out.
Proof.
  intros loop out Hcompile.
  unfold SVerifiedParallelCompilerConfig.compile,
    SVerifiedParallelCompilerConfig.check_config in Hcompile.
  simpl in Hcompile.
  apply mayReturn_alarm in Hcompile. tauto.
Qed.
