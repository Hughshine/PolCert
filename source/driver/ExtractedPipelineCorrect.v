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
Require Import VerifiedLoopPostpass.
Require Import Vpl.Impure.

Local Open Scope impure_scope.

Module BandCorrect := SBandTilingOptShared.BandGeneric.
Module ParallelCorrect :=
  ParallelPolOptCorrect SPolIRs SParallelPolOptShared.Core.
Module CoreCorrect := PolOptCorrect SPolIRs SPolOptShared.Core.
Module ParallelCodegenCore :=
  SVerifiedParallelCompilerConfig.ParallelCodegenCore.
Module ParallelLoop := SVerifiedParallelCompilerConfig.ParallelLoop.

(** * Concrete extracted compiler endpoints

    Generic functor instances carry the semantic proofs, while the extracted
    compiler uses hand-instantiated concrete modules with stable OCaml names.
    The bridge lemmas rewrite concrete executions to their proved generic
    counterparts.  The two [*_compile_verified_correct] theorems then perform
    an explicit constructor-by-constructor coverage audit; the raw [compile]
    theorems add only configuration checking.

    There are four public endpoints, determined by two independent choices:

    - [sequential] returns [SPolIRs.Loop.t]; [parallel] returns the unified
      annotated [ParallelLoop.t], including sequential, parallel, and vector
      routes;
    - [compile_verified] starts after outer configuration checking; [compile]
      starts from [raw_config] and includes that check.

    Thus [extracted_parallel_compile_correct] is the concrete theorem closest
    to the extracted CLI pipeline.  The sequential pair is useful when studying
    the older Loop-to-Loop dispatcher in isolation. *)

(** ** Concrete sequential endpoints *)

(** This theorem is the concrete counterpart of
    [VerifiedCompilerConfig.compile_verified_correct].  Its 14 cases do not
    reprove the transformations: they rewrite the hand-instantiated executable
    route to the corresponding generic module and invoke its existing theorem. *)

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
  - eapply CoreCorrect.Opt_with_iss_correct; eauto.
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
  - rewrite SBandTilingOptBridge.opt_post_tiling_affine_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_post_tiling_affine_band_correct; eauto.
  - rewrite SBandTilingOptBridge.opt_post_tiling_affine_with_iss_impeq_generic in Hcompile.
    eapply BandCorrect.Opt_post_tiling_affine_band_with_iss_correct; eauto.
Qed.

(** Raw-config wrapper for the concrete sequential dispatcher.  Its only new
    step is [SVerifiedCompilerConfig.check_config]; the successful branch calls
    [extracted_sequential_compile_verified_correct]. *)
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

(** The complete concrete sequential endpoint, including optional
    constant-bound unrolling.
    The untrusted CLI chooses a route and a postpass configuration, but every
    returned target crosses both extracted checked boundaries. *)
Theorem extracted_sequential_compile_with_postpass_correct :
  forall cfg postpass loop st st',
    WHEN loop' <-
      SVerifiedCompilerConfig.compile_with_postpass cfg postpass loop THEN
    SPolIRs.Loop.semantics loop' st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg postpass loop st st' loop' Hcompile Hsem.
  unfold SVerifiedCompilerConfig.compile_with_postpass in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hproducer Hpostpass]].
  destruct
    (SVerifiedCompilerConfig.Postpass.apply_correct
       postpass optimized loop' st st' Hpostpass Hsem)
    as [st_mid [Hsem_mid Heq_mid]].
  destruct
    (extracted_sequential_compile_correct
       cfg loop st st_mid optimized Hproducer Hsem_mid)
    as [st_src [Hsem_src Heq_src]].
  exists st_src.
  split; [exact Hsem_src|].
  eapply SPolIRs.State.eq_trans; eauto.
Qed.

(** Concrete end-to-end endpoint for checked unroll-jam.  The extracted CLI
    may compute [select] with any profitability heuristic; every selected
    fusion still crosses the verified local validator. *)
Theorem extracted_sequential_compile_with_unrolljam_correct :
  forall cfg const_first select factor loop st st',
    WHEN loop' <-
      SVerifiedCompilerConfig.compile_with_unrolljam
        cfg const_first select factor loop THEN
    SPolIRs.Loop.semantics loop' st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\
      SPolIRs.State.eq st' st''.
Proof.
  intros cfg const_first select factor loop st st' loop' Hcompile Hsem.
  unfold SVerifiedCompilerConfig.compile_with_unrolljam in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hproducer Hunrolljam]].
  destruct
    (SVerifiedCompilerConfig.Postpass.apply_checked_unrolljam_correct
       const_first
       (fun prepared =>
          SVerifiedCompilerConfig.adapt_unrolljam_plan (select prepared))
       factor optimized loop' st st'
       Hunrolljam Hsem)
    as [st_mid [Hsem_mid Heq_mid]].
  destruct
    (extracted_sequential_compile_correct
       cfg loop st st_mid optimized Hproducer Hsem_mid)
    as [st_src [Hsem_src Heq_src]].
  exists st_src.
  split; [exact Hsem_src|].
  eapply SPolIRs.State.eq_trans; eauto.
Qed.

(** ** Lifting a concrete sequential result into [ParallelLoop] *)

(** The next two lemmas serve only the [VSeq] branch of the concrete unified
    dispatcher.  They turn the concrete sequential target into a trace-safe,
    sequentially tagged [ParallelLoop] target, then compose its state relation
    with the 14-route sequential theorem above. *)

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
      (ParallelLoop.semantics_refines_erased_global
         (ParallelCodegenCore.tag_loop loop) st st' Htrace_safe
         (ParallelCodegenCore.tag_loop_ordered loop) Hsem)
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

(** Compose the concrete 14-route sequential theorem with the checked lift into
    the common [ParallelLoop] target. *)
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

(** ** Concrete unified annotated endpoints *)

(** This is the concrete 31-constructor coverage theorem.  Each branch first
    uses an [SParallelPolOptBridge] equality to identify the extracted route
    with the generic route, then invokes the corresponding
    [ParallelPolOptCorrect] theorem.  The proof is intentionally exhaustive so
    adding an executable constructor without a theorem cannot be silent. *)

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
  (** [VSeq]: bridge the concrete 14-route sequential dispatcher. *)
  - eapply extracted_parallel_compile_seq_verified_correct; eauto.
  (** Ten concrete [VParallelCurrent] constructors. *)
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
  - rewrite SParallelPolOptBridge.opt_parallel_current_post_tiling_affine_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_post_tiling_affine_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_post_tiling_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_post_tiling_affine_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_identity_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_identity_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_affine_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_parallel_current_with_iss_impeq in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_with_iss_correct; eauto.
  (** Ten concrete [VVectorCurrent] constructors. *)
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
  - rewrite SParallelPolOptBridge.opt_vector_current_post_tiling_affine_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_post_tiling_affine_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_post_tiling_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_post_tiling_affine_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_identity_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_identity_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_affine_with_iss_correct; eauto.
  - rewrite SParallelPolOptBridge.opt_vector_current_with_iss_impeq in Hcompile.
    eapply ParallelCorrect.Opt_vector_current_with_iss_correct; eauto.
  (** Ten concrete [VParallelCurrentMany] constructors. *)
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
  - rewrite SParallelPolOptBridge.opt_parallel_current_many_post_tiling_affine_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_post_tiling_affine_correct; eauto.
  - rewrite
      SParallelPolOptBridge.opt_parallel_current_many_post_tiling_affine_with_iss_impeq
      in Hcompile.
    eapply ParallelCorrect.Opt_parallel_current_many_post_tiling_affine_with_iss_correct;
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

(** Raw-config wrapper for the concrete unified dispatcher.  This is the
    theorem to use when relating the extracted CLI-facing compiler to source
    [SPolIRs.Loop.semantics]. *)
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

(** The concrete annotated postpass preserves every existing [ParMode] and
    [VecMode] loop and unfolds only constant-bound [SeqMode] loops. *)
Lemma extracted_checked_parallel_const_unroll_correct :
  forall pl pl' st st',
    mayReturn (SVerifiedParallelCompilerConfig.checked_const_unroll pl) pl' ->
    ParallelLoop.semantics pl' st st' ->
    ParallelLoop.semantics pl st st'.
Proof.
  intros pl pl' st st' Hunroll Hsem.
  unfold SVerifiedParallelCompilerConfig.checked_const_unroll in Hunroll.
  destruct (ParallelLoop.const_unroll_changed pl) eqn:Hchanged.
  - destruct (ParallelCodegenCore.all_es_safeb pl) eqn:Hsafe.
    + destruct
        (ParallelCodegenCore.all_es_safeb
           (ParallelLoop.const_unroll pl)) eqn:Hsafe_unroll.
      * apply mayReturn_pure in Hunroll. subst pl'.
        eapply ParallelLoop.const_unroll_semantics_refine; eauto using
          ParallelCodegenCore.all_es_safeb_sound.
      * apply mayReturn_alarm in Hunroll. tauto.
    + apply mayReturn_alarm in Hunroll. tauto.
  - apply mayReturn_alarm in Hunroll. tauto.
Qed.

(** Concrete end-to-end endpoint for a verified annotated compilation followed
    by sequential-only constant unrolling. *)
Theorem extracted_parallel_compile_with_const_unroll_correct :
  forall cfg loop pl st st',
    mayReturn
      (SVerifiedParallelCompilerConfig.compile_with_const_unroll cfg loop)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\ SPolIRs.State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  unfold SVerifiedParallelCompilerConfig.compile_with_const_unroll in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [annotated [Hproducer Hunroll]].
  pose proof
    (extracted_checked_parallel_const_unroll_correct
       annotated pl st st' Hunroll Hsem)
    as Hannotated.
  eapply extracted_parallel_compile_correct; eauto.
Qed.

(** The Pluto-compatible parallel/unroll-jam composition deliberately obtains
    a fresh certificate after the checked postpass.  It therefore demonstrates
    the combination without claiming certificate transport through arbitrary
    annotated loop nests. *)
Theorem extracted_parallel_after_unrolljam_correct :
  forall seq_cfg const_first select factor d loop pl st st',
    mayReturn
      (SVerifiedParallelCompilerConfig.compile_parallel_after_unrolljam
         seq_cfg const_first select factor d loop)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\ SPolIRs.State.eq st' st''.
Proof.
  intros seq_cfg const_first select factor d loop pl st st' Hcompile Hsem.
  unfold SVerifiedParallelCompilerConfig.compile_parallel_after_unrolljam
    in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hunrolljam Hparallel]].
  destruct
    (extracted_parallel_compile_correct
       (SVerifiedParallelCompilerConfig.RawParallelCurrentIdentity d)
       optimized pl st st' Hparallel Hsem)
    as [st_mid [Hmid Heq_mid]].
  destruct
    (extracted_sequential_compile_with_unrolljam_correct
       seq_cfg const_first select factor loop st st_mid optimized
       Hunrolljam Hmid)
    as [st_src [Hsrc Heq_src]].
  exists st_src. split; [exact Hsrc|].
  eapply SPolIRs.State.eq_trans; eauto.
Qed.

Theorem extracted_parallel_many_after_unrolljam_correct :
  forall seq_cfg const_first select factor dims loop pl st st',
    mayReturn
      (SVerifiedParallelCompilerConfig.compile_parallel_many_after_unrolljam
         seq_cfg const_first select factor dims loop)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      SPolIRs.Loop.semantics loop st st'' /\ SPolIRs.State.eq st' st''.
Proof.
  intros seq_cfg const_first select factor dims loop pl st st' Hcompile Hsem.
  unfold SVerifiedParallelCompilerConfig.compile_parallel_many_after_unrolljam
    in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hunrolljam Hparallel]].
  destruct
    (extracted_parallel_compile_correct
       (SVerifiedParallelCompilerConfig.RawParallelCurrentManyIdentity dims)
       optimized pl st st' Hparallel Hsem)
    as [st_mid [Hmid Heq_mid]].
  destruct
    (extracted_sequential_compile_with_unrolljam_correct
       seq_cfg const_first select factor loop st st_mid optimized
       Hunrolljam Hmid)
    as [st_src [Hsrc Heq_src]].
  exists st_src. split; [exact Hsrc|].
  eapply SPolIRs.State.eq_trans; eauto.
Qed.

(** ** Explicit rejection endpoints *)

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
