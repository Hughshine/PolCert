Require Import String.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import Result.
Require Import Vpl.Impure.
Require Import VerifiedCompilerConfig.
Require Import ParallelPolOptCorrect.

Local Open Scope impure_scope.
Local Open Scope string_scope.

Module VerifiedParallelCompilerConfig (PolIRs: POLIRS).

Module SeqCompiler := VerifiedCompilerConfig PolIRs.
Module ParallelCorrect := ParallelPolOptCorrect PolIRs.
Module ParallelCore := ParallelCorrect.Core.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.
Module ParallelLoop := ParallelCorrect.ParallelLoop.
Module ParallelCodegenCore := ParallelCore.ParallelCodegenCore.

Inductive raw_config : Type :=
| RawSeq (cfg: SeqCompiler.raw_config)
| RawParallelCurrentIdentity (d: nat)
| RawParallelCurrentIdentityTiled (d: nat)
| RawParallelCurrentAffine (d: nat)
| RawParallelCurrentDefault (d: nat)
| RawParallelCurrentDiamond (d: nat)
| RawParallelCurrentDiamondISS (d: nat)
| RawParallelCurrentIdentityISS (d: nat)
| RawParallelCurrentAffineISS (d: nat)
| RawParallelCurrentDefaultISS (d: nat)
| RawUnsupported.

Inductive verified_config : Type :=
| VSeq (cfg: SeqCompiler.verified_config)
| VParallelCurrentIdentity (d: nat)
| VParallelCurrentIdentityTiled (d: nat)
| VParallelCurrentAffine (d: nat)
| VParallelCurrentDefault (d: nat)
| VParallelCurrentDiamond (d: nat)
| VParallelCurrentDiamondISS (d: nat)
| VParallelCurrentIdentityISS (d: nat)
| VParallelCurrentAffineISS (d: nat)
| VParallelCurrentDefaultISS (d: nat).

Definition check_config (cfg: raw_config) : result verified_config :=
  match cfg with
  | RawSeq seq_cfg =>
      match SeqCompiler.check_config seq_cfg with
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
  | RawUnsupported => Err "unsupported verified compiler configuration"
  end.

Definition checked_lift_sequential_loop (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  let pl := ParallelCodegenCore.tag_loop loop in
  if ParallelCodegenCore.all_es_safeb pl then
    pure pl
  else
    res_to_alarm
      ParallelCore.parallel_dummy
      (Err "sequential route produced a non-affine ParallelLoop trace"%string).

Definition lift_sequential_compile
    (compile: imp LoopIR.t)
  : imp ParallelLoop.t :=
  BIND loop <- compile -;
  checked_lift_sequential_loop loop.

Definition checked_sequential_current_annotated_codegen
    (pol: PolyLang.t)
  : imp ParallelLoop.t :=
  BIND res <-
    ParallelCodegenCore.checked_annotated_codegen_many
      (PolyLang.current_view_pprog pol)
      nil -;
  res_to_alarm ParallelCore.parallel_dummy res.

Definition compile_seq_verified
    (cfg: SeqCompiler.verified_config)
    (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  BIND pol0 <-
    res_to_alarm
      PolIRs.PolyLang.dummy
      (ParallelCore.CoreOpt.Extractor.extractor loop) -;
  let pol := ParallelCore.CoreOpt.Strengthen.strengthen_pprog pol0 in
  match cfg with
  | SeqCompiler.VIdentity =>
      checked_sequential_current_annotated_codegen pol
  | SeqCompiler.VAffine =>
      BIND pol' <- ParallelCore.CoreOpt.checked_affine_schedule pol -;
      checked_sequential_current_annotated_codegen pol'
  | SeqCompiler.VDefault =>
      BIND pol' <-
        ParallelCore.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SeqCompiler.VDefaultBand =>
      BIND pol' <-
        ParallelCore.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SeqCompiler.VIdentitySecondLevel =>
      lift_sequential_compile (SeqCompiler.compile_verified cfg loop)
  | SeqCompiler.VIdentitySecondLevelISS =>
      lift_sequential_compile (SeqCompiler.compile_verified cfg loop)
  | SeqCompiler.VIdentityBand =>
      BIND pol' <-
        ParallelCore.identity_tiling_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SeqCompiler.VIdentityBandISS =>
      lift_sequential_compile (SeqCompiler.compile_verified cfg loop)
  | SeqCompiler.VISS =>
      BIND pol' <-
        ParallelCore.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SeqCompiler.VDiamond =>
      BIND pol' <-
        ParallelCore.diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  | SeqCompiler.VDiamondISS =>
      BIND pol' <-
        ParallelCore.diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
      checked_sequential_current_annotated_codegen pol'
  end.

Definition compile_verified
    (cfg: verified_config) (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  match cfg with
  | VSeq seq_cfg =>
      compile_seq_verified seq_cfg loop
  | VParallelCurrentIdentity d =>
      ParallelCore.Opt_parallel_current_identity loop d
  | VParallelCurrentIdentityTiled d =>
      ParallelCore.Opt_parallel_current_identity_tiled loop d
  | VParallelCurrentAffine d =>
      ParallelCore.Opt_parallel_current_affine loop d
  | VParallelCurrentDefault d =>
      ParallelCore.Opt_parallel_current loop d
  | VParallelCurrentDiamond d =>
      ParallelCore.Opt_parallel_current_diamond loop d
  | VParallelCurrentDiamondISS d =>
      ParallelCore.Opt_parallel_current_diamond_with_iss loop d
  | VParallelCurrentIdentityISS d =>
      ParallelCore.Opt_parallel_current_identity_with_iss loop d
  | VParallelCurrentAffineISS d =>
      ParallelCore.Opt_parallel_current_affine_with_iss loop d
  | VParallelCurrentDefaultISS d =>
      ParallelCore.Opt_parallel_current_with_iss loop d
  end.

Definition compile (cfg: raw_config) (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  match check_config cfg with
  | Okk vcfg => compile_verified vcfg loop
  | Err msg => res_to_alarm ParallelCore.parallel_dummy (Err msg)
  end.

Lemma checked_lift_sequential_loop_correct :
  forall loop pl st st',
    mayReturn (checked_lift_sequential_loop loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop pl st st' Hlift Hsem.
  unfold checked_lift_sequential_loop in Hlift.
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

Lemma opt_parallel_current_identity_tiled_correct :
  forall loop d pl st st',
    mayReturn (ParallelCore.Opt_parallel_current_identity_tiled loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold ParallelCore.Opt_parallel_current_identity_tiled in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply ParallelCorrect.Opt_parallel_current_identity_tiled_result_correct; eauto.
Qed.

Lemma checked_sequential_current_annotated_codegen_correct :
  forall pol pl st st',
    mayReturn (checked_sequential_current_annotated_codegen pol) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pl st st' Hcodegen Hwf Hsem.
  unfold checked_sequential_current_annotated_codegen in Hcodegen.
  bind_imp_destruct Hcodegen res Hchecked.
  pose proof Hcodegen as Hres.
  apply res_to_alarm_correct in Hres.
  subst res.
  eapply ParallelCodegenCore.checked_annotated_codegen_many_correct_general;
    eauto.
Qed.

Ltac finish_strengthened_source loop pol0 st Hextok Hroute :=
  let st_str := fresh "st_str" in
  let Hstr_sem := fresh "Hstr_sem" in
  let Heq_str := fresh "Heq_str" in
  destruct Hroute as [st_str [Hstr_sem Heq_str]];
  eapply ParallelCore.CoreOpt.Strengthen.instance_list_semantics_unstrengthen
    in Hstr_sem;
  let Hext_corr := fresh "Hext_corr" in
  pose proof
    (ParallelCore.CoreOpt.Extractor.extractor_correct
       loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr;
  let st_src := fresh "st_src" in
  let Hloop_src := fresh "Hloop_src" in
  let Heq_src := fresh "Heq_src" in
  destruct Hext_corr as [st_src [Hloop_src Heq_src]];
  exists st_src;
  split; [exact Hloop_src|];
  eapply State.eq_trans; [exact Heq_str| exact Heq_src].

Ltac finish_strengthened_source_with loop pol0 st Heq_out Hextok Hroute :=
  let st_str := fresh "st_str" in
  let Hstr_sem := fresh "Hstr_sem" in
  let Heq_str := fresh "Heq_str" in
  destruct Hroute as [st_str [Hstr_sem Heq_str]];
  eapply ParallelCore.CoreOpt.Strengthen.instance_list_semantics_unstrengthen
    in Hstr_sem;
  let Hext_corr := fresh "Hext_corr" in
  pose proof
    (ParallelCore.CoreOpt.Extractor.extractor_correct
       loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr;
  let st_src := fresh "st_src" in
  let Hloop_src := fresh "Hloop_src" in
  let Heq_src := fresh "Heq_src" in
  destruct Hext_corr as [st_src [Hloop_src Heq_src]];
  exists st_src;
  split; [exact Hloop_src|];
  eapply State.eq_trans;
    [exact Heq_out| eapply State.eq_trans; [exact Heq_str| exact Heq_src]].

Lemma compile_seq_verified_correct :
  forall cfg loop pl st st',
    mayReturn (compile_seq_verified cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  unfold compile_seq_verified in Hcompile.
  bind_imp_destruct Hcompile pol0 Hextimp.
  set (pol := ParallelCore.CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (ParallelCore.CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (ParallelCore.CoreOpt.extractor_success_wf_pprog_affine
          loop pol0 Hextok))
    as Hwf_pol.
  destruct cfg; simpl in Hcompile.
  - pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol pl st st' Hcompile
         (PolyLang.wf_pprog_affine_implies_wf_pprog_general _ Hwf_pol)
         Hsem)
      as Hroute.
    finish_strengthened_source loop pol0 st Hextok Hroute.
  - bind_imp_destruct Hcompile pol_mid Hsched.
    pose proof
      (ParallelCore.CoreOpt.scheduler'_preserve_wf
         pol pol_mid Hwf_pol pol_mid Hsched eq_refl)
      as Hwf_mid.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_mid pl st st' Hcompile
         (PolyLang.wf_pprog_affine_implies_wf_pprog_general _ Hwf_mid)
         Hsem)
      as Hmid_corr.
    destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
    pose proof
      (ParallelCore.CoreOpt.scheduler'_correct
         pol st st_mid pol_mid Hsched Hmid_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_mid Hextok Hroute.
  - bind_imp_destruct Hcompile pol_after Hphase.
    pose proof
      (ParallelCorrect.phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
         pol pol_after Hwf_pol Hphase)
      as Hwf_after.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_after pl st st' Hcompile Hwf_after Hsem)
      as Hafter_corr.
    destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
    pose proof
      (ParallelCorrect.phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
         pol pol_after st st_after Hwf_pol Hphase Hafter_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_after Hextok Hroute.
  - bind_imp_destruct Hcompile pol_after Hphase.
    pose proof
      (ParallelCorrect.phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
         pol pol_after Hwf_pol Hphase)
      as Hwf_after.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_after pl st st' Hcompile Hwf_after Hsem)
      as Hafter_corr.
    destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
    pose proof
      (ParallelCorrect.phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
         pol pol_after st st_after Hwf_pol Hphase Hafter_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_after Hextok Hroute.
  - unfold lift_sequential_compile in Hcompile.
    apply mayReturn_bind in Hcompile.
    destruct Hcompile as [loop' [Hseq Hlift]].
    destruct
      (checked_lift_sequential_loop_correct loop' pl st st' Hlift Hsem)
      as [st_mid [Hmid_sem Heq_mid]].
    destruct
      (SeqCompiler.compile_verified_correct
         SeqCompiler.VIdentitySecondLevel loop st st_mid loop' Hseq Hmid_sem)
      as [st_src [Hsrc_sem Heq_src]].
    exists st_src. split; auto. eapply State.eq_trans; eauto.
  - unfold lift_sequential_compile in Hcompile.
    apply mayReturn_bind in Hcompile.
    destruct Hcompile as [loop' [Hseq Hlift]].
    destruct
      (checked_lift_sequential_loop_correct loop' pl st st' Hlift Hsem)
      as [st_mid [Hmid_sem Heq_mid]].
    destruct
      (SeqCompiler.compile_verified_correct
         SeqCompiler.VIdentitySecondLevelISS loop st st_mid loop' Hseq Hmid_sem)
      as [st_src [Hsrc_sem Heq_src]].
    exists st_src. split; auto. eapply State.eq_trans; eauto.
  - bind_imp_destruct Hcompile pol_after Hidentity.
    pose proof
      (ParallelCorrect.identity_tiling_opt_prepared_from_poly_no_iss_poly_wf
         pol pol_after Hwf_pol Hidentity)
      as Hwf_after.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_after pl st st' Hcompile Hwf_after Hsem)
      as Hafter_corr.
    destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
    pose proof
      (ParallelCorrect.identity_tiling_opt_prepared_from_poly_no_iss_poly_correct
         pol pol_after st st_after Hwf_pol Hidentity Hafter_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_after Hextok Hroute.
  - unfold lift_sequential_compile in Hcompile.
    apply mayReturn_bind in Hcompile.
    destruct Hcompile as [loop' [Hseq Hlift]].
    destruct
      (checked_lift_sequential_loop_correct loop' pl st st' Hlift Hsem)
      as [st_mid [Hmid_sem Heq_mid]].
    destruct
      (SeqCompiler.compile_verified_correct
         SeqCompiler.VIdentityBandISS loop st st_mid loop' Hseq Hmid_sem)
      as [st_src [Hsrc_sem Heq_src]].
    exists st_src. split; auto. eapply State.eq_trans; eauto.
  - bind_imp_destruct Hcompile pol_after Hphase.
    pose proof
      (ParallelCorrect.phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
         pol pol_after Hwf_pol Hphase)
      as Hwf_after.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_after pl st st' Hcompile Hwf_after Hsem)
      as Hafter_corr.
    destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
    pose proof
      (ParallelCorrect.phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
         pol pol_after st st_after Hwf_pol Hphase Hafter_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_after Hextok Hroute.
  - bind_imp_destruct Hcompile pol_after Hdiamond.
    pose proof
      (ParallelCorrect.diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
         pol pol_after Hwf_pol Hdiamond)
      as Hwf_after.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_after pl st st' Hcompile Hwf_after Hsem)
      as Hafter_corr.
    destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
    pose proof
      (ParallelCorrect.diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
         pol pol_after st st_after Hwf_pol Hdiamond Hafter_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_after Hextok Hroute.
  - bind_imp_destruct Hcompile pol_after Hdiamond.
    pose proof
      (ParallelCorrect.diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
         pol pol_after Hwf_pol Hdiamond)
      as Hwf_after.
    pose proof
      (checked_sequential_current_annotated_codegen_correct
         pol_after pl st st' Hcompile Hwf_after Hsem)
      as Hafter_corr.
    destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
    pose proof
      (ParallelCorrect.diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
         pol pol_after st st_after Hwf_pol Hdiamond Hafter_sem)
      as Hroute.
    finish_strengthened_source_with loop pol0 st Heq_after Hextok Hroute.
Qed.

Theorem compile_verified_correct :
  forall cfg loop pl st st',
    mayReturn (compile_verified cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  destruct cfg; simpl in Hcompile.
  - eapply compile_seq_verified_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_correct; eauto.
  - eapply opt_parallel_current_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_diamond_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_diamond_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_with_iss_correct; eauto.
Qed.

Theorem compile_correct :
  forall cfg loop pl st st',
    mayReturn (compile cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
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

End VerifiedParallelCompilerConfig.
