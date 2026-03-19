Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Require Import ISSValidatorCorrect.
Require Import PolIRs.
Require Import PolOpt.
Require Import ParallelPolOpt.
Require Import Result.

Local Open Scope impure_scope.

Module ParallelPolOptCorrect (PolIRs: POLIRS).

Module Core := ParallelPolOpt PolIRs.
Module CoreOpt := PolOpt PolIRs.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.
Module ParallelLoop := Core.ParallelCodegenCore.ParallelLoop.

Lemma checked_parallel_current_annotated_codegen_at_correct :
  forall pol d pl st st',
    mayReturn (Core.checked_parallel_current_annotated_codegen_at pol d) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hopt Hwf Hsem.
  unfold Core.checked_parallel_current_annotated_codegen_at in Hopt.
  eapply Core.checked_parallel_current_annotated_codegen_correct; eauto.
Qed.

Lemma try_verified_tiling_after_phase_mid_poly_correct :
  forall pol_mid mid_scop after_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_mid ->
    mayReturn
      (Core.try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\ State.eq st' st''.
Proof.
  intros pol_mid mid_scop after_scop pol_out st st' Hwf_mid Hopt Hsem_out.
  unfold Core.try_verified_tiling_after_phase_mid_poly in Hopt.
  remember (Core.CoreOpt.infer_tiling_witness_scops mid_scop after_scop) as wsres
    eqn:Hws.
  destruct wsres as [ws|msg].
  { remember (Core.ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as after_res eqn:Hafter.
    destruct after_res as [pol_after|msg_after].
    { simpl in Hopt.
      bind_imp_destruct Hopt ok Hcheck.
      destruct ok.
      { eapply mayReturn_pure in Hopt. subst pol_out.
        pose proof
          (Core.ValidatorCore.checked_tiling_validate_poly_implies_wf_after
             pol_mid pol_after ws Hcheck)
          as Hwf_after.
        pose proof
          (proj1 (PolyLang.instance_list_semantics_current_view_iff
                    pol_after st st' Hwf_after) Hsem_out)
          as Hsem_after.
        destruct
          (Core.ValidatorCore.checked_tiling_validate_poly_correct
             pol_mid pol_after ws st st' Hcheck Hsem_after)
          as [st_mid [Hmid_sem Heq_mid]].
        exists st_mid.
        split; assumption. }
      { eapply mayReturn_pure in Hopt. subst pol_out.
        exists st'. split; auto. eapply State.eq_refl. } }
    { simpl in Hopt.
      eapply mayReturn_pure in Hopt. subst pol_out.
      exists st'. split; auto. eapply State.eq_refl. } }
  { simpl in Hopt.
    eapply mayReturn_pure in Hopt. subst pol_out.
    exists st'. split; auto. eapply State.eq_refl. }
Qed.

Lemma try_verified_tiling_after_phase_mid_poly_wf :
  forall pol_mid mid_scop after_scop pol_out,
    PolyLang.wf_pprog_affine pol_mid ->
    mayReturn
      (Core.try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_mid mid_scop after_scop pol_out Hwf_mid Hopt.
  unfold Core.try_verified_tiling_after_phase_mid_poly in Hopt.
  remember (Core.CoreOpt.infer_tiling_witness_scops mid_scop after_scop) as wsres
    eqn:Hws.
  destruct wsres as [ws|msg].
  { remember (Core.ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as after_res eqn:Hafter.
    destruct after_res as [pol_after|msg_after].
    { simpl in Hopt.
      bind_imp_destruct Hopt ok Hcheck.
      destruct ok.
      { eapply mayReturn_pure in Hopt. subst pol_out.
        pose proof
          (Core.ValidatorCore.checked_tiling_validate_poly_implies_wf_after
             pol_mid pol_after ws Hcheck)
          as Hwf_after.
        pose proof
          (PolyLang.wf_pprog_general_current_view_affine pol_after Hwf_after)
          as Hwf_cur_aff.
        eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. }
      { eapply mayReturn_pure in Hopt. subst pol_out.
        eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. } }
    { simpl in Hopt.
      eapply mayReturn_pure in Hopt. subst pol_out.
      eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. } }
  { simpl in Hopt.
    eapply mayReturn_pure in Hopt. subst pol_out.
    eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. }
Qed.

Lemma try_phase_pipeline_from_source_pol_poly_correct :
  forall pol_source phase_runner before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_phase_pipeline_from_source_pol_poly
         pol_source phase_runner before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\ State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop pol_out st st'
         Hwf_source Hopt Hsem_out.
  unfold Core.try_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_tiling_after_phase_mid_poly_correct
             pol_mid mid_scop after_scop pol_out st st'
             Hwf_mid Hopt Hsem_out)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (Core.ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * eapply CoreOpt.scheduler'_correct; eauto.
    + eapply CoreOpt.scheduler'_correct; eauto.
  - eapply CoreOpt.scheduler'_correct; eauto.
Qed.

Lemma try_phase_pipeline_from_source_pol_poly_wf :
  forall pol_source phase_runner before_scop pol_out,
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_phase_pipeline_from_source_pol_poly
         pol_source phase_runner before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_source phase_runner before_scop pol_out Hwf_source Hopt.
  unfold Core.try_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        eapply try_verified_tiling_after_phase_mid_poly_wf; eauto.
      * pose proof
          (CoreOpt.scheduler'_preserve_wf
             pol_source pol_out Hwf_source pol_out Hopt eq_refl)
          as Hwf_out.
        eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
    + pose proof
        (CoreOpt.scheduler'_preserve_wf
           pol_source pol_out Hwf_source pol_out Hopt eq_refl)
        as Hwf_out.
      eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
  - pose proof
      (CoreOpt.scheduler'_preserve_wf
         pol_source pol_out Hwf_source pol_out Hopt eq_refl)
      as Hwf_out.
    eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_phase_pipeline_from_source_pol_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { simpl in Hopt.
      eapply CoreOpt.scheduler'_correct.
      - exact Hopt.
      - exact Hsem_out. } }
  { simpl in Hopt.
    eapply mayReturn_pure in Hopt. subst pol_out.
    exists st'. split; auto. eapply State.eq_refl. }
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_phase_pipeline_from_source_pol_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { simpl in Hopt.
      pose proof
        (CoreOpt.scheduler'_preserve_wf pol pol_out Hwf pol_out Hopt eq_refl)
        as Hwf_out.
      eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. } }
  { simpl in Hopt.
    eapply mayReturn_pure in Hopt. subst pol_out.
    eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. }
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_poly_correct :
  forall pol before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.try_checked_iss_phase_pipeline_from_poly_poly pol before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol before_scop pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.try_checked_iss_phase_pipeline_from_poly_poly in Hopt.
  destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (CoreOpt.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           pose proof
             (try_phase_pipeline_from_source_pol_poly_correct
                pol_iss
                CoreOpt.run_pluto_phase_pipeline_with_iss
                before_scop
                pol_out st st' Hwf_iss Hopt Hsem_out)
             as Hiss_corr.
           destruct Hiss_corr as [st_iss [Hiss_sem Heq_iss]].
           pose proof
             (ISSValidatorCorrectCore
                .checked_iss_complete_cut_shape_validate_semantics_correct
                pol pol_iss w st st_iss Hiss_check Hiss_sem)
             as Hback.
           destruct Hback as [st_src [Hsrc_sem Heq_src]].
           exists st_src.
           split; auto.
           eapply State.eq_trans; eauto.
        -- eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
      * eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
    + eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
  - eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_poly_wf :
  forall pol before_scop pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.try_checked_iss_phase_pipeline_from_poly_poly pol before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol before_scop pol_out Hwf Hopt.
  unfold Core.try_checked_iss_phase_pipeline_from_poly_poly in Hopt.
  destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (CoreOpt.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
        -- eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
      * eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
    + eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
  - eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_checked_iss_phase_pipeline_from_poly_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { simpl in Hopt.
      eapply CoreOpt.scheduler'_correct.
      - exact Hopt.
      - exact Hsem_out. } }
  { simpl in Hopt.
    eapply mayReturn_pure in Hopt. subst pol_out.
    exists st'. split; auto. eapply State.eq_refl. }
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_checked_iss_phase_pipeline_from_poly_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { simpl in Hopt.
      pose proof
        (CoreOpt.scheduler'_preserve_wf pol pol_out Hwf pol_out Hopt eq_refl)
        as Hwf_out.
      eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. } }
  { simpl in Hopt.
    eapply mayReturn_pure in Hopt. subst pol_out.
    eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. }
Qed.

Lemma iss_only_prepared_from_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_only_prepared_from_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.iss_only_prepared_from_poly in Hopt.
  destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
  - destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
      eqn:Hiss_infer.
    + destruct iss_opt as [[pol_iss w]|].
      * destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
          eqn:Hiss_check.
        -- bind_imp_destruct Hopt iss_wf Hiss_wf.
           destruct iss_wf.
           ++ eapply mayReturn_pure in Hopt. subst pol_out.
              eapply ISSValidatorCorrectCore.checked_iss_complete_cut_shape_validate_semantics_correct;
                eauto.
           ++ eapply mayReturn_pure in Hopt. subst pol_out.
              exists st'. split; auto. eapply State.eq_refl.
        -- eapply mayReturn_pure in Hopt. subst pol_out.
           exists st'. split; auto. eapply State.eq_refl.
      * eapply mayReturn_pure in Hopt. subst pol_out.
        exists st'. split; auto. eapply State.eq_refl.
    + eapply mayReturn_pure in Hopt. subst pol_out.
      exists st'. split; auto. eapply State.eq_refl.
  - eapply mayReturn_pure in Hopt. subst pol_out.
    exists st'. split; auto. eapply State.eq_refl.
Qed.

Lemma iss_only_prepared_from_poly_wf_affine :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_only_prepared_from_poly pol) pol_out ->
    PolyLang.wf_pprog_affine pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.iss_only_prepared_from_poly in Hopt.
  destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
  - destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
      eqn:Hiss_infer.
    + destruct iss_opt as [[pol_iss w]|].
      * destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
          eqn:Hiss_check.
        -- bind_imp_destruct Hopt iss_wf Hiss_wf.
           destruct iss_wf.
           ++ eapply mayReturn_pure in Hopt. subst pol_out.
              eapply CoreOpt.check_wf_polyprog_affine_correct.
              ** exact Hiss_wf.
              ** reflexivity.
           ++ eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
        -- eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
      * eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
    + eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
  - eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
Qed.

Lemma iss_affine_prepared_from_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_affine_prepared_from_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.iss_affine_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  pose proof
    (CoreOpt.scheduler'_correct pol_iss st st' pol_out Hopt Hsem_out)
    as Haff_corr.
  destruct Haff_corr as [st_iss [Hiss_sem Heq_iss]].
  pose proof
    (iss_only_prepared_from_poly_correct pol pol_iss st st_iss Hwf Hiss Hiss_sem)
    as Hsrc_corr.
  destruct Hsrc_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma iss_affine_prepared_from_poly_wf_affine :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_affine_prepared_from_poly pol) pol_out ->
    PolyLang.wf_pprog_affine pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.iss_affine_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  eapply CoreOpt.scheduler'_preserve_wf; eauto.
Qed.

Lemma parallel_current_identity_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_identity_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_identity_prepared_from_poly in Hopt.
  eapply checked_parallel_current_annotated_codegen_at_correct; eauto.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
Qed.

Lemma parallel_current_affine_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_affine_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_affine_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol_mid Hsched.
  pose proof
    (CoreOpt.scheduler'_preserve_wf pol pol_mid Hwf pol_mid Hsched eq_refl)
    as Hwf_mid.
  pose proof
    (checked_parallel_current_annotated_codegen_at_correct
       pol_mid d pl st st' Hopt
       (PolyLang.wf_pprog_affine_implies_wf_pprog_general _ Hwf_mid)
       Hsem)
    as Hmid_corr.
  destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
  pose proof
    (CoreOpt.scheduler'_correct pol st st_mid pol_mid Hsched Hmid_sem)
    as Hsched_corr.
  destruct Hsched_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma parallel_current_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol_after Hphase.
  pose proof
    (phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
       pol pol_after Hwf Hphase)
    as Hwf_after.
  pose proof
    (checked_parallel_current_annotated_codegen_at_correct
       pol_after d pl st st' Hopt Hwf_after Hsem)
    as Hafter_corr.
  destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
  pose proof
    (phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
       pol pol_after st st_after Hwf Hphase Hafter_sem)
    as Hphase_corr.
  destruct Hphase_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma parallel_current_identity_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_identity_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_identity_prepared_from_poly_with_iss in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  pose proof
    (checked_parallel_current_annotated_codegen_at_correct
       pol_iss d pl st st' Hopt
       (PolyLang.wf_pprog_affine_implies_wf_pprog_general _ Hwf_iss)
       Hsem)
    as Hiss_corr.
  destruct Hiss_corr as [st_iss [Hiss_sem Heq_iss]].
  pose proof
    (iss_only_prepared_from_poly_correct pol pol_iss st st_iss Hwf Hiss Hiss_sem)
    as Hsrc_corr.
  destruct Hsrc_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma parallel_current_affine_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_affine_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_affine_prepared_from_poly_with_iss in Hopt.
  bind_imp_destruct Hopt pol_mid Hiss_affine.
  pose proof
    (iss_affine_prepared_from_poly_wf_affine pol pol_mid Hwf Hiss_affine)
    as Hwf_mid.
  pose proof
    (checked_parallel_current_annotated_codegen_at_correct
       pol_mid d pl st st' Hopt
       (PolyLang.wf_pprog_affine_implies_wf_pprog_general _ Hwf_mid)
       Hsem)
    as Hmid_corr.
  destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
  pose proof
    (iss_affine_prepared_from_poly_correct pol pol_mid st st_mid Hwf Hiss_affine Hmid_sem)
    as Hsrc_corr.
  destruct Hsrc_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma parallel_current_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_prepared_from_poly_with_iss in Hopt.
  bind_imp_destruct Hopt pol_after Hphase.
  pose proof
    (phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
       pol pol_after Hwf Hphase)
    as Hwf_after.
  pose proof
    (checked_parallel_current_annotated_codegen_at_correct
       pol_after d pl st st' Hopt Hwf_after Hsem)
    as Hafter_corr.
  destruct Hafter_corr as [st_after [Hafter_sem Heq_after]].
  pose proof
    (phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
       pol pol_after st st_after Hwf Hphase Hafter_sem)
    as Hphase_corr.
  destruct Hphase_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Theorem Opt_parallel_current_identity_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_result in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (parallel_current_identity_prepared_from_poly_correct
       pol d pl st st' Hwf_pol Hopt Hsem)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (CoreOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_parallel_current_affine_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_affine_result in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (parallel_current_affine_prepared_from_poly_correct
       pol d pl st st' Hwf_pol Hopt Hsem)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (CoreOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_parallel_current_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_result in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (parallel_current_prepared_from_poly_correct
       pol d pl st st' Hwf_pol Hopt Hsem)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (CoreOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_parallel_current_identity_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_with_iss_result in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (parallel_current_identity_prepared_from_poly_with_iss_correct
       pol d pl st st' Hwf_pol Hopt Hsem)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (CoreOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_parallel_current_affine_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_affine_with_iss_result in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (parallel_current_affine_prepared_from_poly_with_iss_correct
       pol d pl st st' Hwf_pol Hopt Hsem)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (CoreOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_parallel_current_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_with_iss_result in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (parallel_current_prepared_from_poly_with_iss_correct
       pol d pl st st' Hwf_pol Hopt Hsem)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (CoreOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_parallel_current_identity_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Opt_parallel_current_identity_result_correct; eauto.
Qed.

Theorem Opt_parallel_current_affine_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_affine in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Opt_parallel_current_affine_result_correct; eauto.
Qed.

Theorem Opt_parallel_current_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Opt_parallel_current_result_correct; eauto.
Qed.

Theorem Opt_parallel_current_identity_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_with_iss in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Opt_parallel_current_identity_with_iss_result_correct; eauto.
Qed.

Theorem Opt_parallel_current_affine_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_affine_with_iss in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Opt_parallel_current_affine_with_iss_result_correct; eauto.
Qed.

Theorem Opt_parallel_current_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_with_iss in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Opt_parallel_current_with_iss_result_correct; eauto.
Qed.

End ParallelPolOptCorrect.
