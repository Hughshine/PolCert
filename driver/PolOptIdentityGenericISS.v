Require Import PolIRs.
Require Import PolOpt.
Require Import ISSValidatorCorrect.
Require Import LibTactics.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module PolOptIdentityGenericISS (PolIRs: POLIRS).

Module BaseOpt := PolOpt PolIRs.
Module ValidatorCore := BaseOpt.ValidatorCore.
Module PrepareCore := BaseOpt.PrepareCore.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module PolyLang := PolIRs.PolyLang.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

Open Scope impure_scope.
Open Scope opt_scop.

Lemma try_checked_iss_identity_tiling_generic_phase_pipeline_from_poly_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      BaseOpt.try_checked_iss_identity_tiling_generic_phase_pipeline_from_poly
        pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold BaseOpt.try_checked_iss_identity_tiling_generic_phase_pipeline_from_poly in Hopt.
  destruct (BaseOpt.infer_iss_from_source_scop pol before_scop)
    as [[iss_res|]|msg] eqn:Hiss.
  - destruct iss_res as [pol_iss w].
    destruct (ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
      eqn:Hiss_check.
    + bind_imp_destruct Hopt iss_wf Hiss_wf.
      destruct iss_wf.
      * pose proof
          (BaseOpt.check_wf_polyprog_affine_correct
             pol_iss _ Hiss_wf eq_refl)
          as Hwf_iss.
        destruct (BaseOpt.export_for_phase_scheduler pol_iss)
          as [iss_scop|] eqn:Hiss_scop.
        -- pose proof
             (BaseOpt.try_phase_pipeline_from_source_pol_correct
                pol_iss
                BaseOpt.run_pluto_identity_tiling_pipeline
                iss_scop st st' Hwf_iss loop' Hopt Hloop)
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
        -- pose proof
             (PrepareCore.prepared_codegen_correct
                pol_iss st st' loop' Hopt Hwf_iss Hloop)
             as Hiss_sem.
           pose proof
             (ISSValidatorCorrectCore
                .checked_iss_complete_cut_shape_validate_semantics_correct
                pol pol_iss w st st' Hiss_check Hiss_sem)
             as Hback.
           destruct Hback as [st_src [Hsrc_sem Heq_src]].
           exists st_src.
           split; auto.
      * eapply BaseOpt.identity_tiling_generic_opt_prepared_from_poly_correct; eauto.
    + eapply BaseOpt.identity_tiling_generic_opt_prepared_from_poly_correct; eauto.
  - eapply BaseOpt.identity_tiling_generic_opt_prepared_from_poly_correct; eauto.
  - eapply BaseOpt.identity_tiling_generic_opt_prepared_from_poly_correct; eauto.
Qed.

Lemma identity_tiling_generic_opt_prepared_from_poly_with_iss_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      BaseOpt.identity_tiling_generic_opt_prepared_from_poly_with_iss pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold BaseOpt.identity_tiling_generic_opt_prepared_from_poly_with_iss in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_identity_tiling_generic_phase_pipeline_from_poly_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Theorem identity_tiling_generic_opt_prepared_with_iss_correct:
  forall loop st st',
    WHEN loop' <- BaseOpt.identity_tiling_generic_opt_prepared_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold BaseOpt.identity_tiling_generic_opt_prepared_with_iss in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0
          Hextok))
    as Hwf_pol.
  pose proof
    (identity_tiling_generic_opt_prepared_from_poly_with_iss_correct
       pol st st' Hwf_pol loop' Hopt Hloop)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply BaseOpt.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof
    (BaseOpt.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Close Scope opt_scop.
Close Scope impure_scope.

End PolOptIdentityGenericISS.
