Require Import TilingBandScheduleValidator.
Require Import TilingWitness.
Require Import PolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module PolOptBandTiling (PolIRs: POLIRS).

Module BaseOpt := PolOpt PolIRs.
Module ValidatorCore := BaseOpt.ValidatorCore.
Module PrepareCore := BaseOpt.PrepareCore.
Module TilingSched := TilingBandScheduleValidator PolIRs.
Module PolyLang := PolIRs.PolyLang.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

Open Scope impure_scope.
Open Scope opt_scop.

Definition try_verified_tiling_after_phase_mid_band
    (pol_mid: PolyLang.t)
    (mid_scop after_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_tiling_witness_scops mid_scop after_scop with
  | Err _ =>
      PrepareCore.prepared_codegen pol_mid
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws with
      | Err _ =>
          PrepareCore.prepared_codegen pol_mid
      | Okk pol_after =>
          BIND ok_shape <- TilingSched.checked_tiling_schedule_stripmined_validate_poly pol_mid pol_after ws -;
          if ok_shape then
            match TilingSched.infer_pprog_tiling_bands
                    (TilingSched.Base.outer_to_tiling_pprog pol_mid) ws with
            | None =>
                PrepareCore.prepared_codegen pol_mid
            | Some bands =>
                BIND ok_perm <-
                  TilingSched.check_pprog_permutable_tiling_bands_via_validate_tiling
                    (TilingSched.Base.outer_to_tiling_pprog pol_mid)
                    (TilingSched.Base.outer_to_tiling_pprog pol_after)
                    ws bands -;
                if ok_perm then
                  BIND wf_after <- ValidatorCore.check_wf_polyprog_general pol_after -;
                  if wf_after then
                    PrepareCore.prepared_codegen (PolyLang.current_view_pprog pol_after)
                  else
                    PrepareCore.prepared_codegen pol_mid
                else
                  PrepareCore.prepared_codegen pol_mid
            end
          else
            PrepareCore.prepared_codegen pol_mid
      end
  end.

Definition try_phase_pipeline_from_source_pol_band
    (pol_source: PolyLang.t)
    (phase_runner: OpenScop -> result (OpenScop * OpenScop))
    (before_scop: OpenScop): imp LoopIR.t :=
  match phase_runner before_scop with
  | Err _ =>
      BaseOpt.affine_only_opt_prepared_from_poly pol_source
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          BaseOpt.affine_only_opt_prepared_from_poly pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop
          else
            BaseOpt.affine_only_opt_prepared_from_poly pol_source
      end
  end.

Definition phase_pipeline_opt_prepared_from_poly_no_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol
          BaseOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        BaseOpt.affine_only_opt_prepared_from_poly pol
    end
  else
    PrepareCore.prepared_codegen pol.

Definition phase_pipeline_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_pipeline_opt_prepared_from_poly_no_iss_band pol.

Lemma try_verified_tiling_after_phase_mid_band_correct:
  forall pol_mid mid_scop after_scop st st',
    PolyLang.wf_pprog_affine pol_mid ->
    WHEN loop' <- try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\
      State.eq st' st''.
Proof.
  intros pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop.
  unfold try_verified_tiling_after_phase_mid_band in Hopt.
  destruct (BaseOpt.infer_tiling_witness_scops mid_scop after_scop) as [ws|msg] eqn:Hws.
  - destruct
      (ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as [pol_after|msg_after] eqn:Hafter.
    + bind_imp_destruct Hopt ok_shape Hcheck_shape.
      destruct ok_shape.
      * destruct (TilingSched.infer_pprog_tiling_bands
                    (TilingSched.Base.outer_to_tiling_pprog pol_mid) ws)
          as [bands|] eqn:Hbands.
        -- bind_imp_destruct Hopt ok_perm Hcheck_perm.
           destruct ok_perm.
           ++ bind_imp_destruct Hopt wf_after_ok Hwf_check.
              destruct wf_after_ok.
              ** pose proof
                   (ValidatorCore.AffineCore.check_wf_polyprog_tiling_correct
                      pol_after true Hwf_check eq_refl)
                   as Hwf_after.
                 pose proof
                   (PrepareCore.prepared_codegen_correct_general
                      pol_after st st' loop' Hopt Hwf_after Hloop)
                   as Hsem_after.
                 remember (TilingSched.Base.outer_to_tiling_pprog pol_mid)
                   as before_tiling eqn:Hbefore_tiling_eq.
                 remember (TilingSched.Base.outer_to_tiling_pprog pol_after)
                   as after_tiling eqn:Hafter_tiling_eq.
                 pose proof Hcheck_shape as Hcheck_shape_sched.
                 unfold TilingSched.checked_tiling_schedule_stripmined_validate_poly,
                        TilingSched.checked_tiling_schedule_stripmined_validate_outer
                   in Hcheck_shape.
                 unfold TilingSched.checked_tiling_schedule_stripmined_validate_poly,
                        TilingSched.checked_tiling_schedule_stripmined_validate_outer,
                        TilingSched.checked_tiling_schedule_stripmined_validate
                   in Hcheck_shape_sched.
                 apply mayReturn_pure in Hcheck_shape_sched.
                 apply andb_true_iff in Hcheck_shape_sched.
                 destruct Hcheck_shape_sched as [_ Hsched_only].
                 destruct before_tiling as [[before_pis before_ctxt] before_vars].
                 destruct after_tiling as [[after_pis after_ctxt] after_vars].
                 simpl in Hbefore_tiling_eq, Hafter_tiling_eq.
                 rewrite <- Hbefore_tiling_eq in Hcheck_shape, Hsched_only.
                 rewrite <- Hafter_tiling_eq in Hcheck_shape, Hsched_only.
                 simpl in Hcheck_shape, Hsched_only, Hbands.
                 pose proof
                   (TilingSched.check_pprog_tiling_schedule_stripminedb_ctxt_sound
                      (before_pis, before_ctxt, before_vars)
                      (after_pis, after_ctxt, after_vars)
                      ws Hsched_only)
                   as [Hctxt_eq Hvars_eq].
                 pose proof
                   (TilingSched.Base.outer_to_tiling_wf_pprog_affine
                      pol_mid Hwf_mid)
                   as Hwf_before_tiling.
                 rewrite <- Hbefore_tiling_eq in Hwf_before_tiling.
                 destruct Hwf_before_tiling as [_ Hwf_before_tiling].
                 assert (Hwfbefore_pis :
                   List.Forall
                     (TilingSched.Base.Tiling.PL.wf_pinstr_tiling
                        before_ctxt before_vars)
                     before_pis).
                 {
                   eapply List.Forall_forall.
                   intros pi Hin.
                   eapply
                     TilingSched.Base.Tiling.PL.wf_pinstr_affine_implies_wf_pinstr_tiling.
                   eapply Hwf_before_tiling; eauto.
                 }
                 pose proof
                   (TilingSched.Base.outer_to_tiling_wf_pprog_general
                      pol_after Hwf_after)
                   as Hwf_after_tiling.
                 rewrite <- Hafter_tiling_eq in Hwf_after_tiling.
                 rewrite <- Hctxt_eq, <- Hvars_eq in Hwf_after_tiling.
                 destruct Hwf_after_tiling as [_ Hwf_after_tiling].
                 assert (Hwfafter_pis :
                   List.Forall
                     (TilingSched.Base.Tiling.PL.wf_pinstr_tiling
                        before_ctxt before_vars)
                     after_pis).
                 {
                   eapply List.Forall_forall.
                   intros pi Hin.
                   eapply Hwf_after_tiling; eauto.
                 }
                 rewrite <- Hctxt_eq, <- Hvars_eq in Hcheck_shape, Hcheck_perm.
                 pose proof
                   (TilingSched.checked_tiling_schedule_stripmined_and_band_validate_correct_same_ctxt
                      before_pis before_ctxt before_vars
                      after_pis
                      ws bands st st'
                      Hcheck_shape Hbands
                      Hwfbefore_pis Hwfafter_pis
                      Hcheck_perm)
                   as Hcorr.
                 apply TilingSched.Base.outer_to_tiling_instance_list_semantics_iff in Hsem_after.
                 rewrite <- Hafter_tiling_eq in Hsem_after.
                 rewrite <- Hctxt_eq, <- Hvars_eq in Hsem_after.
                 specialize (Hcorr Hsem_after).
                 destruct Hcorr as [st_mid [Hmid_tiling Heq_mid]].
                 rewrite Hbefore_tiling_eq in Hmid_tiling.
                 apply TilingSched.Base.outer_to_tiling_instance_list_semantics_iff in Hmid_tiling.
                 exists st_mid. split; auto.
              ** pose proof
                   (PrepareCore.prepared_codegen_correct
                      pol_mid st st' loop' Hopt Hwf_mid Hloop)
                   as Hmid_sem.
                 exists st'. split; auto. apply State.eq_refl.
           ++ pose proof
                (PrepareCore.prepared_codegen_correct
                   pol_mid st st' loop' Hopt Hwf_mid Hloop)
                as Hmid_sem.
              exists st'. split; auto. apply State.eq_refl.
        -- pose proof
             (PrepareCore.prepared_codegen_correct
                pol_mid st st' loop' Hopt Hwf_mid Hloop)
             as Hmid_sem.
           exists st'. split; auto. apply State.eq_refl.
      * pose proof
           (PrepareCore.prepared_codegen_correct
              pol_mid st st' loop' Hopt Hwf_mid Hloop)
          as Hmid_sem.
        exists st'. split; auto. apply State.eq_refl.
    + pose proof
         (PrepareCore.prepared_codegen_correct
            pol_mid st st' loop' Hopt Hwf_mid Hloop)
        as Hmid_sem.
      exists st'. split; auto. apply State.eq_refl.
  - pose proof
       (PrepareCore.prepared_codegen_correct
          pol_mid st st' loop' Hopt Hwf_mid Hloop)
      as Hmid_sem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Lemma try_phase_pipeline_from_source_pol_band_correct:
  forall pol_source phase_runner before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_phase_pipeline_from_source_pol_band pol_source phase_runner before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_phase_pipeline_from_source_pol_band in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_tiling_after_phase_mid_band_correct
             pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_pipeline_opt_prepared_from_poly_no_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_pipeline_opt_prepared_from_poly_no_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Definition Opt_prepared_band := phase_pipeline_opt_prepared_band.
Definition Opt_band := Opt_prepared_band.

Theorem Opt_prepared_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_band, phase_pipeline_opt_prepared_band in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (phase_pipeline_opt_prepared_from_poly_no_iss_band_correct
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

Theorem Opt_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_band_correct; eauto.
Qed.

End PolOptBandTiling.
