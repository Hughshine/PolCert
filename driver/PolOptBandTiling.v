Require Import TilingBandScheduleValidator.
Require Import TilingWitness.
Require Import PolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ISSValidatorCorrect.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module PolOptBandTiling (PolIRs: POLIRS).

Module BaseOpt := PolOpt PolIRs.
Module ValidatorCore := BaseOpt.ValidatorCore.
Module PrepareCore := BaseOpt.PrepareCore.
Module TilingSched := TilingBandScheduleValidator PolIRs.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
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

Definition try_verified_diamond_after_phase_mid_band
    (pol_mid: PolyLang.t)
    (mid_scop posttile_scop after_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_tiling_witness_scops mid_scop posttile_scop with
  | Err _ =>
      PrepareCore.prepared_codegen pol_mid
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws with
      | Err _ =>
          PrepareCore.prepared_codegen pol_mid
      | Okk pol_posttile =>
          BIND ok_shape <- TilingSched.checked_tiling_schedule_stripmined_validate_poly pol_mid pol_posttile ws -;
          if ok_shape then
            match TilingSched.infer_pprog_tiling_bands
                    (TilingSched.Base.outer_to_tiling_pprog pol_mid) ws with
            | None =>
                PrepareCore.prepared_codegen pol_mid
            | Some bands =>
                BIND ok_perm <-
                  TilingSched.check_pprog_permutable_tiling_bands_via_validate_tiling
                    (TilingSched.Base.outer_to_tiling_pprog pol_mid)
                    (TilingSched.Base.outer_to_tiling_pprog pol_posttile)
                    ws bands -;
                if ok_perm then
                  BIND wf_posttile <- ValidatorCore.check_wf_polyprog_general pol_posttile -;
                  if wf_posttile then
                    match PolyLang.from_openscop_schedule_only pol_posttile after_scop with
                    | Err _ =>
                        PrepareCore.prepared_codegen pol_mid
                    | Okk pol_after =>
                        BIND final_ok <- ValidatorCore.validate_general pol_posttile pol_after -;
                        if final_ok then
                          BIND wf_after <- ValidatorCore.check_wf_polyprog_general pol_after -;
                          if wf_after then
                            PrepareCore.prepared_codegen
                              (PolyLang.current_view_pprog pol_after)
                          else
                            PrepareCore.prepared_codegen pol_mid
                        else
                          PrepareCore.prepared_codegen pol_mid
                    end
                  else
                    PrepareCore.prepared_codegen pol_mid
                else
                  PrepareCore.prepared_codegen pol_mid
            end
          else
            PrepareCore.prepared_codegen pol_mid
      end
  end.

Definition try_diamond_phase_pipeline_from_source_pol_band
    (pol_source: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.run_pluto_diamond_phase_pipeline before_scop with
  | Err _ =>
      BaseOpt.affine_only_opt_prepared_from_poly pol_source
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          BaseOpt.affine_only_opt_prepared_from_poly pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_diamond_after_phase_mid_band
              pol_mid mid_scop posttile_scop after_scop
          else
            BaseOpt.affine_only_opt_prepared_from_poly pol_source
      end
  end.

Definition try_diamond_phase_pipeline_from_source_pol_band_with_iss
    (pol_source: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.run_pluto_diamond_phase_pipeline_with_iss before_scop with
  | Err _ =>
      BaseOpt.affine_only_opt_prepared_from_poly pol_source
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          BaseOpt.affine_only_opt_prepared_from_poly pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_diamond_after_phase_mid_band
              pol_mid mid_scop posttile_scop after_scop
          else
            BaseOpt.affine_only_opt_prepared_from_poly pol_source
      end
  end.

Definition try_checked_iss_diamond_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          try_diamond_phase_pipeline_from_source_pol_band_with_iss
            pol_iss before_scop
        else
          try_diamond_phase_pipeline_from_source_pol_band pol before_scop
      else
        try_diamond_phase_pipeline_from_source_pol_band pol before_scop
  | _ =>
      try_diamond_phase_pipeline_from_source_pol_band pol before_scop
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

Definition identity_tiling_opt_prepared_from_poly_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol
          BaseOpt.run_pluto_identity_tiling_pipeline
          before_scop
    | None =>
        BaseOpt.affine_only_opt_prepared_from_poly pol
    end
  else
    PrepareCore.prepared_codegen pol.

Definition phase_diamond_opt_prepared_from_poly_no_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_diamond_phase_pipeline_from_source_pol_band pol before_scop
    | None =>
        BaseOpt.affine_only_opt_prepared_from_poly pol
    end
  else
    PrepareCore.prepared_codegen pol.

Definition phase_diamond_opt_prepared_from_poly_with_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_diamond_phase_pipeline_from_poly_band pol before_scop
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

Definition identity_tiling_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  identity_tiling_opt_prepared_from_poly_band pol.

Definition phase_diamond_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_diamond_opt_prepared_from_poly_no_iss_band pol.

Definition phase_diamond_opt_prepared_with_iss_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_diamond_opt_prepared_from_poly_with_iss_band pol.

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

Lemma identity_tiling_opt_prepared_from_poly_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- identity_tiling_opt_prepared_from_poly_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold identity_tiling_opt_prepared_from_poly_band in Hopt.
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
Definition Opt_prepared_identity_tiled_band := identity_tiling_opt_prepared_band.
Definition Opt_identity_tiled_band := Opt_prepared_identity_tiled_band.

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

Theorem Opt_prepared_identity_tiled_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_identity_tiled_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_identity_tiled_band, identity_tiling_opt_prepared_band in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (identity_tiling_opt_prepared_from_poly_band_correct
       pol st st' Hwf_pol loop' Hopt Hloop)
    as Hpol.
  destruct Hpol as [st_str [Hstr_sem Heq_str]].
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

Theorem Opt_identity_tiled_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_identity_tiled_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_identity_tiled_band_correct; eauto.
Qed.

Lemma try_verified_diamond_after_phase_mid_band_correct:
  forall pol_mid mid_scop posttile_scop after_scop st st',
    PolyLang.wf_pprog_affine pol_mid ->
    WHEN loop' <-
      try_verified_diamond_after_phase_mid_band
        pol_mid mid_scop posttile_scop after_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\
      State.eq st' st''.
Proof.
  intros pol_mid mid_scop posttile_scop after_scop st st'
         Hwf_mid loop' Hopt Hloop.
  unfold try_verified_diamond_after_phase_mid_band in Hopt.
  destruct (BaseOpt.infer_tiling_witness_scops mid_scop posttile_scop)
    as [ws|msg] eqn:Hws.
  - destruct
      (ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws)
      as [pol_posttile|msg_after] eqn:Hposttile.
    + bind_imp_destruct Hopt ok_shape Hcheck_shape.
      destruct ok_shape.
      * destruct (TilingSched.infer_pprog_tiling_bands
                    (TilingSched.Base.outer_to_tiling_pprog pol_mid) ws)
          as [bands|] eqn:Hbands.
        -- bind_imp_destruct Hopt ok_perm Hcheck_perm.
           destruct ok_perm.
           ++ bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
              destruct wf_posttile_ok.
              ** destruct (PolyLang.from_openscop_schedule_only
                             pol_posttile after_scop)
                   as [pol_after|msg_final] eqn:Hafter.
                 --- bind_imp_destruct Hopt final_ok Hfinal.
                     destruct final_ok.
                     +++ bind_imp_destruct Hopt wf_after_ok Hwf_check.
                         destruct wf_after_ok.
                         *** pose proof
                           (ValidatorCore.check_wf_polyprog_general_correct
                              pol_after true Hwf_check eq_refl)
                           as Hwf_after.
                         pose proof
                           (PrepareCore.prepared_codegen_correct_general
                              pol_after st st' loop' Hopt Hwf_after Hloop)
                           as Hsem_after.
                         pose proof
                           (ValidatorCore.validate_general_correct
                              pol_posttile pol_after st st'
                              true Hfinal eq_refl Hsem_after)
                           as Hfinal_corr.
                         destruct Hfinal_corr as [st_post [Hpost_sem Heq_post]].
                         remember (TilingSched.Base.outer_to_tiling_pprog pol_mid)
                           as before_tiling eqn:Hbefore_tiling_eq.
                         remember (TilingSched.Base.outer_to_tiling_pprog pol_posttile)
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
                           (ValidatorCore.check_wf_polyprog_general_correct
                              pol_posttile true Hwf_posttile_check eq_refl)
                           as Hwf_posttile.
                         pose proof
                           (TilingSched.Base.outer_to_tiling_wf_pprog_general
                              pol_posttile Hwf_posttile)
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
                              ws bands st st_post
                              Hcheck_shape Hbands
                              Hwfbefore_pis Hwfafter_pis
                              Hcheck_perm)
                           as Hcorr.
                         apply TilingSched.Base.outer_to_tiling_instance_list_semantics_iff
                           in Hpost_sem.
                         rewrite <- Hafter_tiling_eq in Hpost_sem.
                         rewrite <- Hctxt_eq, <- Hvars_eq in Hpost_sem.
                         specialize (Hcorr Hpost_sem).
                         destruct Hcorr as [st_mid [Hmid_tiling Heq_mid]].
                         rewrite Hbefore_tiling_eq in Hmid_tiling.
                         apply TilingSched.Base.outer_to_tiling_instance_list_semantics_iff
                           in Hmid_tiling.
                         exists st_mid.
                         split; auto.
                         eapply State.eq_trans; eauto.
                         *** pose proof
                           (PrepareCore.prepared_codegen_correct
                              pol_mid st st' loop' Hopt Hwf_mid Hloop)
                           as Hmid_sem.
                         exists st'. split; auto. apply State.eq_refl.
                     +++ pose proof
                       (PrepareCore.prepared_codegen_correct
                          pol_mid st st' loop' Hopt Hwf_mid Hloop)
                       as Hmid_sem.
                     exists st'. split; auto. apply State.eq_refl.
                 --- pose proof
                   (PrepareCore.prepared_codegen_correct
                      pol_mid st st' loop' Hopt Hwf_mid Hloop)
                   as Hmid_sem.
                 exists st'. split; auto. apply State.eq_refl.
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

Lemma try_diamond_phase_pipeline_from_source_pol_band_correct:
  forall pol_source before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_diamond_phase_pipeline_from_source_pol_band
        pol_source before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_diamond_phase_pipeline_from_source_pol_band in Hopt.
  destruct (BaseOpt.run_pluto_diamond_phase_pipeline before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_diamond_after_phase_mid_band_correct
             pol_mid mid_scop posttile_scop after_scop
             st st' Hwf_mid loop' Hopt Hloop)
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

Lemma try_diamond_phase_pipeline_from_source_pol_band_with_iss_correct:
  forall pol_source before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_diamond_phase_pipeline_from_source_pol_band_with_iss
        pol_source before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_diamond_phase_pipeline_from_source_pol_band_with_iss in Hopt.
  destruct (BaseOpt.run_pluto_diamond_phase_pipeline_with_iss before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_diamond_after_phase_mid_band_correct
             pol_mid mid_scop posttile_scop after_scop
             st st' Hwf_mid loop' Hopt Hloop)
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

Lemma try_checked_iss_diamond_phase_pipeline_from_poly_band_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      try_checked_iss_diamond_phase_pipeline_from_poly_band
        pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold try_checked_iss_diamond_phase_pipeline_from_poly_band in Hopt.
  destruct (BaseOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (BaseOpt.check_wf_polyprog_affine_correct
                pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           pose proof
             (try_diamond_phase_pipeline_from_source_pol_band_with_iss_correct
                pol_iss before_scop st st' Hwf_iss loop' Hopt Hloop)
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
        -- eapply try_diamond_phase_pipeline_from_source_pol_band_correct; eauto.
      * eapply try_diamond_phase_pipeline_from_source_pol_band_correct; eauto.
    + eapply try_diamond_phase_pipeline_from_source_pol_band_correct; eauto.
  - eapply try_diamond_phase_pipeline_from_source_pol_band_correct; eauto.
Qed.

Lemma phase_diamond_opt_prepared_from_poly_no_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_diamond_opt_prepared_from_poly_no_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_diamond_opt_prepared_from_poly_no_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_diamond_phase_pipeline_from_source_pol_band_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Lemma phase_diamond_opt_prepared_from_poly_with_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_diamond_opt_prepared_from_poly_with_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_diamond_opt_prepared_from_poly_with_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_diamond_phase_pipeline_from_poly_band_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Definition Opt_prepared_diamond_band := phase_diamond_opt_prepared_band.
Definition Opt_diamond_band := Opt_prepared_diamond_band.
Definition Opt_prepared_diamond_band_with_iss :=
  phase_diamond_opt_prepared_with_iss_band.
Definition Opt_diamond_band_with_iss := Opt_prepared_diamond_band_with_iss.

Theorem Opt_prepared_diamond_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_diamond_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_diamond_band, phase_diamond_opt_prepared_band in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (phase_diamond_opt_prepared_from_poly_no_iss_band_correct
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

Theorem Opt_diamond_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_diamond_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_diamond_band_correct; eauto.
Qed.

Theorem Opt_prepared_diamond_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_diamond_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_diamond_band_with_iss,
    phase_diamond_opt_prepared_with_iss_band in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (phase_diamond_opt_prepared_from_poly_with_iss_band_correct
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

Theorem Opt_diamond_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_diamond_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_diamond_band_with_iss_correct; eauto.
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
