Require Import TilingBandDirectRuntime.
Require Import TilingWitness.
Require Import PolIRs.
Require Import OpenScop.
Require Import Result.
Require Import String.
Require Import PolOpt.
Require Import ISSValidatorCorrect.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module PolOptBandTiling (PolIRs: POLIRS).

Module BaseOpt := PolOpt PolIRs.
Module ValidatorCore := BaseOpt.ValidatorCore.
Module PrepareCore := BaseOpt.PrepareCore.
Module TilingSched := TilingBandDirectRuntime PolIRs.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module PolyLang := PolIRs.PolyLang.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

Open Scope impure_scope.
Open Scope opt_scop.
Local Open Scope string_scope.

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
          BIND route <-
            TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
              pol_mid pol_after ws -;
          if TilingSched.tiling_band_validation_route_acceptsb route then
            BIND wf_after <- ValidatorCore.check_wf_polyprog_general pol_after -;
            if wf_after then
              PrepareCore.prepared_codegen (PolyLang.current_view_pprog pol_after)
            else
              PrepareCore.prepared_codegen pol_mid
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
          BIND route <-
            TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
              pol_mid pol_posttile ws -;
          if TilingSched.tiling_band_validation_route_acceptsb route then
            BIND wf_posttile <- ValidatorCore.check_wf_polyprog_general pol_posttile -;
            if wf_posttile then
              match PolyLang.from_openscop_schedule_only pol_posttile after_scop with
              | Err _ =>
                  res_to_alarm LoopIR.dummy
                    (Err "Post-tiling affine schedule import failed.")
              | Okk pol_after =>
                  BIND final_ok <- ValidatorCore.validate_general pol_posttile pol_after -;
                  if final_ok then
                    BIND wf_after <- ValidatorCore.check_wf_polyprog_general pol_after -;
                    if wf_after then
                      PrepareCore.prepared_codegen
                        (PolyLang.current_view_pprog pol_after)
                    else
                      res_to_alarm LoopIR.dummy
                        (Err "Post-tiling affine target is not well formed.")
                  else
                    res_to_alarm LoopIR.dummy
                      (Err "Post-tiling affine validation failed.")
              end
            else
              PrepareCore.prepared_codegen pol_mid
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

Definition try_checked_iss_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          try_phase_pipeline_from_source_pol_band
            pol_iss
            BaseOpt.run_pluto_phase_pipeline_with_iss
            before_scop
        else
          try_phase_pipeline_from_source_pol_band
            pol
            BaseOpt.run_pluto_phase_pipeline
            before_scop
      else
        try_phase_pipeline_from_source_pol_band
          pol
          BaseOpt.run_pluto_phase_pipeline
          before_scop
  | _ =>
      try_phase_pipeline_from_source_pol_band
        pol
        BaseOpt.run_pluto_phase_pipeline
        before_scop
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

Definition phase_pipeline_opt_prepared_from_poly_with_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_phase_pipeline_from_poly_band pol before_scop
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

Definition try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match BaseOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_phase_pipeline_from_source_pol_band
                pol_iss
                BaseOpt.run_pluto_identity_tiling_pipeline
                iss_scop
          | None =>
              PrepareCore.prepared_codegen pol_iss
          end
        else
          identity_tiling_opt_prepared_from_poly_band pol
      else
        identity_tiling_opt_prepared_from_poly_band pol
  | _ =>
      identity_tiling_opt_prepared_from_poly_band pol
  end.

Definition identity_tiling_opt_prepared_from_poly_with_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
          pol before_scop
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

Definition phase_pipeline_opt_prepared_with_iss_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_pipeline_opt_prepared_from_poly_with_iss_band pol.

Definition identity_tiling_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  identity_tiling_opt_prepared_from_poly_band pol.

Definition identity_tiling_opt_prepared_with_iss_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  identity_tiling_opt_prepared_from_poly_with_iss_band pol.

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
    + bind_imp_destruct Hopt route Hroute.
      destruct (TilingSched.tiling_band_validation_route_acceptsb route)
        eqn:Haccept.
      * bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        -- pose proof
             (ValidatorCore.check_wf_polyprog_general_correct
                pol_after true Hwf_check eq_refl)
             as Hwf_after.
           pose proof
             (PrepareCore.prepared_codegen_correct_general
                pol_after st st' loop' Hopt Hwf_after Hloop)
             as Hsem_after.
           eapply
             (TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
                pol_mid pol_after ws st st' route); eauto.
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

Lemma try_checked_iss_phase_pipeline_from_poly_band_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      try_checked_iss_phase_pipeline_from_poly_band pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold try_checked_iss_phase_pipeline_from_poly_band in Hopt.
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
             (try_phase_pipeline_from_source_pol_band_correct
                pol_iss
                BaseOpt.run_pluto_phase_pipeline_with_iss
                before_scop st st' Hwf_iss loop' Hopt Hloop)
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
        -- eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
      * eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
    + eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
  - eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
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

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_pipeline_opt_prepared_from_poly_with_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_pipeline_opt_prepared_from_poly_with_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_phase_pipeline_from_poly_band_correct; eauto.
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

Lemma try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
        pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold try_checked_iss_identity_tiling_phase_pipeline_from_poly_band in Hopt.
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
           destruct (BaseOpt.export_for_phase_scheduler pol_iss)
             as [iss_scop|] eqn:Hiss_scop.
           ++ pose proof
                (try_phase_pipeline_from_source_pol_band_correct
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
           ++ pose proof
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
        -- eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
      * eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
    + eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
  - eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
Qed.

Lemma identity_tiling_opt_prepared_from_poly_with_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- identity_tiling_opt_prepared_from_poly_with_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold identity_tiling_opt_prepared_from_poly_with_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Definition Opt_prepared_band := phase_pipeline_opt_prepared_band.
Definition Opt_band := Opt_prepared_band.
Definition Opt_prepared_band_with_iss := phase_pipeline_opt_prepared_with_iss_band.
Definition Opt_band_with_iss := Opt_prepared_band_with_iss.
Definition Opt_prepared_identity_tiled_band := identity_tiling_opt_prepared_band.
Definition Opt_identity_tiled_band := Opt_prepared_identity_tiled_band.
Definition Opt_prepared_identity_tiled_band_with_iss :=
  identity_tiling_opt_prepared_with_iss_band.
Definition Opt_identity_tiled_band_with_iss :=
  Opt_prepared_identity_tiled_band_with_iss.

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

Theorem Opt_prepared_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_band_with_iss,
    phase_pipeline_opt_prepared_with_iss_band in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (phase_pipeline_opt_prepared_from_poly_with_iss_band_correct
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

Theorem Opt_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_band_with_iss_correct; eauto.
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

Theorem Opt_prepared_identity_tiled_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_identity_tiled_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_identity_tiled_band_with_iss,
    identity_tiling_opt_prepared_with_iss_band in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (identity_tiling_opt_prepared_from_poly_with_iss_band_correct
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

Theorem Opt_identity_tiled_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_identity_tiled_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_identity_tiled_band_with_iss_correct; eauto.
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
    + bind_imp_destruct Hopt route Hroute.
      destruct (TilingSched.tiling_band_validation_route_acceptsb route)
        eqn:Haccept.
      * bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- pose proof
             (ValidatorCore.check_wf_polyprog_general_correct
                pol_posttile true Hwf_posttile_check eq_refl)
             as Hwf_posttile.
           destruct (PolyLang.from_openscop_schedule_only
                       pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- pose proof
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
                     destruct
                       (TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
                          pol_mid pol_posttile ws st st_post route
                          Hwf_mid Hwf_posttile Hroute Haccept Hpost_sem)
                       as [st_mid [Hmid_sem Heq_mid]].
                     exists st_mid. split; auto.
                     eapply State.eq_trans; eauto.
                 --- eapply mayReturn_alarm in Hopt.
                     contradiction.
              ** eapply mayReturn_alarm in Hopt.
                 contradiction.
           ++ eapply mayReturn_alarm in Hopt.
              contradiction.
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
