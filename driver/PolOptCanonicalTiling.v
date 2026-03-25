Require Import TilingCanonicalScheduleValidator.
Require Import PolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module PolOptCanonicalTiling (PolIRs: POLIRS).

Module BaseOpt := PolOpt PolIRs.
Module ValidatorCore := BaseOpt.ValidatorCore.
Module PrepareCore := BaseOpt.PrepareCore.
Module TilingSched := TilingCanonicalScheduleValidator PolIRs.
Module PolyLang := PolIRs.PolyLang.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

Open Scope impure_scope.
Open Scope opt_scop.

Definition try_verified_tiling_after_phase_mid_canonical
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
          BIND ok <- TilingSched.checked_tiling_schedule_canonical_validate_poly pol_mid pol_after ws -;
          if ok then
            BIND wf_after <- ValidatorCore.check_wf_polyprog_general pol_after -;
            if wf_after then
              PrepareCore.prepared_codegen (PolyLang.current_view_pprog pol_after)
            else
              PrepareCore.prepared_codegen pol_mid
          else
            PrepareCore.prepared_codegen pol_mid
      end
  end.

Definition try_phase_pipeline_from_source_pol_canonical
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
            try_verified_tiling_after_phase_mid_canonical pol_mid mid_scop after_scop
          else
            BaseOpt.affine_only_opt_prepared_from_poly pol_source
      end
  end.

Definition phase_pipeline_opt_prepared_from_poly_no_iss_canonical
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_canonical
          pol
          BaseOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        BaseOpt.affine_only_opt_prepared_from_poly pol
    end
  else
    PrepareCore.prepared_codegen pol.

Definition phase_pipeline_opt_prepared_canonical
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_pipeline_opt_prepared_from_poly_no_iss_canonical pol.

Lemma try_verified_tiling_after_phase_mid_canonical_correct:
  forall pol_mid mid_scop after_scop st st',
    PolyLang.wf_pprog_affine pol_mid ->
    WHEN loop' <- try_verified_tiling_after_phase_mid_canonical pol_mid mid_scop after_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\
      State.eq st' st''.
Proof.
  intros pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop.
  unfold try_verified_tiling_after_phase_mid_canonical in Hopt.
  destruct (BaseOpt.infer_tiling_witness_scops mid_scop after_scop) as [ws|msg] eqn:Hws.
  - destruct
      (ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as [pol_after|msg_after] eqn:Hafter.
    + bind_imp_destruct Hopt ok Hcheck.
      destruct ok.
      * bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        -- pose proof
             (ValidatorCore.AffineCore.check_wf_polyprog_tiling_correct
                pol_after true Hwf_check eq_refl)
             as Hwf_after.
           pose proof
             (PrepareCore.prepared_codegen_correct_general
                pol_after st st' loop' Hopt Hwf_after Hloop)
             as Hsem_after.
           eapply TilingSched.checked_tiling_schedule_canonical_validate_poly_correct; eauto.
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

Lemma try_phase_pipeline_from_source_pol_canonical_correct:
  forall pol_source phase_runner before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_phase_pipeline_from_source_pol_canonical pol_source phase_runner before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_phase_pipeline_from_source_pol_canonical in Hopt.
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
          (try_verified_tiling_after_phase_mid_canonical_correct
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

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_canonical_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_pipeline_opt_prepared_from_poly_no_iss_canonical pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_pipeline_opt_prepared_from_poly_no_iss_canonical in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_phase_pipeline_from_source_pol_canonical_correct; eauto.
    + eapply BaseOpt.affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Definition Opt_prepared_canonical := phase_pipeline_opt_prepared_canonical.
Definition Opt_canonical := Opt_prepared_canonical.

Theorem Opt_prepared_canonical_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_canonical loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_canonical, phase_pipeline_opt_prepared_canonical in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := BaseOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextok))
    as Hwf_pol.
  pose proof
    (phase_pipeline_opt_prepared_from_poly_no_iss_canonical_correct
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

Theorem Opt_canonical_correct:
  forall loop st st',
    WHEN loop' <- Opt_canonical loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  exact Opt_prepared_canonical_correct.
Qed.

Close Scope impure_scope.
Close Scope opt_scop.

End PolOptCanonicalTiling.
