Require Import Result.
Require Import List.
Require Import String.
Require Import PolyLang.
Require Import SPolIRs.
Require Import OpenScop.
Require Import ParallelCodegen.
Require Import Validator.
Require Import PolOpt.
Require Import STilingBandSched.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt SPolIRs.
Module PolyLang := SPolIRs.PolyLang.
Module ValidatorCore := Validator SPolIRs.
Module ParallelCodegenCore := ParallelCodegen SPolIRs.
Module LoopIR := SPolIRs.Loop.
Module ParallelLoop := ParallelCodegenCore.ParallelLoop.

Definition parallel_plan_of_dim (d : nat) : ValidatorCore.parallel_plan :=
  {| ValidatorCore.ParallelCore.target_dim := d |}.

Definition checked_parallel_current_annotated_codegen
    (pol : PolyLang.t)
    (plan : ValidatorCore.parallel_plan)
  : imp (result ParallelLoop.t) :=
  BIND cert_res <- ValidatorCore.checked_parallelize_current
                     (PolyLang.current_view_pprog pol) plan -;
  match cert_res with
  | Okk cert =>
      let cert' :=
        {| ParallelCodegenCore.ParallelValidator.certified_dim :=
             cert.(ValidatorCore.ParallelCore.certified_dim) |} in
      ParallelCodegenCore.checked_annotated_codegen
        (PolyLang.current_view_pprog pol) cert'
  | Err msg => pure (Err msg)
  end.

Definition checked_parallel_current_annotated_codegen_at
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  checked_parallel_current_annotated_codegen pol (parallel_plan_of_dim d).

Definition parallel_codegen_cert_of_validator_cert
    (cert : ValidatorCore.parallel_cert)
  : ParallelCodegenCore.ParallelValidator.parallel_cert :=
  {| ParallelCodegenCore.ParallelValidator.certified_dim :=
       cert.(ValidatorCore.ParallelCore.certified_dim) |}.

Fixpoint collect_parallel_current_codegen_certs_limited
    (pp : PolyLang.t)
    (remaining : nat)
    (dims : list nat)
  : imp (list ParallelCodegenCore.ParallelValidator.parallel_cert) :=
  match remaining with
  | O => pure nil
  | S remaining' =>
      match dims with
      | nil => pure nil
      | cons d dims' =>
          BIND cert_res <-
            ValidatorCore.checked_parallelize_current pp (parallel_plan_of_dim d) -;
          match cert_res with
          | Okk cert =>
              BIND certs <-
                collect_parallel_current_codegen_certs_limited
                  pp remaining' dims' -;
              pure (cons (parallel_codegen_cert_of_validator_cert cert) certs)
          | Err _ =>
              collect_parallel_current_codegen_certs_limited pp remaining dims'
          end
      end
  end.

Definition collect_parallel_current_codegen_certs
    (pp : PolyLang.t)
    (dims : list nat)
  : imp (list ParallelCodegenCore.ParallelValidator.parallel_cert) :=
  collect_parallel_current_codegen_certs_limited pp 2 dims.

Definition checked_parallel_current_many_annotated_codegen_at
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  let current := PolyLang.current_view_pprog pol in
  BIND certs <- collect_parallel_current_codegen_certs current dims -;
  match certs with
  | nil => pure (Err "Parallel validation failed"%string)
  | cons _ _ =>
      ParallelCodegenCore.checked_annotated_codegen_many current certs
  end.

Definition parallel_current_identity_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  checked_parallel_current_annotated_codegen_at pol d.

Definition parallel_current_affine_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- CoreOpt.checked_affine_schedule pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition try_verified_tiling_after_phase_mid_poly
    (pol_mid : PolyLang.t)
    (mid_scop after_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.infer_tiling_witness_scops mid_scop after_scop with
  | Err _ =>
      pure pol_mid
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws with
      | Err _ =>
          pure pol_mid
      | Okk pol_after =>
          BIND ok <- ValidatorCore.checked_tiling_validate_poly pol_mid pol_after ws -;
          if ok then
            pure (PolyLang.current_view_pprog pol_after)
          else
            pure pol_mid
      end
  end.

Definition try_phase_pipeline_from_source_pol_poly
    (pol_source : PolyLang.t)
    (phase_runner : OpenScop -> result (OpenScop * OpenScop))
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match phase_runner before_scop with
  | Err _ =>
      CoreOpt.checked_affine_schedule pol_source
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          CoreOpt.checked_affine_schedule pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop
          else
            CoreOpt.checked_affine_schedule pol_source
      end
  end.

Definition try_verified_diamond_after_phase_mid_poly
    (pol_mid : PolyLang.t)
    (mid_scop posttile_scop after_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.infer_tiling_witness_scops mid_scop posttile_scop with
  | Err _ =>
      pure pol_mid
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws with
      | Err _ =>
          pure pol_mid
      | Okk pol_posttile =>
          BIND ok_shape <- STilingBandSched.checked_tiling_schedule_stripmined_validate_poly pol_mid pol_posttile ws -;
          if ok_shape then
            match STilingBandSched.infer_pprog_tiling_bands
                    (STilingBandSched.outer_to_tiling_pprog pol_mid) ws with
            | None =>
                pure pol_mid
            | Some bands =>
                BIND ok_perm <-
                  STilingBandSched.check_pprog_permutable_tiling_bands
                    (STilingBandSched.outer_to_tiling_pprog pol_mid)
                    (STilingBandSched.outer_to_tiling_pprog pol_posttile)
                    ws bands -;
                if ok_perm then
                  BIND wf_posttile <- ValidatorCore.check_wf_polyprog_general pol_posttile -;
                  if wf_posttile then
                    match PolyLang.from_openscop_schedule_only pol_posttile after_scop with
                    | Err _ =>
                        pure pol_mid
                    | Okk pol_after =>
                        BIND final_ok <- ValidatorCore.validate_general pol_posttile pol_after -;
                        if final_ok then
                          BIND wf_after <- ValidatorCore.check_wf_polyprog_general pol_after -;
                          if wf_after then
                            pure (PolyLang.current_view_pprog pol_after)
                          else
                            pure pol_mid
                        else
                          pure pol_mid
                    end
                  else
                    pure pol_mid
                else
                  pure pol_mid
            end
          else
            pure pol_mid
      end
  end.

Definition try_diamond_phase_pipeline_from_source_pol_poly
    (pol_source : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.run_pluto_diamond_phase_pipeline before_scop with
  | Err _ =>
      CoreOpt.checked_affine_schedule pol_source
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          CoreOpt.checked_affine_schedule pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_diamond_after_phase_mid_poly
              pol_mid mid_scop posttile_scop after_scop
          else
            CoreOpt.checked_affine_schedule pol_source
      end
  end.

Definition try_diamond_phase_pipeline_from_source_pol_poly_with_iss
    (pol_source : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.run_pluto_diamond_phase_pipeline_with_iss before_scop with
  | Err _ =>
      CoreOpt.checked_affine_schedule pol_source
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          CoreOpt.checked_affine_schedule pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_diamond_after_phase_mid_poly
              pol_mid mid_scop posttile_scop after_scop
          else
            CoreOpt.checked_affine_schedule pol_source
      end
  end.

Definition try_checked_iss_phase_pipeline_from_poly_poly
    (pol : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          try_phase_pipeline_from_source_pol_poly
            pol_iss
            CoreOpt.run_pluto_phase_pipeline_with_iss
            before_scop
        else
          try_phase_pipeline_from_source_pol_poly
            pol
            CoreOpt.run_pluto_phase_pipeline
            before_scop
      else
        try_phase_pipeline_from_source_pol_poly
          pol
          CoreOpt.run_pluto_phase_pipeline
          before_scop
  | _ =>
      try_phase_pipeline_from_source_pol_poly
        pol
        CoreOpt.run_pluto_phase_pipeline
        before_scop
  end.

Definition try_checked_iss_diamond_phase_pipeline_from_poly_poly
    (pol : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          try_diamond_phase_pipeline_from_source_pol_poly_with_iss
            pol_iss
            before_scop
        else
          try_diamond_phase_pipeline_from_source_pol_poly
            pol
            before_scop
      else
        try_diamond_phase_pipeline_from_source_pol_poly
          pol
          before_scop
  | _ =>
      try_diamond_phase_pipeline_from_source_pol_poly
        pol
        before_scop
  end.

Definition iss_only_prepared_from_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  match CoreOpt.export_for_phase_scheduler pol with
  | None =>
      pure pol
  | Some before_scop =>
      match CoreOpt.infer_iss_from_source_scop pol before_scop with
      | Okk (Some (pol_iss, w)) =>
          if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
            BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
            if iss_wf then pure pol_iss else pure pol
          else
            pure pol
      | _ =>
          pure pol
      end
  end.

Definition iss_affine_prepared_from_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  BIND pol_iss <- iss_only_prepared_from_poly pol -;
  CoreOpt.checked_affine_schedule pol_iss.

Definition phase_pipeline_opt_prepared_from_poly_no_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        CoreOpt.checked_affine_schedule pol
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_poly
          pol
          CoreOpt.run_pluto_phase_pipeline
          before_scop
    end
  else
    pure pol.

Definition phase_pipeline_opt_prepared_from_poly_with_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        CoreOpt.checked_affine_schedule pol
    | Some before_scop =>
        try_checked_iss_phase_pipeline_from_poly_poly pol before_scop
    end
  else
    pure pol.

Definition identity_tiling_opt_prepared_from_poly_no_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        CoreOpt.checked_affine_schedule pol
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_poly
          pol
          CoreOpt.run_pluto_identity_tiling_pipeline
          before_scop
    end
  else
    pure pol.

Definition diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        CoreOpt.checked_affine_schedule pol
    | Some before_scop =>
        try_diamond_phase_pipeline_from_source_pol_poly pol before_scop
    end
  else
    pure pol.

Definition diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        CoreOpt.checked_affine_schedule pol
    | Some before_scop =>
        try_checked_iss_diamond_phase_pipeline_from_poly_poly pol before_scop
    end
  else
    pure pol.

Definition parallel_current_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_identity_tiled_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_diamond_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_diamond_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_many_diamond_prepared_from_poly
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- diamond_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_diamond_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- diamond_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_identity_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_only_prepared_from_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_affine_prepared_from_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_dummy : ParallelLoop.t :=
  ParallelCodegenCore.tag_loop LoopIR.dummy.

Definition opt_parallel_current_identity
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_identity_tiled
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_tiled_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_affine
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_affine_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_diamond
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_diamond_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_diamond_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_diamond_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_diamond
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_diamond_prepared_from_poly pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_diamond_with_iss
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_diamond_prepared_from_poly_with_iss pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_identity_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_affine_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_affine_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.
