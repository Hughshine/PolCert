Require Import SPolIRs.
Require Import SPolOpt.
Require Import STilingBandSched.
Require Import OpenScop.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Open Scope impure_scope.
Open Scope opt_scop.

Definition check_pprog_permutable_tiling_bands :=
  STilingBandSched.check_pprog_permutable_tiling_bands.

Definition try_verified_tiling_after_phase_mid_band
    (pol_mid: SPolIRs.PolyLang.t)
    (mid_scop after_scop: OpenScop) : imp SPolIRs.Loop.t :=
  match SPolOpt.CoreOpt.infer_tiling_witness_scops mid_scop after_scop with
  | Err _ =>
      SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol_mid
  | Okk ws =>
      match SPolOpt.CoreOpt.ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws with
      | Err _ =>
          SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol_mid
      | Okk pol_after =>
          BIND ok_shape <- STilingBandSched.checked_tiling_schedule_stripmined_validate_poly pol_mid pol_after ws -;
          if ok_shape then
            match STilingBandSched.infer_pprog_tiling_bands
                    (STilingBandSched.outer_to_tiling_pprog pol_mid) ws with
            | None =>
                SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol_mid
            | Some bands =>
                BIND ok_perm <-
                  check_pprog_permutable_tiling_bands
                    (STilingBandSched.outer_to_tiling_pprog pol_mid)
                    (STilingBandSched.outer_to_tiling_pprog pol_after)
                    ws bands -;
                if ok_perm then
                  BIND wf_after <- SPolOpt.CoreOpt.ValidatorCore.check_wf_polyprog_general pol_after -;
                  if wf_after then
                    SPolOpt.CoreOpt.PrepareCore.prepared_codegen
                      (SPolIRs.PolyLang.current_view_pprog pol_after)
                  else
                    SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol_mid
                else
                  SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol_mid
            end
          else
            SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol_mid
      end
  end.

Definition try_phase_pipeline_from_source_pol_band
    (pol_source: SPolIRs.PolyLang.t)
    (phase_runner: OpenScop -> result (OpenScop * OpenScop))
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
  match phase_runner before_scop with
  | Err _ =>
      SPolOpt.CoreOpt.affine_only_opt_prepared_from_poly pol_source
  | Okk (mid_scop, after_scop) =>
      match SPolIRs.PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          SPolOpt.CoreOpt.affine_only_opt_prepared_from_poly pol_source
      | Okk pol_mid =>
          BIND affine_ok <- SPolOpt.CoreOpt.ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop
          else
            SPolOpt.CoreOpt.affine_only_opt_prepared_from_poly pol_source
      end
  end.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm SPolIRs.PolyLang.dummy (SPolOpt.CoreOpt.Extractor.extractor loop) -;
  let pol := SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  if SPolOpt.CoreOpt.has_nonscalar_stmt pol then
    match SPolOpt.CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol
          SPolOpt.CoreOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        SPolOpt.CoreOpt.affine_only_opt_prepared_from_poly pol
    end
  else
    SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol.

Definition opt_prepared (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  opt loop.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  let pol' := SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol in
  if SPolOpt.CoreOpt.has_nonscalar_stmt pol' then
    match SPolOpt.CoreOpt.export_for_phase_scheduler pol' with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol'
          SPolOpt.CoreOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        SPolOpt.CoreOpt.affine_only_opt_prepared_from_poly pol'
    end
  else
    SPolOpt.CoreOpt.PrepareCore.prepared_codegen pol'.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
