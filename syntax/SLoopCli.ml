type config = SLoopConfig.config = {
  mutable dump_input : bool;
  mutable dump_extracted_openscop : bool;
  mutable dump_scheduled_openscop : bool;
  mutable debug_scheduler : bool;
  mutable extract_only : bool;
  mutable profile_stages : bool;
  mutable force_identity : bool;
  mutable force_notile : bool;
  mutable force_iss : bool;
  mutable force_second_level_tile : bool;
  mutable force_diamond_tile : bool;
  mutable force_full_diamond_tile : bool;
  mutable force_band_tiling_experiment : bool;
  mutable force_legacy_generic_tiling : bool;
  mutable force_parallel : bool;
  mutable force_parallel_strict : bool;
  mutable parallel_current_dim : int option;
  mutable validate_affine_openscop : (string * string) option;
  mutable extract_tiling_witness_openscop : (string * string) option;
  mutable validate_tiling_openscop : (string * string) option;
  mutable validate_iss_debug_dumps : (string * string) option;
  mutable validate_iss_bridge : string option;
  mutable validate_iss_pluto_suite : bool;
  mutable validate_iss_pluto_live_suite : bool;
  mutable input : string option;
}

let usage prog =
  String.concat ""
    [
      Printf.sprintf
        "Usage: %s [--dump-input] [--dump-extracted-openscop] [--dump-scheduled-openscop] [--debug-scheduler] [--extract-only] [--profile-stages] [--identity] [--notile] [--iss] [--second-level-tile] [--diamond-tile] [--full-diamond-tile] [--legacy-generic-tiling] [--parallel] [--parallel-strict] [--parallel-current <dim>] <file.loop>\n"
        prog;
      Printf.sprintf
        "       %s --validate-affine-openscop <before.scop> <after.scop>\n"
        prog;
      Printf.sprintf
        "       %s [--second-level-tile] --extract-tiling-witness-openscop <before.scop> <after.scop>\n"
        prog;
      Printf.sprintf
        "       %s [--second-level-tile] --validate-tiling-openscop <before.scop> <after.scop>\n"
        prog;
      Printf.sprintf "       %s --validate-iss-debug-dumps <before.txt> <after.txt>\n" prog;
      Printf.sprintf "       %s --validate-iss-bridge <bridge.txt>\n" prog;
      Printf.sprintf "       %s --validate-iss-pluto-suite\n" prog;
      Printf.sprintf "       %s --validate-iss-pluto-live-suite\n" prog;
      "\nDefault optimization path:\n";
      "  extracted theorem-aligned affine+tiling pipeline with band-aware ordinary tiling (`SBandTilingOpt.opt`)\n";
      "\nExplicit phase controls:\n";
      "  --profile-stages  : print OCaml-side stage timings for the default no-parallel\n";
      "                      theorem-aligned routes (`--identity`, `--notile`, or default)\n";
      "  --identity        : no Pluto phase, just checked extraction/strengthen/codegen\n";
      "  --notile          : stop after affine scheduling validation\n";
      "  --iss             : switch to the extracted theorem-aligned ISS+affine+tiling pipeline\n";
      "                       (`SPolOpt.opt_with_iss`); with `--identity`, run the ISS-only checked split path\n";
      "  --second-level-tile : experimental verified second-level tiling path; only valid on\n";
      "                        full tiled optimization/validation routes\n";
      "  --diamond-tile    : experimental sequential checked diamond midpoint + tiling route;\n";
      "                      currently only supported on the default non-ISS full tiled path\n";
      "  --full-diamond-tile : stronger diamond producer mode over the same checked route;\n";
      "                        currently only supported on the default non-ISS full tiled path\n";
      "  --legacy-generic-tiling : use the historical generic ordinary-tiling validator path\n";
      "                            instead of the default band-aware path\n";
      "  --parallel        : experimental verified `parallel for` route driven by Pluto `--parallel`\n";
      "                       loop hints; supported on both the default and `--iss` pipelines,\n";
      "                       with or without `--notile`\n";
      "  --parallel-strict : with `--parallel`, require the certified parallel loop to be the\n";
      "                       Pluto-hinted dimension; otherwise keep the sequential optimized loop\n";
      "  --parallel-current d : theorem-aligned verified `parallel for` on explicit current\n";
      "                         dimension d; supported on identity, affine-only, and full\n";
      "                         tiled paths, including their `--iss` variants\n";
      "\nExamples:\n";
      Printf.sprintf "  %s file.loop                        # default theorem-aligned band-aware affine+tiling path\n" prog;
      Printf.sprintf "  %s --profile-stages file.loop       # print per-stage timings for the default route\n" prog;
      Printf.sprintf "  %s --second-level-tile file.loop    # full tiled checked path with second-level tiling enabled\n" prog;
      Printf.sprintf "  %s --diamond-tile file.loop         # sequential checked diamond midpoint + tiling route\n" prog;
      Printf.sprintf "  %s --full-diamond-tile file.loop    # stronger diamond producer mode over the same checked route\n" prog;
      Printf.sprintf "  %s --parallel file.loop             # Pluto-hinted verified parallel path\n" prog;
      Printf.sprintf "  %s --parallel --parallel-strict file.loop\n" prog;
      Printf.sprintf "  %s --parallel-current 0 file.loop   # theorem-aligned explicit-dimension parallel path\n" prog;
      Printf.sprintf "  %s --iss --parallel-current 0 file.loop\n" prog;
      Printf.sprintf "  %s --notile file.loop               # affine-only checked path\n" prog;
      Printf.sprintf "  %s --identity file.loop             # identity/no-schedule path\n" prog;
      Printf.sprintf "  %s --validate-affine-openscop before.scop mid.scop\n" prog;
      Printf.sprintf "  %s --validate-tiling-openscop mid.scop after.scop\n" prog;
      Printf.sprintf "  %s --second-level-tile --validate-tiling-openscop mid.scop after.scop\n" prog;
      Printf.sprintf "  %s --iss --identity file.loop       # ISS-only checked split path\n" prog;
    ]

let usage_error prog msg =
  prerr_endline msg;
  prerr_endline (usage prog);
  exit 2

let parse_args () : config =
  let cfg : config =
    {
      dump_input = false;
      dump_extracted_openscop = false;
      dump_scheduled_openscop = false;
      debug_scheduler = false;
      extract_only = false;
      profile_stages = false;
      force_identity = false;
      force_notile = false;
      force_iss = false;
      force_second_level_tile = false;
      force_diamond_tile = false;
      force_full_diamond_tile = false;
      force_band_tiling_experiment = false;
      force_legacy_generic_tiling = false;
      force_parallel = false;
      force_parallel_strict = false;
      parallel_current_dim = None;
      validate_affine_openscop = None;
      extract_tiling_witness_openscop = None;
      validate_tiling_openscop = None;
      validate_iss_debug_dumps = None;
      validate_iss_bridge = None;
      validate_iss_pluto_suite = false;
      validate_iss_pluto_live_suite = false;
      input = None;
    }
  in
  let invalid_non_negative_int prog =
    usage_error prog "option --parallel-current expects a non-negative integer"
  in
  let rec go i =
    if i >= Array.length Sys.argv then cfg
    else begin
      match Sys.argv.(i) with
      | "--dump-input" -> cfg.dump_input <- true; go (i + 1)
      | "--dump-extracted-openscop" -> cfg.dump_extracted_openscop <- true; go (i + 1)
      | "--dump-scheduled-openscop" -> cfg.dump_scheduled_openscop <- true; go (i + 1)
      | "--debug-scheduler" -> cfg.debug_scheduler <- true; go (i + 1)
      | "--extract-only" -> cfg.extract_only <- true; go (i + 1)
      | "--profile-stages" -> cfg.profile_stages <- true; go (i + 1)
      | "--identity" -> cfg.force_identity <- true; go (i + 1)
      | "--notile" | "--affine-only" -> cfg.force_notile <- true; go (i + 1)
      | "--iss" -> cfg.force_iss <- true; go (i + 1)
      | "--second-level-tile" -> cfg.force_second_level_tile <- true; go (i + 1)
      | "--diamond-tile" -> cfg.force_diamond_tile <- true; go (i + 1)
      | "--full-diamond-tile" ->
          cfg.force_diamond_tile <- true;
          cfg.force_full_diamond_tile <- true;
          go (i + 1)
      | "--band-tiling-experiment" -> cfg.force_band_tiling_experiment <- true; go (i + 1)
      | "--legacy-generic-tiling" -> cfg.force_legacy_generic_tiling <- true; go (i + 1)
      | "--parallel" -> cfg.force_parallel <- true; go (i + 1)
      | "--parallel-strict" -> cfg.force_parallel_strict <- true; go (i + 1)
      | "--parallel-current" ->
          if i + 1 >= Array.length Sys.argv then invalid_non_negative_int Sys.argv.(0);
          let dim =
            try int_of_string Sys.argv.(i + 1)
            with Failure _ -> invalid_non_negative_int Sys.argv.(0)
          in
          if dim < 0 then invalid_non_negative_int Sys.argv.(0);
          cfg.parallel_current_dim <- Some dim;
          go (i + 2)
      | "--help" | "-h" ->
          print_endline (usage Sys.argv.(0));
          exit 0
      | "--validate-affine-openscop" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-affine-openscop expects two file paths";
          cfg.validate_affine_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--extract-tiling-witness-openscop" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --extract-tiling-witness-openscop expects two file paths";
          cfg.extract_tiling_witness_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-tiling-openscop" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-tiling-openscop expects two file paths";
          cfg.validate_tiling_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-iss-debug-dumps" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-iss-debug-dumps expects two file paths";
          cfg.validate_iss_debug_dumps <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-iss-bridge" ->
          if i + 1 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-iss-bridge expects one file path";
          cfg.validate_iss_bridge <- Some Sys.argv.(i + 1);
          go (i + 2)
      | "--validate-iss-pluto-suite" ->
          cfg.validate_iss_pluto_suite <- true;
          go (i + 1)
      | "--validate-iss-pluto-live-suite" ->
          cfg.validate_iss_pluto_live_suite <- true;
          go (i + 1)
      | s when String.length s > 0 && s.[0] = '-' ->
          usage_error Sys.argv.(0) ("unknown option: " ^ s)
      | file ->
          begin match cfg.input with
          | None -> cfg.input <- Some file; go (i + 1)
          | Some _ -> usage_error Sys.argv.(0) "only one input file is supported"
          end
    end
  in
  go 1

let validate_flag_model prog (cfg : config) =
  match SLoopRoute.normalize cfg with
  | Ok _ -> ()
  | Error msg -> usage_error prog msg

let configure_scheduler_modes (cfg : config) =
  Scheduler.set_tiling_mode
    (if cfg.force_second_level_tile
     then Scheduler.SecondLevelTiling
     else Scheduler.OrdinaryTiling);
  Scheduler.set_diamond_mode
    (if cfg.force_full_diamond_tile
     then Scheduler.FullDiamondTiling
     else if cfg.force_diamond_tile
     then Scheduler.DiamondTiling
     else Scheduler.NoDiamondTiling)
