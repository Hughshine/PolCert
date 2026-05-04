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
  mutable pluto_compat_mode : bool;
  mutable pluto_compat_explain : bool;
  mutable pluto_compat_dry_run : bool;
  mutable pluto_tile_seen : bool;
  mutable pluto_notile_seen : bool;
  mutable pluto_diamond_seen : bool;
  mutable pluto_nodiamond_seen : bool;
  mutable pluto_parallel_seen : bool;
  mutable pluto_no_parallel_seen : bool;
  mutable pluto_no_intratileopt_seen : bool;
  mutable pluto_no_prevector_seen : bool;
  mutable pluto_no_unrolljam_seen : bool;
  mutable pluto_compat_notes : string list;
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
        "Usage: %s [--dump-input] [--dump-extracted-openscop] [--dump-scheduled-openscop] [--debug-scheduler] [--extract-only] [--profile-stages] [--identity] [--notile] [--iss] [--second-level-tile] [--diamond-tile] [--full-diamond-tile] [--band-tiling-experiment] [--legacy-generic-tiling] [--parallel] [--parallel-strict] [--parallel-current <dim>] <file.loop>\n"
        prog;
      Printf.sprintf
        "       %s --pluto-compat [--explain] [--dry-run] <Pluto-like optimizer flags> <file.loop>\n"
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
      "                        full tiled optimization routes and tiling witness/validation\n";
      "                        actions\n";
      "  --diamond-tile    : experimental sequential checked diamond midpoint + tiling route;\n";
      "                      supported on non-ISS/ISS and ordinary/second-level tiled paths\n";
      "  --full-diamond-tile : stronger diamond producer mode over the same checked route;\n";
      "                        supported on non-ISS/ISS and ordinary/second-level tiled paths\n";
      "  --band-tiling-experiment : compatibility alias for the default band-aware\n";
      "                             ordinary tiling route; only valid on the default\n";
      "                             non-ISS full tiled path\n";
      "  --legacy-generic-tiling : use the historical generic ordinary-tiling validator path\n";
      "                            instead of the default band-aware path\n";
      "  --parallel        : experimental verified `parallel for` route driven by Pluto `--parallel`\n";
      "                       loop hints; supported on both the default and `--iss` pipelines,\n";
      "                       with or without `--notile`\n";
      "  --parallel-strict : with `--parallel`, require the certified parallel loop to be the\n";
      "                       Pluto-hinted dimension; otherwise keep the sequential optimized loop\n";
      "  --parallel-current d : theorem-aligned verified `parallel for` on explicit current\n";
      "                         dimension d; supported on identity, affine-only, and full\n";
      "                         tiled paths, including their `--iss` variants and the\n";
      "                         non-ISS diamond route\n";
      "  --pluto-compat    : parse Pluto-style optimizer flags in this OCaml driver,\n";
      "                      reject unsupported Pluto defaults/features with explicit\n";
      "                      reasons, then run the matching checked polopt route\n";
      "\nExamples:\n";
      Printf.sprintf "  %s file.loop                        # default theorem-aligned band-aware affine+tiling path\n" prog;
      Printf.sprintf "  %s --profile-stages file.loop       # print per-stage timings for the default route\n" prog;
      Printf.sprintf "  %s --second-level-tile file.loop    # full tiled checked path with second-level tiling enabled\n" prog;
      Printf.sprintf "  %s --diamond-tile file.loop         # sequential checked diamond midpoint + tiling route\n" prog;
      Printf.sprintf "  %s --iss --diamond-tile file.loop   # ISS split plus checked diamond route\n" prog;
      Printf.sprintf "  %s --full-diamond-tile file.loop    # stronger diamond producer mode over the same checked route\n" prog;
      Printf.sprintf "  %s --parallel file.loop             # Pluto-hinted verified parallel path\n" prog;
      Printf.sprintf "  %s --parallel --parallel-strict file.loop\n" prog;
      Printf.sprintf "  %s --parallel-current 0 file.loop   # theorem-aligned explicit-dimension parallel path\n" prog;
      Printf.sprintf "  %s --diamond-tile --parallel-current 0 file.loop\n" prog;
      Printf.sprintf "  %s --iss --parallel-current 0 file.loop\n" prog;
      Printf.sprintf "  %s --notile file.loop               # affine-only checked path\n" prog;
      Printf.sprintf "  %s --identity file.loop             # identity/no-schedule path\n" prog;
      Printf.sprintf "  %s --validate-affine-openscop before.scop mid.scop\n" prog;
      Printf.sprintf "  %s --validate-tiling-openscop mid.scop after.scop\n" prog;
      Printf.sprintf "  %s --second-level-tile --validate-tiling-openscop mid.scop after.scop\n" prog;
      Printf.sprintf "  %s --iss --identity file.loop       # ISS-only checked split path\n" prog;
      Printf.sprintf "  %s --pluto-compat --tile --smartfuse --nointratileopt --noprevector --nounrolljam --rar --nodiamond-tile --noparallel file.loop\n" prog;
    ]

let usage_error prog msg =
  prerr_endline msg;
  prerr_endline (usage prog);
  exit 2

let pluto_reject prog msg =
  ignore prog;
  prerr_endline ("[pluto-compat] reject: " ^ msg);
  exit 2

let enable_pluto_compat cfg =
  cfg.pluto_compat_mode <- true

let add_pluto_note cfg msg =
  cfg.pluto_compat_notes <- cfg.pluto_compat_notes @ [msg]

let starts_with s prefix =
  let len_s = String.length s in
  let len_p = String.length prefix in
  len_s >= len_p && String.sub s 0 len_p = prefix

let split_eq_flag s =
  match String.index_opt s '=' with
  | None -> None
  | Some idx ->
      Some
        (String.sub s 0 idx,
         String.sub s (idx + 1) (String.length s - idx - 1))

let value_options = [
  "--cache-size";
  "--cloogf";
  "--cloogl";
  "--codegen-context";
  "--coeff-bound";
  "--data-element-size";
  "--ft";
  "--lt";
  "--ufactor";
  "-o";
]

let output_value_options = [
  "--cloogf";
  "--cloogl";
  "--codegen-context";
  "-o";
]

let known_rejection_reason = function
  | "--pet" -> Some "frontend is polopt's verified loop extractor, not Pluto/PET"
  | "--readscop" -> Some "frontend is polopt's verified loop extractor, not Pluto OpenScop input"
  | "--dumpscop" -> Some "Pluto OpenScop dumps are an oracle-debug interface, not a polopt input/output mode"
  | "--version" -> Some "CLI version reporting is outside the optimizer-compatibility surface"
  | "--candldep" -> Some "Candl dependence testing is not exposed through the checked polopt route"
  | "--isldepaccesswise" -> Some "ISL dependence-analysis tuning is not exposed through the checked polopt route"
  | "--isldepstmtwise" -> Some "ISL dependence-analysis tuning is not exposed through the checked polopt route"
  | "--isldepcoalesce" -> Some "ISL dependence-analysis tuning is not exposed through the checked polopt route"
  | "--lastwriter" -> Some "last-writer dependence mode is not exposed through the checked polopt route"
  | "--nolastwriter" -> Some "last-writer dependence mode is not exposed through the checked polopt route"
  | "--pipsolve" -> Some "PIP solver selection is not exposed through the checked polopt route"
  | "--scalpriv" -> Some "Candl scalar privatization is not exposed through the checked polopt route"
  | "--clusterscc" -> Some "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists"
  | "--delayedcut" -> Some "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists"
  | "--dfp" -> Some "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists"
  | "--glpk" -> Some "current Pluto build has no GLPK support and polopt has no checked DFP route"
  | "--gurobi" -> Some "current Pluto build has no Gurobi support and polopt has no checked DFP route"
  | "--hybridfuse" -> Some "hybrid fusion depends on DFP/typed fusion, which is outside the checked polopt route"
  | "--ilp" -> Some "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists"
  | "--lp" -> Some "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists"
  | "--lpcolor" -> Some "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists"
  | "--typedfuse" -> Some "typed fusion depends on DFP, which is outside the checked polopt route"
  | "--bee" -> Some "Bee pragmas are Pluto codegen output, while polopt uses its own codegen"
  | "--cloogsh" -> Some "Cloog codegen tuning is outside the polopt checked route"
  | "--indent" -> Some "formatting is outside the optimizer-validation route"
  | "--prevector" -> Some "prevectorization is a Pluto codegen/post-transform effect, while polopt uses its own codegen"
  | "--unrolljam" -> Some "unroll-jam is a Pluto post-codegen transform, not a checked polopt schedule route"
  | "--determine-tile-size" -> Some "automatic Pluto tile-size selection is not exposed through the checked polopt route"
  | "--fast-lin-ind-check" -> Some "fast linear-independence search tuning is not exposed through the checked polopt route"
  | "--flic" -> Some "fast linear-independence search tuning is not exposed through the checked polopt route"
  | "--forceparallel" -> Some "Pluto accepts this flag, but the current source has no effective use site"
  | "--intratileopt" -> Some "Pluto intra-tile schedule rewriting is not exposed through the checked polopt route"
  | "--maxfuse" -> Some "maximal fusion is not exposed as a checked polopt route"
  | "--multipar" -> Some "multi-degree Pluto parallel extraction is not exposed through the checked polopt route"
  | "--nofuse" -> Some "no-fusion scheduling is not exposed as a checked polopt route"
  | "--nodepbound" -> Some "dependence-bound search tuning is not exposed through the checked polopt route"
  | "--per-cc-obj" -> Some "per-connected-component objective is not exposed as a checked polopt route"
  | "--dump-iss-bridge" -> Some "this flag is not accepted by the current Pluto binary"
  | "--lbtile" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | "--multipipe" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | "--output" -> Some "the current Pluto binary uses -o, not --output"
  | "--sched" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | "--variables_not_global" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | _ -> None

let reject_value_option prog flag value =
  if List.mem flag output_value_options then
    pluto_reject prog (flag ^ ": output/codegen shaping is outside the polopt checked route")
  else
    pluto_reject prog (Printf.sprintf "%s: value %S is not exposed through the checked polopt route" flag value)

let pluto_polopt_args cfg =
  let args = ref [] in
  if cfg.force_iss then args := !args @ ["--iss"];
  if cfg.force_identity then args := !args @ ["--identity"]
  else begin
    if cfg.force_notile then args := !args @ ["--notile"];
    if cfg.force_second_level_tile then args := !args @ ["--second-level-tile"];
    if cfg.force_full_diamond_tile then args := !args @ ["--full-diamond-tile"]
    else if cfg.force_diamond_tile then args := !args @ ["--diamond-tile"];
    if cfg.force_parallel then args := !args @ ["--parallel"]
  end;
  !args

let print_pluto_explain cfg =
  let args = pluto_polopt_args cfg in
  print_endline "[pluto-compat] accepted";
  print_endline
    ("[pluto-compat] polopt args: "
     ^ (match args with [] -> "<default>" | _ -> String.concat " " args));
  List.iter
    (fun note -> print_endline ("[pluto-compat] note: " ^ note))
    cfg.pluto_compat_notes

let validate_pluto_compat prog cfg =
  if cfg.pluto_compat_mode then begin
    if cfg.pluto_tile_seen && cfg.pluto_notile_seen then
      pluto_reject prog "--tile and --notile are both present; this driver rejects contradictory phase controls";
    if cfg.parallel_current_dim <> None then
      pluto_reject prog "--parallel-current: not a Pluto flag; use native polopt mode for explicit-current parallel certification";
    if cfg.pluto_parallel_seen && cfg.pluto_no_parallel_seen then
      pluto_reject prog "--parallel and --noparallel are both present; this driver rejects contradictory phase controls";
    if cfg.pluto_diamond_seen && cfg.pluto_nodiamond_seen then
      pluto_reject prog "--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present; this driver rejects contradictory phase controls";
    if not cfg.pluto_no_intratileopt_seen then
      pluto_reject prog "Pluto enables --intratileopt by default; pass --nointratileopt for the current checked polopt subset";
    if not cfg.pluto_no_prevector_seen then
      pluto_reject prog "Pluto enables --prevector by default; pass --noprevector because polopt does not use Pluto codegen vector marking";
    if not cfg.pluto_no_unrolljam_seen then
      pluto_reject prog "Pluto enables --unrolljam by default; pass --nounrolljam because polopt does not use Pluto unroll-jam output";
    if (not cfg.force_parallel) && not cfg.pluto_no_parallel_seen then
      pluto_reject prog "Pluto enables --parallel by default; pass --noparallel or --parallel explicitly";
    if (not cfg.force_diamond_tile) && not cfg.pluto_nodiamond_seen then
      pluto_reject prog "Pluto enables --diamond-tile by default; pass --nodiamond-tile or --diamond-tile explicitly";
    if cfg.force_identity && not cfg.pluto_notile_seen then
      pluto_reject prog "--identity: current Pluto keeps tiling enabled by default; use --identity --notile for polopt's no-tiling identity route";
    if cfg.force_identity && cfg.pluto_tile_seen then
      pluto_reject prog "--identity --tile: Pluto can tile identity schedules, but polopt has no checked identity+tiling route yet";
    if cfg.force_identity && cfg.force_parallel then
      pluto_reject prog "--parallel requires a Pluto scheduling phase and cannot be combined with --identity";
    if cfg.force_second_level_tile && cfg.force_notile then
      pluto_reject prog "--second-level-tile requires tiling and cannot be combined with --notile";
    if cfg.force_second_level_tile && cfg.force_identity then
      pluto_reject prog "--second-level-tile requires a tiled Pluto phase and cannot be combined with --identity";
    if cfg.force_second_level_tile && cfg.force_parallel then
      pluto_reject prog "--second-level-tile is not yet supported with --parallel";
    if cfg.force_diamond_tile then begin
      if cfg.force_notile then
        pluto_reject prog "--diamond-tile requires tiling and cannot be combined with --notile";
      if cfg.force_identity then
        pluto_reject prog "--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity";
      ()
    end
  end

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
      pluto_compat_mode = false;
      pluto_compat_explain = false;
      pluto_compat_dry_run = false;
      pluto_tile_seen = false;
      pluto_notile_seen = false;
      pluto_diamond_seen = false;
      pluto_nodiamond_seen = false;
      pluto_parallel_seen = false;
      pluto_no_parallel_seen = false;
      pluto_no_intratileopt_seen = false;
      pluto_no_prevector_seen = false;
      pluto_no_unrolljam_seen = false;
      pluto_compat_notes = [];
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
      | "--pluto-compat" -> enable_pluto_compat cfg; go (i + 1)
      | "--explain" ->
          enable_pluto_compat cfg;
          cfg.pluto_compat_explain <- true;
          go (i + 1)
      | "--dry-run" ->
          enable_pluto_compat cfg;
          cfg.pluto_compat_dry_run <- true;
          go (i + 1)
      | "--dump-input" -> cfg.dump_input <- true; go (i + 1)
      | "--dump-extracted-openscop" -> cfg.dump_extracted_openscop <- true; go (i + 1)
      | "--dump-scheduled-openscop" -> cfg.dump_scheduled_openscop <- true; go (i + 1)
      | "--debug-scheduler" -> cfg.debug_scheduler <- true; go (i + 1)
      | "--extract-only" -> cfg.extract_only <- true; go (i + 1)
      | "--profile-stages" -> cfg.profile_stages <- true; go (i + 1)
      | "--identity" -> cfg.force_identity <- true; go (i + 1)
      | "--tile" ->
          enable_pluto_compat cfg;
          cfg.pluto_tile_seen <- true;
          cfg.force_notile <- false;
          go (i + 1)
      | "--notile" ->
          cfg.force_notile <- true;
          cfg.pluto_notile_seen <- true;
          go (i + 1)
      | "--affine-only" -> cfg.force_notile <- true; go (i + 1)
      | "--iss" -> cfg.force_iss <- true; go (i + 1)
      | "--second-level-tile" -> cfg.force_second_level_tile <- true; go (i + 1)
      | "--diamond-tile" ->
          cfg.force_diamond_tile <- true;
          cfg.pluto_diamond_seen <- true;
          go (i + 1)
      | "--nodiamond-tile" ->
          enable_pluto_compat cfg;
          cfg.force_diamond_tile <- false;
          cfg.force_full_diamond_tile <- false;
          cfg.pluto_nodiamond_seen <- true;
          go (i + 1)
      | "--full-diamond-tile" ->
          cfg.force_diamond_tile <- true;
          cfg.force_full_diamond_tile <- true;
          cfg.pluto_diamond_seen <- true;
          go (i + 1)
      | "--band-tiling-experiment" -> cfg.force_band_tiling_experiment <- true; go (i + 1)
      | "--legacy-generic-tiling" -> cfg.force_legacy_generic_tiling <- true; go (i + 1)
      | "--parallel" | "--parallelize" ->
          cfg.force_parallel <- true;
          cfg.pluto_parallel_seen <- true;
          go (i + 1)
      | "--noparallel" ->
          enable_pluto_compat cfg;
          cfg.force_parallel <- false;
          cfg.pluto_no_parallel_seen <- true;
          go (i + 1)
      | "--innerpar" ->
          enable_pluto_compat cfg;
          add_pluto_note cfg "--innerpar is implicit in polopt's current --parallel route";
          go (i + 1)
      | "--parallel-strict" -> cfg.force_parallel_strict <- true; go (i + 1)
      | "--nointratileopt" ->
          enable_pluto_compat cfg;
          cfg.pluto_no_intratileopt_seen <- true;
          add_pluto_note cfg "--nointratileopt accepted because checked routes disable Pluto intra-tile rewriting";
          go (i + 1)
      | "--noprevector" ->
          enable_pluto_compat cfg;
          cfg.pluto_no_prevector_seen <- true;
          add_pluto_note cfg "--noprevector accepted because polopt does not use Pluto codegen vector marking";
          go (i + 1)
      | "--nounrolljam" ->
          enable_pluto_compat cfg;
          cfg.pluto_no_unrolljam_seen <- true;
          add_pluto_note cfg "--nounrolljam accepted because polopt does not use Pluto unroll-jam output";
          go (i + 1)
      | (("--debug" | "--isldep" | "--islsolve" | "--moredebug"
         | "--nocloogbacktrack" | "--rar" | "--silent" | "--smartfuse") as flag) ->
          enable_pluto_compat cfg;
          add_pluto_note cfg (flag ^ " accepted as a no-op for the checked polopt route");
          go (i + 1)
      | "--unroll" ->
          pluto_reject Sys.argv.(0) "--unroll: Pluto only accepts this as an abbreviation for --unrolljam; unroll-jam is not a checked polopt route"
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
      | s when List.mem s value_options ->
          enable_pluto_compat cfg;
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) (s ^ " requires a value");
          reject_value_option Sys.argv.(0) s Sys.argv.(i + 1)
      | s when
          begin match split_eq_flag s with
          | Some (flag, _) -> List.mem flag value_options
          | None -> false
          end ->
          enable_pluto_compat cfg;
          begin match split_eq_flag s with
          | Some (flag, value) -> reject_value_option Sys.argv.(0) flag value
          | None -> assert false
          end
      | s when
          begin match known_rejection_reason s with
          | Some reason -> pluto_reject Sys.argv.(0) (s ^ ": " ^ reason)
          | None -> false
          end ->
          assert false
      | s when starts_with s "--" ->
          if cfg.pluto_compat_mode then
            pluto_reject Sys.argv.(0) (s ^ ": not in the current Pluto-compatible checked subset")
          else
            usage_error Sys.argv.(0) ("unknown option: " ^ s)
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
  validate_pluto_compat prog cfg;
  match SLoopRoute.normalize cfg with
  | Ok _ ->
      if cfg.pluto_compat_mode && cfg.pluto_compat_explain then
        print_pluto_explain cfg
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
