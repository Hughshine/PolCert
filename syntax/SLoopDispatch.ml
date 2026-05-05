open SLoopCommon

type standalone_handlers = {
  sa_run_affine_validator : string -> string -> int;
  sa_run_tiling_witness_extractor :
    second_level:bool -> string -> string -> int;
  sa_run_tiling_validator : second_level:bool -> string -> string -> int;
  sa_run_iss_dump_validator : string -> string -> int;
  sa_run_iss_bridge_validator : string -> int;
  sa_run_iss_pluto_suite : unit -> int;
  sa_run_iss_pluto_live_suite : unit -> int;
}

type standalone_dispatch =
  | ContinueToLoop
  | ExitCode of int
  | InvalidStandaloneFlags

let run_standalone_action (cfg : SLoopCli.config) handlers =
  match cfg.validate_affine_openscop, cfg.extract_tiling_witness_openscop,
        cfg.validate_tiling_openscop, cfg.validate_iss_debug_dumps,
        cfg.validate_iss_bridge, cfg.validate_iss_pluto_suite,
        cfg.validate_iss_pluto_live_suite with
  | Some (before_file, after_file), None, None, None, None, false, false ->
      ExitCode (handlers.sa_run_affine_validator before_file after_file)
  | None, Some (before_file, after_file), None, None, None, false, false ->
      ExitCode
        (handlers.sa_run_tiling_witness_extractor
           ~second_level:cfg.force_second_level_tile
           before_file
           after_file)
  | None, None, Some (before_file, after_file), None, None, false, false ->
      ExitCode
        (handlers.sa_run_tiling_validator
           ~second_level:cfg.force_second_level_tile
           before_file
           after_file)
  | None, None, None, Some (before_file, after_file), None, false, false ->
      ExitCode (handlers.sa_run_iss_dump_validator before_file after_file)
  | None, None, None, None, Some bridge_file, false, false ->
      ExitCode (handlers.sa_run_iss_bridge_validator bridge_file)
  | None, None, None, None, None, true, false ->
      ExitCode (handlers.sa_run_iss_pluto_suite ())
  | None, None, None, None, None, false, true ->
      ExitCode (handlers.sa_run_iss_pluto_live_suite ())
  | None, None, None, None, None, false, false ->
      ContinueToLoop
  | _ ->
      InvalidStandaloneFlags

type 'loop sequential_handlers = {
  seq_optimize_diamond : 'loop -> 'loop * bool;
  seq_optimize_diamond_iss : 'loop -> 'loop * bool;
  seq_optimize_iss_identity : 'loop -> 'loop * bool;
  seq_optimize_iss_affine : 'loop -> 'loop * bool;
  seq_optimize_iss_default : 'loop -> 'loop * bool;
  seq_optimize_identity : 'loop -> 'loop * bool;
  seq_optimize_identity_tiled : 'loop -> 'loop * bool;
  seq_optimize_affine : 'loop -> 'loop * bool;
  seq_optimize_legacy : 'loop -> 'loop * bool;
  seq_optimize_default : 'loop -> 'loop * bool;
}

let run_selected_optimization (cfg : SLoopCli.config) handlers loop =
  if cfg.force_diamond_tile then
    if cfg.force_iss then
      handlers.seq_optimize_diamond_iss loop
    else
      handlers.seq_optimize_diamond loop
  else if cfg.force_iss then
    if cfg.force_identity then
      handlers.seq_optimize_iss_identity loop
    else if cfg.force_notile then
      handlers.seq_optimize_iss_affine loop
    else
      handlers.seq_optimize_iss_default loop
  else if cfg.force_identity then
    if cfg.pluto_tile_seen then
      handlers.seq_optimize_identity_tiled loop
    else
      handlers.seq_optimize_identity loop
  else if cfg.force_notile then
    handlers.seq_optimize_affine loop
  else if cfg.force_legacy_generic_tiling then
    handlers.seq_optimize_legacy loop
  else
    handlers.seq_optimize_default loop

type ('loop, 'parallel_loop) hinted_parallel_handlers = {
  hint_optimize_diamond :
    SLoopCli.config -> 'loop -> 'parallel_loop * bool;
  hint_optimize_iss_affine :
    SLoopCli.config -> 'loop -> 'parallel_loop * bool;
  hint_optimize_iss_default :
    SLoopCli.config -> 'loop -> 'parallel_loop * bool;
  hint_optimize_affine :
    SLoopCli.config -> 'loop -> 'parallel_loop * bool;
  hint_optimize_default :
    SLoopCli.config -> 'loop -> 'parallel_loop * bool;
}

let run_selected_parallel_optimization (cfg : SLoopCli.config) handlers loop =
  if cfg.force_diamond_tile then
    handlers.hint_optimize_diamond cfg loop
  else if cfg.force_iss then
    if cfg.force_notile then
      handlers.hint_optimize_iss_affine cfg loop
    else
      handlers.hint_optimize_iss_default cfg loop
  else if cfg.force_notile then
    handlers.hint_optimize_affine cfg loop
  else
    handlers.hint_optimize_default cfg loop

type ('loop, 'parallel_loop) current_parallel_handlers = {
  cur_optimize_diamond :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_diamond_iss :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_iss_identity :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_iss_affine :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_iss_default :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_identity :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_affine :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
  cur_optimize_default :
    'loop -> Datatypes.nat -> 'parallel_loop * bool;
}

let run_selected_parallel_current_optimization
    (cfg : SLoopCli.config)
    handlers
    loop
    dim =
  let dim = nat_of_int dim in
  if cfg.force_diamond_tile then
    if cfg.force_iss then
      handlers.cur_optimize_diamond_iss loop dim
    else
      handlers.cur_optimize_diamond loop dim
  else if cfg.force_iss then
    if cfg.force_identity then
      handlers.cur_optimize_iss_identity loop dim
    else if cfg.force_notile then
      handlers.cur_optimize_iss_affine loop dim
    else
      handlers.cur_optimize_iss_default loop dim
  else if cfg.force_identity then
    handlers.cur_optimize_identity loop dim
  else if cfg.force_notile then
    handlers.cur_optimize_affine loop dim
  else
    handlers.cur_optimize_default loop dim
