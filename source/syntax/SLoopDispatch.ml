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

let run_standalone_action selection handlers =
  match selection with
  | SLoopRoute.Optimize _ ->
      ContinueToLoop
  | SLoopRoute.Standalone
      (SLoopRoute.ValidateAffine (before_file, after_file)) ->
      ExitCode (handlers.sa_run_affine_validator before_file after_file)
  | SLoopRoute.Standalone
      (SLoopRoute.ExtractTilingWitness { second_level; before_file; after_file }) ->
      ExitCode
        (handlers.sa_run_tiling_witness_extractor
           ~second_level
           before_file
           after_file)
  | SLoopRoute.Standalone
      (SLoopRoute.ValidateTiling { second_level; before_file; after_file }) ->
      ExitCode
        (handlers.sa_run_tiling_validator
           ~second_level
           before_file
           after_file)
  | SLoopRoute.Standalone
      (SLoopRoute.ValidateIssDebugDumps (before_file, after_file)) ->
      ExitCode (handlers.sa_run_iss_dump_validator before_file after_file)
  | SLoopRoute.Standalone (SLoopRoute.ValidateIssBridge bridge_file) ->
      ExitCode (handlers.sa_run_iss_bridge_validator bridge_file)
  | SLoopRoute.Standalone SLoopRoute.ValidateIssPlutoSuite ->
      ExitCode (handlers.sa_run_iss_pluto_suite ())
  | SLoopRoute.Standalone SLoopRoute.ValidateIssPlutoLiveSuite ->
      ExitCode (handlers.sa_run_iss_pluto_live_suite ())
