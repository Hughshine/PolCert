type base_route =
  | Identity
  | AffineOnly
  | FullTiled

type structural_extension =
  | Plain
  | ISS

type ordinary_tiling_family =
  | BandAware
  | Generic

type diamond_strength =
  | DiamondNormal
  | DiamondFull

type tiling_family =
  | NoTiling
  | Ordinary of ordinary_tiling_family
  | SecondLevel
  | Diamond of diamond_strength

type parallel_family =
  | Sequential
  | PlutoHint of { strict : bool }
  | ExplicitCurrent of int

type optimize_route = {
  base_route : base_route;
  structural_extension : structural_extension;
  tiling_family : tiling_family;
  parallel_family : parallel_family;
  extract_only : bool;
  profile_stages : bool;
}

type standalone_action =
  | ValidateAffine of string * string
  | ExtractTilingWitness of {
      second_level : bool;
      before_file : string;
      after_file : string;
    }
  | ValidateTiling of {
      second_level : bool;
      before_file : string;
      after_file : string;
    }
  | ValidateIssDebugDumps of string * string
  | ValidateIssBridge of string
  | ValidateIssPlutoSuite
  | ValidateIssPlutoLiveSuite

type selection =
  | Optimize of optimize_route
  | Standalone of standalone_action

let has_parallel_current (cfg : SLoopConfig.config) =
  Option.is_some cfg.parallel_current_dim

let explicit_phase_control_selected (cfg : SLoopConfig.config) =
  cfg.force_identity
  || cfg.force_notile
  || cfg.force_iss
  || cfg.force_parallel
  || cfg.force_diamond_tile

let standalone_actions (cfg : SLoopConfig.config) =
  List.filter_map
    (fun x -> x)
    [
      Option.map
        (fun (before_file, after_file) -> ValidateAffine (before_file, after_file))
        cfg.validate_affine_openscop;
      Option.map
        (fun (before_file, after_file) ->
          ExtractTilingWitness
            {
              second_level = cfg.force_second_level_tile;
              before_file;
              after_file;
            })
        cfg.extract_tiling_witness_openscop;
      Option.map
        (fun (before_file, after_file) ->
          ValidateTiling
            {
              second_level = cfg.force_second_level_tile;
              before_file;
              after_file;
            })
        cfg.validate_tiling_openscop;
      Option.map
        (fun (before_file, after_file) ->
          ValidateIssDebugDumps (before_file, after_file))
        cfg.validate_iss_debug_dumps;
      Option.map
        (fun bridge_file -> ValidateIssBridge bridge_file)
        cfg.validate_iss_bridge;
      (if cfg.validate_iss_pluto_suite then Some ValidateIssPlutoSuite else None);
      (if cfg.validate_iss_pluto_live_suite then Some ValidateIssPlutoLiveSuite else None);
    ]

let optimize_route_of_config (cfg : SLoopConfig.config) =
  let base_route =
    if cfg.force_identity then Identity
    else if cfg.force_notile then AffineOnly
    else FullTiled
  in
  let structural_extension =
    if cfg.force_iss then ISS else Plain
  in
  let tiling_family =
    match base_route with
    | Identity | AffineOnly -> NoTiling
    | FullTiled ->
        if cfg.force_diamond_tile then
          Diamond
            (if cfg.force_full_diamond_tile
             then DiamondFull
             else DiamondNormal)
        else if cfg.force_second_level_tile then
          SecondLevel
        else if cfg.force_legacy_generic_tiling then
          Ordinary Generic
        else
          Ordinary BandAware
  in
  let parallel_family =
    match cfg.parallel_current_dim with
    | Some dim -> ExplicitCurrent dim
    | None ->
        if cfg.force_parallel then
          PlutoHint { strict = cfg.force_parallel_strict }
        else
          Sequential
  in
  {
    base_route;
    structural_extension;
    tiling_family;
    parallel_family;
    extract_only = cfg.extract_only;
    profile_stages = cfg.profile_stages;
  }

let normalize (cfg : SLoopConfig.config) =
  match standalone_actions cfg with
  | _ :: _ :: _ ->
      Error "only one experimental validation action may be selected"
  | [action] ->
      if explicit_phase_control_selected cfg then
        Error
          "phase-control flags (--identity/--notile/--iss/--diamond-tile) cannot be combined with standalone validation actions"
      else if cfg.force_parallel_strict then
        Error "--parallel-strict cannot be combined with standalone validation actions"
      else if has_parallel_current cfg then
        Error "--parallel-current cannot be combined with standalone validation actions"
      else if cfg.force_band_tiling_experiment then
        Error
          "--band-tiling-experiment only applies to the default non-ISS full tiled optimization route"
      else if cfg.force_legacy_generic_tiling then
        Error
          "--legacy-generic-tiling only applies to the default non-ISS full tiled optimization route"
      else if cfg.force_second_level_tile
              && match action with
                 | ExtractTilingWitness _ | ValidateTiling _ -> false
                 | _ -> true
      then
        Error
          "--second-level-tile only applies to tiled optimization or tiling witness/validation actions"
      else
        Ok (Standalone action)
  | [] ->
      if has_parallel_current cfg && cfg.extract_only then
        Error "--parallel-current cannot be combined with --extract-only"
      else if cfg.force_parallel_strict && not cfg.force_parallel then
        Error "--parallel-strict requires --parallel"
      else if cfg.force_parallel && cfg.force_identity then
        Error "--parallel requires a Pluto scheduling phase and cannot be combined with --identity"
      else if cfg.force_parallel && has_parallel_current cfg then
        Error "--parallel cannot be combined with --parallel-current"
      else if cfg.force_band_tiling_experiment
              && cfg.force_legacy_generic_tiling
      then
        Error "--band-tiling-experiment cannot be combined with --legacy-generic-tiling"
      else if cfg.force_band_tiling_experiment
              && (cfg.force_identity
                  || cfg.force_notile
                  || cfg.force_iss
                  || cfg.force_parallel
                  || cfg.force_parallel_strict
                  || has_parallel_current cfg)
      then
        Error
          "--band-tiling-experiment is now only a compatibility alias for the default non-ISS full tiled route"
      else if cfg.force_legacy_generic_tiling
              && (cfg.force_identity
                  || cfg.force_notile
                  || cfg.force_iss
                  || cfg.force_parallel
                  || cfg.force_parallel_strict
                  || has_parallel_current cfg)
      then
        Error
          "--legacy-generic-tiling only supports the default non-ISS full tiled route"
      else if cfg.force_second_level_tile && cfg.force_identity then
        Error
          "--second-level-tile requires a tiled Pluto phase and cannot be combined with --identity"
      else if cfg.force_second_level_tile && cfg.force_notile then
        Error
          "--second-level-tile requires tiling and cannot be combined with --notile"
      else if cfg.force_second_level_tile && cfg.force_parallel then
        Error "--second-level-tile is not yet supported with --parallel"
      else if cfg.force_second_level_tile && has_parallel_current cfg then
        Error "--second-level-tile is not yet supported with --parallel-current"
      else if cfg.force_diamond_tile && cfg.force_identity then
        Error
          "--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity"
      else if cfg.force_diamond_tile && cfg.force_notile then
        Error "--diamond-tile requires tiling and cannot be combined with --notile"
      else if cfg.force_diamond_tile && cfg.force_parallel && cfg.force_iss then
        Error "--diamond-tile --iss is not yet supported with --parallel"
      else if cfg.force_diamond_tile
              && cfg.force_band_tiling_experiment
      then
        Error "--diamond-tile cannot be combined with --band-tiling-experiment"
      else if cfg.force_diamond_tile
              && cfg.force_legacy_generic_tiling
      then
        Error "--diamond-tile cannot be combined with --legacy-generic-tiling"
      else
        Ok (Optimize (optimize_route_of_config cfg))
