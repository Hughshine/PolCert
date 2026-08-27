type schedule_family =
  | IdentitySchedule
  | AffineSchedule

type structural_extension =
  | Plain
  | ISS

type diamond_concurrent_start =
  | OneDimensionalStart
  | FullDimensionalStart

type tiling_shape =
  | Rectangular
  | Diamond of diamond_concurrent_start

type tiling_levels =
  | OneLevel
  | TwoLevels

type tiling_family =
  | NoTiling
  | Tiled of {
      shape : tiling_shape;
      levels : tiling_levels;
      explicitly_requested : bool;
    }

type execution_family =
  | Sequential
  | PlutoParallelHint of {
      strict : bool;
      multiple : bool;
    }
  | ParallelCurrent of int
  | PlutoVectorHint of { strict : bool }
  | VectorCurrent of int

type intra_tile_policy =
  | IntraTileDisabled
  | IntraTileEnabled

type optimize_route = {
  schedule_family : schedule_family;
  structural_extension : structural_extension;
  tiling_family : tiling_family;
  execution_family : execution_family;
  intra_tile_policy : intra_tile_policy;
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

let has_vector_current (cfg : SLoopConfig.config) =
  Option.is_some cfg.vector_current_dim

let has_parallel_or_vector_consumer (cfg : SLoopConfig.config) =
  cfg.force_parallel
  || cfg.force_vector
  || has_parallel_current cfg
  || has_vector_current cfg

let has_tiling route =
  match route.tiling_family with
  | NoTiling -> false
  | Tiled _ -> true

let identity_schedule route =
  route.schedule_family = IdentitySchedule

let iss_enabled route =
  route.structural_extension = ISS

let tiling_explicitly_requested route =
  match route.tiling_family with
  | NoTiling -> false
  | Tiled { explicitly_requested; _ } -> explicitly_requested

let incompatible_standalone_route_flag_selected (cfg : SLoopConfig.config) =
  cfg.force_identity
  || cfg.force_notile
  || cfg.force_iss
  || cfg.force_parallel
  || cfg.force_vector
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
  let schedule_family =
    if cfg.force_identity then IdentitySchedule else AffineSchedule
  in
  let structural_extension =
    if cfg.force_iss then ISS else Plain
  in
  let tiling_family =
    if cfg.force_notile || (cfg.force_identity && not cfg.pluto_tile_seen) then
      NoTiling
    else
      Tiled {
        shape =
          (if cfg.force_diamond_tile then
             Diamond
               (if cfg.force_full_diamond_tile
                then FullDimensionalStart
                else OneDimensionalStart)
           else
             Rectangular);
        levels =
          (if cfg.force_second_level_tile then TwoLevels else OneLevel);
        explicitly_requested =
          cfg.pluto_tile_seen
          || cfg.force_second_level_tile
          || cfg.force_diamond_tile;
      }
  in
  let execution_family =
    match cfg.vector_current_dim, cfg.parallel_current_dim with
    | Some dim, None -> VectorCurrent dim
    | None, Some dim -> ParallelCurrent dim
    | None, None ->
        if cfg.force_vector then
          PlutoVectorHint { strict = cfg.force_vector_strict }
        else if cfg.force_parallel then
          PlutoParallelHint {
            strict = cfg.force_parallel_strict;
            multiple = cfg.force_multipar;
          }
        else
          Sequential
    | Some _, Some _ ->
        (* [normalize] rejects this case before the route can be used. *)
        Sequential
  in
  let intra_tile_policy =
    if cfg.pluto_intratileopt_seen then IntraTileEnabled
    else IntraTileDisabled
  in
  {
    schedule_family;
    structural_extension;
    tiling_family;
    execution_family;
    intra_tile_policy;
    extract_only = cfg.extract_only;
    profile_stages = cfg.profile_stages;
  }

let normalize (cfg : SLoopConfig.config) =
  if cfg.pluto_tile_seen && cfg.pluto_notile_seen then
    Error "--tile and --notile select contradictory tiling routes"
  else if cfg.pluto_diamond_seen && cfg.pluto_nodiamond_seen then
    Error "--diamond-tile and --nodiamond-tile select contradictory tiling shapes"
  else if cfg.pluto_parallel_seen && cfg.pluto_no_parallel_seen then
    Error "--parallel and --noparallel select contradictory execution modes"
  else if cfg.pluto_intratileopt_seen && cfg.pluto_no_intratileopt_seen then
    Error "--intratileopt and --nointratileopt select contradictory intra-tile policies"
  else if cfg.pluto_prevector_seen && cfg.pluto_no_prevector_seen then
    Error "--prevector and --noprevector select contradictory vector modes"
  else if cfg.pluto_unrolljam_seen && cfg.pluto_no_unrolljam_seen then
    Error "--unrolljam and --nounrolljam select contradictory post passes"
  else
  match standalone_actions cfg with
  | _ :: _ :: _ ->
      Error "only one experimental validation action may be selected"
  | [action] ->
      if incompatible_standalone_route_flag_selected cfg then
        Error
          "optimization-route flags (--identity, --notile, --iss, --diamond-tile, --parallel, and --vector) cannot be combined with standalone validation actions"
      else if cfg.force_parallel_strict then
        Error "--parallel-strict cannot be combined with standalone validation actions"
      else if has_parallel_current cfg then
        Error "--parallel-current cannot be combined with standalone validation actions"
      else if cfg.force_vector_strict then
        Error "--vector-strict cannot be combined with standalone validation actions"
      else if has_vector_current cfg then
        Error "--vector-current cannot be combined with standalone validation actions"
      else if cfg.force_band_tiling_experiment then
        Error
          "--band-tiling-experiment only applies to the default non-ISS full tiled optimization route"
      else if cfg.force_legacy_generic_tiling then
        Error
          "--legacy-generic-tiling only applies to the default non-ISS full tiled optimization route"
      else if cfg.force_const_unroll then
        Error "--const-unroll cannot be combined with standalone validation actions"
      else if cfg.pluto_intratileopt_seen then
        Error "--intratileopt applies to optimization routes, not standalone validation actions"
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
      else if has_vector_current cfg && cfg.extract_only then
        Error "--vector-current cannot be combined with --extract-only"
      else if cfg.force_const_unroll && cfg.extract_only then
        Error "--const-unroll cannot be combined with --extract-only"
      else if cfg.force_iss && cfg.force_identity && not cfg.pluto_tile_seen
              && not (has_parallel_or_vector_consumer cfg)
      then
        Error
          "sequential --iss --identity is not a verified compiler route; add --tile or a checked parallel/vector consumer"
      else if cfg.force_iss && cfg.force_notile
              && not (has_parallel_or_vector_consumer cfg)
      then
        Error
          "sequential --iss --notile is not a verified compiler route; use --iss or add a checked parallel/vector consumer"
      else if cfg.force_parallel_strict && not cfg.force_parallel then
        Error "--parallel-strict requires --parallel"
      else if cfg.force_vector_strict && not cfg.force_vector then
        Error "--vector-strict requires --vector"
      else if cfg.force_parallel && cfg.force_identity && not cfg.pluto_tile_seen then
        Error "--parallel with --identity requires --tile so the checked identity-tiling route has a Pluto loop hint"
      else if cfg.force_vector && cfg.force_identity && not cfg.pluto_tile_seen then
        Error "--vector/--prevector with --identity requires --tile so the checked identity-tiling route has a Pluto loop hint"
      else if cfg.force_parallel && has_parallel_current cfg then
        Error "--parallel cannot be combined with --parallel-current"
      else if cfg.force_parallel && cfg.force_vector then
        Error "--parallel cannot be combined with --vector/--prevector"
      else if cfg.force_parallel && has_vector_current cfg then
        Error "--parallel cannot be combined with --vector-current"
      else if cfg.force_vector && has_parallel_current cfg then
        Error "--vector/--prevector cannot be combined with --parallel-current"
      else if cfg.force_vector && has_vector_current cfg then
        Error "--vector/--prevector cannot be combined with --vector-current"
      else if has_parallel_current cfg && has_vector_current cfg then
        Error "--parallel-current cannot be combined with --vector-current"
      else if cfg.force_multipar && not cfg.force_parallel then
        Error "--multipar requires the Pluto-hinted --parallel route"
      else if cfg.force_const_unroll
              && (cfg.force_parallel
                  || cfg.force_vector
                  || has_parallel_current cfg
                  || has_vector_current cfg)
      then
        Error "--const-unroll currently applies only to sequential Loop IR routes"
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
                  || cfg.force_vector
                  || cfg.force_vector_strict
                  || cfg.force_second_level_tile
                  || has_parallel_current cfg
                  || has_vector_current cfg)
      then
        Error
          "--band-tiling-experiment is now only a compatibility alias for the default non-ISS full tiled route"
      else if cfg.force_legacy_generic_tiling
              && (cfg.force_identity
                  || cfg.force_notile
                  || cfg.force_iss
                  || cfg.force_parallel
                  || cfg.force_parallel_strict
                  || cfg.force_vector
                  || cfg.force_vector_strict
                  || cfg.force_second_level_tile
                  || has_parallel_current cfg
                  || has_vector_current cfg)
      then
        Error
          "--legacy-generic-tiling only supports the default non-ISS full tiled route"
      else if cfg.force_second_level_tile && cfg.force_identity && not cfg.pluto_tile_seen then
        Error
          "--second-level-tile with --identity requires --tile"
      else if cfg.force_second_level_tile && cfg.force_notile then
        Error
          "--second-level-tile requires tiling and cannot be combined with --notile"
      else if cfg.force_diamond_tile && cfg.force_identity then
        Error
          "--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity"
      else if cfg.force_diamond_tile && cfg.force_notile then
        Error "--diamond-tile requires tiling and cannot be combined with --notile"
      else if cfg.force_diamond_tile
              && cfg.force_band_tiling_experiment
      then
        Error "--diamond-tile cannot be combined with --band-tiling-experiment"
      else if cfg.force_diamond_tile
              && cfg.force_legacy_generic_tiling
      then
        Error "--diamond-tile cannot be combined with --legacy-generic-tiling"
      else
        let route = optimize_route_of_config cfg in
        if cfg.pluto_intratileopt_seen && not (has_tiling route) then
          Error
            "--intratileopt requires a tiling route (default, --identity-tiled, --second-level-tile, or --diamond-tile)"
        else
          Ok (Optimize route)
