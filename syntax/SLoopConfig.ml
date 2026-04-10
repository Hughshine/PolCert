type config = {
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
