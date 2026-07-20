Require Import SPolIRs.
Require Import TilingBandDirectRuntime.
Require Import TilingWitness.
Require Import PolOpt.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Local Open Scope string_scope.
Open Scope impure_scope.

Module CoreBandRuntime := TilingBandDirectRuntime SPolIRs.
Module CoreBandSched := CoreBandRuntime.Legacy.

Definition check_pprog_permutable_tiling_bands :=
  CoreBandSched.check_pprog_permutable_tiling_bands_runtime.

Definition check_pprog_permutable_tiling_bands_route
    (before after: CoreBandSched.Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list CoreBandSched.pinstr_tiling_band)
  : imp CoreBandRuntime.tiling_band_validation_route :=
  BIND direct_ok <-
    CoreBandSched.check_pprog_pluto_permutable_tiling_bands_direct
      before after ws bands -;
  if direct_ok then pure CoreBandRuntime.DirectBandAccepted
  else
    BIND legacy_route <-
      CoreBandSched.check_pprog_permutable_tiling_bands_runtime_route
        before after ws bands -;
    pure
      (if CoreBandSched.tiling_band_validation_route_acceptsb legacy_route
       then CoreBandRuntime.GeneralFallbackAccepted
       else CoreBandRuntime.Rejected).

Definition tiling_band_validation_route_acceptsb :=
  CoreBandRuntime.tiling_band_validation_route_acceptsb.

Definition check_pprog_pluto_permutable_tiling_bands_strong :=
  CoreBandSched.check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling.

Definition check_pprog_pluto_permutable_tiling_bands_direct_band :=
  CoreBandSched.check_pprog_pluto_permutable_tiling_bands_direct.

Definition checked_tiling_schedule_stripmined_validate_poly :=
  CoreBandSched.checked_tiling_schedule_stripmined_validate_poly.

Definition checked_tiling_schedule_stripmined_and_runtime_validate_poly :=
  CoreBandSched.checked_tiling_schedule_stripmined_and_runtime_validate_poly.

Definition infer_pprog_tiling_bands :=
  CoreBandSched.infer_pprog_tiling_bands.

Definition check_pprog_second_level_schedule_stripmined :=
  CoreBandSched.check_pprog_second_level_schedule_stripminedb.

Definition check_pprog_second_level_permutable_bands :=
  CoreBandSched.check_pprog_second_level_permutable_bands_via_validate_tiling.

Definition outer_to_tiling_pprog :=
  CoreBandSched.Base.outer_to_tiling_pprog.

Definition checked_tiling_schedule_sourceb_first_runtime_validate_route :=
  CoreBandRuntime.checked_tiling_schedule_sourceb_first_direct_runtime_validate_route.

Definition checked_tiling_schedule_stripmined_and_runtime_validate_route_poly :=
  checked_tiling_schedule_sourceb_first_runtime_validate_route.

Definition tiling_validation_route_label
    (route: CoreBandRuntime.tiling_band_validation_route) : string :=
  match route with
  | CoreBandRuntime.DirectBandAccepted => "permutable-band"
  | CoreBandRuntime.GeneralFallbackAccepted => "general-fallback"
  | CoreBandRuntime.Rejected => "rejected"
  end.

Definition print_tiling_validation_route_label (_: string) : unit := tt.

Definition observe_tiling_validation_route
    (route: CoreBandRuntime.tiling_band_validation_route)
  : CoreBandRuntime.tiling_band_validation_route :=
  PolOpt.print
    (fun selected =>
       print_tiling_validation_route_label
         (tiling_validation_route_label selected))
    route.

Lemma observe_tiling_validation_route_eq :
  forall route, observe_tiling_validation_route route = route.
Proof.
  reflexivity.
Qed.
