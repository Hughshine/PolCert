Require Import SPolIRs.
Require Import TilingBandScheduleValidator.
Require Import TilingWitness.
Require Import PolOpt.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Local Open Scope string_scope.

Module CoreBandSched := TilingBandScheduleValidator SPolIRs.

Definition check_pprog_permutable_tiling_bands :=
  CoreBandSched.check_pprog_permutable_tiling_bands_runtime.

Definition check_pprog_permutable_tiling_bands_route :=
  CoreBandSched.check_pprog_permutable_tiling_bands_runtime_route.

Definition tiling_band_validation_route_acceptsb :=
  CoreBandSched.tiling_band_validation_route_acceptsb.

Definition check_pprog_permutable_tiling_bands_direct :=
  CoreBandSched.check_pprog_permutable_tiling_bands_via_validate_tiling.

Definition check_pprog_pluto_permutable_tiling_bands_strong :=
  CoreBandSched.check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling.

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
  CoreBandSched.checked_tiling_schedule_sourceb_first_runtime_validate_route.

Definition checked_tiling_schedule_stripmined_and_runtime_validate_route_poly :=
  checked_tiling_schedule_sourceb_first_runtime_validate_route.

Definition tiling_validation_route_label
    (route: CoreBandSched.tiling_band_validation_route) : string :=
  match route with
  | CoreBandSched.TilingBandAccepted => "permutable-band"
  | CoreBandSched.TilingBandGeneralFallbackAccepted => "general-fallback"
  | CoreBandSched.TilingBandRejected => "rejected"
  end.

Definition print_tiling_validation_route_label (_: string) : unit := tt.

Definition observe_tiling_validation_route
    (route: CoreBandSched.tiling_band_validation_route)
  : CoreBandSched.tiling_band_validation_route :=
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
