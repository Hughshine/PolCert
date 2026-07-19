Require Import String.

Require Import ImpureAlarmConfig.
Require Import Result.
Require Import SPolIRs.
Require Import SPolOpt.
Require Import SBandTilingOpt.

Local Open Scope string_scope.

Inductive raw_config : Type :=
| RawIdentity
| RawAffine
| RawDefault
| RawDefaultBand
| RawSecondLevel
| RawSecondLevelISS
| RawIdentitySecondLevel
| RawIdentitySecondLevelISS
| RawIdentityBand
| RawIdentityBandISS
| RawISS
| RawDiamond
| RawDiamondISS
| RawUnsupported.

Inductive verified_config : Type :=
| VIdentity
| VAffine
| VDefault
| VDefaultBand
| VSecondLevel
| VSecondLevelISS
| VIdentitySecondLevel
| VIdentitySecondLevelISS
| VIdentityBand
| VIdentityBandISS
| VISS
| VDiamond
| VDiamondISS.

Definition check_config (cfg: raw_config) : result verified_config :=
  match cfg with
  | RawIdentity => Okk VIdentity
  | RawAffine => Okk VAffine
  | RawDefault => Okk VDefault
  | RawDefaultBand => Okk VDefaultBand
  | RawSecondLevel => Okk VSecondLevel
  | RawSecondLevelISS => Okk VSecondLevelISS
  | RawIdentitySecondLevel => Okk VIdentitySecondLevel
  | RawIdentitySecondLevelISS => Okk VIdentitySecondLevelISS
  | RawIdentityBand => Okk VIdentityBand
  | RawIdentityBandISS => Okk VIdentityBandISS
  | RawISS => Okk VISS
  | RawDiamond => Okk VDiamond
  | RawDiamondISS => Okk VDiamondISS
  | RawUnsupported => Err "unsupported verified compiler configuration"
  end.
(* This executable dispatcher is intentionally enumerated for now. A later
   version can replace [verified_config] with a compositional pass descriptor
   list once the route theorems are exposed in a uniform pass-composition form. *)
Definition compile_verified
    (cfg: verified_config) (loop: SPolIRs.Loop.t)
    : imp SPolIRs.Loop.t :=
  match cfg with
  | VIdentity => SPolOpt.opt_identity loop
  | VAffine => SPolOpt.opt_affine loop
  | VDefault => SBandTilingOpt.opt loop
  | VDefaultBand => SBandTilingOpt.opt loop
  | VSecondLevel => SBandTilingOpt.opt loop
  | VSecondLevelISS => SBandTilingOpt.opt_with_iss loop
  | VIdentitySecondLevel => SBandTilingOpt.opt_identity_tiled loop
  | VIdentitySecondLevelISS =>
      SBandTilingOpt.opt_identity_tiled_with_iss loop
  | VIdentityBand => SBandTilingOpt.opt_identity_tiled loop
  | VIdentityBandISS => SBandTilingOpt.opt_identity_tiled_with_iss loop
  | VISS => SBandTilingOpt.opt_with_iss loop
  | VDiamond => SBandTilingOpt.opt_diamond loop
  | VDiamondISS => SBandTilingOpt.opt_diamond_with_iss loop
  end.

Definition compile (cfg: raw_config) (loop: SPolIRs.Loop.t)
    : imp SPolIRs.Loop.t :=
  match check_config cfg with
  | Okk vcfg => compile_verified vcfg loop
  | Err msg => res_to_alarm loop (Err msg)
  end.
