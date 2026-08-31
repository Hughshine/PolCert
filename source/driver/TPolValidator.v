Require Import TPolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import AffineValidator.

Module AffineCore := AffineValidator TPolIRs.

Definition validate := AffineCore.validate.
Definition check_wf_polyprog_general := AffineCore.check_wf_polyprog_general.
