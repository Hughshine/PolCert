Require Import TPolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import PolOpt.

Module TValidatorOpt := PolOpt TPolIRs.

Definition validate := TValidatorOpt.ValidatorCore.validate.
