Require Import TPolIRs.
Require Import Validator.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
(** The final polyhedral optimizer *)

Require Import PolOpt.
Module TValidatorOpt := PolOpt TPolIRs.
Module TVal := TValidatorOpt.Validator.
