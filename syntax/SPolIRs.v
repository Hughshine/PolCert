Require Import PolIRs.
Require Import SInstr.
Require Import PolyLang.
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import String.

Local Open Scope string_scope.

Module SPolIRs <: POLIRS with Module Instr := SInstr.
  Module Instr := SInstr.
  Module State := State.
  Module Ty := Ty.
  Module PolyLang := PolyLang SInstr.
  Module PolyLoop := PolyLoop SInstr.
  Module Loop := Loop SInstr.
  Parameter scop_scheduler : OpenScop -> result OpenScop.

  Definition scheduler cpol :=
    match PolyLang.to_openscop cpol with
    | Some inscop =>
        match scop_scheduler inscop with
      | Okk outscop => PolyLang.from_openscop_like_source cpol outscop
        | Err msg => Err msg
        end
    | None => Err "Transform pol to openscop failed"
    end.
End SPolIRs.
