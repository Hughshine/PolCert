Require Import PolIRs.
Require Import TInstr.
Require Import PolyLang. 
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import String.

Local Open Scope string_scope.

Module TPolIRs <: POLIRS with Module Instr := TInstr.
   Module Instr := TInstr.
   Module State := State.
   Module Ty := Ty.
   Module PolyLang := PolyLang TInstr.
   Module PolyLoop := PolyLoop TInstr.
   Module Loop := Loop TInstr.
   Parameter scop_scheduler: OpenScop -> result OpenScop.

   Definition scheduler cpol :=
      match PolyLang.to_openscop cpol with
      | Some inscop =>
         match scop_scheduler inscop with
         | Okk outscop => PolyLang.from_openscop cpol outscop
         | Err msg => Err msg
         end
      | None => Err "Transform pol to openscop failed"
      end
   .
End TPolIRs.
