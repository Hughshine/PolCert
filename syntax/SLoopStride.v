Require Import SPolIRs.
Require Import LoopStride.

Module CoreStride := LoopStride SPolIRs.

Definition stride_loop :
    nat -> SPolIRs.Loop.expr -> SPolIRs.Loop.expr -> SPolIRs.Loop.stmt ->
    SPolIRs.Loop.stmt :=
  CoreStride.stride_loop.

Definition stride_count_expr :
    nat -> SPolIRs.Loop.expr -> SPolIRs.Loop.expr -> SPolIRs.Loop.expr :=
  CoreStride.stride_count_expr.
