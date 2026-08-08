Require Import PolIRs.
Require Import ParallelCodegenCorrect.

(** Compatibility facade for the parallel code-generation proof layers. *)
Module ParallelCodegen (PolIRs : POLIRS).

Module Correct := ParallelCodegenCorrect PolIRs.
Include Correct.

End ParallelCodegen.
