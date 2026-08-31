Require Import PolIRs.
Require Import ParallelCodegenCorrect.

(** Compatibility facade for the parallel code-generation proof layers. *)
Module ParallelCodegen (PolIRs : POLIRS).
Include ParallelCodegenCorrect PolIRs.

End ParallelCodegen.
