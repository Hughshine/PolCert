Require Import PolIRs.
Require Import ExtractorCorrect.

(** Compatibility facade for the extractor implementation layers. *)
Module Extractor (PolIRs : POLIRS).

Module Correct := ExtractorCorrect PolIRs.
Include Correct.

End Extractor.
