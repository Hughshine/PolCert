Require Import PolOpt.
Require Import PolIRs.

Module PolOptPrepared (PolIRs: POLIRS).
Module Export Core := PolOpt PolIRs.
End PolOptPrepared.
