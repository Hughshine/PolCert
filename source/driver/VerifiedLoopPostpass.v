Require Import Bool.
Require Import String.

Require Import ImpureAlarmConfig.
Require Import LoopCleanup.
Require Import LoopJamBridge.
Require Import LoopUnroll.
Require Import PolIRs.
Require Import Result.
Require Import Vpl.Impure.

Local Open Scope impure_scope.
Local Open Scope string_scope.

(** Constant-bound unrolling is an independent compiler dimension, rather
    than another copy of every affine, tiling, and ISS route. *)
Inductive loop_postpass_config : Type :=
| NoLoopPostpass
| ConstUnrollPostpass.

Module VerifiedLoopPostpass (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module State := PolIRs.State.
Module Unroll := LoopUnroll PolIRs.
Module Cleanup := LoopCleanup PolIRs.
Module JamBridge := LoopJamBridge PolIRs.
Module JamLower := JamBridge.Lower.

Definition apply (cfg : loop_postpass_config) (loop : Loop.t) : imp Loop.t :=
  match cfg with
  | NoLoopPostpass => pure loop
  | ConstUnrollPostpass =>
      if Unroll.const_unroll_changed loop then
        pure (Cleanup.cleanup (Unroll.const_unroll loop))
      else
        res_to_alarm loop
          (Err "constant unroll requested, but no constant-bounded loop exists")
  end.

(** Execute the complete checked unroll-jam postpass.  [select] is an
    untrusted policy function: it may choose any subset of loop positions, but
    every fusion it requests is independently accepted or rejected by the
    extracted validator.  Quantifying over [select] keeps profitability and
    command-line policy outside the trusted base. *)
Definition apply_checked_unrolljam
    (const_first : bool)
    (select : Loop.t -> JamLower.unrolljam_plan)
    (factor : nat) (loop : Loop.t) : imp Loop.t :=
  let prepared :=
    if const_first && Unroll.const_unroll_changed loop then
      Cleanup.cleanup (Unroll.const_unroll loop)
    else loop in
  BIND jammed <-
    JamLower.checked_unrolljam_loop_with_plan
      (select prepared) factor prepared -;
  pure (Cleanup.cleanup jammed).

Theorem apply_correct :
  forall cfg loop loop' st st',
    mayReturn (apply cfg loop) loop' ->
    Loop.semantics loop' st st' ->
    exists st'',
      Loop.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop loop' st st' Happly Hsem.
  destruct cfg as [|]; simpl in Happly.
  - apply mayReturn_pure in Happly.
    subst loop'.
    exists st'.
    split; [exact Hsem|apply State.eq_refl].
  - destruct (Unroll.const_unroll_changed loop) eqn:Hchanged.
    + apply mayReturn_pure in Happly.
      subst loop'.
      pose proof
        ((proj1
           (Cleanup.cleanup_correct
              (Unroll.const_unroll loop) st st')) Hsem) as Hunrolled.
      pose proof
        ((proj1 (Unroll.const_unroll_correct loop st st')) Hunrolled)
        as Hsource.
      exists st'.
      split; [exact Hsource|apply State.eq_refl].
    + apply mayReturn_alarm in Happly.
      contradiction.
Qed.

Theorem apply_checked_unrolljam_correct :
  forall const_first select factor loop loop' st st',
    mayReturn
      (apply_checked_unrolljam const_first select factor loop)
      loop' ->
    Loop.semantics loop' st st' ->
    exists st'',
      Loop.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros const_first select factor loop loop' st st' Happly Hsem.
  unfold apply_checked_unrolljam in Happly.
  remember
    (if const_first && Unroll.const_unroll_changed loop then
       Cleanup.cleanup (Unroll.const_unroll loop)
     else loop) as prepared eqn:Hprepared.
  apply mayReturn_bind in Happly.
  destruct Happly as [jammed [Hjam Hret]].
  apply mayReturn_pure in Hret.
  subst loop'.
  pose proof
    ((proj1 (Cleanup.cleanup_correct jammed st st')) Hsem)
    as Hjammed_sem.
  assert
    (Hpair :
       let '(_, varctxt, vars) := prepared in
       JamBridge.Context.checked_pair_refines varctxt vars).
  {
    destruct prepared as [[prepared_stmt varctxt] vars].
    simpl.
    apply JamBridge.checked_pair_refines_sound.
  }
  pose proof
    (JamBridge.Context.checked_unrolljam_loop_with_plan_refines
       (select prepared) factor prepared jammed Hpair Hjam)
    as Hrefines.
  unfold JamBridge.Context.loop_refines in Hrefines.
  destruct (Hrefines st st' Hjammed_sem)
    as [st_prepared [Hprepared_sem Heq]].
  destruct (const_first && Unroll.const_unroll_changed loop) eqn:Hconst.
  - subst prepared.
    pose proof
      ((proj1
          (Cleanup.cleanup_correct
             (Unroll.const_unroll loop) st st_prepared)) Hprepared_sem)
      as Hunrolled_sem.
    pose proof
      ((proj1 (Unroll.const_unroll_correct loop st st_prepared))
         Hunrolled_sem)
      as Hsource_sem.
    exists st_prepared.
    split; assumption.
  - subst prepared.
    exists st_prepared.
    split; assumption.
Qed.

End VerifiedLoopPostpass.
