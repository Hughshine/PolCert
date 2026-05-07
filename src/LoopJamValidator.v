Require Import Lia.
Require Import String.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Local Open Scope string_scope.

Require Import Extractor.
Require Import JamValidator.
Require Import PolIRs.
Require Import StrengthenDomain.

Module LoopJamValidator (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module ExtractorCore := Extractor PolIRs.
Module StrengthenCore := StrengthenDomain PolIRs.
Module JamCore := JamValidator PolIRs.

Record loop_jam_cert := {
  loop_jam_poly : PolyLang.t;
  loop_jam_core_cert : JamCore.jam_cert
}.

Definition checked_loop_jam_current
    (loop : Loop.t) (plan : JamCore.jam_plan)
  : imp (result loop_jam_cert) :=
  match ExtractorCore.extractor loop with
  | Okk pol0 =>
      let pol := StrengthenCore.strengthen_pprog pol0 in
      BIND cert_res <- JamCore.checked_jam_current pol plan -;
      match cert_res with
      | Okk cert =>
          pure
            (Okk
              {|
                loop_jam_poly := pol;
                loop_jam_core_cert := cert
              |})
      | Err msg => pure (Err msg)
      end
  | Err msg => pure (Err msg)
  end.

Definition loop_jam_cert_sound (cert : loop_jam_cert) : Prop :=
  JamCore.adjacent_jam_cert_sound
    cert.(loop_jam_poly)
    cert.(loop_jam_core_cert).

Theorem checked_loop_jam_current_sound :
  forall loop plan cert,
    mayReturn (checked_loop_jam_current loop plan) (Okk cert) ->
    loop_jam_cert_sound cert.
Proof.
  intros loop plan cert Hchecked.
  unfold checked_loop_jam_current in Hchecked.
  destruct (ExtractorCore.extractor loop) as [pol0|msg] eqn:Hext.
  - apply mayReturn_bind in Hchecked.
    destruct Hchecked as [cert_res [Hcore Hret]].
    destruct cert_res as [core_cert|core_msg].
    + apply mayReturn_pure in Hret.
      inversion Hret; subst; clear Hret.
      unfold loop_jam_cert_sound; simpl.
      eapply JamCore.checked_jam_current_sound.
      exact Hcore.
    + apply mayReturn_pure in Hret.
      discriminate.
  - apply mayReturn_pure in Hchecked.
    discriminate.
Qed.

Theorem checked_loop_jam_current_factor_positive :
  forall loop plan cert,
    mayReturn (checked_loop_jam_current loop plan) (Okk cert) ->
    (0 < JamCore.certified_factor cert.(loop_jam_core_cert))%nat.
Proof.
  intros loop plan cert Hchecked.
  unfold checked_loop_jam_current in Hchecked.
  destruct (ExtractorCore.extractor loop) as [pol0|msg] eqn:Hext.
  - apply mayReturn_bind in Hchecked.
    destruct Hchecked as [cert_res [Hcore Hret]].
    destruct cert_res as [core_cert|core_msg].
    + apply mayReturn_pure in Hret.
      inversion Hret; subst; clear Hret.
      simpl.
      eapply JamCore.checked_jam_current_factor_positive.
      exact Hcore.
    + apply mayReturn_pure in Hret.
      discriminate.
  - apply mayReturn_pure in Hchecked.
    discriminate.
Qed.

End LoopJamValidator.
