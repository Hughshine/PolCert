Require Import Bool.
Require Import List.
Require Import String.
Import ListNotations.
Require Import Result.
Require Import Base.
Require Import PolyBase.
Require Import PolyLang.
Require Import AST.
Require Import BinPos.
Require Import PolyTest.
Require Import Linalg.
Require Import PolyOperations.
Require Import Loop.
Require Import ZArith.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import SelectionSort.

Require Import Extractor.
Require Import CodeGen.
Require Import Validator.
Require Import PolOpt.
Require Import PrepareCodegen.
Require Import StrengthenDomain.
Require Import LibTactics.
Require Import sflib.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import PolIRs.

Module PolOptPrepared (PolIRs: POLIRS).

Definition scheduler := PolIRs.scheduler.
Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module Loop := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.

Module Extractor := Extractor PolIRs.
Module CodeGen := CodeGen PolIRs.
Module Validator := Validator PolIRs.
Module Prepare := PrepareCodegen PolIRs.
Module Strengthen := StrengthenDomain PolIRs.
Module BaseOpt := PolOpt PolIRs.

Local Open Scope impure_scope.

Definition Opt_prepared (loop: Loop.t): imp Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  BIND pol' <- BaseOpt.scheduler' (Strengthen.strengthen_pprog pol0) -;
  Prepare.prepared_codegen pol'.

Definition Opt : Loop.t -> imp Loop.t := Opt_prepared.

Lemma extractor_success_wf_pprog:
  forall loop pol,
    Extractor.extractor loop = Okk pol ->
    PolyLang.wf_pprog pol.
Proof.
  intros loop [[pis varctxt] vars] Hext.
  split.
  - eapply Extractor.extractor_success_implies_varctxt_le_vars; eauto.
  - intros pi Hin.
    pose proof (Extractor.extractor_success_implies_wf_pinstrs loop pis varctxt vars Hext) as Hall.
    eapply Forall_forall in Hall; eauto.
Qed.

Lemma scheduler'_preserve_wf:
  forall pol pol',
    PolyLang.wf_pprog pol ->
    WHEN pol'' <- BaseOpt.scheduler' pol THEN
    pol'' = pol' ->
    PolyLang.wf_pprog pol'.
Proof.
  intros pol pol' Hwf pol'' Hsched Heq.
  subst pol''.
  unfold BaseOpt.scheduler' in Hsched.
  destruct scheduler eqn:Hschedsrc.
  2: {
    exfalso.
    eapply mayReturn_alarm in Hsched.
    exact Hsched.
  }
  bind_imp_destruct Hsched res Hval.
  destruct res.
  2: {
    exfalso.
    eapply mayReturn_alarm in Hsched.
    exact Hsched.
  }
  eapply mayReturn_pure in Hsched. subst.
  pose proof (Validator.validate_preserve_wf_pprog pol pol' _ Hval eq_refl) as [_ Hwf'].
  exact Hwf'.
Qed.

Theorem Extract_Schedule_Prepared_correct:
  forall loop pol st1 st2,
    Extractor.extractor loop = Okk pol ->
    WHEN pol' <- BaseOpt.scheduler' (Strengthen.strengthen_pprog pol) THEN
    PolyLang.wf_pprog pol' ->
    PolyLang.semantics (Prepare.prepare_codegen pol') st1 st2 ->
    exists st2',
      Loop.semantics loop st1 st2' /\ State.eq st2 st2'.
Proof.
  intros loop pol st1 st2 Hext pol' Hsched Hwf Hsem.
  eapply Prepare.prepare_codegen_semantics_correct in Hsem; eauto.
  pose proof (BaseOpt.scheduler'_correct (Strengthen.strengthen_pprog pol) st1 st2 pol' Hsched Hsem)
    as Hsched_corr.
  destruct Hsched_corr as [st_mid [Hips Heq]].
  eapply Strengthen.instance_list_semantics_unstrengthen in Hips.
  pose proof (Extractor.extractor_correct loop pol st1 st_mid Hext Hips) as Hext_corr.
  destruct Hext_corr as [st_src [Hloop Heq_src]].
  exists st_src. split; auto.
  eapply State.eq_trans; eauto.
Qed.

Theorem Opt_prepared_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared loop THEN
    Loop.semantics loop' st st' ->
    exists st'',
      Loop.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  bind_imp_destruct Hopt pol' Hsched.
  apply res_to_alarm_correct in Hextimp.
  assert (Hwfpol' : PolyLang.wf_pprog pol').
  {
    eapply scheduler'_preserve_wf.
    - eapply Strengthen.strengthen_pprog_wf.
      eapply extractor_success_wf_pprog; eauto.
    - exact Hsched.
    - reflexivity.
  }
  pose proof (Prepare.prepared_codegen_correct pol' st st' loop' Hopt Hwfpol' Hloop) as Hips.
  pose proof (BaseOpt.scheduler'_correct (Strengthen.strengthen_pprog pol0) st st' pol' Hsched Hips)
    as Hsched_corr.
  destruct Hsched_corr as [st_mid [Hips' Heq]].
  eapply Strengthen.instance_list_semantics_unstrengthen in Hips'.
  pose proof (Extractor.extractor_correct loop pol0 st st_mid Hextimp Hips') as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src. split; auto.
  eapply State.eq_trans; eauto.
Qed.

Theorem Opt_correct:
  forall loop st st',
    WHEN loop' <- Opt loop THEN
    Loop.semantics loop' st st' ->
    exists st'',
      Loop.semantics loop st st'' /\ State.eq st' st''.
Proof.
  exact Opt_prepared_correct.
Qed.

End PolOptPrepared.
