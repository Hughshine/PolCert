Require Import String.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import Result.
Require Import Vpl.Impure.
Require Import VerifiedCompilerConfig.
Require Import ParallelPolOpt.
Require Import ParallelPolOptCorrect.

Local Open Scope impure_scope.
Local Open Scope string_scope.

Module VerifiedParallelCompilerConfig (PolIRs: POLIRS).

Module SeqCompiler := VerifiedCompilerConfig PolIRs.
Module ParallelCore := ParallelPolOpt.ParallelPolOpt PolIRs.
Module ParallelCorrect := ParallelPolOptCorrect PolIRs ParallelCore.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.
Module ParallelLoop := ParallelCorrect.ParallelLoop.
Module ParallelCodegenCore := ParallelCore.ParallelCodegenCore.

(** * Proof map

    This is the final theorem-facing dispatcher.  Sequential routes are lifted
    into the common annotated-loop target language; parallel and vector routes
    call their corresponding [ParallelPolOptCorrect] theorems.
    [compile_verified_correct] handles the verified constructors and
    [compile_correct] discharges raw configuration checking. *)

Inductive raw_config : Type :=
| RawSeq (cfg: SeqCompiler.raw_config)
| RawParallelCurrentIdentity (d: nat)
| RawParallelCurrentIdentityTiled (d: nat)
| RawParallelCurrentIdentityTiledISS (d: nat)
| RawParallelCurrentAffine (d: nat)
| RawParallelCurrentDefault (d: nat)
| RawParallelCurrentDiamond (d: nat)
| RawParallelCurrentDiamondISS (d: nat)
| RawParallelCurrentIdentityISS (d: nat)
| RawParallelCurrentAffineISS (d: nat)
| RawParallelCurrentDefaultISS (d: nat)
| RawVectorCurrentIdentity (d: nat)
| RawVectorCurrentIdentityTiled (d: nat)
| RawVectorCurrentIdentityTiledISS (d: nat)
| RawVectorCurrentAffine (d: nat)
| RawVectorCurrentDefault (d: nat)
| RawVectorCurrentDiamond (d: nat)
| RawVectorCurrentDiamondISS (d: nat)
| RawVectorCurrentIdentityISS (d: nat)
| RawVectorCurrentAffineISS (d: nat)
| RawVectorCurrentDefaultISS (d: nat)
| RawParallelCurrentManyIdentity (dims: list nat)
| RawParallelCurrentManyIdentityTiled (dims: list nat)
| RawParallelCurrentManyIdentityTiledISS (dims: list nat)
| RawParallelCurrentManyAffine (dims: list nat)
| RawParallelCurrentManyDefault (dims: list nat)
| RawParallelCurrentManyDiamond (dims: list nat)
| RawParallelCurrentManyDiamondISS (dims: list nat)
| RawParallelCurrentManyIdentityISS (dims: list nat)
| RawParallelCurrentManyAffineISS (dims: list nat)
| RawParallelCurrentManyDefaultISS (dims: list nat)
| RawUnsupported.

Inductive verified_config : Type :=
| VSeq (cfg: SeqCompiler.verified_config)
| VParallelCurrentIdentity (d: nat)
| VParallelCurrentIdentityTiled (d: nat)
| VParallelCurrentIdentityTiledISS (d: nat)
| VParallelCurrentAffine (d: nat)
| VParallelCurrentDefault (d: nat)
| VParallelCurrentDiamond (d: nat)
| VParallelCurrentDiamondISS (d: nat)
| VParallelCurrentIdentityISS (d: nat)
| VParallelCurrentAffineISS (d: nat)
| VParallelCurrentDefaultISS (d: nat)
| VVectorCurrentIdentity (d: nat)
| VVectorCurrentIdentityTiled (d: nat)
| VVectorCurrentIdentityTiledISS (d: nat)
| VVectorCurrentAffine (d: nat)
| VVectorCurrentDefault (d: nat)
| VVectorCurrentDiamond (d: nat)
| VVectorCurrentDiamondISS (d: nat)
| VVectorCurrentIdentityISS (d: nat)
| VVectorCurrentAffineISS (d: nat)
| VVectorCurrentDefaultISS (d: nat)
| VParallelCurrentManyIdentity (dims: list nat)
| VParallelCurrentManyIdentityTiled (dims: list nat)
| VParallelCurrentManyIdentityTiledISS (dims: list nat)
| VParallelCurrentManyAffine (dims: list nat)
| VParallelCurrentManyDefault (dims: list nat)
| VParallelCurrentManyDiamond (dims: list nat)
| VParallelCurrentManyDiamondISS (dims: list nat)
| VParallelCurrentManyIdentityISS (dims: list nat)
| VParallelCurrentManyAffineISS (dims: list nat)
| VParallelCurrentManyDefaultISS (dims: list nat).

Definition check_config (cfg: raw_config) : result verified_config :=
  match cfg with
  | RawSeq seq_cfg =>
      match SeqCompiler.check_config seq_cfg with
      | Okk vcfg => Okk (VSeq vcfg)
      | Err msg => Err msg
      end
  | RawParallelCurrentIdentity d => Okk (VParallelCurrentIdentity d)
  | RawParallelCurrentIdentityTiled d => Okk (VParallelCurrentIdentityTiled d)
  | RawParallelCurrentIdentityTiledISS d =>
      Okk (VParallelCurrentIdentityTiledISS d)
  | RawParallelCurrentAffine d => Okk (VParallelCurrentAffine d)
  | RawParallelCurrentDefault d => Okk (VParallelCurrentDefault d)
  | RawParallelCurrentDiamond d => Okk (VParallelCurrentDiamond d)
  | RawParallelCurrentDiamondISS d => Okk (VParallelCurrentDiamondISS d)
  | RawParallelCurrentIdentityISS d => Okk (VParallelCurrentIdentityISS d)
  | RawParallelCurrentAffineISS d => Okk (VParallelCurrentAffineISS d)
  | RawParallelCurrentDefaultISS d => Okk (VParallelCurrentDefaultISS d)
  | RawVectorCurrentIdentity d => Okk (VVectorCurrentIdentity d)
  | RawVectorCurrentIdentityTiled d => Okk (VVectorCurrentIdentityTiled d)
  | RawVectorCurrentIdentityTiledISS d => Okk (VVectorCurrentIdentityTiledISS d)
  | RawVectorCurrentAffine d => Okk (VVectorCurrentAffine d)
  | RawVectorCurrentDefault d => Okk (VVectorCurrentDefault d)
  | RawVectorCurrentDiamond d => Okk (VVectorCurrentDiamond d)
  | RawVectorCurrentDiamondISS d => Okk (VVectorCurrentDiamondISS d)
  | RawVectorCurrentIdentityISS d => Okk (VVectorCurrentIdentityISS d)
  | RawVectorCurrentAffineISS d => Okk (VVectorCurrentAffineISS d)
  | RawVectorCurrentDefaultISS d => Okk (VVectorCurrentDefaultISS d)
  | RawParallelCurrentManyIdentity dims => Okk (VParallelCurrentManyIdentity dims)
  | RawParallelCurrentManyIdentityTiled dims => Okk (VParallelCurrentManyIdentityTiled dims)
  | RawParallelCurrentManyIdentityTiledISS dims =>
      Okk (VParallelCurrentManyIdentityTiledISS dims)
  | RawParallelCurrentManyAffine dims => Okk (VParallelCurrentManyAffine dims)
  | RawParallelCurrentManyDefault dims => Okk (VParallelCurrentManyDefault dims)
  | RawParallelCurrentManyDiamond dims => Okk (VParallelCurrentManyDiamond dims)
  | RawParallelCurrentManyDiamondISS dims => Okk (VParallelCurrentManyDiamondISS dims)
  | RawParallelCurrentManyIdentityISS dims => Okk (VParallelCurrentManyIdentityISS dims)
  | RawParallelCurrentManyAffineISS dims => Okk (VParallelCurrentManyAffineISS dims)
  | RawParallelCurrentManyDefaultISS dims => Okk (VParallelCurrentManyDefaultISS dims)
  | RawUnsupported => Err "unsupported verified compiler configuration"
  end.

Definition checked_lift_sequential_loop (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  let pl := ParallelCodegenCore.tag_loop loop in
  if ParallelCodegenCore.all_es_safeb pl then
    pure pl
  else
    res_to_alarm
      ParallelCore.parallel_dummy
      (Err "sequential route produced a non-affine ParallelLoop trace"%string).

Definition lift_sequential_compile
    (compile: imp LoopIR.t)
  : imp ParallelLoop.t :=
  BIND loop <- compile -;
  checked_lift_sequential_loop loop.

Definition checked_sequential_current_annotated_codegen
    (pol: PolyLang.t)
  : imp ParallelLoop.t :=
  BIND res <-
    ParallelCodegenCore.checked_annotated_codegen_many
      (PolyLang.current_view_pprog pol)
      nil -;
  res_to_alarm ParallelCore.parallel_dummy res.

Definition compile_seq_verified
    (cfg: SeqCompiler.verified_config)
    (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  lift_sequential_compile (SeqCompiler.compile_verified cfg loop).

Definition compile_verified
    (cfg: verified_config) (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  match cfg with
  | VSeq seq_cfg =>
      compile_seq_verified seq_cfg loop
  | VParallelCurrentIdentity d =>
      ParallelCore.Opt_parallel_current_identity loop d
  | VParallelCurrentIdentityTiled d =>
      ParallelCore.Opt_parallel_current_identity_tiled loop d
  | VParallelCurrentIdentityTiledISS d =>
      ParallelCore.Opt_parallel_current_identity_tiled_with_iss loop d
  | VParallelCurrentAffine d =>
      ParallelCore.Opt_parallel_current_affine loop d
  | VParallelCurrentDefault d =>
      ParallelCore.Opt_parallel_current loop d
  | VParallelCurrentDiamond d =>
      ParallelCore.Opt_parallel_current_diamond loop d
  | VParallelCurrentDiamondISS d =>
      ParallelCore.Opt_parallel_current_diamond_with_iss loop d
  | VParallelCurrentIdentityISS d =>
      ParallelCore.Opt_parallel_current_identity_with_iss loop d
  | VParallelCurrentAffineISS d =>
      ParallelCore.Opt_parallel_current_affine_with_iss loop d
  | VParallelCurrentDefaultISS d =>
      ParallelCore.Opt_parallel_current_with_iss loop d
  | VVectorCurrentIdentity d =>
      ParallelCore.Opt_vector_current_identity loop d
  | VVectorCurrentIdentityTiled d =>
      ParallelCore.Opt_vector_current_identity_tiled loop d
  | VVectorCurrentIdentityTiledISS d =>
      ParallelCore.Opt_vector_current_identity_tiled_with_iss loop d
  | VVectorCurrentAffine d =>
      ParallelCore.Opt_vector_current_affine loop d
  | VVectorCurrentDefault d =>
      ParallelCore.Opt_vector_current loop d
  | VVectorCurrentDiamond d =>
      ParallelCore.Opt_vector_current_diamond loop d
  | VVectorCurrentDiamondISS d =>
      ParallelCore.Opt_vector_current_diamond_with_iss loop d
  | VVectorCurrentIdentityISS d =>
      ParallelCore.Opt_vector_current_identity_with_iss loop d
  | VVectorCurrentAffineISS d =>
      ParallelCore.Opt_vector_current_affine_with_iss loop d
  | VVectorCurrentDefaultISS d =>
      ParallelCore.Opt_vector_current_with_iss loop d
  | VParallelCurrentManyIdentity dims =>
      ParallelCore.Opt_parallel_current_many_identity loop dims
  | VParallelCurrentManyIdentityTiled dims =>
      ParallelCore.Opt_parallel_current_many_identity_tiled loop dims
  | VParallelCurrentManyIdentityTiledISS dims =>
      ParallelCore.Opt_parallel_current_many_identity_tiled_with_iss loop dims
  | VParallelCurrentManyAffine dims =>
      ParallelCore.Opt_parallel_current_many_affine loop dims
  | VParallelCurrentManyDefault dims =>
      ParallelCore.Opt_parallel_current_many loop dims
  | VParallelCurrentManyDiamond dims =>
      ParallelCore.Opt_parallel_current_many_diamond loop dims
  | VParallelCurrentManyDiamondISS dims =>
      ParallelCore.Opt_parallel_current_many_diamond_with_iss loop dims
  | VParallelCurrentManyIdentityISS dims =>
      ParallelCore.Opt_parallel_current_many_identity_with_iss loop dims
  | VParallelCurrentManyAffineISS dims =>
      ParallelCore.Opt_parallel_current_many_affine_with_iss loop dims
  | VParallelCurrentManyDefaultISS dims =>
      ParallelCore.Opt_parallel_current_many_with_iss loop dims
  end.

Definition compile (cfg: raw_config) (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  match check_config cfg with
  | Okk vcfg => compile_verified vcfg loop
  | Err msg => res_to_alarm ParallelCore.parallel_dummy (Err msg)
  end.

Lemma checked_lift_sequential_loop_correct :
  forall loop pl st st',
    mayReturn (checked_lift_sequential_loop loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop pl st st' Hlift Hsem.
  unfold checked_lift_sequential_loop in Hlift.
  destruct (ParallelCodegenCore.all_es_safeb
              (ParallelCodegenCore.tag_loop loop)) eqn:Hsafe.
  - apply mayReturn_pure in Hlift.
    subst pl.
    pose proof
      (ParallelCodegenCore.all_es_safeb_sound
         (ParallelCodegenCore.tag_loop loop) Hsafe)
      as Htrace_safe.
    pose proof
      (ParallelLoop.semantics_refines_erased
         (ParallelCodegenCore.tag_loop loop) st st' Htrace_safe Hsem)
      as [st'' [Herased Heq]].
    exists st''.
    split.
    + eapply ParallelCodegenCore.erase_to_loop_semantics in Herased.
      rewrite ParallelCodegenCore.erase_tag_loop_eq in Herased.
      exact Herased.
    + exact Heq.
  - apply mayReturn_alarm in Hlift.
    tauto.
Qed.

Lemma opt_parallel_current_identity_tiled_correct :
  forall loop d pl st st',
    mayReturn (ParallelCore.Opt_parallel_current_identity_tiled loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold ParallelCore.Opt_parallel_current_identity_tiled in Hopt.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply ParallelCorrect.Opt_parallel_current_identity_tiled_result_correct; eauto.
Qed.

Lemma checked_sequential_current_annotated_codegen_correct :
  forall pol pl st st',
    mayReturn (checked_sequential_current_annotated_codegen pol) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pl st st' Hcodegen Hwf Hsem.
  unfold checked_sequential_current_annotated_codegen in Hcodegen.
  bind_imp_destruct Hcodegen res Hchecked.
  pose proof Hcodegen as Hres.
  apply res_to_alarm_correct in Hres.
  subst res.
  eapply ParallelCodegenCore.checked_annotated_codegen_many_correct_general;
    eauto.
Qed.

Ltac finish_strengthened_source loop pol0 st Hextok Hroute :=
  let st_str := fresh "st_str" in
  let Hstr_sem := fresh "Hstr_sem" in
  let Heq_str := fresh "Heq_str" in
  destruct Hroute as [st_str [Hstr_sem Heq_str]];
  eapply ParallelCore.CoreOpt.Strengthen.instance_list_semantics_unstrengthen
    in Hstr_sem;
  let Hext_corr := fresh "Hext_corr" in
  pose proof
    (ParallelCore.CoreOpt.Extractor.extractor_correct
       loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr;
  let st_src := fresh "st_src" in
  let Hloop_src := fresh "Hloop_src" in
  let Heq_src := fresh "Heq_src" in
  destruct Hext_corr as [st_src [Hloop_src Heq_src]];
  exists st_src;
  split; [exact Hloop_src|];
  eapply State.eq_trans; [exact Heq_str| exact Heq_src].

Ltac finish_strengthened_source_with loop pol0 st Heq_out Hextok Hroute :=
  let st_str := fresh "st_str" in
  let Hstr_sem := fresh "Hstr_sem" in
  let Heq_str := fresh "Heq_str" in
  destruct Hroute as [st_str [Hstr_sem Heq_str]];
  eapply ParallelCore.CoreOpt.Strengthen.instance_list_semantics_unstrengthen
    in Hstr_sem;
  let Hext_corr := fresh "Hext_corr" in
  pose proof
    (ParallelCore.CoreOpt.Extractor.extractor_correct
       loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr;
  let st_src := fresh "st_src" in
  let Hloop_src := fresh "Hloop_src" in
  let Heq_src := fresh "Heq_src" in
  destruct Hext_corr as [st_src [Hloop_src Heq_src]];
  exists st_src;
  split; [exact Hloop_src|];
  eapply State.eq_trans;
    [exact Heq_out| eapply State.eq_trans; [exact Heq_str| exact Heq_src]].

Lemma compile_seq_verified_correct :
  forall cfg loop pl st st',
    mayReturn (compile_seq_verified cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  unfold compile_seq_verified, lift_sequential_compile in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [loop' [Hseq Hlift]].
  destruct
    (checked_lift_sequential_loop_correct loop' pl st st' Hlift Hsem)
    as [st_mid [Hmid_sem Heq_mid]].
  destruct
    (SeqCompiler.compile_verified_correct
       cfg loop st st_mid loop' Hseq Hmid_sem)
    as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; [exact Hsrc_sem|].
  eapply State.eq_trans; eauto.
Qed.

Theorem compile_verified_correct :
  forall cfg loop pl st st',
    mayReturn (compile_verified cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  destruct cfg; simpl in Hcompile.
  - eapply compile_seq_verified_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_correct; eauto.
  - eapply opt_parallel_current_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_tiled_with_iss_correct;
      eauto.
  - eapply ParallelCorrect.Opt_parallel_current_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_diamond_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_diamond_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_tiled_with_iss_correct;
      eauto.
  - eapply ParallelCorrect.Opt_vector_current_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_diamond_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_diamond_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_tiled_with_iss_correct;
      eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_diamond_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_diamond_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_with_iss_correct; eauto.
Qed.

Theorem compile_correct :
  forall cfg loop pl st st',
    mayReturn (compile cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  unfold compile in Hcompile.
  destruct (check_config cfg) as [vcfg|msg] eqn:Hcheck.
  - simpl in Hcompile.
    eapply compile_verified_correct; eauto.
  - simpl in Hcompile.
    apply mayReturn_alarm in Hcompile.
    tauto.
Qed.

Theorem compile_unsupported_no_result :
  forall loop out,
    ~ mayReturn (compile RawUnsupported loop) out.
Proof.
  intros loop out H.
  unfold compile, check_config, res_to_alarm in H.
  simpl in H.
  apply mayReturn_alarm in H.
  tauto.
Qed.

End VerifiedParallelCompilerConfig.
