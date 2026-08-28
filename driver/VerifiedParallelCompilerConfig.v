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

(** * Unified generic compiler endpoint

    This is the final theorem-facing dispatcher.  Sequential routes are lifted
    into the common annotated-loop target language; parallel and vector routes
    call their corresponding [ParallelPolOptCorrect] theorems.
    [compile_verified_correct] handles the verified constructors and
    [compile_correct] discharges raw configuration checking.

    The name differs from [VerifiedCompilerConfig] in one important respect:
    this module always returns [ParallelLoop.t].  Its 31 verified constructors
    are one wrapped sequential family, ten single-parallel routes, ten vector
    routes, and ten multi-parallel routes.  The sequential family is not a
    second compiler proof; [compile_seq_verified] runs the small sequential
    dispatcher and then checked-lifts its result into [ParallelLoop].

    The concrete executable mirror is [SVerifiedParallelCompilerConfig].
    [ExtractedPipelineCorrect.extracted_parallel_compile_correct] is the theorem
    about that hand-instantiated, extraction-facing implementation. *)

(** ** Unified configuration naming

    - [VSeq] wraps one of the 14 sequential configurations.
    - [VParallelCurrent* d] requests one certified parallel schedule coordinate.
    - [VVectorCurrent* d] requests one certified innermost vector coordinate.
    - [VParallelCurrentMany* dims] requests every accepted coordinate in [dims].
    - [Identity], [IdentityTiled], [Affine], [Default], and [Diamond] select the
      preprocessing route; the [ISS] suffix selects its ISS-aware variant.

    The word [Current] is retained for API compatibility.  On this branch the
    numeric payload denotes a canonical padded schedule coordinate, not an
    unproved source-current-coordinate to target-depth identification. *)

Inductive raw_config : Type :=
| RawSeq (cfg: SeqCompiler.raw_config)
| RawParallelCurrentIdentity (d: nat)
| RawParallelCurrentIdentityTiled (d: nat)
| RawParallelCurrentIdentityTiledISS (d: nat)
| RawParallelCurrentAffine (d: nat)
| RawParallelCurrentDefault (d: nat)
| RawParallelCurrentPostTilingAffine (d: nat)
| RawParallelCurrentPostTilingAffineISS (d: nat)
| RawParallelCurrentIdentityISS (d: nat)
| RawParallelCurrentAffineISS (d: nat)
| RawParallelCurrentDefaultISS (d: nat)
| RawVectorCurrentIdentity (d: nat)
| RawVectorCurrentIdentityTiled (d: nat)
| RawVectorCurrentIdentityTiledISS (d: nat)
| RawVectorCurrentAffine (d: nat)
| RawVectorCurrentDefault (d: nat)
| RawVectorCurrentPostTilingAffine (d: nat)
| RawVectorCurrentPostTilingAffineISS (d: nat)
| RawVectorCurrentIdentityISS (d: nat)
| RawVectorCurrentAffineISS (d: nat)
| RawVectorCurrentDefaultISS (d: nat)
| RawParallelCurrentManyIdentity (dims: list nat)
| RawParallelCurrentManyIdentityTiled (dims: list nat)
| RawParallelCurrentManyIdentityTiledISS (dims: list nat)
| RawParallelCurrentManyAffine (dims: list nat)
| RawParallelCurrentManyDefault (dims: list nat)
| RawParallelCurrentManyPostTilingAffine (dims: list nat)
| RawParallelCurrentManyPostTilingAffineISS (dims: list nat)
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
| VParallelCurrentPostTilingAffine (d: nat)
| VParallelCurrentPostTilingAffineISS (d: nat)
| VParallelCurrentIdentityISS (d: nat)
| VParallelCurrentAffineISS (d: nat)
| VParallelCurrentDefaultISS (d: nat)
| VVectorCurrentIdentity (d: nat)
| VVectorCurrentIdentityTiled (d: nat)
| VVectorCurrentIdentityTiledISS (d: nat)
| VVectorCurrentAffine (d: nat)
| VVectorCurrentDefault (d: nat)
| VVectorCurrentPostTilingAffine (d: nat)
| VVectorCurrentPostTilingAffineISS (d: nat)
| VVectorCurrentIdentityISS (d: nat)
| VVectorCurrentAffineISS (d: nat)
| VVectorCurrentDefaultISS (d: nat)
| VParallelCurrentManyIdentity (dims: list nat)
| VParallelCurrentManyIdentityTiled (dims: list nat)
| VParallelCurrentManyIdentityTiledISS (dims: list nat)
| VParallelCurrentManyAffine (dims: list nat)
| VParallelCurrentManyDefault (dims: list nat)
| VParallelCurrentManyPostTilingAffine (dims: list nat)
| VParallelCurrentManyPostTilingAffineISS (dims: list nat)
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
  | RawParallelCurrentPostTilingAffine d => Okk (VParallelCurrentPostTilingAffine d)
  | RawParallelCurrentPostTilingAffineISS d => Okk (VParallelCurrentPostTilingAffineISS d)
  | RawParallelCurrentIdentityISS d => Okk (VParallelCurrentIdentityISS d)
  | RawParallelCurrentAffineISS d => Okk (VParallelCurrentAffineISS d)
  | RawParallelCurrentDefaultISS d => Okk (VParallelCurrentDefaultISS d)
  | RawVectorCurrentIdentity d => Okk (VVectorCurrentIdentity d)
  | RawVectorCurrentIdentityTiled d => Okk (VVectorCurrentIdentityTiled d)
  | RawVectorCurrentIdentityTiledISS d => Okk (VVectorCurrentIdentityTiledISS d)
  | RawVectorCurrentAffine d => Okk (VVectorCurrentAffine d)
  | RawVectorCurrentDefault d => Okk (VVectorCurrentDefault d)
  | RawVectorCurrentPostTilingAffine d => Okk (VVectorCurrentPostTilingAffine d)
  | RawVectorCurrentPostTilingAffineISS d => Okk (VVectorCurrentPostTilingAffineISS d)
  | RawVectorCurrentIdentityISS d => Okk (VVectorCurrentIdentityISS d)
  | RawVectorCurrentAffineISS d => Okk (VVectorCurrentAffineISS d)
  | RawVectorCurrentDefaultISS d => Okk (VVectorCurrentDefaultISS d)
  | RawParallelCurrentManyIdentity dims => Okk (VParallelCurrentManyIdentity dims)
  | RawParallelCurrentManyIdentityTiled dims => Okk (VParallelCurrentManyIdentityTiled dims)
  | RawParallelCurrentManyIdentityTiledISS dims =>
      Okk (VParallelCurrentManyIdentityTiledISS dims)
  | RawParallelCurrentManyAffine dims => Okk (VParallelCurrentManyAffine dims)
  | RawParallelCurrentManyDefault dims => Okk (VParallelCurrentManyDefault dims)
  | RawParallelCurrentManyPostTilingAffine dims => Okk (VParallelCurrentManyPostTilingAffine dims)
  | RawParallelCurrentManyPostTilingAffineISS dims => Okk (VParallelCurrentManyPostTilingAffineISS dims)
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

(** ** Sequential lift into the common annotated target *)

(** [compile_seq_verified] is an adapter, not a third public compiler family.
    It runs [SeqCompiler.compile_verified], tags the resulting ordinary loop as
    sequential [ParallelLoop], and checks affine trace construction.  Its
    correctness lemma is needed only for the [VSeq] branch of the unified
    dispatcher. *)

Definition compile_seq_verified
    (cfg: SeqCompiler.verified_config)
    (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  lift_sequential_compile (SeqCompiler.compile_verified cfg loop).

(** ** Verified unified dispatcher

    A [verified_config] records that the outer configuration was accepted.
    Every checker belonging to the chosen transformation route still executes
    inside the selected [Opt_*] definition. *)

Definition compile_verified
    (cfg: verified_config) (loop: LoopIR.t)
  : imp ParallelLoop.t :=
  match cfg with
  (** One wrapper for all 14 sequential configurations. *)
  | VSeq seq_cfg =>
      compile_seq_verified seq_cfg loop
  (** Ten single-coordinate parallel routes. *)
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
  | VParallelCurrentPostTilingAffine d =>
      ParallelCore.Opt_parallel_current_post_tiling_affine loop d
  | VParallelCurrentPostTilingAffineISS d =>
      ParallelCore.Opt_parallel_current_post_tiling_affine_with_iss loop d
  | VParallelCurrentIdentityISS d =>
      ParallelCore.Opt_parallel_current_identity_with_iss loop d
  | VParallelCurrentAffineISS d =>
      ParallelCore.Opt_parallel_current_affine_with_iss loop d
  | VParallelCurrentDefaultISS d =>
      ParallelCore.Opt_parallel_current_with_iss loop d
  (** Ten single-coordinate vector routes. *)
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
  | VVectorCurrentPostTilingAffine d =>
      ParallelCore.Opt_vector_current_post_tiling_affine loop d
  | VVectorCurrentPostTilingAffineISS d =>
      ParallelCore.Opt_vector_current_post_tiling_affine_with_iss loop d
  | VVectorCurrentIdentityISS d =>
      ParallelCore.Opt_vector_current_identity_with_iss loop d
  | VVectorCurrentAffineISS d =>
      ParallelCore.Opt_vector_current_affine_with_iss loop d
  | VVectorCurrentDefaultISS d =>
      ParallelCore.Opt_vector_current_with_iss loop d
  (** Ten multi-coordinate parallel routes. *)
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
  | VParallelCurrentManyPostTilingAffine dims =>
      ParallelCore.Opt_parallel_current_many_post_tiling_affine loop dims
  | VParallelCurrentManyPostTilingAffineISS dims =>
      ParallelCore.Opt_parallel_current_many_post_tiling_affine_with_iss loop dims
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

(** Checked unroll-jam is performed on the ordinary Loop result, after the
    selected polyhedral producer.  The transformed loop is then re-extracted
    and annotated through the identity parallel route.  Revalidation avoids
    transporting a pre-unroll parallel certificate across the changed loop
    structure. *)
Definition compile_parallel_after_unrolljam
    (seq_cfg : SeqCompiler.raw_config) (const_first : bool)
    (select : LoopIR.t -> SeqCompiler.Postpass.JamLower.unrolljam_plan)
    (factor d : nat) (loop : LoopIR.t) : imp ParallelLoop.t :=
  BIND optimized <-
    SeqCompiler.compile_with_unrolljam
      seq_cfg const_first select factor loop -;
  compile (RawParallelCurrentIdentity d) optimized.

Definition compile_parallel_many_after_unrolljam
    (seq_cfg : SeqCompiler.raw_config) (const_first : bool)
    (select : LoopIR.t -> SeqCompiler.Postpass.JamLower.unrolljam_plan)
    (factor : nat) (dims : list nat) (loop : LoopIR.t)
    : imp ParallelLoop.t :=
  BIND optimized <-
    SeqCompiler.compile_with_unrolljam
      seq_cfg const_first select factor loop -;
  compile (RawParallelCurrentManyIdentity dims) optimized.

(** ** Correctness support for sequential lifting *)

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
      (ParallelLoop.semantics_refines_erased_global
         (ParallelCodegenCore.tag_loop loop) st st' Htrace_safe
         (ParallelCodegenCore.tag_loop_ordered loop) Hsem)
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
  exact ParallelCorrect.Opt_parallel_current_identity_tiled_correct.
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

(** ** Generic unified correctness endpoints

    [compile_verified_correct] is the 31-constructor coverage theorem after
    configuration checking.  [compile_correct] is the paper-facing generic
    endpoint for a raw configuration.  For the executable extracted compiler,
    use [ExtractedPipelineCorrect.extracted_parallel_compile_correct] instead.

    The long proof below adds no new transformation semantics.  Its four blocks
    establish exhaustive routing: [VSeq], ten [VParallelCurrent] variants, ten
    [VVectorCurrent] variants, and ten [VParallelCurrentMany] variants.  Read
    one representative theorem in [ParallelPolOptCorrect] from the desired
    block, then skim the remaining dispatch bullets. *)

Theorem compile_verified_correct :
  forall cfg loop pl st st',
    mayReturn (compile_verified cfg loop) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros cfg loop pl st st' Hcompile Hsem.
  destruct cfg; simpl in Hcompile.
  (** [VSeq]: reuse the complete 14-route sequential dispatcher. *)
  - eapply compile_seq_verified_correct; eauto.
  (** Ten [VParallelCurrent] constructors. *)
  - eapply ParallelCorrect.Opt_parallel_current_identity_correct; eauto.
  - eapply opt_parallel_current_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_tiled_with_iss_correct;
      eauto.
  - eapply ParallelCorrect.Opt_parallel_current_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_post_tiling_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_post_tiling_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_with_iss_correct; eauto.
  (** Ten [VVectorCurrent] constructors. *)
  - eapply ParallelCorrect.Opt_vector_current_identity_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_tiled_with_iss_correct;
      eauto.
  - eapply ParallelCorrect.Opt_vector_current_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_post_tiling_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_post_tiling_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_vector_current_with_iss_correct; eauto.
  (** Ten [VParallelCurrentMany] constructors. *)
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_tiled_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_tiled_with_iss_correct;
      eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_post_tiling_affine_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_post_tiling_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_identity_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_affine_with_iss_correct; eauto.
  - eapply ParallelCorrect.Opt_parallel_current_many_with_iss_correct; eauto.
Qed.

(** Raw-config wrapper around the 31-constructor theorem.  No parallel or
    transformation argument is repeated here: the accepted branch calls
    [compile_verified_correct], and the rejected branch cannot return a target. *)
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

Theorem compile_parallel_after_unrolljam_correct :
  forall seq_cfg const_first select factor d loop pl st st',
    mayReturn
      (compile_parallel_after_unrolljam
         seq_cfg const_first select factor d loop)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros seq_cfg const_first select factor d loop pl st st' Hcompile Hsem.
  unfold compile_parallel_after_unrolljam in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hunrolljam Hparallel]].
  destruct
    (compile_correct
       (RawParallelCurrentIdentity d) optimized pl st st'
       Hparallel Hsem)
    as [st_mid [Hmid Heq_mid]].
  destruct
    (SeqCompiler.compile_with_unrolljam_correct
       seq_cfg const_first select factor loop st st_mid optimized
       Hunrolljam Hmid)
    as [st_src [Hsrc Heq_src]].
  exists st_src. split; [exact Hsrc|].
  eapply State.eq_trans; eauto.
Qed.

Theorem compile_parallel_many_after_unrolljam_correct :
  forall seq_cfg const_first select factor dims loop pl st st',
    mayReturn
      (compile_parallel_many_after_unrolljam
         seq_cfg const_first select factor dims loop)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros seq_cfg const_first select factor dims loop pl st st' Hcompile Hsem.
  unfold compile_parallel_many_after_unrolljam in Hcompile.
  apply mayReturn_bind in Hcompile.
  destruct Hcompile as [optimized [Hunrolljam Hparallel]].
  destruct
    (compile_correct
       (RawParallelCurrentManyIdentity dims) optimized pl st st'
       Hparallel Hsem)
    as [st_mid [Hmid Heq_mid]].
  destruct
    (SeqCompiler.compile_with_unrolljam_correct
       seq_cfg const_first select factor loop st st_mid optimized
       Hunrolljam Hmid)
    as [st_src [Hsrc Heq_src]].
  exists st_src. split; [exact Hsrc|].
  eapply State.eq_trans; eauto.
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
