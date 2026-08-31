Require Import List.
Require Import Lia.
Require Import ZArith.

Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import LoopJamLower.
Require Import PolIRs.

(** Contextual refinement lemmas for the syntax-directed loop-jam lowering.

    This module deliberately separates two obligations:

    - [checked_pair_refines] is the local bridge from an accepted polyhedral
      pair certificate to refinement of the corresponding Loop statements;
    - the theorems below lift that bridge through loops, guards, sequences,
      and the recursive search performed by [checked_jam_stmt_fuel].

    Keeping the bridge explicit prevents the recursive proof from silently
    assuming that the polyhedral certificate already has the trace-level form
    consumed by [LoopJamNative]. *)
Module LoopJamContext (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module Instr := PolIRs.Instr.
Module State := Instr.State.
Module Lower := LoopJamLower PolIRs.

Definition stmt_refines (after before : Loop.stmt) : Prop :=
  forall env mem1 mem2,
    Instr.NonAlias mem1 ->
    Loop.loop_semantics after env mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics before env mem1 mem2' /\
      State.eq mem2 mem2'.

Scheme stmt_mut := Induction for Loop.stmt Sort Prop
with stmt_list_mut := Induction for Loop.stmt_list Sort Prop.

Combined Scheme stmt_stmt_list_mutind from stmt_mut, stmt_list_mut.

Lemma loop_semantics_preserves_nonalias_mutual :
  (forall st,
      forall env mem1 mem2,
        Loop.loop_semantics st env mem1 mem2 ->
        Instr.NonAlias mem1 ->
        Instr.NonAlias mem2) /\
  (forall sts,
      forall env mem1 mem2,
        Loop.loop_semantics (Loop.Seq sts) env mem1 mem2 ->
        Instr.NonAlias mem1 ->
        Instr.NonAlias mem2).
Proof.
  apply stmt_stmt_list_mutind.
  - intros lb ub body IHbody env mem1 mem2 Hsem Hna.
    inversion Hsem as [| | | | |env' lb' ub' body' mem1' mem2' Hiter];
      subst; clear Hsem.
    induction Hiter.
    + exact Hna.
    + apply IHHiter.
      eapply IHbody; eauto.
  - intros i es env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    eapply Instr.sema_prsv_nonalias; eauto.
  - intros sts IHsts env mem1 mem2 Hsem Hna.
    eapply IHsts; eauto.
  - intros tst body IHbody env mem1 mem2 Hsem Hna.
    inversion Hsem; subst; eauto.
  - intros env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    exact Hna.
  - intros st IHst sts IHsts env mem1 mem3 Hsem Hna.
    inversion Hsem as
      [| |env' st' sts' mem1' mem2 mem3' Hhead Htail| | |];
      subst; clear Hsem.
    eapply IHsts; eauto.
Qed.

Lemma loop_semantics_preserves_nonalias :
  forall st env mem1 mem2,
    Loop.loop_semantics st env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.
Proof.
  exact (proj1 loop_semantics_preserves_nonalias_mutual).
Qed.

Lemma iter_semantics_transport_initial :
  forall (A : Type) (P : A -> State.t -> State.t -> Prop) xs mem1 mem2,
    (forall x st1 st2 st1',
        State.eq st1 st1' ->
        P x st1 st2 ->
        exists st2', P x st1' st2' /\ State.eq st2 st2') ->
    Instr.IterSem.iter_semantics P xs mem1 mem2 ->
    forall mem1',
      State.eq mem1 mem1' ->
      exists mem2',
        Instr.IterSem.iter_semantics P xs mem1' mem2' /\
        State.eq mem2 mem2'.
Proof.
  intros A P xs mem1 mem2 Hstep Hiter.
  induction Hiter; intros mem1' Heq.
  - exists mem1'.
    split; [constructor | exact Heq].
  - destruct (Hstep _ _ _ _ Heq H) as [mem_mid' [Hhead' Heq_mid]].
    destruct (IHHiter _ Heq_mid) as [mem2' [Htail' Heq_out]].
    exists mem2'.
    split; [econstructor; eauto | exact Heq_out].
Qed.

(** Executions can be restarted from an observationally equal state.  The
    final state need only be observationally equal: empty sequences and false
    guards expose why requiring the same concrete final state would be too
    strong. *)
Lemma loop_semantics_transport_initial_mutual :
  (forall st,
      forall env mem1 mem2 mem1',
        State.eq mem1 mem1' ->
        Loop.loop_semantics st env mem1 mem2 ->
        exists mem2',
          Loop.loop_semantics st env mem1' mem2' /\
          State.eq mem2 mem2') /\
  (forall sts,
      forall env mem1 mem2 mem1',
        State.eq mem1 mem1' ->
        Loop.loop_semantics (Loop.Seq sts) env mem1 mem2 ->
        exists mem2',
          Loop.loop_semantics (Loop.Seq sts) env mem1' mem2' /\
          State.eq mem2 mem2').
Proof.
  apply stmt_stmt_list_mutind.
  - intros lb ub body IHbody env mem1 mem2 mem1' Heq Hsem.
    inversion Hsem as [| | | | |env' lb' ub' body' mem1x mem2x Hiter];
      subst; clear Hsem.
    destruct
      (iter_semantics_transport_initial
         Z
         (fun x => Loop.loop_semantics body (x :: env))
         _ _ _ (fun x => IHbody (x :: env)) Hiter _ Heq)
      as [mem2' [Hiter' Heq_out]].
    exists mem2'.
    split; [econstructor; eauto | exact Heq_out].
  - intros i es env mem1 mem2 mem1' Heq Hsem.
    inversion Hsem as [i' es' env' mem1x mem2x wcs rcs Hinstr| | | | |];
      subst; clear Hsem.
    exists mem2.
    split.
    + econstructor.
      eapply Instr.instr_semantics_stable_under_state_eq;
        [exact Heq | apply State.eq_refl | exact Hinstr].
    + apply State.eq_refl.
  - intros sts IHsts env mem1 mem2 mem1' Heq Hsem.
    eapply IHsts; eauto.
  - intros tst body IHbody env mem1 mem2 mem1' Heq Hsem.
    inversion Hsem as
      [| | |env' tst' body' mem1x mem2x Hbody Htest
       |env' tst' body' mem Htest|]; subst; clear Hsem.
    + destruct (IHbody _ _ _ _ Heq Hbody) as [mem2' [Hbody' Heq_out]].
      exists mem2'.
      split; [eapply Loop.LGuardTrue; eauto | exact Heq_out].
    + exists mem1'.
      split; [eapply Loop.LGuardFalse; eauto | exact Heq].
  - intros env mem1 mem2 mem1' Heq Hsem.
    inversion Hsem; subst.
    exists mem1'.
    split; [constructor | exact Heq].
  - intros st IHst sts IHsts env mem1 mem3 mem1' Heq Hsem.
    inversion Hsem as
      [| |env' st' sts' mem1x mem2 mem3x Hhead Htail| | |];
      subst; clear Hsem.
    destruct (IHst _ _ _ _ Heq Hhead) as [mem2' [Hhead' Heq_mid]].
    destruct (IHsts _ _ _ _ Heq_mid Htail) as [mem3' [Htail' Heq_out]].
    exists mem3'.
    split; [econstructor; eauto | exact Heq_out].
Qed.

Lemma loop_semantics_transport_initial :
  forall st env mem1 mem2 mem1',
    State.eq mem1 mem1' ->
    Loop.loop_semantics st env mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics st env mem1' mem2' /\
      State.eq mem2 mem2'.
Proof.
  exact (proj1 loop_semantics_transport_initial_mutual).
Qed.

Lemma stmt_refines_refl : forall st, stmt_refines st st.
Proof.
  intros st env mem1 mem2 _ Hsem.
  exists mem2.
  split; [exact Hsem | apply State.eq_refl].
Qed.

Lemma stmt_refines_trans :
  forall st3 st2 st1,
    stmt_refines st3 st2 ->
    stmt_refines st2 st1 ->
    stmt_refines st3 st1.
Proof.
  intros st3 st2 st1 H32 H21 env mem1 mem3 Hna Hsem3.
  destruct (H32 _ _ _ Hna Hsem3) as [mem2 [Hsem2 Heq32]].
  destruct (H21 _ _ _ Hna Hsem2) as [mem1' [Hsem1 Heq21]].
  exists mem1'.
  split; [exact Hsem1 | eapply State.eq_trans; eauto].
Qed.

Lemma stmt_refines_guard :
  forall after before tst,
    stmt_refines after before ->
    stmt_refines (Loop.Guard tst after) (Loop.Guard tst before).
Proof.
  intros after before tst Href env mem1 mem2 Hna Hsem.
  inversion Hsem as
    [| | |env' tst' after' mem1' mem2' Hafter Htest
     |env' tst' after' mem Htest|]; subst; clear Hsem.
  - destruct (Href _ _ _ Hna Hafter) as [mem2' [Hbefore Heq]].
    exists mem2'.
    split; [eapply Loop.LGuardTrue; eauto | exact Heq].
  - eexists.
    split; [eapply Loop.LGuardFalse; eauto | apply State.eq_refl].
Qed.

Lemma stmt_refines_seq_cons :
  forall after_hd before_hd after_tl before_tl,
    stmt_refines after_hd before_hd ->
    stmt_refines (Loop.Seq after_tl) (Loop.Seq before_tl) ->
    stmt_refines
      (Loop.Seq (Loop.SCons after_hd after_tl))
      (Loop.Seq (Loop.SCons before_hd before_tl)).
Proof.
  intros after_hd before_hd after_tl before_tl Hhd Htl
    env mem1 mem3 Hna Hsem.
  inversion Hsem as
    [| |env' st' sts' mem1' mem2 mem3' Hhead Htail| | |];
    subst; clear Hsem.
  destruct (Hhd _ _ _ Hna Hhead) as [mem2' [Hhead' Heq_mid]].
  pose proof (loop_semantics_preserves_nonalias _ _ _ _ Hhead' Hna) as Hna_mid.
  destruct (loop_semantics_transport_initial _ _ _ _ _ Heq_mid Htail)
    as [mem3x [Htailx Heq_3x]].
  destruct (Htl _ _ _ Hna_mid Htailx) as [mem3y [Htail' Heq_xy]].
  exists mem3y.
  split.
  - econstructor; eauto.
  - eapply State.eq_trans; eauto.
Qed.

Lemma stmt_refines_seq_two :
  forall a1 b1 a2 b2,
    stmt_refines a1 b1 ->
    stmt_refines a2 b2 ->
    stmt_refines (Lower.seq2 a1 a2) (Lower.seq2 b1 b2).
Proof.
  intros a1 b1 a2 b2 H1 H2.
  unfold Lower.seq2, Lower.Native.seq2.
  eapply stmt_refines_seq_cons; [exact H1|].
  eapply stmt_refines_seq_cons; [exact H2|].
  apply stmt_refines_refl.
Qed.

Lemma iter_semantics_refines_nonalias :
  forall (A : Type)
      (after before : A -> State.t -> State.t -> Prop) xs mem1 mem2,
    (forall x st1 st2 st1',
        State.eq st1 st1' ->
        after x st1 st2 ->
        exists st2', after x st1' st2' /\ State.eq st2 st2') ->
    (forall x st1 st2,
        before x st1 st2 ->
        Instr.NonAlias st1 ->
        Instr.NonAlias st2) ->
    (forall x st1 st2,
        Instr.NonAlias st1 ->
        after x st1 st2 ->
        exists st2', before x st1 st2' /\ State.eq st2 st2') ->
    Instr.IterSem.iter_semantics after xs mem1 mem2 ->
    forall mem1',
      State.eq mem1 mem1' ->
      Instr.NonAlias mem1' ->
      exists mem2',
        Instr.IterSem.iter_semantics before xs mem1' mem2' /\
        State.eq mem2 mem2'.
Proof.
  intros A after before xs mem1 mem2
    Hafter_transport Hbefore_na Hstep Hiter.
  induction Hiter; intros mem1' Heq Hna.
  - exists mem1'.
    split; [constructor | exact Heq].
  - destruct (Hafter_transport _ _ _ _ Heq H) as
      [after_mid [Hafter_head Heq_after]].
    destruct (Hstep _ _ _ Hna Hafter_head) as
      [before_mid [Hbefore_head Heq_before]].
    pose proof (Hbefore_na _ _ _ Hbefore_head Hna) as Hna_mid.
    assert (Heq_mid : State.eq st2 before_mid).
    {
      eapply State.eq_trans; eauto.
    }
    destruct (IHHiter _ Heq_mid Hna_mid) as
      [mem2' [Hbefore_tail Heq_out]].
    exists mem2'.
    split; [econstructor; eauto | exact Heq_out].
Qed.

Lemma stmt_refines_loop :
  forall after before lb ub,
    stmt_refines after before ->
    stmt_refines (Loop.Loop lb ub after) (Loop.Loop lb ub before).
Proof.
  intros after before lb ub Hbody env mem1 mem2 Hna Hsem.
  inversion Hsem as [| | | | |env' lb' ub' after' mem1' mem2' Hiter];
    subst; clear Hsem.
  destruct
    (iter_semantics_refines_nonalias
       Z
       (fun x => Loop.loop_semantics after (x :: env))
       (fun x => Loop.loop_semantics before (x :: env))
       _ _ _
       (fun x => loop_semantics_transport_initial after (x :: env))
       (fun x => loop_semantics_preserves_nonalias before (x :: env))
       (fun x => Hbody (x :: env))
       Hiter _ (State.eq_refl _) Hna)
    as [mem2' [Hiter' Heq_out]].
  exists mem2'.
  split; [econstructor; eauto | exact Heq_out].
Qed.

(** Refinement at a syntactic loop depth.  The local affine certificate treats
    the [varctxt] coordinates as parameters and the [depth] enclosing iterator
    coordinates as the remaining environment, so this length invariant is part
    of the certificate-to-trace interface. *)
Definition stmt_refines_at
    (varctxt : list Instr.ident) (depth : nat)
    (after before : Loop.stmt) : Prop :=
  forall env,
    Datatypes.length env = (Datatypes.length varctxt + depth)%nat ->
    forall mem1 mem2,
      Instr.NonAlias mem1 ->
      Loop.loop_semantics after env mem1 mem2 ->
      exists mem2',
        Loop.loop_semantics before env mem1 mem2' /\
        State.eq mem2 mem2'.

Lemma stmt_refines_to_at :
  forall varctxt depth after before,
    stmt_refines after before ->
    stmt_refines_at varctxt depth after before.
Proof.
  intros varctxt depth after before Href env _.
  eapply Href.
Qed.

Lemma stmt_refines_at_refl :
  forall varctxt depth st, stmt_refines_at varctxt depth st st.
Proof.
  intros varctxt depth st.
  apply stmt_refines_to_at.
  apply stmt_refines_refl.
Qed.

Lemma stmt_refines_at_trans :
  forall varctxt depth st3 st2 st1,
    stmt_refines_at varctxt depth st3 st2 ->
    stmt_refines_at varctxt depth st2 st1 ->
    stmt_refines_at varctxt depth st3 st1.
Proof.
  intros varctxt depth st3 st2 st1 H32 H21 env Hlen
    mem1 mem3 Hna Hsem3.
  destruct (H32 _ Hlen _ _ Hna Hsem3) as [mem2 [Hsem2 Heq32]].
  destruct (H21 _ Hlen _ _ Hna Hsem2) as [mem1' [Hsem1 Heq21]].
  exists mem1'.
  split; [exact Hsem1 | eapply State.eq_trans; eauto].
Qed.

Lemma stmt_refines_at_guard :
  forall varctxt depth after before tst,
    stmt_refines_at varctxt depth after before ->
    stmt_refines_at varctxt depth
      (Loop.Guard tst after) (Loop.Guard tst before).
Proof.
  intros varctxt depth after before tst Href env Hlen
    mem1 mem2 Hna Hsem.
  inversion Hsem as
    [| | |env' tst' after' mem1' mem2' Hafter Htest
     |env' tst' after' mem Htest|]; subst; clear Hsem.
  - destruct (Href _ Hlen _ _ Hna Hafter) as [mem2' [Hbefore Heq]].
    exists mem2'.
    split; [eapply Loop.LGuardTrue; eauto | exact Heq].
  - eexists.
    split; [eapply Loop.LGuardFalse; eauto | apply State.eq_refl].
Qed.

Lemma stmt_refines_at_seq_cons :
  forall varctxt depth after_hd before_hd after_tl before_tl,
    stmt_refines_at varctxt depth after_hd before_hd ->
    stmt_refines_at varctxt depth
      (Loop.Seq after_tl) (Loop.Seq before_tl) ->
    stmt_refines_at varctxt depth
      (Loop.Seq (Loop.SCons after_hd after_tl))
      (Loop.Seq (Loop.SCons before_hd before_tl)).
Proof.
  intros varctxt depth after_hd before_hd after_tl before_tl Hhd Htl
    env Hlen mem1 mem3 Hna Hsem.
  inversion Hsem as
    [| |env' st' sts' mem1' mem2 mem3' Hhead Htail| | |];
    subst; clear Hsem.
  destruct (Hhd _ Hlen _ _ Hna Hhead) as [mem2' [Hhead' Heq_mid]].
  pose proof (loop_semantics_preserves_nonalias _ _ _ _ Hhead' Hna) as Hna_mid.
  destruct (loop_semantics_transport_initial _ _ _ _ _ Heq_mid Htail)
    as [mem3x [Htailx Heq_3x]].
  destruct (Htl _ Hlen _ _ Hna_mid Htailx) as [mem3y [Htail' Heq_xy]].
  exists mem3y.
  split.
  - econstructor; eauto.
  - eapply State.eq_trans; eauto.
Qed.

Lemma stmt_refines_at_loop :
  forall varctxt depth after before lb ub,
    stmt_refines_at varctxt (S depth) after before ->
    stmt_refines_at varctxt depth
      (Loop.Loop lb ub after) (Loop.Loop lb ub before).
Proof.
  intros varctxt depth after before lb ub Hbody env Hlen
    mem1 mem2 Hna Hsem.
  inversion Hsem as [| | | | |env' lb' ub' after' mem1' mem2' Hiter];
    subst; clear Hsem.
  destruct
    (iter_semantics_refines_nonalias
       Z
       (fun x => Loop.loop_semantics after (x :: env))
       (fun x => Loop.loop_semantics before (x :: env))
       _ _ _
       (fun x => loop_semantics_transport_initial after (x :: env))
       (fun x => loop_semantics_preserves_nonalias before (x :: env))
       (fun x => Hbody (x :: env) (ltac:(simpl; lia)))
       Hiter _ (State.eq_refl _) Hna)
    as [mem2' [Hiter' Heq_out]].
  exists mem2'.
  split; [econstructor; eauto | exact Heq_out].
Qed.

Definition checked_pair_refines
    (varctxt : list Instr.ident)
    (vars : list (Instr.ident * PolIRs.Ty.t)) : Prop :=
  forall depth st1 st2 fused,
    mayReturn
      (Lower.checked_try_jam_pair varctxt vars depth st1 st2)
      (Some fused) ->
    stmt_refines_at varctxt depth fused (Lower.seq2 st1 st2).

Lemma seq_nested_two_refines_flat :
  forall st1 st2 rest,
    stmt_refines
      (Loop.Seq (Loop.SCons (Lower.seq2 st1 st2) rest))
      (Loop.Seq (Loop.SCons st1 (Loop.SCons st2 rest))).
Proof.
  intros st1 st2 rest env mem1 mem3 _ Hsem.
  inversion Hsem as
    [| |env' nested rest' mem1' mem2 mem3' Hnested Hrest| | |];
    subst; clear Hsem.
  apply Lower.Unroll.seq_two_semantics in Hnested.
  destruct Hnested as [mem_mid [Hst1 Hst2]].
  exists mem3.
  split.
  - econstructor; [exact Hst1|].
    econstructor; eauto.
  - apply State.eq_refl.
Qed.

Lemma checked_jam_stmt_fuel_refines_mutual :
  forall fuel varctxt vars,
    checked_pair_refines varctxt vars ->
    (forall depth st result,
        mayReturn
          (Lower.checked_jam_stmt_fuel
             varctxt vars depth fuel st)
          result ->
        stmt_refines_at varctxt depth (fst result) st) /\
    (forall depth sts result,
        mayReturn
          (Lower.checked_jam_stmt_list_fuel
             varctxt vars depth fuel sts)
          result ->
        stmt_refines_at varctxt depth
          (Loop.Seq (fst result)) (Loop.Seq sts)).
Proof.
  induction fuel as [|fuel IH]; intros varctxt vars Hpair.
  - split.
    + intros depth st result Hret.
      simpl in Hret.
      apply mayReturn_pure in Hret.
      subst result.
      apply stmt_refines_at_refl.
    + intros depth sts result Hret.
      simpl in Hret.
      apply mayReturn_pure in Hret.
      subst result.
      apply stmt_refines_at_refl.
  - destruct (IH varctxt vars Hpair) as [IHstmt IHlist].
    split.
    + intros depth st result Hret.
      destruct st as [lb ub body|i es|sts|tst body]; simpl in Hret.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body_res [Hbody Hret]].
        destruct body_res as [body' changed].
        pose proof (IHstmt _ _ _ Hbody) as Hbody_refines.
        simpl in Hbody_refines.
        apply mayReturn_pure in Hret.
        subst result.
        apply stmt_refines_at_loop.
        exact Hbody_refines.
      * apply mayReturn_pure in Hret.
        subst result.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [sts_res [Hsts Hret]].
        destruct sts_res as [sts' changed].
        pose proof (IHlist _ _ _ Hsts) as Hsts_refines.
        simpl in Hsts_refines.
        apply mayReturn_pure in Hret.
        subst result.
        exact Hsts_refines.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body_res [Hbody Hret]].
        destruct body_res as [body' changed].
        pose proof (IHstmt _ _ _ Hbody) as Hbody_refines.
        simpl in Hbody_refines.
        apply mayReturn_pure in Hret.
        subst result.
        apply stmt_refines_at_guard.
        exact Hbody_refines.
    + intros depth sts result Hret.
      destruct sts as [|st1 sts']; simpl in Hret.
      * apply mayReturn_pure in Hret.
        subst result.
        apply stmt_refines_at_refl.
      * destruct sts' as [|st2 rest].
        -- apply mayReturn_bind in Hret.
           destruct Hret as [st_res [Hst Hret]].
           destruct st_res as [st' changed].
           pose proof (IHstmt _ _ _ Hst) as Hst_refines.
           simpl in Hst_refines.
           apply mayReturn_pure in Hret.
           subst result.
           eapply stmt_refines_at_seq_cons.
           ++ exact Hst_refines.
           ++ apply stmt_refines_at_refl.
        -- apply mayReturn_bind in Hret.
           destruct Hret as [st1_res [Hst1 Hret]].
           destruct st1_res as [st1' changed1].
           pose proof (IHstmt _ _ _ Hst1) as Hst1_refines.
           simpl in Hst1_refines.
           apply mayReturn_bind in Hret.
           destruct Hret as [st2_res [Hst2 Hret]].
           destruct st2_res as [st2' changed2].
           pose proof (IHstmt _ _ _ Hst2) as Hst2_refines.
           simpl in Hst2_refines.
           apply mayReturn_bind in Hret.
           destruct Hret as [fused_opt [Hfused Hret]].
           destruct fused_opt as [fused|].
           ++ apply mayReturn_bind in Hret.
              destruct Hret as [rest_res [Hrest Hret]].
              destruct rest_res as [out changed_rest].
              pose proof (IHlist _ _ _ Hrest) as Hrest_refines.
              simpl in Hrest_refines.
              apply mayReturn_pure in Hret.
              subst result.
              eapply stmt_refines_at_trans.
              ** exact Hrest_refines.
              ** eapply stmt_refines_at_trans.
                 --- eapply stmt_refines_at_seq_cons.
                     +++ eapply Hpair; eauto.
                     +++ apply stmt_refines_at_refl.
                 --- eapply stmt_refines_at_trans.
                     +++ eapply stmt_refines_to_at.
                         apply seq_nested_two_refines_flat.
                     +++ eapply stmt_refines_at_seq_cons.
                         *** exact Hst1_refines.
                         *** eapply stmt_refines_at_seq_cons.
                             ---- exact Hst2_refines.
                             ---- apply stmt_refines_at_refl.
           ++ apply mayReturn_bind in Hret.
              destruct Hret as [tail_res [Htail Hret]].
              destruct tail_res as [tail' changed_tail].
              pose proof (IHlist _ _ _ Htail) as Htail_refines.
              simpl in Htail_refines.
              apply mayReturn_pure in Hret.
              subst result.
              eapply stmt_refines_at_trans.
              ** eapply stmt_refines_at_seq_cons.
                 --- exact Hst1_refines.
                 --- exact Htail_refines.
              ** eapply stmt_refines_at_seq_cons.
                 --- apply stmt_refines_at_refl.
                 --- eapply stmt_refines_at_seq_cons.
                     +++ exact Hst2_refines.
                     +++ apply stmt_refines_at_refl.
Qed.

Theorem checked_jam_stmt_fuel_refines :
  forall varctxt vars depth fuel st result,
    checked_pair_refines varctxt vars ->
    mayReturn
      (Lower.checked_jam_stmt_fuel varctxt vars depth fuel st)
      result ->
    stmt_refines_at varctxt depth (fst result) st.
Proof.
  intros varctxt vars depth fuel st result Hpair Hret.
  eapply (proj1 (checked_jam_stmt_fuel_refines_mutual
                   fuel varctxt vars Hpair)); eauto.
Qed.

Theorem checked_jam_stmt_refines :
  forall varctxt vars depth st result,
    checked_pair_refines varctxt vars ->
    mayReturn (Lower.checked_jam_stmt varctxt vars depth st) result ->
    stmt_refines_at varctxt depth (fst result) st.
Proof.
  intros varctxt vars depth st result Hpair Hret.
  unfold Lower.checked_jam_stmt in Hret.
  eapply checked_jam_stmt_fuel_refines; eauto.
Qed.

Lemma block_unroll_stmt_refines_loop :
  forall factor lb ub body,
    stmt_refines
      (Lower.Unroll.block_unroll_stmt factor lb ub body)
      (Loop.Loop lb ub body).
Proof.
  intros factor lb ub body.
  destruct factor as [|factor].
  - simpl.
    apply stmt_refines_refl.
  - intros env mem1 mem2 _ Hsem.
    exists mem2.
    split.
    + apply Lower.Unroll.block_unroll_stmt_semantics in Hsem; [exact Hsem|lia].
    + apply State.eq_refl.
Qed.

Lemma checked_unrolljam_with_plan_fuel_refines_mutual :
  forall fuel plan varctxt vars factor,
    checked_pair_refines varctxt vars ->
    (forall depth path st out,
        mayReturn
          (Lower.checked_unrolljam_stmt_with_plan_fuel
             plan varctxt vars depth path fuel factor st)
          out ->
        stmt_refines_at varctxt depth out st) /\
    (forall depth path index sts out,
        mayReturn
          (Lower.checked_unrolljam_stmt_list_with_plan_fuel
             plan varctxt vars depth path index fuel factor sts)
          out ->
        stmt_refines_at varctxt depth (Loop.Seq out) (Loop.Seq sts)) /\
    (forall depth path st out,
        mayReturn
          (Lower.checked_descend_unrolljam_stmt_with_plan_fuel
             plan varctxt vars depth path fuel factor st)
          out ->
        stmt_refines_at varctxt depth out st) /\
    (forall depth path index sts out,
        mayReturn
          (Lower.checked_descend_unrolljam_stmt_list_with_plan_fuel
             plan varctxt vars depth path index fuel factor sts)
          out ->
        stmt_refines_at varctxt depth (Loop.Seq out) (Loop.Seq sts)).
Proof.
  induction fuel as [|fuel IH]; intros plan varctxt vars factor Hpair.
  - repeat split; intros; simpl in *;
      apply mayReturn_pure in H; subst; apply stmt_refines_at_refl.
  - destruct (IH plan varctxt vars factor Hpair) as
      [IHstmt [IHlist [IHdesc IHdesclist]]].
    repeat split.
    + intros depth path st out Hret.
      destruct st as [lb ub body|i es|sts|tst body]; simpl in Hret.
      * destruct (Lower.unrolljam_plan_selects_loopb depth path plan) eqn:Hselect.
        -- apply mayReturn_bind in Hret.
           destruct Hret as [jam_res [Hjam Hret]].
           destruct jam_res as [jammed changed].
           pose proof
             (checked_jam_stmt_refines
                varctxt vars depth
                (Lower.Unroll.block_unroll_stmt factor lb ub body)
                (jammed, changed) Hpair Hjam) as Hjam_refines.
           simpl in Hjam_refines.
           pose proof (IHdesc _ _ _ _ Hret) as Hdesc_refines.
           eapply stmt_refines_at_trans; [exact Hdesc_refines|].
           eapply stmt_refines_at_trans.
           ++ exact Hjam_refines.
           ++ eapply stmt_refines_to_at.
              apply block_unroll_stmt_refines_loop.
        -- apply mayReturn_bind in Hret.
           destruct Hret as [body' [Hbody Hret]].
           pose proof (IHstmt _ _ _ _ Hbody) as Hbody_refines.
           apply mayReturn_pure in Hret.
           subst out.
           apply stmt_refines_at_loop.
           exact Hbody_refines.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [sts' [Hsts Hret]].
        pose proof (IHlist _ _ _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        exact Hsts_refines.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body' [Hbody Hret]].
        pose proof (IHstmt _ _ _ _ Hbody) as Hbody_refines.
        apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_guard.
        exact Hbody_refines.
    + intros depth path index sts out Hret.
      destruct sts as [|st sts']; simpl in Hret.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [st' [Hst Hret]].
        pose proof (IHstmt _ _ _ _ Hst) as Hst_refines.
        apply mayReturn_bind in Hret.
        destruct Hret as [sts'' [Hsts Hret]].
        pose proof (IHlist _ _ _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        eapply stmt_refines_at_seq_cons; eauto.
    + intros depth path st out Hret.
      destruct st as [lb ub body|i es|sts|tst body]; simpl in Hret.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body' [Hbody Hret]].
        pose proof (IHstmt _ _ _ _ Hbody) as Hbody_refines.
        apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_loop.
        exact Hbody_refines.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [sts' [Hsts Hret]].
        pose proof (IHdesclist _ _ _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        exact Hsts_refines.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body' [Hbody Hret]].
        pose proof (IHdesc _ _ _ _ Hbody) as Hbody_refines.
        apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_guard.
        exact Hbody_refines.
    + intros depth path index sts out Hret.
      destruct sts as [|st sts']; simpl in Hret.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [st' [Hst Hret]].
        pose proof (IHdesc _ _ _ _ Hst) as Hst_refines.
        apply mayReturn_bind in Hret.
        destruct Hret as [sts'' [Hsts Hret]].
        pose proof (IHdesclist _ _ _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        eapply stmt_refines_at_seq_cons; eauto.
Qed.

Theorem checked_unrolljam_stmt_with_plan_fuel_refines :
  forall plan varctxt vars depth path fuel factor st out,
    checked_pair_refines varctxt vars ->
    mayReturn
      (Lower.checked_unrolljam_stmt_with_plan_fuel
         plan varctxt vars depth path fuel factor st)
      out ->
    stmt_refines_at varctxt depth out st.
Proof.
  intros plan varctxt vars depth path fuel factor st out Hpair Hret.
  eapply (proj1 (checked_unrolljam_with_plan_fuel_refines_mutual
                   fuel plan varctxt vars factor Hpair)); eauto.
Qed.

Theorem checked_unrolljam_stmt_with_plan_refines :
  forall plan varctxt vars factor st out,
    checked_pair_refines varctxt vars ->
    mayReturn
      (Lower.checked_unrolljam_stmt_with_plan
         plan varctxt vars factor st)
      out ->
    stmt_refines_at varctxt 0 out st.
Proof.
  intros plan varctxt vars factor st out Hpair Hret.
  unfold Lower.checked_unrolljam_stmt_with_plan in Hret.
  eapply checked_unrolljam_stmt_with_plan_fuel_refines; eauto.
Qed.

Lemma checked_unrolljam_fuel_refines_mutual :
  forall fuel varctxt vars factor,
    checked_pair_refines varctxt vars ->
    (forall depth st out,
        mayReturn
          (Lower.checked_unrolljam_stmt_fuel
             varctxt vars depth fuel factor st)
          out ->
        stmt_refines_at varctxt depth out st) /\
    (forall depth sts out,
        mayReturn
          (Lower.checked_unrolljam_stmt_list_fuel
             varctxt vars depth fuel factor sts)
          out ->
        stmt_refines_at varctxt depth (Loop.Seq out) (Loop.Seq sts)) /\
    (forall depth st out,
        mayReturn
          (Lower.checked_descend_unrolljam_stmt_fuel
             varctxt vars depth fuel factor st)
          out ->
        stmt_refines_at varctxt depth out st) /\
    (forall depth sts out,
        mayReturn
          (Lower.checked_descend_unrolljam_stmt_list_fuel
             varctxt vars depth fuel factor sts)
          out ->
        stmt_refines_at varctxt depth (Loop.Seq out) (Loop.Seq sts)).
Proof.
  induction fuel as [|fuel IH]; intros varctxt vars factor Hpair.
  - repeat split; intros; simpl in *;
      apply mayReturn_pure in H; subst; apply stmt_refines_at_refl.
  - destruct (IH varctxt vars factor Hpair) as
      [IHstmt [IHlist [IHdesc IHdesclist]]].
    repeat split.
    + intros depth st out Hret.
      destruct st as [lb ub body|i es|sts|tst body]; simpl in Hret.
      * apply mayReturn_bind in Hret.
        destruct Hret as [jam_res [Hjam Hret]].
        destruct jam_res as [jammed changed].
        pose proof
          (checked_jam_stmt_refines
             varctxt vars depth
             (Lower.Unroll.block_unroll_stmt factor lb ub body)
             (jammed, changed) Hpair Hjam) as Hjam_refines.
        simpl in Hjam_refines.
        pose proof (IHdesc _ _ _ Hret) as Hdesc_refines.
        eapply stmt_refines_at_trans; [exact Hdesc_refines|].
        eapply stmt_refines_at_trans.
        -- exact Hjam_refines.
        -- eapply stmt_refines_to_at.
           apply block_unroll_stmt_refines_loop.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [sts' [Hsts Hret]].
        pose proof (IHlist _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        exact Hsts_refines.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body' [Hbody Hret]].
        pose proof (IHstmt _ _ _ Hbody) as Hbody_refines.
        apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_guard.
        exact Hbody_refines.
    + intros depth sts out Hret.
      destruct sts as [|st sts']; simpl in Hret.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [st' [Hst Hret]].
        pose proof (IHstmt _ _ _ Hst) as Hst_refines.
        apply mayReturn_bind in Hret.
        destruct Hret as [sts'' [Hsts Hret]].
        pose proof (IHlist _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        eapply stmt_refines_at_seq_cons; eauto.
    + intros depth st out Hret.
      destruct st as [lb ub body|i es|sts|tst body]; simpl in Hret.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body' [Hbody Hret]].
        pose proof (IHstmt _ _ _ Hbody) as Hbody_refines.
        apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_loop.
        exact Hbody_refines.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [sts' [Hsts Hret]].
        pose proof (IHdesclist _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        exact Hsts_refines.
      * apply mayReturn_bind in Hret.
        destruct Hret as [body' [Hbody Hret]].
        pose proof (IHdesc _ _ _ Hbody) as Hbody_refines.
        apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_guard.
        exact Hbody_refines.
    + intros depth sts out Hret.
      destruct sts as [|st sts']; simpl in Hret.
      * apply mayReturn_pure in Hret.
        subst out.
        apply stmt_refines_at_refl.
      * apply mayReturn_bind in Hret.
        destruct Hret as [st' [Hst Hret]].
        pose proof (IHdesc _ _ _ Hst) as Hst_refines.
        apply mayReturn_bind in Hret.
        destruct Hret as [sts'' [Hsts Hret]].
        pose proof (IHdesclist _ _ _ Hsts) as Hsts_refines.
        apply mayReturn_pure in Hret.
        subst out.
        eapply stmt_refines_at_seq_cons; eauto.
Qed.

Theorem checked_unrolljam_stmt_fuel_refines :
  forall varctxt vars depth fuel factor st out,
    checked_pair_refines varctxt vars ->
    mayReturn
      (Lower.checked_unrolljam_stmt_fuel
         varctxt vars depth fuel factor st)
      out ->
    stmt_refines_at varctxt depth out st.
Proof.
  intros varctxt vars depth fuel factor st out Hpair Hret.
  eapply (proj1 (checked_unrolljam_fuel_refines_mutual
                   fuel varctxt vars factor Hpair)); eauto.
Qed.

Theorem checked_unrolljam_stmt_refines :
  forall varctxt vars factor st out,
    checked_pair_refines varctxt vars ->
    mayReturn
      (Lower.checked_unrolljam_stmt varctxt vars factor st)
      out ->
    stmt_refines_at varctxt 0 out st.
Proof.
  intros varctxt vars factor st out Hpair Hret.
  unfold Lower.checked_unrolljam_stmt in Hret.
  eapply checked_unrolljam_stmt_fuel_refines; eauto.
Qed.

Definition loop_refines (after before : Loop.t) : Prop :=
  forall mem1 mem2,
    Loop.semantics after mem1 mem2 ->
    exists mem2',
      Loop.semantics before mem1 mem2' /\
      State.eq mem2 mem2'.

Lemma stmt_refines_lifts_to_loop :
  forall after before varctxt vars,
    stmt_refines after before ->
    loop_refines
      (after, varctxt, vars)
      (before, varctxt, vars).
Proof.
  intros after before varctxt vars Href mem1 mem2 Hsem.
  inversion Hsem as
    [loop_ext loop ctxt vars' env mem1' mem2'
       Hloop_ext Hcompat Hna Hinit Hstmt]; subst mem1' mem2'; clear Hsem.
  inversion Hloop_ext; subst loop ctxt vars'; clear Hloop_ext.
  destruct (Href _ _ _ Hna Hstmt) as [mem2x [Hbefore Heq]].
  exists mem2x.
  split.
  - econstructor; eauto.
  - exact Heq.
Qed.

Lemma stmt_refines_at_lifts_to_loop :
  forall after before varctxt vars,
    stmt_refines_at varctxt 0 after before ->
    loop_refines
      (after, varctxt, vars)
      (before, varctxt, vars).
Proof.
  intros after before varctxt vars Href mem1 mem2 Hsem.
  inversion Hsem as
    [loop_ext loop ctxt vars' env mem1' mem2'
       Hloop_ext Hcompat Hna Hinit Hstmt]; subst mem1' mem2'; clear Hsem.
  inversion Hloop_ext; subst loop ctxt vars'; clear Hloop_ext.
  assert (Henvlen : Datatypes.length env = Datatypes.length varctxt).
  {
    pose proof (Instr.init_env_samelen _ _ _ Hinit) as Hinitlen.
    rewrite rev_length in Hinitlen.
    lia.
  }
  destruct (Href env (ltac:(simpl; lia)) _ _ Hna Hstmt)
    as [mem2x [Hbefore Heq]].
  exists mem2x.
  split.
  - econstructor; eauto.
  - exact Heq.
Qed.

Theorem checked_unrolljam_loop_with_plan_refines :
  forall plan factor before after,
    (let '(_, varctxt, vars) := before in
       checked_pair_refines varctxt vars) ->
    mayReturn
      (Lower.checked_unrolljam_loop_with_plan plan factor before)
      after ->
    loop_refines after before.
Proof.
  intros plan factor [[st varctxt] vars] after Hpair Hret.
  simpl in Hpair, Hret.
  apply mayReturn_bind in Hret.
  destruct Hret as [st' [Hst Hret]].
  apply mayReturn_pure in Hret.
  subst after.
  apply stmt_refines_at_lifts_to_loop.
  eapply checked_unrolljam_stmt_with_plan_refines; eauto.
Qed.

Theorem checked_unrolljam_loop_refines :
  forall factor before after,
    (let '(_, varctxt, vars) := before in
       checked_pair_refines varctxt vars) ->
    mayReturn (Lower.checked_unrolljam_loop factor before) after ->
    loop_refines after before.
Proof.
  intros factor [[st varctxt] vars] after Hpair Hret.
  simpl in Hpair, Hret.
  apply mayReturn_bind in Hret.
  destruct Hret as [st' [Hst Hret]].
  apply mayReturn_pure in Hret.
  subst after.
  apply stmt_refines_at_lifts_to_loop.
  eapply checked_unrolljam_stmt_refines; eauto.
Qed.

End LoopJamContext.
