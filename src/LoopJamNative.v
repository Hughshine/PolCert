Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import Misc.
Require Import PolIRs.
Require Import Result.

Module LoopJamNative (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module Loop := PolIRs.Loop.
Module ILSema := Loop.ILSema.
Module State := Instr.State.

Definition InstrPoint := Loop.InstrPoint.
Definition trace := list InstrPoint.

Definition seq2 (s1 s2 : Loop.stmt) : Loop.stmt :=
  Loop.Seq (Loop.SCons s1 (Loop.SCons s2 Loop.SNil)).

Definition jammed_two_loop
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) : Loop.stmt :=
  Loop.Loop lb ub (seq2 body1 body2).

Definition unjammed_two_loop
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) : Loop.stmt :=
  seq2 (Loop.Loop lb ub body1) (Loop.Loop lb ub body2).

Fixpoint trace_safe_stmt (s : Loop.stmt) : Prop :=
  match s with
  | Loop.Loop _ _ body => trace_safe_stmt body
  | Loop.Instr _ es => exists affs, Loop.exprlist_to_aff es = Okk affs
  | Loop.Seq ss => trace_safe_stmts ss
  | Loop.Guard _ body => trace_safe_stmt body
  end
with trace_safe_stmts (ss : Loop.stmt_list) : Prop :=
  match ss with
  | Loop.SNil => True
  | Loop.SCons s ss' => trace_safe_stmt s /\ trace_safe_stmts ss'
  end.

Definition traces_permutable (left right : trace) : Prop :=
  forall ip_left ip_right,
    In ip_left left ->
    In ip_right right ->
    ILSema.Permutable ip_left ip_right.

Fixpoint jam_cross_permutable
    (outer_traces inner_traces : list trace) : Prop :=
  match outer_traces, inner_traces with
  | _ :: outer_tail, inner_head :: inner_tail =>
      traces_permutable (concat outer_tail) inner_head /\
      jam_cross_permutable outer_tail inner_tail
  | _, _ => True
  end.

Fixpoint jam_zip (outer_traces inner_traces : list trace) : trace :=
  match outer_traces, inner_traces with
  | outer_head :: outer_tail, inner_head :: inner_tail =>
      outer_head ++ inner_head ++ jam_zip outer_tail inner_tail
  | _, _ => concat outer_traces ++ concat inner_traces
  end.

Lemma instr_point_sema_preserve_nonalias :
  forall ip st1 st2,
    Instr.NonAlias st1 ->
    ILSema.instr_point_sema ip st1 st2 ->
    Instr.NonAlias st2.
Proof.
  intros ip st1 st2 Hna Hsem.
  inversion Hsem as [wcs rcs Hinstr]; subst.
  eapply Instr.sema_prsv_nonalias; eauto.
Qed.

Lemma instr_point_sema_stable_under_state_eq :
  forall ip st1 st2 st1' st2',
    State.eq st1 st1' ->
    State.eq st2 st2' ->
    ILSema.instr_point_sema ip st1 st2 ->
    ILSema.instr_point_sema ip st1' st2'.
Proof.
  exact ILSema.instr_point_sema_stable_under_state_eq.
Qed.

Lemma instr_point_list_semantics_nil_inv :
  forall st1 st2,
    ILSema.instr_point_list_semantics [] st1 st2 ->
    State.eq st1 st2.
Proof.
  exact ILSema.instr_point_list_semantics_nil_inv.
Qed.

Lemma instr_point_list_semantics_singleton_inv :
  forall ip st1 st2,
    ILSema.instr_point_list_semantics [ip] st1 st2 ->
    ILSema.instr_point_sema ip st1 st2.
Proof.
  exact ILSema.instr_point_list_semantics_singleton_inv.
Qed.

Lemma instr_point_list_semantics_app_inv :
  forall l1 l2 st1 st3,
    ILSema.instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      ILSema.instr_point_list_semantics l1 st1 st2 /\
      ILSema.instr_point_list_semantics l2 st2 st3.
Proof.
  exact ILSema.instr_point_list_semantics_app_inv.
Qed.

Lemma instr_point_list_semantics_cons_inv :
  forall ip rest st1 st2,
    ILSema.instr_point_list_semantics (ip :: rest) st1 st2 ->
    exists stmid,
      ILSema.instr_point_sema ip st1 stmid /\
      ILSema.instr_point_list_semantics rest stmid st2.
Proof.
  exact ILSema.instr_point_list_semantics_cons_inv.
Qed.

Lemma instr_point_list_semantics_swap_adj :
  forall ip1 ip2 rest st1 st4,
    Instr.NonAlias st1 ->
    ILSema.Permutable ip1 ip2 ->
    ILSema.instr_point_list_semantics (ip1 :: ip2 :: rest) st1 st4 ->
    exists st4',
      ILSema.instr_point_list_semantics (ip2 :: ip1 :: rest) st1 st4' /\
      State.eq st4 st4'.
Proof.
  intros ip1 ip2 rest st1 st4 Hna Hperm Hsem.
  inversion Hsem as [|st1' st2 st4' ip1' l1 Hip1 Htail]; subst.
  inversion Htail as [|st2' st3 st4'' ip2' l2 Hip2 Hrest]; subst.
  unfold ILSema.Permutable in Hperm.
  specialize (Hperm st1 Hna).
  destruct Hperm as [Hfwd _].
  destruct (Hfwd _ _ Hip1 Hip2) as (st2'' & st3' & Hip2' & Hip1' & Heq3).
  pose proof
    (ILSema.instr_point_list_sema_stable_under_state_eq
       rest st3 st4 st3' st4
       Hrest Heq3 (State.eq_refl st4))
    as Hrest'.
  exists st4.
  split.
  - econstructor.
    + exact Hip2'.
    + econstructor.
      * exact Hip1'.
      * exact Hrest'.
  - apply State.eq_refl.
Qed.

Lemma move_back_permutable :
  forall x prefix rest st1 st2,
    Instr.NonAlias st1 ->
    (forall y, In y prefix -> ILSema.Permutable y x) ->
    ILSema.instr_point_list_semantics (x :: prefix ++ rest) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (prefix ++ x :: rest) st1 st2' /\
      State.eq st2 st2'.
Proof.
  induction prefix as [|y prefix IH]; intros rest st1 st2 Hna Hperm Hsem.
  - simpl in *.
    exists st2.
    split; [exact Hsem | apply State.eq_refl].
  - simpl in Hsem.
    assert (Hyx : ILSema.Permutable x y).
    {
      eapply ILSema.Permutable_symm.
      apply Hperm.
      left; reflexivity.
    }
    pose proof
      (instr_point_list_semantics_swap_adj
         x y (prefix ++ rest) st1 st2 Hna Hyx Hsem)
      as [st2' [Hswapped Heq_swap]].
    inversion Hswapped as [|st1' stmid st2'' ip' rest' Hy Htail]; subst.
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    assert (Hperm_tail : forall y0, In y0 prefix -> ILSema.Permutable y0 x).
    {
      intros y0 Hin.
      apply Hperm.
      right; exact Hin.
    }
    destruct (IH rest stmid st2' Hna_mid Hperm_tail Htail)
      as [st2'' [Hmoved Heq_tail]].
    exists st2''.
    split.
    + econstructor; eauto.
    + eapply State.eq_trans; eauto.
Qed.

Inductive jam_interleave_safe : list trace -> trace -> Prop :=
| JIS_nil :
    jam_interleave_safe [] []
| JIS_skip_nil : forall pre post out,
    jam_interleave_safe (pre ++ post) out ->
    jam_interleave_safe (pre ++ [] :: post) out
| JIS_take : forall pre x xs post out,
    (forall y, In y (concat pre) -> ILSema.Permutable y x) ->
    jam_interleave_safe (pre ++ xs :: post) out ->
    jam_interleave_safe (pre ++ (x :: xs) :: post) (x :: out).

Lemma concat_insert_nil :
  forall (pre post : list trace),
    concat (pre ++ [] :: post) = concat (pre ++ post).
Proof.
  intros pre post.
  rewrite !concat_app.
  reflexivity.
Qed.

Lemma jam_interleave_safe_refines_concat :
  forall traces out st1 st2,
    Instr.NonAlias st1 ->
    jam_interleave_safe traces out ->
    ILSema.instr_point_list_semantics out st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (concat traces) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros traces out st1 st2 Hna Hsafe.
  revert st1 st2 Hna.
  induction Hsafe; intros st1 st2 Hna Hsem.
  - simpl in Hsem.
    exists st1.
    split.
    + constructor. apply State.eq_refl.
    + eapply State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - destruct (IHHsafe st1 st2 Hna Hsem)
      as [st2' [Hconcat Heq]].
    exists st2'.
    split.
    + rewrite concat_insert_nil.
      exact Hconcat.
    + exact Heq.
  - destruct (instr_point_list_semantics_cons_inv _ _ _ _ Hsem)
      as [stmid [Hx Htail]].
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    destruct (IHHsafe stmid st2 Hna_mid Htail)
      as [st2' [Hconcat_tail Heq_tail]].
    assert
      (Hshape_rest :
         concat (pre ++ xs :: post) =
         concat pre ++ concat (xs :: post)).
    {
      rewrite concat_app.
      reflexivity.
    }
    assert
      (Hcons :
         ILSema.instr_point_list_semantics
           (x :: concat pre ++ concat (xs :: post)) st1 st2').
    {
      econstructor.
      - exact Hx.
      - rewrite <- Hshape_rest.
        exact Hconcat_tail.
    }
    destruct
      (move_back_permutable
         x (concat pre) (concat (xs :: post)) st1 st2'
         Hna H Hcons)
      as [st2'' [Hconcat_full Heq_move]].
    exists st2''.
    split.
    + rewrite concat_app.
      simpl.
      exact Hconcat_full.
    + eapply State.eq_trans.
      * exact Heq_tail.
      * exact Heq_move.
Qed.

Lemma jam_interleave_safe_take_head_trace :
  forall tr traces out,
    jam_interleave_safe traces out ->
    jam_interleave_safe (tr :: traces) (tr ++ out).
Proof.
  induction tr as [|ip tr IH]; intros traces out Hsafe; simpl.
  - apply (JIS_skip_nil [] traces out).
    exact Hsafe.
  - eapply (JIS_take [] ip tr traces (tr ++ out)).
    + intros y Hin.
      inversion Hin.
    + apply IH.
      exact Hsafe.
Qed.

Lemma jam_interleave_safe_take_trace_after_pre :
  forall tr pre post out,
    traces_permutable (concat pre) tr ->
    jam_interleave_safe (pre ++ post) out ->
    jam_interleave_safe (pre ++ tr :: post) (tr ++ out).
Proof.
  induction tr as [|ip tr IH]; intros pre post out Hperm Hsafe; simpl.
  - apply JIS_skip_nil.
    exact Hsafe.
  - eapply JIS_take.
    + intros y Hin.
      eapply Hperm.
      * exact Hin.
      * left; reflexivity.
    + apply IH.
      * intros y z Hy Hz.
        eapply Hperm.
        -- exact Hy.
        -- right; exact Hz.
      * exact Hsafe.
Qed.

Lemma jam_interleave_safe_concat :
  forall traces,
    jam_interleave_safe traces (concat traces).
Proof.
  induction traces as [|tr traces IH]; simpl.
  - constructor.
  - apply jam_interleave_safe_take_head_trace.
    exact IH.
Qed.

Theorem jam_zip_interleave_safe :
  forall outer_traces inner_traces,
    jam_cross_permutable outer_traces inner_traces ->
    jam_interleave_safe
      (outer_traces ++ inner_traces)
      (jam_zip outer_traces inner_traces).
Proof.
  induction outer_traces as [|outer_head outer_tail IH];
    intros inner_traces Hcross.
  - simpl.
    apply jam_interleave_safe_concat.
  - destruct inner_traces as [|inner_head inner_tail].
    + simpl.
      repeat rewrite app_nil_r.
      apply jam_interleave_safe_concat.
    + simpl in Hcross.
      destruct Hcross as [Hperm Hcross].
      simpl.
      apply jam_interleave_safe_take_head_trace.
      eapply jam_interleave_safe_take_trace_after_pre.
      * exact Hperm.
      * apply IH.
        exact Hcross.
Qed.

Theorem jam_zip_refines_unjammed :
  forall outer_traces inner_traces st1 st2,
    Instr.NonAlias st1 ->
    jam_cross_permutable outer_traces inner_traces ->
    ILSema.instr_point_list_semantics
      (jam_zip outer_traces inner_traces) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics
        (concat outer_traces ++ concat inner_traces) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros outer_traces inner_traces st1 st2 Hna Hcross Hsem.
  destruct
    (jam_interleave_safe_refines_concat
       (outer_traces ++ inner_traces)
       (jam_zip outer_traces inner_traces)
       st1 st2 Hna
       (jam_zip_interleave_safe outer_traces inner_traces Hcross)
       Hsem)
    as [st2' [Hconcat Heq]].
  exists st2'.
  split.
  - rewrite concat_app in Hconcat.
    exact Hconcat.
  - exact Heq.
Qed.

Inductive seq_trace : Loop.stmt -> list Z -> trace -> Prop :=
| STInstr : forall i es env,
    seq_trace (Loop.Instr i es) env [Loop.mk_instr_point i es env]
| STSeqStmt : forall env sts tr,
    seq_traces sts env tr ->
    seq_trace (Loop.Seq sts) env tr
| STGuardTrue : forall env tst st tr,
    Loop.eval_test env tst = true ->
    seq_trace st env tr ->
    seq_trace (Loop.Guard tst st) env tr
| STGuardFalse : forall env tst st,
    Loop.eval_test env tst = false ->
    seq_trace (Loop.Guard tst st) env []
| STLoop : forall lb ub body env zs traces tr,
    zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) ->
    Forall2 (fun z tri => seq_trace body (z :: env) tri) zs traces ->
    tr = concat traces ->
    seq_trace (Loop.Loop lb ub body) env tr
with seq_traces : Loop.stmt_list -> list Z -> trace -> Prop :=
| STTracesNil : forall env,
    seq_traces Loop.SNil env []
| STTracesCons : forall env st sts tr1 tr2,
    seq_trace st env tr1 ->
    seq_traces sts env tr2 ->
    seq_traces (Loop.SCons st sts) env (tr1 ++ tr2).

Lemma seq_trace_seq_inv :
  forall sts env tr,
    seq_trace (Loop.Seq sts) env tr ->
    seq_traces sts env tr.
Proof.
  intros sts env tr Htrace.
  inversion Htrace; subst; assumption.
Qed.

Lemma seq_trace_forall2_refines_loop :
  forall body env,
    (forall env' tr mem1 mem2,
       trace_safe_stmt body ->
       seq_trace body env' tr ->
       ILSema.instr_point_list_semantics tr mem1 mem2 ->
       exists mem2',
         Loop.loop_semantics body env' mem1 mem2' /\
         State.eq mem2 mem2') ->
    forall zs traces mem1 mem2,
      trace_safe_stmt body ->
      Forall2 (fun z tri => seq_trace body (z :: env) tri) zs traces ->
      ILSema.instr_point_list_semantics (concat traces) mem1 mem2 ->
      exists mem2',
        Instr.IterSem.iter_semantics
          (fun z => Loop.loop_semantics body (z :: env))
          zs mem1 mem2' /\
        State.eq mem2 mem2'.
Proof.
  intros body env Hbody zs traces mem1 mem2 Hsafe Hfor.
  revert mem1 mem2 Hsafe.
  induction Hfor as [|z tr zs' traces' Htr Hfor' IH];
    intros mem1 mem2 Hsafe Hsem_concat.
  - simpl in Hsem_concat.
    exists mem1.
    split.
    + constructor.
    + eapply State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem_concat.
    eapply instr_point_list_semantics_app_inv in Hsem_concat.
    destruct Hsem_concat as [mem_mid [Hsem_head Hsem_tail]].
    pose proof (Hbody (z :: env) tr mem1 mem_mid Hsafe Htr Hsem_head)
      as [mem_mid' [Hbody_sem Heq_mid]].
    pose proof
      (ILSema.instr_point_list_sema_stable_under_state_eq
         (concat traces') mem_mid mem2 mem_mid' mem2
         Hsem_tail Heq_mid (State.eq_refl mem2))
      as Hsem_tail'.
    pose proof (IH mem_mid' mem2 Hsafe Hsem_tail')
      as [mem2' [Hrest_sem Heq_tail]].
    exists mem2'.
    split.
    + econstructor; eauto.
    + exact Heq_tail.
Qed.

Lemma seq_trace_refines_loop_stmt :
  forall s env tr mem1 mem2,
    trace_safe_stmt s ->
    seq_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics s env mem1 mem2' /\
      State.eq mem2 mem2'
with seq_trace_refines_loop_stmts :
  forall ss env tr mem1 mem2,
    trace_safe_stmts ss ->
    seq_traces ss env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics (Loop.Seq ss) env mem1 mem2' /\
      State.eq mem2 mem2'.
Proof.
  - intros s.
    induction s as [lb ub body IHbody|i es|ss _|t body IHbody];
      intros env tr mem1 mem2 Hsafe Htrace Hsem.
    + inversion Htrace as
        [| | | |
         lb0 ub0 body0 env0 zs traces tr0 Hrange Htraces Hconcat];
        subst; clear Htrace.
      pose proof
        (seq_trace_forall2_refines_loop
           body env IHbody
           (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub))
           traces mem1 mem2 Hsafe Htraces Hsem)
        as [mem2' [Hloop_sem Heq]].
      exists mem2'.
      split.
      * econstructor. exact Hloop_sem.
      * exact Heq.
    + inversion Htrace; subst.
      simpl in Hsafe.
      pose proof (instr_point_list_semantics_singleton_inv _ _ _ Hsem) as Hip.
      inversion Hip as [wcs rcs Hinstr]; subst.
      unfold Loop.mk_instr_point in Hinstr.
      destruct Hsafe as [affs Haff].
      rewrite Haff in Hinstr.
      simpl in Hinstr.
      pose proof (Loop.exprlist_to_aff_correct es env affs Haff) as Haff_ok.
      exists mem2.
      split.
      * eapply Loop.LInstr with (wcs := wcs) (rcs := rcs).
        rewrite <- Haff_ok in Hinstr.
        exact Hinstr.
      * apply State.eq_refl.
    + inversion Htrace; subst.
      eapply seq_trace_refines_loop_stmts; eauto.
    + inversion Htrace as
        [| | env' tst st tr' Heval Hbodytrace | env' tst st Heval |];
        subst; simpl in Hsafe.
      * pose proof (IHbody env tr mem1 mem2 Hsafe Hbodytrace Hsem)
          as [mem2' [Hbody_sem Heq]].
        exists mem2'.
        split; [eapply Loop.LGuardTrue; eauto | exact Heq].
      * exists mem1.
        split.
        -- eapply Loop.LGuardFalse; eauto.
        -- eapply State.eq_sym.
           eapply instr_point_list_semantics_nil_inv; eauto.
  - intros ss.
    induction ss as [|s ss IHss']; intros env tr mem1 mem2 Hsafe Htrace Hsem.
    + inversion Htrace; subst.
      exists mem1.
      split.
      * constructor.
      * eapply State.eq_sym.
        eapply instr_point_list_semantics_nil_inv; eauto.
    + inversion Htrace as [|env' st sts tr1 tr2 Hst Hsts]; subst.
      simpl in Hsafe.
      destruct Hsafe as [Hsafe_s Hsafe_ss].
      eapply instr_point_list_semantics_app_inv in Hsem.
      destruct Hsem as [mem_mid [Hsem_head Hsem_tail]].
      pose proof
        (seq_trace_refines_loop_stmt
           s env tr1 mem1 mem_mid Hsafe_s Hst Hsem_head)
        as [mem_mid' [Hs_sem Heq_mid]].
      pose proof
        (ILSema.instr_point_list_sema_stable_under_state_eq
           tr2 mem_mid mem2 mem_mid' mem2
           Hsem_tail Heq_mid (State.eq_refl mem2))
        as Hsem_tail'.
      pose proof
        (IHss' env tr2 mem_mid' mem2 Hsafe_ss Hsts Hsem_tail')
        as [mem2' [Hss_sem Heq_tail]].
      exists mem2'.
      split.
      * econstructor; eauto.
      * exact Heq_tail.
Qed.

Lemma seq_trace_refines_loop :
  forall s env tr mem1 mem2,
    trace_safe_stmt s ->
    seq_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics s env mem1 mem2' /\
      State.eq mem2 mem2'.
Proof.
  intros. eapply seq_trace_refines_loop_stmt; eauto.
Qed.

Lemma seq_trace_seq2_inv :
  forall body1 body2 env tr,
    seq_trace (seq2 body1 body2) env tr ->
    exists tr1 tr2,
      seq_trace body1 env tr1 /\
      seq_trace body2 env tr2 /\
      tr = tr1 ++ tr2.
Proof.
  intros body1 body2 env tr Htrace.
  inversion Htrace as [|env' sts tr' Htraces| | |]; subst.
  simpl in Htraces.
  inversion Htraces as
      [|env1 st1 sts1 tr1 tr_tail Hbody1 Htail]; subst.
  inversion Htail as
      [|env2 st2 sts2 tr2 tr_nil Hbody2 Hnil]; subst.
  inversion Hnil; subst.
  exists tr1, tr2.
  repeat split; auto.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma seq2_forall2_trace_split :
  forall zs traces body1 body2 env,
    Forall2
      (fun z tr => seq_trace (seq2 body1 body2) (z :: env) tr)
      zs traces ->
    exists traces1 traces2,
      Forall2 (fun z tr => seq_trace body1 (z :: env) tr) zs traces1 /\
      Forall2 (fun z tr => seq_trace body2 (z :: env) tr) zs traces2 /\
      concat traces = jam_zip traces1 traces2.
Proof.
  intros zs traces body1 body2 env Hfor.
  induction Hfor as [|z tr zs traces Hhead Htail IH].
  - exists [], [].
    repeat split; constructor.
  - destruct IH as [traces1 [traces2 [Hfor1 [Hfor2 Hconcat]]]].
    destruct (seq_trace_seq2_inv body1 body2 (z :: env) tr Hhead)
      as [tr1 [tr2 [Htr1 [Htr2 Heq]]]].
    exists (tr1 :: traces1), (tr2 :: traces2).
    repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + simpl.
      rewrite Heq.
      rewrite Hconcat.
      rewrite app_assoc.
      reflexivity.
Qed.

Lemma seq_trace_jammed_two_inv :
  forall lb ub body1 body2 env tr,
    seq_trace (jammed_two_loop lb ub body1 body2) env tr ->
    exists zs traces1 traces2,
      zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) /\
      Forall2 (fun z tr => seq_trace body1 (z :: env) tr) zs traces1 /\
      Forall2 (fun z tr => seq_trace body2 (z :: env) tr) zs traces2 /\
      tr = jam_zip traces1 traces2.
Proof.
  intros lb ub body1 body2 env tr Htrace.
  inversion Htrace as
    [| | | |
     lb0 ub0 body0 env0 zs0 traces0 tr0 Hrange Htraces Hconcat];
    subst; clear Htrace.
  destruct (seq2_forall2_trace_split
              (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub))
              traces0 body1 body2 env Htraces)
    as [traces1 [traces2 [Hfor1 [Hfor2 Hzip]]]].
  exists (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub)),
    traces1, traces2.
  repeat split; auto.
Qed.

Definition same_range_trace_cross_permutable
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) (env : list Z)
  : Prop :=
  forall zs traces1 traces2,
    zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) ->
    Forall2 (fun z tr => seq_trace body1 (z :: env) tr) zs traces1 ->
    Forall2 (fun z tr => seq_trace body2 (z :: env) tr) zs traces2 ->
    jam_cross_permutable traces1 traces2.

Lemma seq_trace_unjammed_two :
  forall lb ub body1 body2 env zs traces1 traces2,
    zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) ->
    Forall2 (fun z tr => seq_trace body1 (z :: env) tr) zs traces1 ->
    Forall2 (fun z tr => seq_trace body2 (z :: env) tr) zs traces2 ->
    seq_trace
      (unjammed_two_loop lb ub body1 body2)
      env
      (concat traces1 ++ concat traces2).
Proof.
  intros lb ub body1 body2 env zs traces1 traces2 Hzs Hfor1 Hfor2.
  apply STSeqStmt.
  simpl.
  eapply STTracesCons.
  - eapply STLoop.
    + exact Hzs.
    + exact Hfor1.
    + reflexivity.
  - rewrite <- app_nil_r with (l := concat traces2).
    eapply STTracesCons.
    + eapply STLoop.
      * exact Hzs.
      * exact Hfor2.
      * reflexivity.
    + apply STTracesNil.
Qed.

Theorem jammed_two_loop_trace_refines_unjammed :
  forall lb ub body1 body2 env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt (unjammed_two_loop lb ub body1 body2) ->
    seq_trace (jammed_two_loop lb ub body1 body2) env tr ->
    same_range_trace_cross_permutable lb ub body1 body2 env ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics
        (unjammed_two_loop lb ub body1 body2) env mem1 mem2' /\
      State.eq mem2 mem2'.
Proof.
  intros lb ub body1 body2 env tr mem1 mem2
    Hna Hsafe Htrace Hcross Hsem.
  destruct (seq_trace_jammed_two_inv lb ub body1 body2 env tr Htrace)
    as [zs [traces1 [traces2 [Hzs [Hfor1 [Hfor2 Htr]]]]]].
  subst tr.
  pose proof (Hcross zs traces1 traces2 Hzs Hfor1 Hfor2) as Hperm.
  destruct
    (jam_zip_refines_unjammed
       traces1 traces2 mem1 mem2 Hna Hperm Hsem)
    as [mem_mid [Hsem_unjammed_trace Heq_mid]].
  pose proof
    (seq_trace_unjammed_two lb ub body1 body2 env zs traces1 traces2
       Hzs Hfor1 Hfor2)
    as Htrace_unjammed.
  destruct
    (seq_trace_refines_loop
       (unjammed_two_loop lb ub body1 body2)
       env
       (concat traces1 ++ concat traces2)
       mem1 mem_mid
       Hsafe Htrace_unjammed Hsem_unjammed_trace)
    as [mem_out [Hloop Heq_out]].
  exists mem_out.
  split.
  - exact Hloop.
  - eapply State.eq_trans; eauto.
Qed.

Lemma loop_instance_list_semantics_to_seq_trace :
  forall stmt env il mem1 mem2,
    Loop.loop_instance_list_semantics stmt env il mem1 mem2 ->
    seq_trace stmt env il
with loop_instance_list_semantics_list_to_seq_traces :
  forall zs stmt env il mem1 mem2,
    Loop.loop_instance_list_semantics_list zs stmt env il mem1 mem2 ->
    exists traces,
      Forall2 (fun z tr => seq_trace stmt (z :: env) tr) zs traces /\
      il = concat traces.
Proof.
  - intros stmt env il mem1 mem2 Hsem.
    induction Hsem
      using Loop.loop_instance_list_semantics_mutual_ind
      with
        (P0 := fun zs stmt env il mem1 mem2 Hlist =>
                 exists traces,
                   Forall2 (fun z tr => seq_trace stmt (z :: env) tr) zs traces /\
                   il = concat traces).
    + subst.
      apply STInstr.
    + apply STSeqStmt.
      apply STTracesNil.
    + apply STSeqStmt.
      simpl.
      eapply STTracesCons.
      * exact IHHsem1.
      * eapply seq_trace_seq_inv.
        exact IHHsem2.
    + eapply STGuardTrue; eauto.
    + eapply STGuardFalse; eauto.
    + destruct IHHsem as [traces [Hfor Hconcat]].
      subst il.
      eapply STLoop.
      * reflexivity.
      * exact Hfor.
      * reflexivity.
    + exists [].
      split; [constructor | reflexivity].
    + destruct IHHsem0 as [traces [Hfor Hconcat]].
      exists (il1 :: traces).
      split.
      * constructor; assumption.
      * subst il2.
        reflexivity.
  - intros zs stmt env il mem1 mem2 Hsem.
    induction Hsem
      using Loop.loop_instance_list_semantics_list_mutual_ind
      with
        (P := fun stmt env il mem1 mem2 Hstmt =>
                seq_trace stmt env il).
    + subst.
      apply STInstr.
    + apply STSeqStmt.
      apply STTracesNil.
    + apply STSeqStmt.
      simpl.
      eapply STTracesCons.
      * exact IHHsem.
      * eapply seq_trace_seq_inv.
        exact IHHsem0.
    + eapply STGuardTrue; eauto.
    + eapply STGuardFalse; eauto.
    + destruct IHHsem as [traces [Hfor Hconcat]].
      subst il.
      eapply STLoop.
      * reflexivity.
      * exact Hfor.
      * reflexivity.
    + exists [].
      split; [constructor | reflexivity].
    + destruct IHHsem0 as [traces [Hfor Hconcat]].
      exists (il1 :: traces).
      split.
      * constructor; assumption.
      * subst il2.
        reflexivity.
Qed.

Lemma loop_instance_list_semantics_implies_instr_point_trace_safe :
  forall s env mem1 mem2 il,
    Loop.loop_instance_list_semantics s env il mem1 mem2 ->
    trace_safe_stmt s ->
    ILSema.instr_point_list_semantics il mem1 mem2.
Proof.
  intros s env mem1 mem2 il Hsem.
  induction Hsem
    using Loop.loop_instance_list_semantics_mutual_ind
    with (P0 := fun zs s env il mem1 mem2 _ =>
                  trace_safe_stmt s ->
                  ILSema.instr_point_list_semantics il mem1 mem2);
    intros Hsafe; simpl in *.
  - destruct Hsafe as [affs Haff].
    econstructor.
    + econstructor.
      unfold Loop.mk_instr_point.
      rewrite Haff.
      simpl.
      pose proof (Loop.exprlist_to_aff_correct es env affs Haff) as Haff_ok.
      rewrite <- Haff_ok.
      lazymatch goal with
      | Hiv : ?iv = map (Loop.eval_expr env) es,
        Hinstr : Loop.instr_semantics i ?iv ?wcs ?rcs mem1 mem2 |- _ =>
          rewrite <- Hiv;
          exact Hinstr
      end.
    + constructor. apply State.eq_refl.
  - constructor. apply State.eq_refl.
  - destruct Hsafe as [Hsafe_st Hsafe_sts].
    eapply ILSema.instr_point_list_sema_concat.
    + eapply IHHsem1; eauto.
    + eapply IHHsem2; eauto.
  - eapply IHHsem; eauto.
  - constructor. apply State.eq_refl.
  - eapply IHHsem; eauto.
  - constructor. apply State.eq_refl.
  - eapply ILSema.instr_point_list_sema_concat.
    + eapply IHHsem; eauto.
    + eapply IHHsem0; eauto.
Qed.

Theorem jammed_two_loop_instance_refines_unjammed :
  forall lb ub body1 body2 env il mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt (unjammed_two_loop lb ub body1 body2) ->
    Loop.loop_instance_list_semantics
      (jammed_two_loop lb ub body1 body2) env il mem1 mem2 ->
    same_range_trace_cross_permutable lb ub body1 body2 env ->
    exists mem2',
      Loop.loop_semantics
        (unjammed_two_loop lb ub body1 body2) env mem1 mem2' /\
      State.eq mem2 mem2'.
Proof.
  intros lb ub body1 body2 env il mem1 mem2
    Hna Hsafe_unjammed Hinst Hcross.
  assert (Hsafe_jammed : trace_safe_stmt (jammed_two_loop lb ub body1 body2)).
  {
    simpl in Hsafe_unjammed.
    simpl.
    exact Hsafe_unjammed.
  }
  pose proof
    (loop_instance_list_semantics_to_seq_trace
       (jammed_two_loop lb ub body1 body2) env il mem1 mem2 Hinst)
    as Htrace.
  pose proof
    (loop_instance_list_semantics_implies_instr_point_trace_safe
       (jammed_two_loop lb ub body1 body2) env mem1 mem2 il
       Hinst Hsafe_jammed)
    as Hips.
  eapply jammed_two_loop_trace_refines_unjammed; eauto.
Qed.

End LoopJamNative.
