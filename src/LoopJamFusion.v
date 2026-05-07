Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import Misc.
Require Import PolIRs.
Require Import ParallelLoop.
Require Import ParallelCodegen.
Require Import LoopJamTrace.

Module LoopJamFusion (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module Loop := PolIRs.Loop.
Module Trace := LoopJamTrace PolIRs.
Module PC := Trace.PC.
Module PL := Trace.PL.
Module ILSema := PL.ILSema.
Module State := Instr.State.

Definition trace := Trace.trace.

Definition seq2 (s1 s2 : Loop.stmt) : Loop.stmt :=
  Loop.Seq (Loop.SCons s1 (Loop.SCons s2 Loop.SNil)).

Definition jammed_two_loop
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) : Loop.stmt :=
  Loop.Loop lb ub (seq2 body1 body2).

Definition unjammed_two_loop
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) : Loop.stmt :=
  seq2 (Loop.Loop lb ub body1) (Loop.Loop lb ub body2).

Lemma tag_expr_eval_eq :
  forall env e,
    PL.BaseLoop.eval_expr env (PC.tag_expr e) =
    Loop.eval_expr env e.
Proof.
  induction e; simpl; try rewrite ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.

Definition same_range_trace_cross_permutable
    (d : nat) (lb ub : Loop.expr) (body1 body2 : Loop.stmt) (env : list Z)
  : Prop :=
  forall zs traces1 traces2,
    zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) ->
    Forall2
      (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at (S d) body1) (z :: env) tr)
      zs traces1 ->
    Forall2
      (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at (S d) body2) (z :: env) tr)
      zs traces2 ->
    Trace.jam_cross_permutable traces1 traces2.

Lemma seq_trace_seq2_inv :
  forall d body1 body2 env tr,
    PL.seq_trace (PC.tag_loop_stmt_at d (seq2 body1 body2)) env tr ->
    exists tr1 tr2,
      PL.seq_trace (PC.tag_loop_stmt_at d body1) env tr1 /\
      PL.seq_trace (PC.tag_loop_stmt_at d body2) env tr2 /\
      tr = tr1 ++ tr2.
Proof.
  intros d body1 body2 env tr Htrace.
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
  forall d zs traces body1 body2 env,
    Forall2
      (fun z tr =>
         PL.seq_trace (PC.tag_loop_stmt_at d (seq2 body1 body2)) (z :: env) tr)
      zs traces ->
    exists traces1 traces2,
      Forall2
        (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at d body1) (z :: env) tr)
        zs traces1 /\
      Forall2
        (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at d body2) (z :: env) tr)
        zs traces2 /\
      concat traces = Trace.jam_zip traces1 traces2.
Proof.
  intros d zs traces body1 body2 env Hfor.
  induction Hfor as [|z tr zs traces Hhead Htail IH].
  - exists [], [].
    repeat split; constructor.
  - destruct IH as [traces1 [traces2 [Hfor1 [Hfor2 Hconcat]]]].
    destruct (seq_trace_seq2_inv d body1 body2 (z :: env) tr Hhead)
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
  forall d lb ub body1 body2 env tr,
    PL.seq_trace
      (PC.tag_loop_stmt_at d (jammed_two_loop lb ub body1 body2)) env tr ->
    exists zs traces1 traces2,
      zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) /\
      Forall2
        (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at (S d) body1) (z :: env) tr)
        zs traces1 /\
      Forall2
        (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at (S d) body2) (z :: env) tr)
        zs traces2 /\
      tr = Trace.jam_zip traces1 traces2.
Proof.
  intros d lb ub body1 body2 env tr Htrace.
  simpl in Htrace.
  inversion Htrace; subst; clear Htrace.
  lazymatch goal with
  | Hfor : Forall2 _ (Zrange _ _) ?traces0 |- _ =>
      rewrite !tag_expr_eval_eq in Hfor;
      destruct
        (seq2_forall2_trace_split
           (S d)
           (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub))
           traces0 body1 body2 env Hfor)
        as [traces1 [traces2 [Hfor1 [Hfor2 Hzip]]]];
      exists (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub)),
        traces1, traces2;
      repeat split; auto;
      exact Hzip
  end.
Qed.

Lemma seq_trace_unjammed_two :
  forall d lb ub body1 body2 env zs traces1 traces2,
    zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) ->
    Forall2
      (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at (S d) body1) (z :: env) tr)
      zs traces1 ->
    Forall2
      (fun z tr => PL.seq_trace (PC.tag_loop_stmt_at (S d) body2) (z :: env) tr)
      zs traces2 ->
    PL.seq_trace
      (PC.tag_loop_stmt_at d (unjammed_two_loop lb ub body1 body2))
      env
      (concat traces1 ++ concat traces2).
Proof.
  intros d lb ub body1 body2 env zs traces1 traces2 Hzs Hfor1 Hfor2.
  apply PL.STSeqStmt.
  simpl.
  eapply PL.STTracesCons.
  - eapply PL.STLoop.
    + rewrite !tag_expr_eval_eq. exact Hzs.
    + exact Hfor1.
    + reflexivity.
  - rewrite <- app_nil_r with (l := concat traces2).
    eapply PL.STTracesCons.
    + eapply PL.STLoop.
      * rewrite !tag_expr_eval_eq. exact Hzs.
      * exact Hfor2.
      * reflexivity.
    + apply PL.STTracesNil.
Qed.

Theorem jammed_two_loop_trace_refines_unjammed :
  forall d lb ub body1 body2 env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    PL.trace_safe_stmt
      (PC.tag_loop_stmt_at d (unjammed_two_loop lb ub body1 body2)) ->
    PL.seq_trace
      (PC.tag_loop_stmt_at d (jammed_two_loop lb ub body1 body2)) env tr ->
    same_range_trace_cross_permutable d lb ub body1 body2 env ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      Loop.loop_semantics
        (unjammed_two_loop lb ub body1 body2) env mem1 mem2' /\
      State.eq mem2 mem2'.
Proof.
  intros d lb ub body1 body2 env tr mem1 mem2
    Hna Hsafe Htrace Hcross Hsem.
  destruct (seq_trace_jammed_two_inv d lb ub body1 body2 env tr Htrace)
    as [zs [traces1 [traces2 [Hzs [Hfor1 [Hfor2 Htr]]]]]].
  subst tr.
  pose proof (Hcross zs traces1 traces2 Hzs Hfor1 Hfor2) as Hperm.
  destruct
    (Trace.jam_zip_refines_unjammed
       traces1 traces2 mem1 mem2 Hna Hperm Hsem)
    as [mem_mid [Hsem_unjammed_trace Heq_mid]].
  pose proof
    (seq_trace_unjammed_two d lb ub body1 body2 env zs traces1 traces2
       Hzs Hfor1 Hfor2)
    as Htrace_unjammed.
  destruct
    (PL.seq_trace_refines_erased
       (PC.tag_loop_stmt_at d (unjammed_two_loop lb ub body1 body2))
       env
       (concat traces1 ++ concat traces2)
       mem1 mem_mid
       Hsafe Htrace_unjammed Hsem_unjammed_trace)
    as [mem_out [Hloop Heq_out]].
  exists mem_out.
  split.
  - eapply PC.erase_to_loop_stmt_semantics in Hloop.
    rewrite PC.erase_tag_loop_stmt_at_eq in Hloop.
    exact Hloop.
  - eapply State.eq_trans.
    + exact Heq_mid.
    + exact Heq_out.
Qed.

End LoopJamFusion.
