Require Import List.
Require Import Lia.
Require Import ZArith.
Import ListNotations.

Require Import Misc.
Require Import PolIRs.
Require Import LoopSingletonCleanup.
Require Import LoopUnroll.

Module LoopStride (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Loop := PolIRs.Loop.
Module Subst := LoopSingletonCleanup PolIRs.
Module Unroll := LoopUnroll PolIRs.

Definition stride_iter_expr (step: nat) (lb: Loop.expr) : Loop.expr :=
  Loop.Sum (Subst.lift_expr lb) (Loop.Mult (Z.of_nat step) (Loop.Var 0)).

Definition stride_count_expr (step: nat) (lb ub: Loop.expr) : Loop.expr :=
  match step with
  | O => Loop.Constant 0
  | S _ => Loop.Sum ub (Loop.Mult (-1) lb)
  end.

Definition stride_guard_test
    (step: nat) (lb ub: Loop.expr) : Loop.test :=
  Loop.LE
    (Loop.Sum (stride_iter_expr step lb) (Loop.Constant 1))
    (Subst.lift_expr ub).

Definition stride_body_stmt
    (step: nat) (lb ub: Loop.expr) (body: Loop.stmt) : Loop.stmt :=
  Loop.make_guard
    (stride_guard_test step lb ub)
    (Subst.subst_stmt_at 0
      (stride_iter_expr step lb)
      (Unroll.insert_stmt_at 1 body)).

Definition stride_loop_stmt
    (step: nat) (lb ub: Loop.expr) (body: Loop.stmt) : Loop.stmt :=
  match step with
  | O => Loop.Seq Loop.SNil
  | S _ =>
      Loop.Loop
        (Loop.Constant 0)
        (stride_count_expr step lb ub)
        (stride_body_stmt step lb ub body)
  end.

Definition stride_loop (step: nat) (lb ub: Loop.expr) (body: Loop.stmt)
    : Loop.stmt :=
  stride_loop_stmt step lb ub body.

Definition down_stride_iter_expr (step: nat) (lb: Loop.expr) : Loop.expr :=
  Loop.Sum (Subst.lift_expr lb) (Loop.Mult (- Z.of_nat step) (Loop.Var 0)).

Definition down_stride_count_expr (step: nat) (lb ub: Loop.expr) : Loop.expr :=
  match step with
  | O => Loop.Constant 0
  | S _ => Loop.Sum lb (Loop.Mult (-1) ub)
  end.

Definition down_stride_guard_test
    (step: nat) (lb ub: Loop.expr) : Loop.test :=
  Loop.LE
    (Loop.Sum (Subst.lift_expr ub) (Loop.Constant 1))
    (down_stride_iter_expr step lb).

Definition down_stride_body_stmt
    (step: nat) (lb ub: Loop.expr) (body: Loop.stmt) : Loop.stmt :=
  Loop.make_guard
    (down_stride_guard_test step lb ub)
    (Subst.subst_stmt_at 0
      (down_stride_iter_expr step lb)
      (Unroll.insert_stmt_at 1 body)).

Definition down_stride_loop_stmt
    (step: nat) (lb ub: Loop.expr) (body: Loop.stmt) : Loop.stmt :=
  match step with
  | O => Loop.Seq Loop.SNil
  | S _ =>
      Loop.Loop
        (Loop.Constant 0)
        (down_stride_count_expr step lb ub)
        (down_stride_body_stmt step lb ub body)
  end.

Definition down_stride_loop (step: nat) (lb ub: Loop.expr) (body: Loop.stmt)
    : Loop.stmt :=
  down_stride_loop_stmt step lb ub body.

Definition stride_trip_count (step lb ub: Z) : Z :=
  ub - lb.

Definition stride_values (step lb ub: Z) : list Z :=
  map
    (fun k => lb + step * k)
    (filter
      (fun k => (lb + step * k + 1 <=? ub))
      (Zrange 0 (stride_trip_count step lb ub))).

Definition down_stride_trip_count (step lb ub: Z) : Z :=
  lb - ub.

Definition down_stride_values (step lb ub: Z) : list Z :=
  map
    (fun k => lb - step * k)
    (filter
      (fun k => (ub + 1 <=? lb - step * k))
      (Zrange 0 (down_stride_trip_count step lb ub))).

Lemma stride_iter_expr_correct :
  forall step lb j env,
    Loop.eval_expr (j :: env) (stride_iter_expr step lb) =
    Loop.eval_expr env lb + Z.of_nat step * j.
Proof.
  intros step lb j env.
  unfold stride_iter_expr. simpl.
  rewrite Subst.lift_expr_correct. lia.
Qed.

Lemma stride_count_expr_correct :
  forall step lb ub env,
    (0 < step)%nat ->
    Loop.eval_expr env (stride_count_expr step lb ub) =
    stride_trip_count
      (Z.of_nat step)
      (Loop.eval_expr env lb)
      (Loop.eval_expr env ub).
Proof.
  intros step lb ub env Hstep.
  destruct step as [|step']; [lia|].
  unfold stride_count_expr, stride_trip_count. simpl.
  lia.
Qed.

Lemma stride_guard_test_correct :
  forall step lb ub j env,
    Loop.eval_test (j :: env) (stride_guard_test step lb ub) =
    (Loop.eval_expr env lb + Z.of_nat step * j + 1 <=?
     Loop.eval_expr env ub).
Proof.
  intros step lb ub j env.
  unfold stride_guard_test. simpl.
  rewrite !Subst.lift_expr_correct.
  reflexivity.
Qed.

Lemma stride_body_raw_stmt_semantics :
  forall step lb body j env mem1 mem2,
    Loop.loop_semantics
      (Subst.subst_stmt_at 0
        (stride_iter_expr step lb)
        (Unroll.insert_stmt_at 1 body))
      (j :: env) mem1 mem2 <->
    Loop.loop_semantics
      body
      ((Loop.eval_expr env lb + Z.of_nat step * j) :: env)
      mem1
      mem2.
Proof.
  intros step lb body j env mem1 mem2.
  split; intros Hsem.
  - apply Subst.subst_stmt_at_semantics in Hsem.
    rewrite stride_iter_expr_correct in Hsem.
    pose proof
      (proj1 Unroll.insert_stmt_at_correct
        body
        [Loop.eval_expr env lb + Z.of_nat step * j]
        j
        env
        mem1
        mem2) as Hinsert.
    simpl in Hinsert.
    apply Hinsert in Hsem.
    exact Hsem.
  - apply Subst.subst_stmt_at_semantics.
    rewrite stride_iter_expr_correct.
    pose proof
      (proj1 Unroll.insert_stmt_at_correct
        body
        [Loop.eval_expr env lb + Z.of_nat step * j]
        j
        env
        mem1
        mem2) as Hinsert.
    simpl in Hinsert.
    apply <- Hinsert in Hsem.
    exact Hsem.
Qed.

Lemma stride_body_stmt_semantics :
  forall step lb ub body j env mem1 mem2,
    Loop.loop_semantics
      (stride_body_stmt step lb ub body)
      (j :: env) mem1 mem2 <->
    (if (Loop.eval_expr env lb + Z.of_nat step * j + 1 <=?
         Loop.eval_expr env ub)
     then
       Loop.loop_semantics
         body
         ((Loop.eval_expr env lb + Z.of_nat step * j) :: env)
         mem1
         mem2
     else mem1 = mem2).
Proof.
  intros step lb ub body j env mem1 mem2.
  unfold stride_body_stmt.
  rewrite Loop.make_guard_correct.
  rewrite stride_guard_test_correct.
  destruct (Loop.eval_expr env lb + Z.of_nat step * j + 1 <=?
            Loop.eval_expr env ub) eqn:Hguard.
  - apply stride_body_raw_stmt_semantics.
  - reflexivity.
Qed.

Lemma iter_semantics_filter :
  forall (A: Type) (P Q: A -> State.t -> State.t -> Prop)
    (keep: A -> bool) xs mem1 mem2,
    (forall x st1 st2,
      Q x st1 st2 <->
      if keep x then P x st1 st2 else st1 = st2) ->
    Instr.IterSem.iter_semantics Q xs mem1 mem2 <->
    Instr.IterSem.iter_semantics P (filter keep xs) mem1 mem2.
Proof.
  induction xs as [|x xs IH]; intros mem1 mem2 Hstep; simpl.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - destruct (keep x) eqn:Hkeep; split; intros Hsem.
    + inversion_clear Hsem.
      apply Hstep in H.
      rewrite Hkeep in H.
      econstructor; [exact H|].
      apply IH; [exact Hstep|exact H0].
    + inversion_clear Hsem.
      econstructor.
      * apply Hstep. rewrite Hkeep. exact H.
      * apply IH; [exact Hstep|exact H0].
    + inversion_clear Hsem.
      apply Hstep in H.
      rewrite Hkeep in H. subst.
      apply IH; [exact Hstep|exact H0].
    + econstructor.
      * apply Hstep. rewrite Hkeep. reflexivity.
      * apply IH; [exact Hstep|exact Hsem].
Qed.

Theorem stride_loop_stmt_semantics :
  forall step lb ub body env mem1 mem2,
    (0 < step)%nat ->
    Loop.loop_semantics (stride_loop_stmt step lb ub body) env mem1 mem2 <->
    Instr.IterSem.iter_semantics
      (fun x => Loop.loop_semantics body (x :: env))
      (stride_values
        (Z.of_nat step)
        (Loop.eval_expr env lb)
        (Loop.eval_expr env ub))
      mem1
      mem2.
Proof.
  intros step lb ub body env mem1 mem2 Hstep.
  destruct step as [|step']; [lia|].
  change (stride_loop_stmt (S step') lb ub body) with
    (Loop.Loop
      (Loop.Constant 0)
      (stride_count_expr (S step') lb ub)
      (stride_body_stmt (S step') lb ub body)).
  split; intros Hsem.
  - inversion Hsem as
      [| | | | |
       env0 lb0 ub0 body0 mem10 mem20 Hiter]; subst; clear Hsem.
    change (Instr.IterSem.iter_semantics
      (fun j => Loop.loop_semantics
        (stride_body_stmt (S step') lb ub body) (j :: env))
      (Zrange (Loop.eval_expr env (Loop.Constant 0))
        (Loop.eval_expr env (stride_count_expr (S step') lb ub)))
      mem1 mem2) in Hiter.
    rewrite (stride_count_expr_correct (S step') lb ub env ltac:(lia)) in Hiter.
    eapply iter_semantics_filter in Hiter.
    + rewrite <- Instr.IterSem.iter_semantics_mapl in Hiter.
      exact Hiter.
    + intros j st1 st2.
      apply stride_body_stmt_semantics.
  - unfold stride_values in Hsem.
    rewrite Instr.IterSem.iter_semantics_mapl in Hsem.
    pose
      (keep := fun j =>
        (Loop.eval_expr env lb + Z.of_nat (S step') * j + 1 <=?
         Loop.eval_expr env ub)).
    pose
      (P := fun j =>
        Loop.loop_semantics
          body
          ((Loop.eval_expr env lb + Z.of_nat (S step') * j) :: env)).
    pose
      (Q := fun j =>
        Loop.loop_semantics
          (stride_body_stmt (S step') lb ub body)
          (j :: env)).
    assert (Hfilter : forall j st1 st2,
      Q j st1 st2 <-> if keep j then P j st1 st2 else st1 = st2).
    {
      intros j st1 st2. unfold P, Q, keep.
      apply stride_body_stmt_semantics.
    }
    pose proof
      (proj2
        (iter_semantics_filter Z P Q keep
          (Zrange 0
            (stride_trip_count
              (Z.of_nat (S step'))
              (Loop.eval_expr env lb)
              (Loop.eval_expr env ub)))
          mem1 mem2 Hfilter)
        Hsem) as Hfull.
    apply Loop.LLoop.
    change (Instr.IterSem.iter_semantics
      (fun j => Loop.loop_semantics
        (stride_body_stmt (S step') lb ub body) (j :: env))
      (Zrange (Loop.eval_expr env (Loop.Constant 0))
        (Loop.eval_expr env (stride_count_expr (S step') lb ub)))
      mem1 mem2).
    rewrite (stride_count_expr_correct (S step') lb ub env ltac:(lia)).
    exact Hfull.
Qed.

Lemma down_stride_iter_expr_correct :
  forall step lb j env,
    Loop.eval_expr (j :: env) (down_stride_iter_expr step lb) =
    Loop.eval_expr env lb - Z.of_nat step * j.
Proof.
  intros step lb j env.
  unfold down_stride_iter_expr. simpl.
  rewrite Subst.lift_expr_correct. lia.
Qed.

Lemma down_stride_count_expr_correct :
  forall step lb ub env,
    (0 < step)%nat ->
    Loop.eval_expr env (down_stride_count_expr step lb ub) =
    down_stride_trip_count
      (Z.of_nat step)
      (Loop.eval_expr env lb)
      (Loop.eval_expr env ub).
Proof.
  intros step lb ub env Hstep.
  destruct step as [|step']; [lia|].
  unfold down_stride_count_expr, down_stride_trip_count. simpl.
  lia.
Qed.

Lemma down_stride_guard_test_correct :
  forall step lb ub j env,
    Loop.eval_test (j :: env) (down_stride_guard_test step lb ub) =
    (Loop.eval_expr env ub + 1 <=?
     Loop.eval_expr env lb - Z.of_nat step * j).
Proof.
  intros step lb ub j env.
  unfold down_stride_guard_test, down_stride_iter_expr. simpl.
  rewrite !Subst.lift_expr_correct.
  replace (Loop.eval_expr env lb + - Z.of_nat step * j)
    with (Loop.eval_expr env lb - Z.of_nat step * j) by lia.
  reflexivity.
Qed.

Lemma down_stride_body_raw_stmt_semantics :
  forall step lb body j env mem1 mem2,
    Loop.loop_semantics
      (Subst.subst_stmt_at 0
        (down_stride_iter_expr step lb)
        (Unroll.insert_stmt_at 1 body))
      (j :: env) mem1 mem2 <->
    Loop.loop_semantics
      body
      ((Loop.eval_expr env lb - Z.of_nat step * j) :: env)
      mem1
      mem2.
Proof.
  intros step lb body j env mem1 mem2.
  split; intros Hsem.
  - apply Subst.subst_stmt_at_semantics in Hsem.
    rewrite down_stride_iter_expr_correct in Hsem.
    pose proof
      (proj1 Unroll.insert_stmt_at_correct
        body
        [Loop.eval_expr env lb - Z.of_nat step * j]
        j
        env
        mem1
        mem2) as Hinsert.
    simpl in Hinsert.
    apply Hinsert in Hsem.
    exact Hsem.
  - apply Subst.subst_stmt_at_semantics.
    rewrite down_stride_iter_expr_correct.
    pose proof
      (proj1 Unroll.insert_stmt_at_correct
        body
        [Loop.eval_expr env lb - Z.of_nat step * j]
        j
        env
        mem1
        mem2) as Hinsert.
    simpl in Hinsert.
    apply <- Hinsert in Hsem.
    exact Hsem.
Qed.

Lemma down_stride_body_stmt_semantics :
  forall step lb ub body j env mem1 mem2,
    Loop.loop_semantics
      (down_stride_body_stmt step lb ub body)
      (j :: env) mem1 mem2 <->
    (if (Loop.eval_expr env ub + 1 <=?
         Loop.eval_expr env lb - Z.of_nat step * j)
     then
       Loop.loop_semantics
         body
         ((Loop.eval_expr env lb - Z.of_nat step * j) :: env)
         mem1
         mem2
     else mem1 = mem2).
Proof.
  intros step lb ub body j env mem1 mem2.
  unfold down_stride_body_stmt.
  rewrite Loop.make_guard_correct.
  rewrite down_stride_guard_test_correct.
  destruct (Loop.eval_expr env ub + 1 <=?
            Loop.eval_expr env lb - Z.of_nat step * j) eqn:Hguard.
  - apply down_stride_body_raw_stmt_semantics.
  - reflexivity.
Qed.

Theorem down_stride_loop_stmt_semantics :
  forall step lb ub body env mem1 mem2,
    (0 < step)%nat ->
    Loop.loop_semantics (down_stride_loop_stmt step lb ub body) env mem1 mem2 <->
    Instr.IterSem.iter_semantics
      (fun x => Loop.loop_semantics body (x :: env))
      (down_stride_values
        (Z.of_nat step)
        (Loop.eval_expr env lb)
        (Loop.eval_expr env ub))
      mem1
      mem2.
Proof.
  intros step lb ub body env mem1 mem2 Hstep.
  destruct step as [|step']; [lia|].
  change (down_stride_loop_stmt (S step') lb ub body) with
    (Loop.Loop
      (Loop.Constant 0)
      (down_stride_count_expr (S step') lb ub)
      (down_stride_body_stmt (S step') lb ub body)).
  split; intros Hsem.
  - inversion Hsem as
      [| | | | |
       env0 lb0 ub0 body0 mem10 mem20 Hiter]; subst; clear Hsem.
    change (Instr.IterSem.iter_semantics
      (fun j => Loop.loop_semantics
        (down_stride_body_stmt (S step') lb ub body) (j :: env))
      (Zrange (Loop.eval_expr env (Loop.Constant 0))
        (Loop.eval_expr env (down_stride_count_expr (S step') lb ub)))
      mem1 mem2) in Hiter.
    rewrite (down_stride_count_expr_correct (S step') lb ub env ltac:(lia)) in Hiter.
    eapply iter_semantics_filter in Hiter.
    + rewrite <- Instr.IterSem.iter_semantics_mapl in Hiter.
      exact Hiter.
    + intros j st1 st2.
      apply down_stride_body_stmt_semantics.
  - unfold down_stride_values in Hsem.
    rewrite Instr.IterSem.iter_semantics_mapl in Hsem.
    pose
      (keep := fun j =>
        (Loop.eval_expr env ub + 1 <=?
         Loop.eval_expr env lb - Z.of_nat (S step') * j)).
    pose
      (P := fun j =>
        Loop.loop_semantics
          body
          ((Loop.eval_expr env lb - Z.of_nat (S step') * j) :: env)).
    pose
      (Q := fun j =>
        Loop.loop_semantics
          (down_stride_body_stmt (S step') lb ub body)
          (j :: env)).
    assert (Hfilter : forall j st1 st2,
      Q j st1 st2 <-> if keep j then P j st1 st2 else st1 = st2).
    {
      intros j st1 st2. unfold P, Q, keep.
      apply down_stride_body_stmt_semantics.
    }
    pose proof
      (proj2
        (iter_semantics_filter Z P Q keep
          (Zrange 0
            (down_stride_trip_count
              (Z.of_nat (S step'))
              (Loop.eval_expr env lb)
              (Loop.eval_expr env ub)))
          mem1 mem2 Hfilter)
        Hsem) as Hfull.
    apply Loop.LLoop.
    change (Instr.IterSem.iter_semantics
      (fun j => Loop.loop_semantics
        (down_stride_body_stmt (S step') lb ub body) (j :: env))
      (Zrange (Loop.eval_expr env (Loop.Constant 0))
        (Loop.eval_expr env (down_stride_count_expr (S step') lb ub)))
      mem1 mem2).
    rewrite (down_stride_count_expr_correct (S step') lb ub env ltac:(lia)).
    exact Hfull.
Qed.

End LoopStride.
