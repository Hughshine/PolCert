Require Import Bool.
Require Import List.
Require Import Lia.
Require Import ZArith.
Import ListNotations.

Require Import Misc.
Require Import PolIRs.
Require Import LoopCleanup.

Module LoopSingletonCleanup (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Loop := PolIRs.Loop.
Module BaseCleanup := LoopCleanup PolIRs.

Fixpoint expr_eqb (e1 e2: Loop.expr) : bool :=
  match e1, e2 with
  | Loop.Constant z1, Loop.Constant z2 => Z.eqb z1 z2
  | Loop.Sum a1 b1, Loop.Sum a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | Loop.Mult k1 e1, Loop.Mult k2 e2 => Z.eqb k1 k2 && expr_eqb e1 e2
  | Loop.Div e1 k1, Loop.Div e2 k2 => expr_eqb e1 e2 && Z.eqb k1 k2
  | Loop.Mod e1 k1, Loop.Mod e2 k2 => expr_eqb e1 e2 && Z.eqb k1 k2
  | Loop.Var n1, Loop.Var n2 => Nat.eqb n1 n2
  | Loop.Max a1 b1, Loop.Max a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | Loop.Min a1 b1, Loop.Min a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | _, _ => false
  end.

Lemma expr_eqb_correct :
  forall e1 e2,
    expr_eqb e1 e2 = true ->
    forall env, Loop.eval_expr env e1 = Loop.eval_expr env e2.
Proof.
  induction e1; destruct e2; simpl; try discriminate; intros Heq env;
    try reflexivity.
  - apply Z.eqb_eq in Heq. subst. reflexivity.
  - apply andb_true_iff in Heq as [Ha Hb].
    rewrite (IHe1_1 _ Ha env), (IHe1_2 _ Hb env). reflexivity.
  - apply andb_true_iff in Heq as [Hk He].
    apply Z.eqb_eq in Hk. subst.
    rewrite (IHe1 _ He env). reflexivity.
  - apply andb_true_iff in Heq as [He Hk].
    apply Z.eqb_eq in Hk. subst.
    rewrite (IHe1 _ He env). reflexivity.
  - apply andb_true_iff in Heq as [He Hk].
    apply Z.eqb_eq in Hk. subst.
    rewrite (IHe1 _ He env). reflexivity.
  - apply Nat.eqb_eq in Heq. subst. reflexivity.
  - apply andb_true_iff in Heq as [Ha Hb].
    rewrite (IHe1_1 _ Ha env), (IHe1_2 _ Hb env). reflexivity.
  - apply andb_true_iff in Heq as [Ha Hb].
    rewrite (IHe1_1 _ Ha env), (IHe1_2 _ Hb env). reflexivity.
Qed.

Fixpoint lift_expr (e: Loop.expr) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant c
  | Loop.Sum e1 e2 => Loop.Sum (lift_expr e1) (lift_expr e2)
  | Loop.Mult k e1 => Loop.Mult k (lift_expr e1)
  | Loop.Div e1 k => Loop.Div (lift_expr e1) k
  | Loop.Mod e1 k => Loop.Mod (lift_expr e1) k
  | Loop.Var n => Loop.Var (S n)
  | Loop.Max e1 e2 => Loop.Max (lift_expr e1) (lift_expr e2)
  | Loop.Min e1 e2 => Loop.Min (lift_expr e1) (lift_expr e2)
  end.

Fixpoint subst_expr_at (k: nat) (rep: Loop.expr) (e: Loop.expr) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant c
  | Loop.Sum e1 e2 => Loop.Sum (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | Loop.Mult n e1 => Loop.Mult n (subst_expr_at k rep e1)
  | Loop.Div e1 n => Loop.Div (subst_expr_at k rep e1) n
  | Loop.Mod e1 n => Loop.Mod (subst_expr_at k rep e1) n
  | Loop.Var n =>
      if Nat.ltb n k then Loop.Var n
      else if Nat.eqb n k then rep
      else Loop.Var (Nat.pred n)
  | Loop.Max e1 e2 => Loop.Max (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | Loop.Min e1 e2 => Loop.Min (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  end.

Fixpoint subst_test_at (k: nat) (rep: Loop.expr) (t: Loop.test) : Loop.test :=
  match t with
  | Loop.LE e1 e2 => Loop.LE (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | Loop.EQ e1 e2 => Loop.EQ (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | Loop.And t1 t2 => Loop.And (subst_test_at k rep t1) (subst_test_at k rep t2)
  | Loop.Or t1 t2 => Loop.Or (subst_test_at k rep t1) (subst_test_at k rep t2)
  | Loop.Not t1 => Loop.Not (subst_test_at k rep t1)
  | Loop.TConstantTest b => Loop.TConstantTest b
  end.

Fixpoint subst_stmt_at (k: nat) (rep: Loop.expr) (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      Loop.Loop
        (subst_expr_at k rep lb)
        (subst_expr_at k rep ub)
        (subst_stmt_at (S k) (lift_expr rep) body)
  | Loop.Instr i es => Loop.Instr i (map (subst_expr_at k rep) es)
  | Loop.Seq sts => Loop.Seq (subst_stmt_list_at k rep sts)
  | Loop.Guard t body => Loop.Guard (subst_test_at k rep t) (subst_stmt_at k rep body)
  end
with subst_stmt_list_at (k: nat) (rep: Loop.expr) (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' => Loop.SCons (subst_stmt_at k rep st) (subst_stmt_list_at k rep sts')
  end.

Lemma nth_insert_middle :
  forall (A: Type) pre suf (x d: A),
    nth (length pre) (pre ++ x :: suf) d = x.
Proof.
  induction pre as [|a pre IH]; intros suf x d; simpl; auto.
Qed.

Lemma nth_insert_before :
  forall (A: Type) pre suf (x d: A) n,
    (n < length pre)%nat ->
    nth n (pre ++ x :: suf) d = nth n (pre ++ suf) d.
Proof.
  induction pre as [|a pre IH]; intros suf x d n Hlt; simpl in *; [lia|].
  destruct n; simpl; auto.
  apply IH. lia.
Qed.

Lemma nth_insert_after :
  forall (A: Type) pre suf (x d: A) n,
    (length pre < n)%nat ->
    nth n (pre ++ x :: suf) d = nth (Nat.pred n) (pre ++ suf) d.
Proof.
  induction pre as [|a pre IH]; intros suf x d n Hlt; simpl in *.
  - destruct n; [lia|]. reflexivity.
  - destruct n as [|n']; [lia|].
    destruct n' as [|m]; [lia|].
    simpl. apply IH. lia.
Qed.

Lemma lift_expr_correct :
  forall env x e,
    Loop.eval_expr (x :: env) (lift_expr e) = Loop.eval_expr env e.
Proof.
  induction e; simpl; intros; try reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma subst_expr_at_correct :
  forall pre suf rep e,
    Loop.eval_expr (pre ++ suf) (subst_expr_at (length pre) rep e) =
    Loop.eval_expr (pre ++ Loop.eval_expr (pre ++ suf) rep :: suf) e.
Proof.
  induction e; intros; simpl; try reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - remember (Nat.ltb n (length pre)) as bl eqn:Hlt.
    destruct bl.
    + symmetry in Hlt. apply Nat.ltb_lt in Hlt.
      rewrite nth_insert_before; auto.
    + remember (Nat.eqb n (length pre)) as beq eqn:Heq.
      destruct beq.
      * symmetry in Heq. apply Nat.eqb_eq in Heq. subst.
        rewrite nth_insert_middle. reflexivity.
      * symmetry in Heq. apply Nat.eqb_neq in Heq.
        symmetry in Hlt. apply Nat.ltb_ge in Hlt.
        assert ((length pre < n)%nat) by lia.
        rewrite nth_insert_after; auto.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma subst_expr_list_at_correct :
  forall pre suf rep es,
    map (Loop.eval_expr (pre ++ suf)) (map (subst_expr_at (length pre) rep) es) =
    map (Loop.eval_expr (pre ++ Loop.eval_expr (pre ++ suf) rep :: suf)) es.
Proof.
  intros pre suf rep es.
  rewrite map_map.
  apply map_ext.
  intro e.
  apply subst_expr_at_correct.
Qed.

Lemma subst_test_at_correct :
  forall pre suf rep t,
    Loop.eval_test (pre ++ suf) (subst_test_at (length pre) rep t) =
    Loop.eval_test (pre ++ Loop.eval_expr (pre ++ suf) rep :: suf) t.
Proof.
  induction t; intros; simpl; try reflexivity.
  - rewrite !subst_expr_at_correct. reflexivity.
  - rewrite !subst_expr_at_correct. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Scheme stmt_ind_mut := Induction for Loop.stmt Sort Prop
with stmt_list_ind_mut := Induction for Loop.stmt_list Sort Prop.
Combined Scheme stmt_stmt_list_ind from stmt_ind_mut, stmt_list_ind_mut.

Theorem subst_stmt_at_correct :
  (forall st pre suf rep mem1 mem2,
      Loop.loop_semantics (subst_stmt_at (length pre) rep st) (pre ++ suf) mem1 mem2 <->
      Loop.loop_semantics st (pre ++ Loop.eval_expr (pre ++ suf) rep :: suf) mem1 mem2)
  /\
  (forall sts pre suf rep mem1 mem2,
      Loop.loop_semantics (Loop.Seq (subst_stmt_list_at (length pre) rep sts)) (pre ++ suf) mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) (pre ++ Loop.eval_expr (pre ++ suf) rep :: suf) mem1 mem2).
Proof.
  apply stmt_stmt_list_ind; intros; simpl.
  - split; intros Hsem.
    + inversion_clear Hsem.
      rewrite !subst_expr_at_correct in H0.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      specialize (H (x :: pre) suf (lift_expr rep) mem3 mem4).
      change ((x :: pre) ++ suf) with (x :: pre ++ suf) in H.
      apply H in Hbody.
      change ((x :: pre) ++ Loop.eval_expr (x :: pre ++ suf) (lift_expr rep) :: suf)
        with (x :: pre ++ Loop.eval_expr (x :: pre ++ suf) (lift_expr rep) :: suf) in Hbody.
      rewrite lift_expr_correct in Hbody.
      exact Hbody.
    + inversion_clear Hsem.
      rewrite <- !subst_expr_at_correct in H0.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      specialize (H (x :: pre) suf (lift_expr rep) mem3 mem4).
      change ((x :: pre) ++ suf) with (x :: pre ++ suf) in H.
      rewrite lift_expr_correct in H.
      apply <- H in Hbody.
      exact Hbody.
  - split; intros Hsem.
    + inversion Hsem; subst; clear Hsem.
      econstructor.
      rewrite subst_expr_list_at_correct in H4.
      exact H4.
    + inversion Hsem; subst; clear Hsem.
      econstructor.
      rewrite subst_expr_list_at_correct.
      exact H4.
  - split; intros Hsem.
    + apply H. exact Hsem.
    + apply <- H. exact Hsem.
  - split; intros Hsem.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue.
        -- apply H. exact Hbody.
        -- rewrite subst_test_at_correct in Heq. exact Heq.
      * apply Loop.LGuardFalse.
        rewrite subst_test_at_correct in Heq. exact Heq.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue.
        -- apply <- H. exact Hbody.
        -- rewrite subst_test_at_correct. exact Heq.
      * apply Loop.LGuardFalse.
        rewrite subst_test_at_correct. exact Heq.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem; inversion_clear Hsem.
    + apply H in H1. apply H0 in H2. econstructor; eauto.
    + apply <- H in H1. apply <- H0 in H2. econstructor; eauto.
Qed.

Lemma subst_stmt_at_semantics :
  forall st rep env mem1 mem2,
    Loop.loop_semantics (subst_stmt_at 0 rep st) env mem1 mem2 <->
    Loop.loop_semantics st (Loop.eval_expr env rep :: env) mem1 mem2.
Proof.
  intros.
  specialize (proj1 subst_stmt_at_correct st [] env rep mem1 mem2) as H.
  simpl in H. exact H.
Qed.

Lemma singleton_loop_semantics :
  forall lb ub body env mem1 mem2,
    expr_eqb ub (Loop.make_sum lb (Loop.Constant 1)) = true ->
    Loop.loop_semantics (Loop.Loop lb ub body) env mem1 mem2 <->
    Loop.loop_semantics body (Loop.eval_expr env lb :: env) mem1 mem2.
Proof.
  intros lb ub body env mem1 mem2 Heq.
  pose proof (expr_eqb_correct _ _ Heq env) as Heval.
  rewrite Loop.make_sum_correct in Heval.
  split.
  - intros H. inversion_clear H.
    rewrite Heval in H0.
    rewrite Zrange_single in H0.
    inversion_clear H0. inversion H1. congruence.
  - intros H.
    apply Loop.LLoop.
    rewrite Heval.
    rewrite Zrange_single.
    econstructor; [exact H|constructor].
Qed.

Fixpoint singleton_elim_stmt (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      let body' := singleton_elim_stmt body in
      if expr_eqb ub (Loop.make_sum lb (Loop.Constant 1))
      then subst_stmt_at 0 lb body'
      else Loop.Loop lb ub body'
  | Loop.Instr i es => Loop.Instr i es
  | Loop.Seq sts => Loop.Seq (singleton_elim_stmt_list sts)
  | Loop.Guard t body => Loop.Guard t (singleton_elim_stmt body)
  end
with singleton_elim_stmt_list (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' => Loop.SCons (singleton_elim_stmt st) (singleton_elim_stmt_list sts')
  end.

Theorem singleton_elim_stmt_correct :
  (forall st env mem1 mem2,
      Loop.loop_semantics (singleton_elim_stmt st) env mem1 mem2 <->
      Loop.loop_semantics st env mem1 mem2)
  /\
  (forall sts env mem1 mem2,
      Loop.loop_semantics (Loop.Seq (singleton_elim_stmt_list sts)) env mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2).
Proof.
  apply stmt_stmt_list_ind; intros; simpl.
  - lazymatch goal with
    | |- context[if expr_eqb ?ub (Loop.make_sum ?lb (Loop.Constant 1))
                 then subst_stmt_at 0 ?lb (singleton_elim_stmt ?body)
                 else Loop.Loop ?lb ?ub (singleton_elim_stmt ?body)] =>
        destruct (expr_eqb ub (Loop.make_sum lb (Loop.Constant 1))) eqn:Hsingle
    end.
    + split; intros Hsem.
      * apply subst_stmt_at_semantics in Hsem.
        apply H in Hsem.
        lazymatch goal with
        | |- _ =>
            eapply (proj2 (singleton_loop_semantics _ _ _ env mem1 mem2 Hsingle)); exact Hsem
        end.
      * lazymatch goal with
        | |- _ =>
            eapply (proj1 (singleton_loop_semantics _ _ _ env mem1 mem2 Hsingle)) in Hsem
        end.
        apply <- H in Hsem.
        apply subst_stmt_at_semantics. exact Hsem.
    + split; intros Hsem.
      * inversion_clear Hsem.
        apply Loop.LLoop.
        eapply Instr.IterSem.iter_semantics_map; [|exact H0].
        intros x mem3 mem4 Hx Hbody.
        apply H in Hbody. exact Hbody.
      * inversion_clear Hsem.
        apply Loop.LLoop.
        eapply Instr.IterSem.iter_semantics_map; [|exact H0].
        intros x mem3 mem4 Hx Hbody.
        apply <- H in Hbody. exact Hbody.
  - split; intros Hsem; exact Hsem.
  - split; intros Hsem.
    + apply H. exact Hsem.
    + apply <- H. exact Hsem.
  - split; intros Hsem.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue; [apply H; exact Hbody|exact Heq].
      * apply Loop.LGuardFalse. exact Heq.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue; [apply <- H; exact Hbody|exact Heq].
      * apply Loop.LGuardFalse. exact Heq.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem; inversion_clear Hsem.
    + apply H in H1. apply H0 in H2. econstructor; eauto.
    + apply <- H in H1. apply <- H0 in H2. econstructor; eauto.
Qed.

Lemma singleton_elim_stmt_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics (singleton_elim_stmt st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof. intros. apply singleton_elim_stmt_correct. Qed.

Definition cleanup_stmt_pass (st: Loop.stmt) : Loop.stmt :=
  BaseCleanup.cleanup_stmt
    (BaseCleanup.simplify_stmt
      (singleton_elim_stmt
        (BaseCleanup.cleanup_stmt
          (BaseCleanup.simplify_stmt st)))).

Definition cleanup (prog: Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (cleanup_stmt_pass st, ctxt, vars).

Lemma cleanup_stmt_pass_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics (cleanup_stmt_pass st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof.
  intros st env mem1 mem2.
  unfold cleanup_stmt_pass.
  rewrite BaseCleanup.cleanup_stmt_semantics.
  rewrite BaseCleanup.simplify_stmt_semantics.
  rewrite singleton_elim_stmt_semantics.
  rewrite BaseCleanup.cleanup_stmt_semantics.
  apply BaseCleanup.simplify_stmt_semantics.
Qed.

Theorem cleanup_correct :
  forall prog mem1 mem2,
    Loop.semantics (cleanup prog) mem1 mem2 <->
    Loop.semantics prog mem1 mem2.
Proof.
  intros prog mem1 mem2.
  destruct prog as [[st ctxt] vars]; simpl.
  split; intros Hsem; inversion_clear Hsem; subst.
  - inversion H; subst.
    econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply cleanup_stmt_pass_semantics. exact H3.
  - inversion H; subst.
    econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply cleanup_stmt_pass_semantics. exact H3.
Qed.

End LoopSingletonCleanup.
