Require Import List.
Require Import Bool.
Require Import Lia.
Require Import ZArith.
Import ListNotations.

Require Import Misc.
Require Import PolIRs.
Require Import LoopSingletonCleanup.

Module LoopUnroll (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Loop := PolIRs.Loop.
Module Subst := LoopSingletonCleanup PolIRs.

Definition succ_expr (e: Loop.expr) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant (c + 1)
  | _ => Loop.Sum e (Loop.Constant 1)
  end.

Lemma expr_eqb_refl :
  forall e,
    Subst.expr_eqb e e = true.
Proof.
  induction e; simpl.
  - apply Z.eqb_refl.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite Z.eqb_refl, IHe. reflexivity.
  - rewrite IHe, Z.eqb_refl. reflexivity.
  - rewrite IHe, Z.eqb_refl. reflexivity.
  - apply Nat.eqb_refl.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

Fixpoint prefix_peel_steps (fuel: nat) (cur: Loop.expr) : list Loop.expr :=
  match fuel with
  | O => nil
  | S fuel' =>
      cur :: prefix_peel_steps fuel' (succ_expr cur)
  end.

Fixpoint check_peel_steps (expected: Loop.expr) (steps: list Loop.expr) : bool :=
  match steps with
  | nil => true
  | step :: steps' =>
      Subst.expr_eqb step expected &&
      check_peel_steps (succ_expr expected) steps'
  end.

Fixpoint lower_peel_steps
    (expected ub: Loop.expr) (body: Loop.stmt) (steps: list Loop.expr)
    : Loop.stmt_list :=
  match steps with
  | nil =>
      Loop.SCons (Loop.Loop expected ub body) Loop.SNil
  | step :: steps' =>
      Loop.SCons
        (Loop.Guard
           (Loop.LE (succ_expr step) ub)
           (Subst.subst_stmt_at 0 step body))
        (lower_peel_steps (succ_expr expected) ub body steps')
  end.

Inductive peel_plan : Type :=
| PeelPrefix : list Loop.expr -> peel_plan.

Definition prefix_peel_plan (fuel: nat) (cur: Loop.expr) : peel_plan :=
  PeelPrefix (prefix_peel_steps fuel cur).

Definition check_peel_plan
    (cur _ub: Loop.expr) (plan: peel_plan) : bool :=
  match plan with
  | PeelPrefix steps => check_peel_steps cur steps
  end.

Definition lower_peel_plan_stmt_list
    (plan: peel_plan) (cur ub: Loop.expr) (body: Loop.stmt) : Loop.stmt_list :=
  match plan with
  | PeelPrefix steps => lower_peel_steps cur ub body steps
  end.

Definition peel_unroll_stmt_list
    (fuel: nat) (cur ub: Loop.expr) (body: Loop.stmt) : Loop.stmt_list :=
  lower_peel_plan_stmt_list (prefix_peel_plan fuel cur) cur ub body.

Lemma prefix_peel_steps_checked :
  forall fuel cur,
    check_peel_steps cur (prefix_peel_steps fuel cur) = true.
Proof.
  induction fuel as [|fuel IH]; intros cur; simpl.
  - reflexivity.
  - rewrite expr_eqb_refl. apply IH.
Qed.

Example check_peel_steps_accepts_prefix_example :
  check_peel_steps
    (Loop.Var 0)
    (prefix_peel_steps 2 (Loop.Var 0)) = true.
Proof. reflexivity. Qed.

Example check_peel_steps_rejects_skipped_prefix_example :
  check_peel_steps
    (Loop.Var 0)
    [succ_expr (Loop.Var 0)] = false.
Proof. reflexivity. Qed.

Fixpoint seq_values (vals: list Z) (body: Loop.stmt) : Loop.stmt_list :=
  match vals with
  | nil => Loop.SNil
  | v :: vals' =>
      Loop.SCons
        (Subst.subst_stmt_at 0 (Loop.Constant v) body)
        (seq_values vals' body)
  end.

Lemma seq_values_semantics :
  forall vals body env mem1 mem2,
    Loop.loop_semantics (Loop.Seq (seq_values vals body)) env mem1 mem2 <->
    Instr.IterSem.iter_semantics
      (fun x => Loop.loop_semantics body (x :: env))
      vals
      mem1
      mem2.
Proof.
  induction vals as [|v vals IH]; intros body env mem1 mem2; simpl.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem.
    + inversion_clear Hsem.
      match goal with
      | Hhead: Loop.loop_semantics
          (Subst.subst_stmt_at 0 (Loop.Constant v) body) env _ _,
        Htail: Loop.loop_semantics (Loop.Seq (seq_values vals body)) env _ _ |- _ =>
          apply Subst.subst_stmt_at_semantics in Hhead;
          simpl in Hhead;
          apply IH in Htail;
          econstructor; eauto
      end.
    + inversion_clear Hsem.
      match goal with
      | Hhead: Loop.loop_semantics body (v :: env) _ _,
        Htail: Instr.IterSem.iter_semantics
          (fun x : Z => Loop.loop_semantics body (x :: env)) vals _ _ |- _ =>
          eapply Loop.LSeq;
          [ apply Subst.subst_stmt_at_semantics; simpl; exact Hhead
          | apply IH; exact Htail ]
      end.
Qed.

Lemma seq_single_loop_semantics :
  forall cur ub body env mem1 mem2,
    Loop.loop_semantics
      (Loop.Seq (Loop.SCons (Loop.Loop cur ub body) Loop.SNil))
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  intros cur ub body env mem1 mem2.
  split; intros Hsem.
  - inversion_clear Hsem.
    inversion H0; subst; clear H0.
    exact H.
  - eapply Loop.LSeq.
    + exact Hsem.
    + constructor.
Qed.

Lemma succ_expr_correct :
  forall env e,
    Loop.eval_expr env (succ_expr e) = Loop.eval_expr env e + 1.
Proof.
  intros env e. destruct e; simpl; lia.
Qed.

Lemma checked_peel_steps_semantics :
  forall steps cur ub body env mem1 mem2,
    check_peel_steps cur steps = true ->
    Loop.loop_semantics
      (Loop.Seq (lower_peel_steps cur ub body steps))
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  induction steps as [|step steps IH]; intros cur ub body env mem1 mem2 Hcheck; simpl in *.
  - apply seq_single_loop_semantics.
  - apply andb_true_iff in Hcheck as [Hstep Hrest].
    pose proof (Subst.expr_eqb_correct _ _ Hstep env) as Hstep_eval.
    remember (Loop.eval_expr env cur) as curv.
    remember (Loop.eval_expr env ub) as ubv.
    assert (Htest_true :
      Loop.eval_test env (Loop.LE (succ_expr step) ub) = true <->
      curv < ubv).
    {
      subst curv ubv. simpl. rewrite succ_expr_correct. rewrite Hstep_eval.
      rewrite Z.leb_le. lia.
    }
    assert (Htest_false :
      Loop.eval_test env (Loop.LE (succ_expr step) ub) = false <->
      curv >= ubv).
    {
      subst curv ubv. simpl. rewrite succ_expr_correct. rewrite Hstep_eval.
      rewrite Z.leb_gt. lia.
    }
    split; intros Hsem.
    + inversion_clear Hsem.
      eapply (proj1 (IH (succ_expr cur) ub body env _ _ Hrest)) in H0.
      rename H0 into Htail.
      destruct (Z_lt_ge_dec curv ubv) as [Hlt|Hge].
      * apply Loop.LLoop.
        rewrite <- Heqcurv, <- Hequbv.
        rewrite Zrange_begin by lia.
        inversion_clear H as [| | | ? ? ? ? ? Hbody Hguard | ? ? ? ? Hguard |].
        -- apply Subst.subst_stmt_at_semantics in Hbody.
           simpl in Hbody.
           rewrite Hstep_eval in Hbody.
           inversion Htail; subst; clear Htail;
           simpl in *;
           try rewrite succ_expr_correct in *;
           try rewrite <- Heqcurv in *;
           try rewrite <- Hequbv in *;
           econstructor; eauto.
        -- apply Htest_false in Hguard. lia.
      * inversion_clear H as [| | | ? ? ? ? ? Hbody Hguard | ? ? ? ? Hguard |].
        -- apply Htest_true in Hguard. lia.
        -- inversion Htail; subst; clear Htail.
           simpl in *;
           try rewrite succ_expr_correct in *;
           try rewrite <- Heqcurv in *;
           try rewrite <- Hequbv in *;
           try rewrite Zrange_empty in * by lia;
           repeat match goal with
           | Hiter: Instr.IterSem.iter_semantics _ nil _ _ |- _ =>
               inversion Hiter; subst; clear Hiter
           end.
           apply Loop.LLoop.
           simpl.
           rewrite Zrange_empty by lia.
           constructor.
    + inversion_clear Hsem.
      destruct (Z_lt_ge_dec curv ubv) as [Hlt|Hge].
      * match goal with
        | Hiter: PolIRs.Instr.IterSem.iter_semantics
            (fun x : Z => Loop.loop_semantics body (x :: env))
            (Zrange _ _) _ _ |- _ =>
            rewrite <- Heqcurv, <- Hequbv in Hiter;
            rewrite Zrange_begin in Hiter by lia;
            inversion_clear Hiter
        end.
        eapply Loop.LSeq.
        -- apply Loop.LGuardTrue.
           ++ apply Subst.subst_stmt_at_semantics.
              simpl.
              rewrite Hstep_eval.
              match goal with
              | Hbody: Loop.loop_semantics body (curv :: env) _ _ |- _ =>
                  exact Hbody
              end.
           ++ apply Htest_true. exact Hlt.
        -- eapply (proj2 (IH (succ_expr cur) ub body env _ _ Hrest)).
           apply Loop.LLoop.
           simpl. rewrite succ_expr_correct.
           rewrite <- Heqcurv, <- Hequbv.
           match goal with
           | Htail: Instr.IterSem.iter_semantics _ (Zrange (curv + 1) ubv) _ _ |- _ =>
               exact Htail
           end.
      * match goal with
        | Hiter: PolIRs.Instr.IterSem.iter_semantics
            (fun x : Z => Loop.loop_semantics body (x :: env))
            (Zrange _ _) _ _ |- _ =>
            rewrite <- Heqcurv, <- Hequbv in Hiter;
            rewrite Zrange_empty in Hiter by lia;
            inversion Hiter; subst; clear Hiter
        end.
        eapply Loop.LSeq.
        -- apply Loop.LGuardFalse.
           apply Htest_false. exact Hge.
        -- eapply (proj2 (IH (succ_expr cur) ub body env _ _ Hrest)).
           apply Loop.LLoop.
           simpl. rewrite succ_expr_correct.
           rewrite Zrange_empty by lia.
           constructor.
Qed.

Lemma checked_peel_plan_stmt_list_semantics :
  forall plan cur ub body env mem1 mem2,
    check_peel_plan cur ub plan = true ->
    Loop.loop_semantics
      (Loop.Seq (lower_peel_plan_stmt_list plan cur ub body))
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  intros [steps] cur ub body env mem1 mem2 Hcheck.
  simpl in *.
  apply checked_peel_steps_semantics. exact Hcheck.
Qed.

Definition checked_lower_peel_plan_stmt
    (plan: peel_plan) (cur ub: Loop.expr) (body: Loop.stmt) : option Loop.stmt :=
  if check_peel_plan cur ub plan
  then Some (Loop.Seq (lower_peel_plan_stmt_list plan cur ub body))
  else None.

Theorem checked_lower_peel_plan_stmt_correct :
  forall plan cur ub body st env mem1 mem2,
    checked_lower_peel_plan_stmt plan cur ub body = Some st ->
    Loop.loop_semantics st env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  intros plan cur ub body st env mem1 mem2 Hlower.
  unfold checked_lower_peel_plan_stmt in Hlower.
  destruct (check_peel_plan cur ub plan) eqn:Hcheck; try discriminate.
  inversion Hlower; subst; clear Hlower.
  apply checked_peel_plan_stmt_list_semantics. exact Hcheck.
Qed.

Lemma peel_unroll_stmt_list_semantics :
  forall fuel cur ub body env mem1 mem2,
    Loop.loop_semantics
      (Loop.Seq (peel_unroll_stmt_list fuel cur ub body))
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  intros fuel cur ub body env mem1 mem2.
  unfold peel_unroll_stmt_list.
  apply checked_peel_plan_stmt_list_semantics.
  unfold check_peel_plan, prefix_peel_plan.
  apply prefix_peel_steps_checked.
Qed.

Fixpoint const_unroll_stmt (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop (Loop.Constant lb) (Loop.Constant ub) body =>
      Loop.Seq (seq_values (Zrange lb ub) (const_unroll_stmt body))
  | Loop.Loop lb ub body =>
      Loop.Loop lb ub (const_unroll_stmt body)
  | Loop.Instr i es => Loop.Instr i es
  | Loop.Seq sts => Loop.Seq (const_unroll_stmt_list sts)
  | Loop.Guard t body => Loop.Guard t (const_unroll_stmt body)
  end
with const_unroll_stmt_list (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' =>
      Loop.SCons (const_unroll_stmt st) (const_unroll_stmt_list sts')
  end.

Fixpoint const_unroll_stmt_changed (st: Loop.stmt) : bool :=
  match st with
  | Loop.Loop (Loop.Constant _) (Loop.Constant _) _ => true
  | Loop.Loop _ _ body => const_unroll_stmt_changed body
  | Loop.Instr _ _ => false
  | Loop.Seq sts => const_unroll_stmt_list_changed sts
  | Loop.Guard _ body => const_unroll_stmt_changed body
  end
with const_unroll_stmt_list_changed (sts: Loop.stmt_list) : bool :=
  match sts with
  | Loop.SNil => false
  | Loop.SCons st sts' =>
      orb (const_unroll_stmt_changed st) (const_unroll_stmt_list_changed sts')
  end.

Fixpoint peel_unroll_stmt (fuel: nat) (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      Loop.Seq (peel_unroll_stmt_list fuel lb ub body)
  | Loop.Instr i es => Loop.Instr i es
  | Loop.Seq sts => Loop.Seq (peel_unroll_stmt_list_rec fuel sts)
  | Loop.Guard t body => Loop.Guard t (peel_unroll_stmt fuel body)
  end
with peel_unroll_stmt_list_rec (fuel: nat) (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' =>
      Loop.SCons (peel_unroll_stmt fuel st) (peel_unroll_stmt_list_rec fuel sts')
  end.

Fixpoint peel_unroll_stmt_changed (fuel: nat) (st: Loop.stmt) : bool :=
  match fuel with
  | O => false
  | S _ =>
      match st with
      | Loop.Loop _ _ _ => true
      | Loop.Instr _ _ => false
      | Loop.Seq sts => peel_unroll_stmt_list_changed fuel sts
      | Loop.Guard _ body => peel_unroll_stmt_changed fuel body
      end
  end
with peel_unroll_stmt_list_changed (fuel: nat) (sts: Loop.stmt_list) : bool :=
  match sts with
  | Loop.SNil => false
  | Loop.SCons st sts' =>
      orb (peel_unroll_stmt_changed fuel st) (peel_unroll_stmt_list_changed fuel sts')
  end.

Scheme stmt_ind_mut := Induction for Loop.stmt Sort Prop
with stmt_list_ind_mut := Induction for Loop.stmt_list Sort Prop.
Combined Scheme stmt_stmt_list_ind from stmt_ind_mut, stmt_list_ind_mut.

Theorem const_unroll_stmt_correct :
  (forall st env mem1 mem2,
      Loop.loop_semantics (const_unroll_stmt st) env mem1 mem2 <->
      Loop.loop_semantics st env mem1 mem2)
  /\
  (forall sts env mem1 mem2,
      Loop.loop_semantics (Loop.Seq (const_unroll_stmt_list sts)) env mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2).
Proof.
  apply stmt_stmt_list_ind; intros; simpl.
  - destruct e; destruct e0; try solve [
      split; intros Hsem; inversion_clear Hsem;
      apply Loop.LLoop;
      match goal with
      | Hiter: Instr.IterSem.iter_semantics _ (Zrange _ _) _ _ |- _ =>
          eapply Instr.IterSem.iter_semantics_map; [|exact Hiter]
      end;
      intros x mem3 mem4 Hx Hbody;
      [apply H | apply <- H]; exact Hbody
    ].
    split; intros Hsem.
    + apply seq_values_semantics in Hsem.
      apply Loop.LLoop.
      match goal with
      | Hiter: Instr.IterSem.iter_semantics _ (Zrange _ _) _ _ |- _ =>
          eapply Instr.IterSem.iter_semantics_map; [|exact Hiter]
      end.
      intros x mem3 mem4 Hx Hbody.
      apply H. exact Hbody.
    + inversion_clear Hsem.
      apply seq_values_semantics.
      match goal with
      | Hiter: Instr.IterSem.iter_semantics _ (Zrange _ _) _ _ |- _ =>
          eapply Instr.IterSem.iter_semantics_map; [|exact Hiter]
      end.
      intros x mem3 mem4 Hx Hbody.
      apply <- H. exact Hbody.
    all: try solve [eauto].
  - split; intros Hsem; exact Hsem.
  - split; intros Hsem.
    + apply H. exact Hsem.
    + apply <- H. exact Hsem.
  - split; intros Hsem; inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
    + apply Loop.LGuardTrue; [apply H; exact Hbody|exact Heq].
    + apply Loop.LGuardFalse. exact Heq.
    + apply Loop.LGuardTrue; [apply <- H; exact Hbody|exact Heq].
    + apply Loop.LGuardFalse. exact Heq.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem; inversion_clear Hsem.
    + apply H in H1. apply H0 in H2. econstructor; eauto.
    + apply <- H in H1. apply <- H0 in H2. econstructor; eauto.
Qed.

Theorem peel_unroll_stmt_correct :
  forall fuel,
  (forall st env mem1 mem2,
      Loop.loop_semantics (peel_unroll_stmt fuel st) env mem1 mem2 <->
      Loop.loop_semantics st env mem1 mem2)
  /\
  (forall sts env mem1 mem2,
      Loop.loop_semantics (Loop.Seq (peel_unroll_stmt_list_rec fuel sts)) env mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2).
Proof.
  intro fuel.
  apply stmt_stmt_list_ind; intros; simpl.
  - split; intros Hsem.
    + apply peel_unroll_stmt_list_semantics in Hsem.
      exact Hsem.
    + inversion_clear Hsem.
      apply peel_unroll_stmt_list_semantics.
      apply Loop.LLoop.
      exact H0.
  - split; intros Hsem; exact Hsem.
  - split; intros Hsem.
    + apply H. exact Hsem.
    + apply <- H. exact Hsem.
  - split; intros Hsem; inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
    + apply Loop.LGuardTrue; [apply H; exact Hbody|exact Heq].
    + apply Loop.LGuardFalse. exact Heq.
    + apply Loop.LGuardTrue; [apply <- H; exact Hbody|exact Heq].
    + apply Loop.LGuardFalse. exact Heq.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem; inversion_clear Hsem.
    + apply H in H1. apply H0 in H2. econstructor; eauto.
    + apply <- H in H1. apply <- H0 in H2. econstructor; eauto.
Qed.

Lemma peel_unroll_stmt_semantics :
  forall fuel st env mem1 mem2,
    Loop.loop_semantics (peel_unroll_stmt fuel st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof. intros. apply peel_unroll_stmt_correct. Qed.

Lemma const_unroll_stmt_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics (const_unroll_stmt st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof. intros. apply const_unroll_stmt_correct. Qed.

Definition const_unroll (prog: Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (const_unroll_stmt st, ctxt, vars).

Definition const_unroll_changed (prog: Loop.t) : bool :=
  let '(st, _, _) := prog in
  const_unroll_stmt_changed st.

Definition peel_unroll (fuel: nat) (prog: Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (peel_unroll_stmt fuel st, ctxt, vars).

Definition peel_unroll_changed (fuel: nat) (prog: Loop.t) : bool :=
  let '(st, _, _) := prog in
  peel_unroll_stmt_changed fuel st.

Theorem const_unroll_correct :
  forall prog mem1 mem2,
    Loop.semantics (const_unroll prog) mem1 mem2 <->
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
    + eapply const_unroll_stmt_semantics. exact H3.
  - inversion H; subst.
    econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply const_unroll_stmt_semantics. exact H3.
Qed.

Theorem peel_unroll_correct :
  forall fuel prog mem1 mem2,
    Loop.semantics (peel_unroll fuel prog) mem1 mem2 <->
    Loop.semantics prog mem1 mem2.
Proof.
  intros fuel prog mem1 mem2.
  destruct prog as [[st ctxt] vars]; simpl.
  split; intros Hsem; inversion_clear Hsem; subst.
  - inversion H; subst.
    econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply peel_unroll_stmt_semantics. exact H3.
  - inversion H; subst.
    econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply peel_unroll_stmt_semantics. exact H3.
Qed.

End LoopUnroll.
