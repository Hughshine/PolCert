Require Import Bool.
Require Import List.
Require Import ZArith.
Import ListNotations.

Require Import Misc.
Require Import ImpureAlarmConfig.
Require Import PolIRs.

Module LoopCleanup (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Loop := PolIRs.Loop.

Fixpoint simpl_expr (e: Loop.expr) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant c
  | Loop.Sum e1 e2 => Loop.make_sum (simpl_expr e1) (simpl_expr e2)
  | Loop.Mult k e1 => Loop.make_mult k (simpl_expr e1)
  | Loop.Div e1 k => Loop.make_div (simpl_expr e1) k
  | Loop.Mod e1 k => Loop.make_mod (simpl_expr e1) k
  | Loop.Var n => Loop.Var n
  | Loop.Max e1 e2 => Loop.make_max (simpl_expr e1) (simpl_expr e2)
  | Loop.Min e1 e2 => Loop.make_min (simpl_expr e1) (simpl_expr e2)
  end.

Fixpoint simpl_test (t: Loop.test) : Loop.test :=
  match t with
  | Loop.LE e1 e2 => Loop.make_le (simpl_expr e1) (simpl_expr e2)
  | Loop.EQ e1 e2 => Loop.make_eq (simpl_expr e1) (simpl_expr e2)
  | Loop.And t1 t2 => Loop.make_and (simpl_test t1) (simpl_test t2)
  | Loop.Or t1 t2 => Loop.make_or (simpl_test t1) (simpl_test t2)
  | Loop.Not t1 => Loop.make_not (simpl_test t1)
  | Loop.TConstantTest b => Loop.TConstantTest b
  end.

Lemma simpl_expr_correct :
  forall env e,
    Loop.eval_expr env (simpl_expr e) = Loop.eval_expr env e.
Proof.
  induction e; simpl; intros; try reflexivity.
  - rewrite Loop.make_sum_correct, IHe1, IHe2. reflexivity.
  - rewrite Loop.make_mult_correct, IHe. reflexivity.
  - rewrite Loop.make_div_correct, IHe. reflexivity.
  - rewrite Loop.make_mod_correct, IHe. reflexivity.
  - rewrite Loop.make_max_correct, IHe1, IHe2. reflexivity.
  - rewrite Loop.make_min_correct, IHe1, IHe2. reflexivity.
Qed.

Lemma simpl_expr_list_correct :
  forall env es,
    map (Loop.eval_expr env) (map simpl_expr es) = map (Loop.eval_expr env) es.
Proof.
  intros env es.
  rewrite map_map.
  apply map_ext.
  intro e.
  apply simpl_expr_correct.
Qed.

Lemma simpl_test_correct :
  forall env t,
    Loop.eval_test env (simpl_test t) = Loop.eval_test env t.
Proof.
  induction t; simpl; intros; try reflexivity.
  - rewrite Loop.make_le_correct, !simpl_expr_correct. reflexivity.
  - rewrite Loop.make_eq_correct, !simpl_expr_correct. reflexivity.
  - rewrite Loop.make_and_correct, IHt1, IHt2. reflexivity.
  - rewrite Loop.make_or_correct, IHt1, IHt2. reflexivity.
  - rewrite Loop.make_not_correct, IHt. reflexivity.
Qed.

Definition make_stmt_from_list (sts: Loop.stmt_list) : Loop.stmt :=
  match sts with
  | Loop.SNil => Loop.Seq Loop.SNil
  | Loop.SCons st Loop.SNil => st
  | _ => Loop.Seq sts
  end.

Fixpoint simplify_stmt (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      Loop.Loop (simpl_expr lb) (simpl_expr ub) (simplify_stmt body)
  | Loop.Instr i es =>
      Loop.Instr i (map simpl_expr es)
  | Loop.Seq sts =>
      Loop.Seq (simplify_stmt_list sts)
  | Loop.Guard t body =>
      Loop.Guard (simpl_test t) (simplify_stmt body)
  end
with simplify_stmt_list (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' => Loop.SCons (simplify_stmt st) (simplify_stmt_list sts')
  end.

Fixpoint cleanup_stmt (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      Loop.Loop lb ub (cleanup_stmt body)
  | Loop.Instr i es =>
      Loop.Instr i es
  | Loop.Seq sts =>
      make_stmt_from_list (cleanup_stmt_list sts)
  | Loop.Guard t body =>
      Loop.make_guard t (cleanup_stmt body)
  end
with cleanup_stmt_list (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' =>
      match cleanup_stmt st with
      | Loop.Seq Loop.SNil => cleanup_stmt_list sts'
      | st' => Loop.SCons st' (cleanup_stmt_list sts')
      end
  end.

Definition cleanup_stmt_pass (st: Loop.stmt) : Loop.stmt :=
  cleanup_stmt (simplify_stmt st).

Definition cleanup (prog: Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (cleanup_stmt_pass st, ctxt, vars).

Fixpoint no_skip_stmt_list (sts: Loop.stmt_list) : Prop :=
  match sts with
  | Loop.SNil => True
  | Loop.SCons st sts' => st <> Loop.Seq Loop.SNil /\ no_skip_stmt_list sts'
  end.

Lemma cleanup_stmt_list_no_skip :
  forall sts,
    no_skip_stmt_list (cleanup_stmt_list sts).
Proof.
  induction sts as [|st sts IH]; simpl.
  - exact I.
  - destruct (cleanup_stmt st) eqn:Hc.
    + split.
      * discriminate.
      * exact IH.
    + split.
      * discriminate.
      * exact IH.
    + destruct s.
      * exact IH.
      * split.
        -- discriminate.
        -- exact IH.
    + split.
      * discriminate.
      * exact IH.
Qed.

Lemma make_stmt_from_list_skip_inv :
  forall sts,
    no_skip_stmt_list sts ->
    make_stmt_from_list sts = Loop.Seq Loop.SNil ->
    sts = Loop.SNil.
Proof.
  intros sts Hnoskip Hmk.
  destruct sts as [|st sts].
  - reflexivity.
  - simpl in Hnoskip.
    destruct Hnoskip as [Hnonskip Hnoskip].
    destruct sts as [|st2 sts].
    + simpl in Hmk. exfalso. apply Hnonskip. exact Hmk.
    + simpl in Hmk. discriminate.
Qed.

Lemma make_stmt_from_list_correct :
  forall sts env mem1 mem2,
    Loop.loop_semantics (make_stmt_from_list sts) env mem1 mem2 <->
    Loop.loop_semantics (Loop.Seq sts) env mem1 mem2.
Proof.
  intros sts env mem1 mem2.
  destruct sts as [|st sts]; simpl.
  - split; intros H; inversion_clear H; constructor.
  - destruct sts as [|st2 sts]; simpl.
    + split; intros H.
      * econstructor; eauto. constructor.
      * inversion H; subst; clear H.
        repeat match goal with
               | Hnil : Loop.loop_semantics (Loop.Seq Loop.SNil) _ _ _ |- _ =>
                   inversion Hnil; subst; clear Hnil
               end.
        assumption.
    + tauto.
Qed.

Scheme stmt_ind_mut := Induction for Loop.stmt Sort Prop
with stmt_list_ind_mut := Induction for Loop.stmt_list Sort Prop.

Combined Scheme stmt_stmt_list_ind from stmt_ind_mut, stmt_list_ind_mut.

Theorem simplify_stmt_correct :
  (forall st env mem1 mem2,
      Loop.loop_semantics (simplify_stmt st) env mem1 mem2 <->
      Loop.loop_semantics st env mem1 mem2)
  /\
  (forall sts env mem1 mem2,
      Loop.loop_semantics (Loop.Seq (simplify_stmt_list sts)) env mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2).
Proof.
  apply stmt_stmt_list_ind; intros; simpl.
  - split; intros Hsem; inversion_clear Hsem.
    + rewrite !simpl_expr_correct in H0.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      apply H in Hbody. exact Hbody.
    + apply Loop.LLoop.
      rewrite !simpl_expr_correct.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      apply <- H in Hbody. exact Hbody.
  - split; intros Hsem.
    + inversion Hsem; subst; clear Hsem.
      eapply Loop.LInstr.
      rewrite simpl_expr_list_correct in H4.
      exact H4.
    + inversion Hsem; subst; clear Hsem.
      eapply Loop.LInstr.
      rewrite simpl_expr_list_correct.
      exact H4.
  - split; intros Hsem.
    + apply H. exact Hsem.
    + apply <- H. exact Hsem.
  - split; intros Hsem.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue.
        -- apply H. exact Hbody.
        -- rewrite simpl_test_correct in Heq. exact Heq.
      * apply Loop.LGuardFalse.
        rewrite simpl_test_correct in Heq. exact Heq.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue.
        -- apply <- H. exact Hbody.
        -- rewrite simpl_test_correct. exact Heq.
      * apply Loop.LGuardFalse.
        rewrite simpl_test_correct. exact Heq.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem; inversion_clear Hsem.
    + apply H in H1. apply H0 in H2. econstructor; eauto.
    + apply <- H in H1. apply <- H0 in H2. econstructor; eauto.
Qed.

Lemma simplify_stmt_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics (simplify_stmt st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof. intros. apply simplify_stmt_correct. Qed.

Lemma simplify_stmt_list_semantics :
  forall sts env mem1 mem2,
    Loop.loop_semantics (Loop.Seq (simplify_stmt_list sts)) env mem1 mem2 <->
    Loop.loop_semantics (Loop.Seq sts) env mem1 mem2.
Proof. intros. apply simplify_stmt_correct. Qed.

Lemma cleanup_stmt_skip_semantics :
  (forall st env mem1 mem2,
      cleanup_stmt st = Loop.Seq Loop.SNil ->
      (Loop.loop_semantics st env mem1 mem2 <-> mem1 = mem2))
  /\
  (forall sts env mem1 mem2,
      cleanup_stmt_list sts = Loop.SNil ->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2 <-> mem1 = mem2).
Proof.
  apply stmt_stmt_list_ind; intros; simpl in *.
  - discriminate.
  - discriminate.
  - destruct (cleanup_stmt_list s) eqn:Hc.
    + exact (H env mem1 mem2 eq_refl).
    + exfalso.
      pose proof (cleanup_stmt_list_no_skip s) as Hnoskip.
      rewrite Hc in Hnoskip.
      eapply make_stmt_from_list_skip_inv in H0; [|exact Hnoskip].
      discriminate.
  - destruct t; try discriminate; destruct b; simpl in *.
    + split; intros Hsem.
      * inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
        -- apply (H env mem1 mem2 H0). exact Hbody.
        -- discriminate Heq.
      * apply Loop.LGuardTrue.
        -- apply (proj2 (H env mem1 mem2 H0)). exact Hsem.
        -- reflexivity.
    + split; intros Hsem.
      * inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
        -- discriminate Heq.
        -- reflexivity.
      * subst. apply Loop.LGuardFalse. reflexivity.
  - split; intros Hsem.
    + inversion_clear Hsem. reflexivity.
    + subst. constructor.
  - destruct (cleanup_stmt s) eqn:Hc; simpl in H1; try discriminate.
    + destruct s1.
      * split; intros Hsem.
        -- inversion_clear Hsem.
           pose proof (H env mem1 mem3 eq_refl) as Hskip.
           pose proof (H0 env mem3 mem2 H1) as Htail.
           apply Hskip in H2.
           apply Htail in H3.
           congruence.
        -- subst.
           lazymatch goal with
           | |- Loop.loop_semantics (Loop.Seq (Loop.SCons _ _)) env ?m ?m =>
               eapply Loop.LSeq with (mem2 := m);
               [ apply (proj2 (H env m m eq_refl)); reflexivity
               | apply (proj2 (H0 env m m H1)); reflexivity ]
           end.
      * discriminate.
Qed.

Theorem cleanup_stmt_correct :
  (forall st env mem1 mem2,
      Loop.loop_semantics (cleanup_stmt st) env mem1 mem2 <->
      Loop.loop_semantics st env mem1 mem2)
  /\
  (forall sts env mem1 mem2,
      Loop.loop_semantics (Loop.Seq (cleanup_stmt_list sts)) env mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2).
Proof.
  apply stmt_stmt_list_ind; intros; simpl.
  - split; intros Hsem.
    + inversion_clear Hsem.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      apply H in Hbody. exact Hbody.
    + inversion_clear Hsem.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      apply <- H in Hbody. exact Hbody.
  - split; intros Hsem; exact Hsem.
  - split; intros Hsem.
    + apply (proj1 (H env mem1 mem2)).
      apply (proj1 (make_stmt_from_list_correct (cleanup_stmt_list s) env mem1 mem2)).
      exact Hsem.
    + apply (proj2 (make_stmt_from_list_correct (cleanup_stmt_list s) env mem1 mem2)).
      apply (proj2 (H env mem1 mem2)).
      exact Hsem.
  - split; intros Hsem.
    + rewrite Loop.make_guard_correct in Hsem.
      destruct (Loop.eval_test env t) eqn:Htest.
      * apply Loop.LGuardTrue.
        -- apply (proj1 (H env mem1 mem2)). exact Hsem.
        -- exact Htest.
      * subst. apply Loop.LGuardFalse. exact Htest.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * rewrite Loop.make_guard_correct.
        rewrite Heq.
        apply (proj2 (H env mem1 mem2)). exact Hbody.
      * rewrite Loop.make_guard_correct.
        rewrite Heq. reflexivity.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - remember (cleanup_stmt s) as cs eqn:Hc.
    destruct cs as [lb ub body | i es | sts | t body]; simpl.
    + split; intros Hsem.
      * inversion_clear Hsem.
        apply (proj1 (H env mem1 mem3)) in H1.
        apply (proj1 (H0 env mem3 mem2)) in H2.
        econstructor; eauto.
      * inversion_clear Hsem.
        apply (proj2 (H env mem1 mem3)) in H1.
        apply (proj2 (H0 env mem3 mem2)) in H2.
        econstructor; eauto.
    + split; intros Hsem.
      * inversion_clear Hsem.
        apply (proj1 (H env mem1 mem3)) in H1.
        apply (proj1 (H0 env mem3 mem2)) in H2.
        econstructor; eauto.
      * inversion_clear Hsem.
        apply (proj2 (H env mem1 mem3)) in H1.
        apply (proj2 (H0 env mem3 mem2)) in H2.
        econstructor; eauto.
    + destruct sts as [|st' sts'].
      * split; intros Hsem.
        -- apply (proj1 (H0 env mem1 mem2)) in Hsem.
           econstructor.
           ++ apply (proj2 (((proj1 cleanup_stmt_skip_semantics) s env mem1 mem1 (eq_sym Hc)))). reflexivity.
           ++ exact Hsem.
        -- inversion_clear Hsem.
           pose proof ((proj1 (((proj1 cleanup_stmt_skip_semantics) s env mem1 mem3 (eq_sym Hc))) H1)) as Heq.
           subst.
           match goal with
           | Htl : Loop.loop_semantics (Loop.Seq s0) env ?m ?n |- _ =>
               apply (proj2 (H0 env m n)); exact Htl
           end.
      * split; intros Hsem.
        -- inversion_clear Hsem.
           apply (proj1 (H env mem1 mem3)) in H1.
           apply (proj1 (H0 env mem3 mem2)) in H2.
           econstructor; eauto.
        -- inversion_clear Hsem.
           apply (proj2 (H env mem1 mem3)) in H1.
           apply (proj2 (H0 env mem3 mem2)) in H2.
           econstructor; eauto.
    + split; intros Hsem.
      * inversion_clear Hsem.
        apply (proj1 (H env mem1 mem3)) in H1.
        apply (proj1 (H0 env mem3 mem2)) in H2.
        econstructor; eauto.
      * inversion_clear Hsem.
        apply (proj2 (H env mem1 mem3)) in H1.
        apply (proj2 (H0 env mem3 mem2)) in H2.
        econstructor; eauto.
Qed.

Lemma cleanup_stmt_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics (cleanup_stmt st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof. intros. apply cleanup_stmt_correct. Qed.

Lemma cleanup_stmt_list_semantics :
  forall sts env mem1 mem2,
    Loop.loop_semantics (Loop.Seq (cleanup_stmt_list sts)) env mem1 mem2 <->
    Loop.loop_semantics (Loop.Seq sts) env mem1 mem2.
Proof. intros. apply cleanup_stmt_correct. Qed.

Lemma cleanup_stmt_pass_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics (cleanup_stmt_pass st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof.
  intros st env mem1 mem2.
  unfold cleanup_stmt_pass.
  rewrite cleanup_stmt_semantics.
  apply simplify_stmt_semantics.
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

End LoopCleanup.
