Require Import List.
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
  Loop.Sum e (Loop.Constant 1).

Fixpoint peel_unroll_stmt_list
    (fuel: nat) (cur ub: Loop.expr) (body: Loop.stmt) : Loop.stmt_list :=
  match fuel with
  | O =>
      Loop.SCons (Loop.Loop cur ub body) Loop.SNil
  | S fuel' =>
      Loop.SCons
        (Loop.Guard
           (Loop.LE (succ_expr cur) ub)
           (Subst.subst_stmt_at 0 cur body))
        (peel_unroll_stmt_list fuel' (succ_expr cur) ub body)
  end.

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

Lemma peel_unroll_stmt_list_semantics :
  forall fuel cur ub body env mem1 mem2,
    Loop.loop_semantics
      (Loop.Seq (peel_unroll_stmt_list fuel cur ub body))
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  induction fuel as [|fuel IH]; intros cur ub body env mem1 mem2; simpl.
  - apply seq_single_loop_semantics.
  - remember (Loop.eval_expr env cur) as curv.
    remember (Loop.eval_expr env ub) as ubv.
    assert (Htest_true :
      Loop.eval_test env (Loop.LE (succ_expr cur) ub) = true <->
      curv < ubv).
    {
      subst curv ubv. simpl. rewrite Z.leb_le. lia.
    }
    assert (Htest_false :
      Loop.eval_test env (Loop.LE (succ_expr cur) ub) = false <->
      curv >= ubv).
    {
      subst curv ubv. simpl. rewrite Z.leb_gt. lia.
    }
    split; intros Hsem.
    + inversion_clear Hsem.
      apply IH in H0.
      destruct (Z_lt_ge_dec curv ubv) as [Hlt|Hge].
      * apply Loop.LLoop.
        rewrite <- Heqcurv, <- Hequbv.
        rewrite Zrange_begin by lia.
        inversion H; subst; clear H.
        -- match goal with
           | Hbody: Loop.loop_semantics (Subst.subst_stmt_at 0 cur body) env _ _,
             Hguard: Loop.eval_test env (Loop.LE (succ_expr cur) ub) = true |- _ =>
               apply Subst.subst_stmt_at_semantics in Hbody;
               simpl in Hbody;
               inversion_clear H0;
               econstructor; eauto
           end.
        -- match goal with
           | Hguard: Loop.eval_test env (Loop.LE (succ_expr cur) ub) = false |- _ =>
               apply Htest_false in Hguard; lia
           end.
      * inversion H; subst; clear H.
        -- match goal with
           | Hguard: Loop.eval_test env (Loop.LE (succ_expr cur) ub) = true |- _ =>
               apply Htest_true in Hguard; lia
           end.
        -- inversion H0; subst; clear H0.
           match goal with
           | Hiter: _ |- _ =>
               simpl in Hiter;
               rewrite Zrange_empty in Hiter by lia;
               inversion Hiter; subst
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
              rewrite <- Heqcurv.
              match goal with
              | Hbody: Loop.loop_semantics body (curv :: env) _ _ |- _ =>
                  exact Hbody
              end.
           ++ apply Htest_true. exact Hlt.
        -- apply IH.
           apply Loop.LLoop.
           simpl.
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
        -- apply IH.
           apply Loop.LLoop.
           simpl.
           rewrite Zrange_empty by lia.
           constructor.
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
