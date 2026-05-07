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

Fixpoint add_const_expr (e: Loop.expr) (k: Z) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant (c + k)
  | Loop.Sum e1 (Loop.Constant c) => add_const_expr e1 (c + k)
  | _ =>
      if Z.eqb k 0
      then e
      else Loop.Sum e (Loop.Constant k)
  end.

Definition succ_expr (e: Loop.expr) : Loop.expr :=
  add_const_expr e 1.

Definition pred_expr (e: Loop.expr) : Loop.expr :=
  add_const_expr e (-1).

Fixpoint insert_expr_at (k: nat) (e: Loop.expr) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant c
  | Loop.Sum e1 e2 => Loop.Sum (insert_expr_at k e1) (insert_expr_at k e2)
  | Loop.Mult n e1 => Loop.Mult n (insert_expr_at k e1)
  | Loop.Div e1 n => Loop.Div (insert_expr_at k e1) n
  | Loop.Mod e1 n => Loop.Mod (insert_expr_at k e1) n
  | Loop.Var n =>
      if Nat.ltb n k then Loop.Var n else Loop.Var (S n)
  | Loop.Max e1 e2 => Loop.Max (insert_expr_at k e1) (insert_expr_at k e2)
  | Loop.Min e1 e2 => Loop.Min (insert_expr_at k e1) (insert_expr_at k e2)
  end.

Fixpoint insert_test_at (k: nat) (t: Loop.test) : Loop.test :=
  match t with
  | Loop.LE e1 e2 => Loop.LE (insert_expr_at k e1) (insert_expr_at k e2)
  | Loop.EQ e1 e2 => Loop.EQ (insert_expr_at k e1) (insert_expr_at k e2)
  | Loop.And t1 t2 => Loop.And (insert_test_at k t1) (insert_test_at k t2)
  | Loop.Or t1 t2 => Loop.Or (insert_test_at k t1) (insert_test_at k t2)
  | Loop.Not t1 => Loop.Not (insert_test_at k t1)
  | Loop.TConstantTest b => Loop.TConstantTest b
  end.

Fixpoint insert_stmt_at (k: nat) (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      Loop.Loop
        (insert_expr_at k lb)
        (insert_expr_at k ub)
        (insert_stmt_at (S k) body)
  | Loop.Instr i es => Loop.Instr i (map (insert_expr_at k) es)
  | Loop.Seq sts => Loop.Seq (insert_stmt_list_at k sts)
  | Loop.Guard t body => Loop.Guard (insert_test_at k t) (insert_stmt_at k body)
  end
with insert_stmt_list_at (k: nat) (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' =>
      Loop.SCons (insert_stmt_at k st) (insert_stmt_list_at k sts')
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

Fixpoint suffix_peel_stmt
    (fuel: nat) (lb ub: Loop.expr) (body: Loop.stmt) : Loop.stmt :=
  match fuel with
  | O => Loop.Loop lb ub body
  | S fuel' =>
      let last := pred_expr ub in
      Loop.Seq
        (Loop.SCons
          (suffix_peel_stmt fuel' lb last body)
          (Loop.SCons
            (Loop.Guard
              (Loop.LE (succ_expr lb) ub)
              (Subst.subst_stmt_at 0 last body))
            Loop.SNil))
  end.

Inductive peel_plan : Type :=
| PeelPrefix : list Loop.expr -> peel_plan
| PeelSuffix : nat -> peel_plan.

Definition prefix_peel_plan (fuel: nat) (cur: Loop.expr) : peel_plan :=
  PeelPrefix (prefix_peel_steps fuel cur).

Definition check_peel_plan
    (cur _ub: Loop.expr) (plan: peel_plan) : bool :=
  match plan with
  | PeelPrefix steps => check_peel_steps cur steps
  | PeelSuffix _ => true
  end.

Definition lower_peel_plan_stmt_list
    (plan: peel_plan) (cur ub: Loop.expr) (body: Loop.stmt) : Loop.stmt_list :=
  match plan with
  | PeelPrefix steps => lower_peel_steps cur ub body steps
  | PeelSuffix fuel => Loop.SCons (suffix_peel_stmt fuel cur ub body) Loop.SNil
  end.

Definition lower_peel_plan_stmt
    (plan: peel_plan) (cur ub: Loop.expr) (body: Loop.stmt) : Loop.stmt :=
  match plan with
  | PeelPrefix steps => Loop.Seq (lower_peel_steps cur ub body steps)
  | PeelSuffix fuel => suffix_peel_stmt fuel cur ub body
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

Example check_peel_plan_accepts_suffix_example :
  check_peel_plan
    (Loop.Var 0)
    (Loop.Var 1)
    (PeelSuffix 2) = true.
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

Lemma seq_single_stmt_semantics :
  forall st env mem1 mem2,
    Loop.loop_semantics
      (Loop.Seq (Loop.SCons st Loop.SNil))
      env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof.
  intros st env mem1 mem2.
  split; intros Hsem.
  - inversion_clear Hsem.
    inversion H0; subst; clear H0.
    exact H.
  - eapply Loop.LSeq.
    + exact Hsem.
    + constructor.
Qed.

Lemma add_const_expr_correct :
  forall env e k,
    Loop.eval_expr env (add_const_expr e k) = Loop.eval_expr env e + k.
Proof.
  intros env e.
  induction e; intros k; simpl.
  - lia.
  - destruct e2; simpl.
    + rewrite IHe1. lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
    + destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
  - destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
  - destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
  - destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
  - destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
  - destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
  - destruct (Z.eqb k 0) eqn:Hk; simpl; [apply Z.eqb_eq in Hk|]; lia.
Qed.

Lemma succ_expr_correct :
  forall env e,
    Loop.eval_expr env (succ_expr e) = Loop.eval_expr env e + 1.
Proof.
  intros env e. apply add_const_expr_correct.
Qed.

Lemma pred_expr_correct :
  forall env e,
    Loop.eval_expr env (pred_expr e) = Loop.eval_expr env e - 1.
Proof.
  intros env e. unfold pred_expr. rewrite add_const_expr_correct. lia.
Qed.

Lemma iter_semantics_app :
  forall (A: Type) (P: A -> State.t -> State.t -> Prop) xs ys mem1 mem2 mem3,
    Instr.IterSem.iter_semantics P xs mem1 mem2 ->
    Instr.IterSem.iter_semantics P ys mem2 mem3 ->
    Instr.IterSem.iter_semantics P (xs ++ ys) mem1 mem3.
Proof.
  intros A P xs ys mem1 mem2 mem3 Hxs Hys.
  induction Hxs.
  - simpl. exact Hys.
  - simpl. econstructor; eauto.
Qed.

Lemma iter_semantics_app_inv :
  forall (A: Type) (P: A -> State.t -> State.t -> Prop) xs ys mem1 mem3,
    Instr.IterSem.iter_semantics P (xs ++ ys) mem1 mem3 ->
    exists mem2,
      Instr.IterSem.iter_semantics P xs mem1 mem2 /\
      Instr.IterSem.iter_semantics P ys mem2 mem3.
Proof.
  induction xs as [|x xs IH]; intros ys mem1 mem3 Hsem; simpl in Hsem.
  - exists mem1. split; [constructor|exact Hsem].
  - inversion_clear Hsem.
    apply IH in H0 as [mem2 [Hxs Hys]].
    exists mem2. split; [econstructor; eauto|exact Hys].
Qed.

Lemma iter_semantics_single_inv :
  forall (A: Type) (P: A -> State.t -> State.t -> Prop) x mem1 mem2,
    Instr.IterSem.iter_semantics P [x] mem1 mem2 ->
    P x mem1 mem2.
Proof.
  intros A P x mem1 mem2 Hsem.
  inversion_clear Hsem.
  inversion H0; subst; clear H0.
  exact H.
Qed.

Lemma iter_semantics_concat_map :
  forall (A B: Type) (P: B -> State.t -> State.t -> Prop)
    (f: A -> list B) xs mem1 mem2,
    Instr.IterSem.iter_semantics
      (fun x => Instr.IterSem.iter_semantics P (f x))
      xs mem1 mem2 <->
    Instr.IterSem.iter_semantics P (concat (map f xs)) mem1 mem2.
Proof.
  induction xs as [|x xs IH]; intros mem1 mem2; simpl.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem.
    + inversion_clear Hsem.
      eapply iter_semantics_app; eauto.
      apply IH. exact H0.
    + apply iter_semantics_app_inv in Hsem as [mem_mid [Hhead Htail]].
      econstructor.
      * exact Hhead.
      * apply IH. exact Htail.
Qed.

Lemma seq_two_semantics :
  forall st1 st2 env mem1 mem3,
    Loop.loop_semantics
      (Loop.Seq (Loop.SCons st1 (Loop.SCons st2 Loop.SNil)))
      env mem1 mem3 <->
    exists mem2,
      Loop.loop_semantics st1 env mem1 mem2 /\
      Loop.loop_semantics st2 env mem2 mem3.
Proof.
  intros st1 st2 env mem1 mem3.
  split; intros Hsem.
  - inversion_clear Hsem.
    inversion_clear H0.
    inversion H2; subst; clear H2.
    exists mem2. split; assumption.
  - destruct Hsem as [mem2 [Hst1 Hst2]].
    eapply Loop.LSeq.
    + exact Hst1.
    + eapply Loop.LSeq.
      * exact Hst2.
      * constructor.
Qed.

Lemma insert_expr_at_correct :
  forall pre inserted suf e,
    Loop.eval_expr (pre ++ inserted :: suf) (insert_expr_at (length pre) e) =
    Loop.eval_expr (pre ++ suf) e.
Proof.
  intros pre inserted suf e.
  revert pre inserted suf.
  induction e; intros pre0 inserted suf; simpl; try reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - destruct (Nat.ltb n (length pre0)) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      apply Subst.nth_insert_before; auto.
    + apply Nat.ltb_ge in Hlt.
      change (nth (S n) (pre0 ++ inserted :: suf) 0 =
              nth n (pre0 ++ suf) 0).
      rewrite Subst.nth_insert_after by lia.
      reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma insert_expr_list_at_correct :
  forall pre inserted suf es,
    map (Loop.eval_expr (pre ++ inserted :: suf))
      (map (insert_expr_at (length pre)) es) =
    map (Loop.eval_expr (pre ++ suf)) es.
Proof.
  intros pre inserted suf es.
  rewrite map_map.
  apply map_ext.
  intro e.
  apply insert_expr_at_correct.
Qed.

Lemma insert_test_at_correct :
  forall pre inserted suf t,
    Loop.eval_test (pre ++ inserted :: suf) (insert_test_at (length pre) t) =
    Loop.eval_test (pre ++ suf) t.
Proof.
  intros pre inserted suf t.
  revert pre inserted suf.
  induction t; intros pre0 inserted suf; simpl; try reflexivity.
  - rewrite !insert_expr_at_correct. reflexivity.
  - rewrite !insert_expr_at_correct. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Scheme insert_stmt_ind_mut := Induction for Loop.stmt Sort Prop
with insert_stmt_list_ind_mut := Induction for Loop.stmt_list Sort Prop.
Combined Scheme insert_stmt_stmt_list_ind
  from insert_stmt_ind_mut, insert_stmt_list_ind_mut.

Theorem insert_stmt_at_correct :
  (forall st pre inserted suf mem1 mem2,
      Loop.loop_semantics (insert_stmt_at (length pre) st)
        (pre ++ inserted :: suf) mem1 mem2 <->
      Loop.loop_semantics st (pre ++ suf) mem1 mem2)
  /\
  (forall sts pre inserted suf mem1 mem2,
      Loop.loop_semantics (Loop.Seq (insert_stmt_list_at (length pre) sts))
        (pre ++ inserted :: suf) mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) (pre ++ suf) mem1 mem2).
Proof.
  apply insert_stmt_stmt_list_ind; intros; simpl.
  - split; intros Hsem.
    + inversion_clear Hsem.
      rewrite !(insert_expr_at_correct pre inserted suf) in H0.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      specialize (H (x :: pre) inserted suf mem3 mem4).
      change ((x :: pre) ++ inserted :: suf)
        with (x :: pre ++ inserted :: suf) in Hbody.
      apply H in Hbody.
      exact Hbody.
    + inversion_clear Hsem.
      rewrite <- !(insert_expr_at_correct pre inserted suf) in H0.
      apply Loop.LLoop.
      eapply Instr.IterSem.iter_semantics_map; [|exact H0].
      intros x mem3 mem4 Hx Hbody.
      specialize (H (x :: pre) inserted suf mem3 mem4).
      change ((x :: pre) ++ inserted :: suf)
        with (x :: pre ++ inserted :: suf).
      apply <- H in Hbody.
      exact Hbody.
  - split; intros Hsem.
    + inversion Hsem; subst; clear Hsem.
      econstructor.
      rewrite (insert_expr_list_at_correct pre inserted suf) in H4.
      exact H4.
    + inversion Hsem; subst; clear Hsem.
      econstructor.
      rewrite (insert_expr_list_at_correct pre inserted suf).
      exact H4.
  - split; intros Hsem.
    + apply (H pre inserted suf). exact Hsem.
    + apply <- (H pre inserted suf). exact Hsem.
  - split; intros Hsem.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue.
        -- apply (H pre inserted suf). exact Hbody.
        -- rewrite (insert_test_at_correct pre inserted suf) in Heq. exact Heq.
      * apply Loop.LGuardFalse.
        rewrite (insert_test_at_correct pre inserted suf) in Heq. exact Heq.
    + inversion_clear Hsem as [| | | ? ? ? ? ? Hbody Heq | ? ? ? ? Heq |].
      * apply Loop.LGuardTrue.
        -- apply <- (H pre inserted suf). exact Hbody.
        -- rewrite (insert_test_at_correct pre inserted suf). exact Heq.
      * apply Loop.LGuardFalse.
        rewrite (insert_test_at_correct pre inserted suf). exact Heq.
  - split; intros Hsem; inversion_clear Hsem; constructor.
  - split; intros Hsem; inversion_clear Hsem.
    + apply (H pre inserted suf) in H1.
      apply (H0 pre inserted suf) in H2.
      econstructor; eauto.
    + apply <- (H pre inserted suf) in H1.
      apply <- (H0 pre inserted suf) in H2.
      econstructor; eauto.
Qed.

Lemma insert_stmt_at_semantics :
  forall st inserted env mem1 mem2,
    Loop.loop_semantics (insert_stmt_at 0 st) (inserted :: env) mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof.
  intros.
  specialize (proj1 insert_stmt_at_correct st [] inserted env mem1 mem2) as H.
  simpl in H. exact H.
Qed.

Definition block_iter_expr
    (factor offset: nat) (lb: Loop.expr) : Loop.expr :=
  add_const_expr
    (Loop.Sum (Subst.lift_expr lb) (Loop.Mult (Z.of_nat factor) (Loop.Var 0)))
    (Z.of_nat offset).

Fixpoint block_offset_stmt_list
    (fuel factor offset: nat) (lb: Loop.expr) (body: Loop.stmt)
    : Loop.stmt_list :=
  match fuel with
  | O => Loop.SNil
  | S fuel' =>
      Loop.SCons
        (Subst.subst_stmt_at 0
          (block_iter_expr factor offset lb)
          (insert_stmt_at 1 body))
        (block_offset_stmt_list fuel' factor (S offset) lb body)
  end.

Lemma block_iter_expr_correct :
  forall factor offset lb j env,
    Loop.eval_expr (j :: env) (block_iter_expr factor offset lb) =
    Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat offset.
Proof.
  intros factor offset lb j env.
  unfold block_iter_expr.
  rewrite add_const_expr_correct.
  simpl. rewrite Subst.lift_expr_correct. lia.
Qed.

Lemma block_offset_stmt_list_semantics :
  forall fuel factor offset lb body j env mem1 mem2,
    Loop.loop_semantics
      (Loop.Seq (block_offset_stmt_list fuel factor offset lb body))
      (j :: env) mem1 mem2 <->
    Instr.IterSem.iter_semantics
      (fun x => Loop.loop_semantics body (x :: env))
      (Zrange
        (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat offset)
        (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat offset + Z.of_nat fuel))
      mem1 mem2.
Proof.
  induction fuel as [|fuel IH]; intros factor offset lb body j env mem1 mem2; simpl.
  - rewrite Zrange_empty by lia.
    split; intros Hsem; inversion_clear Hsem; constructor.
  - remember (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat offset) as base.
    replace (Loop.eval_expr env lb + Z.of_nat factor * j + Z.pos (Pos.of_succ_nat offset))
      with (base + 1) by (subst base; lia).
    replace (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat offset + Z.pos (Pos.of_succ_nat fuel))
      with (base + 1 + Z.of_nat fuel) by (subst base; lia).
    rewrite Zrange_begin by lia.
    replace (base + Z.pos (Pos.of_succ_nat fuel))
      with (base + 1 + Z.of_nat fuel) by lia.
    split; intros Hsem.
    + inversion_clear Hsem.
      apply Subst.subst_stmt_at_semantics in H.
      rewrite block_iter_expr_correct in H.
      rewrite <- Heqbase in H.
      match type of H with
      | Loop.loop_semantics _ _ ?m1 ?m2 =>
          pose proof (proj1 insert_stmt_at_correct body [base] j env m1 m2)
            as Hinsert;
          simpl in Hinsert;
          apply Hinsert in H
      end.
      apply IH in H0.
      replace (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat (S offset))
        with (base + 1) in H0 by (subst base; lia).
      replace (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat (S offset) + Z.of_nat fuel)
        with (base + 1 + Z.of_nat fuel) in H0 by (subst base; lia).
      econstructor.
      * exact H.
      * exact H0.
    + inversion_clear Hsem.
      eapply Loop.LSeq.
      * apply Subst.subst_stmt_at_semantics.
        rewrite block_iter_expr_correct.
        rewrite <- Heqbase.
        match type of H with
        | Loop.loop_semantics _ _ ?m1 ?m2 =>
            pose proof (proj1 insert_stmt_at_correct body [base] j env m1 m2)
              as Hinsert;
            simpl in Hinsert;
            apply <- Hinsert in H
        end.
        exact H.
      * apply IH.
        replace (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat (S offset))
          with (base + 1) by (subst base; lia).
        replace (Loop.eval_expr env lb + Z.of_nat factor * j + Z.of_nat (S offset) + Z.of_nat fuel)
          with (base + 1 + Z.of_nat fuel) by (subst base; lia).
        exact H0.
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

Lemma suffix_peel_stmt_semantics :
  forall fuel lb ub body env mem1 mem2,
    Loop.loop_semantics (suffix_peel_stmt fuel lb ub body) env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop lb ub body) env mem1 mem2.
Proof.
  induction fuel as [|fuel IH]; intros lb ub body env mem1 mem2; simpl.
  - reflexivity.
  - remember (Loop.eval_expr env lb) as lbv.
    remember (Loop.eval_expr env ub) as ubv.
    assert (Htest_true :
      Loop.eval_test env (Loop.LE (succ_expr lb) ub) = true <->
      lbv < ubv).
    {
      subst lbv ubv. simpl. rewrite succ_expr_correct. rewrite Z.leb_le. lia.
    }
    assert (Htest_false :
      Loop.eval_test env (Loop.LE (succ_expr lb) ub) = false <->
      lbv >= ubv).
    {
      subst lbv ubv. simpl. rewrite succ_expr_correct. rewrite Z.leb_gt. lia.
    }
    split; intros Hsem.
    + apply seq_two_semantics in Hsem as [mem_mid [Hprefix Hlast]].
      apply IH in Hprefix.
      destruct (Z_lt_ge_dec lbv ubv) as [Hlt|Hge].
      * apply Loop.LLoop.
        rewrite <- Heqlbv, <- Hequbv.
        replace (Zrange lbv ubv) with (Zrange lbv (ubv - 1) ++ [ubv - 1])
          by (symmetry; apply Zrange_end; lia).
        inversion_clear Hprefix.
        inversion_clear Hlast as [| | | ? ? ? ? ? Hbody Hguard | ? ? ? ? Hguard |].
        -- apply Subst.subst_stmt_at_semantics in Hbody.
           simpl in Hbody.
           rewrite pred_expr_correct in Hbody.
           rewrite <- Hequbv in Hbody.
           simpl in H.
           rewrite pred_expr_correct in H.
           rewrite <- Heqlbv, <- Hequbv in H.
           eapply iter_semantics_app.
           ++ exact H.
           ++ econstructor; [exact Hbody|constructor].
        -- apply Htest_false in Hguard. lia.
      * inversion_clear Hprefix.
        simpl in H.
        rewrite pred_expr_correct in H.
        rewrite <- Heqlbv, <- Hequbv in H.
        rewrite Zrange_empty in H by lia.
        inversion H; subst; clear H.
        inversion_clear Hlast as [| | | ? ? ? ? ? Hbody Hguard | ? ? ? ? Hguard |].
        -- apply Htest_true in Hguard. lia.
        -- apply Loop.LLoop.
           simpl.
           rewrite Zrange_empty by lia.
           constructor.
    + inversion_clear Hsem.
      destruct (Z_lt_ge_dec lbv ubv) as [Hlt|Hge].
      * rewrite <- Heqlbv, <- Hequbv in H.
        replace (Zrange lbv ubv) with (Zrange lbv (ubv - 1) ++ [ubv - 1]) in H
          by (symmetry; apply Zrange_end; lia).
        apply iter_semantics_app_inv in H as [mem_mid [Hprefix Hlast]].
        apply iter_semantics_single_inv in Hlast as Hbody.
        apply seq_two_semantics.
        exists mem_mid. split.
        -- apply IH.
           apply Loop.LLoop.
           simpl. rewrite pred_expr_correct.
           rewrite <- Heqlbv, <- Hequbv.
           exact Hprefix.
        -- apply Loop.LGuardTrue.
           ++ apply Subst.subst_stmt_at_semantics.
              simpl. rewrite pred_expr_correct.
              rewrite <- Hequbv.
              exact Hbody.
           ++ apply Htest_true. exact Hlt.
      * rewrite <- Heqlbv, <- Hequbv in H.
        rewrite Zrange_empty in H by lia.
        inversion H; subst; clear H.
        apply seq_two_semantics.
        eexists. split.
        -- apply IH.
           apply Loop.LLoop.
           simpl. rewrite pred_expr_correct.
           rewrite Zrange_empty by lia.
           constructor.
        -- apply Loop.LGuardFalse.
           apply Htest_false. exact Hge.
Qed.

Lemma checked_peel_plan_stmt_list_semantics :
  forall plan cur ub body env mem1 mem2,
    check_peel_plan cur ub plan = true ->
    Loop.loop_semantics
      (Loop.Seq (lower_peel_plan_stmt_list plan cur ub body))
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  intros plan cur ub body env mem1 mem2 Hcheck.
  destruct plan as [steps|fuel]; simpl in *.
  - apply checked_peel_steps_semantics. exact Hcheck.
  - rewrite seq_single_stmt_semantics.
    apply suffix_peel_stmt_semantics.
Qed.

Lemma checked_peel_plan_stmt_semantics :
  forall plan cur ub body env mem1 mem2,
    check_peel_plan cur ub plan = true ->
    Loop.loop_semantics
      (lower_peel_plan_stmt plan cur ub body)
      env mem1 mem2 <->
    Loop.loop_semantics (Loop.Loop cur ub body) env mem1 mem2.
Proof.
  intros plan cur ub body env mem1 mem2 Hcheck.
  destruct plan as [steps|fuel]; simpl in *.
  - apply checked_peel_steps_semantics. exact Hcheck.
  - apply suffix_peel_stmt_semantics.
Qed.

Definition checked_lower_peel_plan_stmt
    (plan: peel_plan) (cur ub: Loop.expr) (body: Loop.stmt) : option Loop.stmt :=
  if check_peel_plan cur ub plan
  then Some (lower_peel_plan_stmt plan cur ub body)
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
  apply checked_peel_plan_stmt_semantics. exact Hcheck.
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

Fixpoint suffix_peel_unroll_stmt (fuel: nat) (st: Loop.stmt) : Loop.stmt :=
  match st with
  | Loop.Loop lb ub body =>
      suffix_peel_stmt fuel lb ub body
  | Loop.Instr i es => Loop.Instr i es
  | Loop.Seq sts => Loop.Seq (suffix_peel_unroll_stmt_list_rec fuel sts)
  | Loop.Guard t body => Loop.Guard t (suffix_peel_unroll_stmt fuel body)
  end
with suffix_peel_unroll_stmt_list_rec (fuel: nat) (sts: Loop.stmt_list) : Loop.stmt_list :=
  match sts with
  | Loop.SNil => Loop.SNil
  | Loop.SCons st sts' =>
      Loop.SCons
        (suffix_peel_unroll_stmt fuel st)
        (suffix_peel_unroll_stmt_list_rec fuel sts')
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

Definition suffix_peel_unroll_stmt_changed : nat -> Loop.stmt -> bool :=
  peel_unroll_stmt_changed.

Definition suffix_peel_unroll_stmt_list_changed : nat -> Loop.stmt_list -> bool :=
  peel_unroll_stmt_list_changed.

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

Theorem suffix_peel_unroll_stmt_correct :
  forall fuel,
  (forall st env mem1 mem2,
      Loop.loop_semantics (suffix_peel_unroll_stmt fuel st) env mem1 mem2 <->
      Loop.loop_semantics st env mem1 mem2)
  /\
  (forall sts env mem1 mem2,
      Loop.loop_semantics (Loop.Seq (suffix_peel_unroll_stmt_list_rec fuel sts)) env mem1 mem2 <->
      Loop.loop_semantics (Loop.Seq sts) env mem1 mem2).
Proof.
  intro fuel.
  apply stmt_stmt_list_ind; intros; simpl.
  - apply suffix_peel_stmt_semantics.
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

Lemma suffix_peel_unroll_stmt_semantics :
  forall fuel st env mem1 mem2,
    Loop.loop_semantics (suffix_peel_unroll_stmt fuel st) env mem1 mem2 <->
    Loop.loop_semantics st env mem1 mem2.
Proof. intros. apply suffix_peel_unroll_stmt_correct. Qed.

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

Definition suffix_peel_unroll (fuel: nat) (prog: Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (suffix_peel_unroll_stmt fuel st, ctxt, vars).

Definition suffix_peel_unroll_changed (fuel: nat) (prog: Loop.t) : bool :=
  let '(st, _, _) := prog in
  suffix_peel_unroll_stmt_changed fuel st.

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

Theorem suffix_peel_unroll_correct :
  forall fuel prog mem1 mem2,
    Loop.semantics (suffix_peel_unroll fuel prog) mem1 mem2 <->
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
    + eapply suffix_peel_unroll_stmt_semantics. exact H3.
  - inversion H; subst.
    econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply suffix_peel_unroll_stmt_semantics. exact H3.
Qed.

End LoopUnroll.
