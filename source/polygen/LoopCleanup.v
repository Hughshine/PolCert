Require Import Bool.
Require Import Lia.
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

Fixpoint collect_sum_norm (e: Loop.expr) : list Loop.expr * Z :=
  match e with
  | Loop.Constant c => ([], c)
  | Loop.Sum e1 e2 =>
      let '(ts1, c1) := collect_sum_norm e1 in
      let '(ts2, c2) := collect_sum_norm e2 in
      (ts1 ++ ts2, c1 + c2)
  | _ => ([e], 0)
  end.

Definition build_sum (terms: list Loop.expr) (c: Z) : Loop.expr :=
  fold_right Loop.make_sum (Loop.Constant c) terms.

Fixpoint zsum (zs: list Z) : Z :=
  match zs with
  | [] => 0
  | z :: zs' => z + zsum zs'
  end.

Definition normalize_le (e1 e2: Loop.expr) : Loop.test :=
  match e1, e2 with
  | Loop.Mult k e, Loop.Constant c =>
      if Z.eqb k (-1) then Loop.make_le (Loop.Constant (- c)) e else Loop.make_le e1 e2
  | Loop.Constant c, Loop.Mult k e =>
      if Z.eqb k (-1) then Loop.make_le e (Loop.Constant (- c)) else Loop.make_le e1 e2
  | _, _ => Loop.make_le e1 e2
  end.

Fixpoint simpl_expr (e: Loop.expr) : Loop.expr :=
  match e with
  | Loop.Constant c => Loop.Constant c
  | Loop.Sum e1 e2 =>
      let e1' := simpl_expr e1 in
      let e2' := simpl_expr e2 in
      let '(terms, c) := collect_sum_norm (Loop.Sum e1' e2') in
      build_sum terms c
  | Loop.Mult k e1 => Loop.make_mult k (simpl_expr e1)
  | Loop.Div e1 k => Loop.make_div (simpl_expr e1) k
  | Loop.Mod e1 k => Loop.make_mod (simpl_expr e1) k
  | Loop.Var n => Loop.Var n
  | Loop.Max e1 e2 => Loop.make_max (simpl_expr e1) (simpl_expr e2)
  | Loop.Min e1 e2 => Loop.make_min (simpl_expr e1) (simpl_expr e2)
  end.

Fixpoint simpl_test (t: Loop.test) : Loop.test :=
  match t with
  | Loop.LE e1 e2 => normalize_le (simpl_expr e1) (simpl_expr e2)
  | Loop.EQ e1 e2 => Loop.make_eq (simpl_expr e1) (simpl_expr e2)
  | Loop.And t1 t2 => Loop.make_and (simpl_test t1) (simpl_test t2)
  | Loop.Or t1 t2 => Loop.make_or (simpl_test t1) (simpl_test t2)
  | Loop.Not t1 => Loop.make_not (simpl_test t1)
  | Loop.TConstantTest b => Loop.TConstantTest b
  end.

Lemma build_sum_correct :
  forall env terms c,
    Loop.eval_expr env (build_sum terms c) =
    zsum (map (Loop.eval_expr env) terms) + c.
Proof.
  intros env terms c.
  induction terms as [|t ts IH]; simpl.
  - reflexivity.
  - rewrite Loop.make_sum_correct, IH. lia.
Qed.

Lemma zsum_app :
  forall zs1 zs2,
    zsum (zs1 ++ zs2) = zsum zs1 + zsum zs2.
Proof.
  induction zs1 as [|z zs1 IH]; intros zs2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma collect_sum_norm_correct :
  forall env e terms c,
    collect_sum_norm e = (terms, c) ->
    zsum (map (Loop.eval_expr env) terms) + c = Loop.eval_expr env e.
Proof.
  induction e; intros terms c Hcol; simpl in Hcol.
  - inversion Hcol; subst. reflexivity.
  - destruct (collect_sum_norm e1) as [ts1 c1] eqn:H1.
    destruct (collect_sum_norm e2) as [ts2 c2] eqn:H2.
    inversion Hcol; subst; clear Hcol.
    rewrite map_app, zsum_app.
    specialize (IHe1 ts1 c1 eq_refl).
    specialize (IHe2 ts2 c2 eq_refl).
    replace (zsum (map (Loop.eval_expr env) ts1) +
             (zsum (map (Loop.eval_expr env) ts2) + (c1 + c2)))
      with ((zsum (map (Loop.eval_expr env) ts1) + c1) +
            (zsum (map (Loop.eval_expr env) ts2) + c2)) by lia.
    assert (Hz1 :
      zsum (map (Loop.eval_expr env) ts1) = Loop.eval_expr env e1 - c1) by lia.
    assert (Hz2 :
      zsum (map (Loop.eval_expr env) ts2) = Loop.eval_expr env e2 - c2) by lia.
    rewrite Hz1, Hz2.
    simpl.
    lia.
  - inversion Hcol; subst. simpl. lia.
  - inversion Hcol; subst. simpl. lia.
  - inversion Hcol; subst. simpl. lia.
  - inversion Hcol; subst. simpl. lia.
  - inversion Hcol; subst. simpl. lia.
  - inversion Hcol; subst. simpl. lia.
Qed.

Lemma opp_leb_swap :
  forall x c,
    (- c <=? x) = (- x <=? c).
Proof.
  intros x c.
  destruct (Z.leb_spec0 (- c) x);
    destruct (Z.leb_spec0 (- x) c); simpl; lia.
Qed.

Lemma leb_neg_rhs_swap :
  forall x c,
    (x <=? - c) = (c <=? - x).
Proof.
  intros x c.
  destruct (Z.leb_spec0 x (- c));
    destruct (Z.leb_spec0 c (- x)); simpl; lia.
Qed.

Lemma opp_leb_mult_m1 :
  forall x c,
    (- c <=? x) = (((-1) * x) <=? c).
Proof.
  intros x c.
  rewrite opp_leb_swap.
  replace ((-1) * x) with (- x) by lia.
  reflexivity.
Qed.

Lemma leb_neg_rhs_mult_m1 :
  forall x c,
    (x <=? - c) = (c <=? ((-1) * x)).
Proof.
  intros x c.
  rewrite leb_neg_rhs_swap.
  replace ((-1) * x) with (- x) by lia.
  reflexivity.
Qed.

Lemma normalize_le_correct :
  forall env e1 e2,
    Loop.eval_test env (normalize_le e1 e2) = Loop.eval_test env (Loop.LE e1 e2).
Proof.
  intros env e1 e2.
  unfold normalize_le.
  destruct e1 as [c1|a1 b1|kleft eleft|dleft kdleft|mleft kmleft|n1|max1l max1r|min1l min1r].
  - destruct e2 as [c2|a2 b2|kright eright|dright kdright|mright kmright|n2|max2l max2r|min2l min2r];
      simpl; try reflexivity.
    destruct (Z.eqb kright (-1)) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct eright; simpl; rewrite leb_neg_rhs_mult_m1; reflexivity.
    + unfold Loop.make_le. simpl. reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2 as [c2|a2 b2|kright eright|dright kdright|mright kmright|n2|max2l max2r|min2l min2r];
      simpl; try reflexivity.
    destruct (Z.eqb kleft (-1)) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct eleft; simpl; rewrite opp_leb_mult_m1; reflexivity.
    + unfold Loop.make_le. simpl. reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
Qed.

Lemma simpl_expr_correct :
  forall env e,
    Loop.eval_expr env (simpl_expr e) = Loop.eval_expr env e.
Proof.
  induction e; simpl; intros; try reflexivity.
  - destruct (collect_sum_norm (Loop.Sum (simpl_expr e1) (simpl_expr e2))) as [terms c] eqn:Hsc.
    change (Loop.eval_expr env
      (let '(terms0, c0) := collect_sum_norm (Loop.Sum (simpl_expr e1) (simpl_expr e2))
       in build_sum terms0 c0) = Loop.eval_expr env (Loop.Sum e1 e2)).
    rewrite Hsc. simpl.
    pose proof (collect_sum_norm_correct env (Loop.Sum (simpl_expr e1) (simpl_expr e2)) terms c Hsc) as Hnorm.
    simpl in Hnorm.
    rewrite IHe1, IHe2 in Hnorm.
    etransitivity.
    + apply build_sum_correct.
    + exact Hnorm.
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
  - rewrite normalize_le_correct. simpl. rewrite !simpl_expr_correct. reflexivity.
  - rewrite Loop.make_eq_correct. simpl. rewrite !simpl_expr_correct. reflexivity.
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
      * inversion H as
          [| |env0 st0 sts0 mem10 mem20 mem30 Hhead Htail| | |];
          subst; clear H.
        inversion Htail; subst; clear Htail.
        exact Hhead.
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
           econstructor.
           ++ apply (proj2 (H env mem2 mem2 eq_refl)). reflexivity.
           ++ apply (proj2 (H0 env mem2 mem2 H1)). reflexivity.
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
           apply (proj2 (H0 env mem3 mem2)). exact H2.
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
