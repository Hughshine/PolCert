Require Import List.
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

End LoopUnroll.
