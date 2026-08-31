Require Import List.
Require Import Lia.
Require Import ZArith.
Import ListNotations.

Require Import SPolIRs.
Require Import LoopCleanup.
Open Scope Z_scope.

Module Loop := SPolIRs.Loop.
Module Instr := SPolIRs.Instr.
Module State := SPolIRs.State.
Module Cleanup := LoopCleanup SPolIRs.

Definition slot_expr (slots: list Loop.expr) (n: nat) : Loop.expr :=
  nth n slots (Loop.Constant 0%Z).

Lemma slot_expr_correct :
  forall env slots n,
    Loop.eval_expr env (slot_expr slots n) =
    nth n (map (Loop.eval_expr env) slots) 0%Z.
Proof.
  intros env slots.
  induction slots as [|slot slots IH]; intros [|n]; simpl; try reflexivity.
  apply IH.
Qed.

Fixpoint eval_affine_expr (e: Instr.affine_expr) (p: list Z) : Z :=
  match e with
  | Instr.AeConst z => z
  | Instr.AeVar n => nth n p 0%Z
  | Instr.AeAdd e1 e2 => eval_affine_expr e1 p + eval_affine_expr e2 p
  | Instr.AeSub e1 e2 => eval_affine_expr e1 p - eval_affine_expr e2 p
  | Instr.AeMul z e1 => z * eval_affine_expr e1 p
  end.

Fixpoint lower_affine_expr
    (slots: list Loop.expr) (e: Instr.affine_expr) : Loop.expr :=
  match e with
  | Instr.AeConst z => Loop.Constant z
  | Instr.AeVar n => slot_expr slots n
  | Instr.AeAdd e1 e2 =>
      Cleanup.simpl_expr
        (Loop.Sum (lower_affine_expr slots e1) (lower_affine_expr slots e2))
  | Instr.AeSub e1 e2 =>
      Cleanup.simpl_expr
        (Loop.Sum
          (lower_affine_expr slots e1)
          (Loop.Mult (-1) (lower_affine_expr slots e2)))
  | Instr.AeMul z e1 =>
      Cleanup.simpl_expr (Loop.Mult z (lower_affine_expr slots e1))
  end.

Definition loop_add (a b: Loop.expr) : Loop.expr :=
  Cleanup.simpl_expr (Loop.Sum a b).

Definition loop_sub (a b: Loop.expr) : Loop.expr :=
  Cleanup.simpl_expr (Loop.Sum a (Loop.Mult (-1) b)).

Definition loop_mul (a b: Loop.expr) : option Loop.expr :=
  match a, b with
  | Loop.Constant z, e
  | e, Loop.Constant z => Some (Loop.make_mult z e)
  | _, _ => None
  end.

Definition loop_div (a b: Loop.expr) : option Loop.expr :=
  match b with
  | Loop.Constant z => Some (Loop.make_div a z)
  | _ => None
  end.

Fixpoint lower_instr_expr
    (slots: list Loop.expr) (e: Instr.expr) : option Loop.expr :=
  match e with
  | Instr.ExConst z => Some (Loop.Constant z)
  | Instr.ExVar n => Some (slot_expr slots n)
  | Instr.ExAdd e1 e2 =>
      match lower_instr_expr slots e1, lower_instr_expr slots e2 with
      | Some l1, Some l2 => Some (loop_add l1 l2)
      | _, _ => None
      end
  | Instr.ExSub e1 e2 =>
      match lower_instr_expr slots e1, lower_instr_expr slots e2 with
      | Some l1, Some l2 => Some (loop_sub l1 l2)
      | _, _ => None
      end
  | Instr.ExMul e1 e2 =>
      match lower_instr_expr slots e1, lower_instr_expr slots e2 with
      | Some l1, Some l2 => loop_mul l1 l2
      | _, _ => None
      end
  | Instr.ExDiv e1 e2 =>
      match lower_instr_expr slots e1, lower_instr_expr slots e2 with
      | Some l1, Some l2 => loop_div l1 l2
      | _, _ => None
      end
  | _ => None
  end.

Definition simplified_slots (slots: list Loop.expr) : list Loop.expr :=
  map Cleanup.simpl_expr slots.

Definition display_affine_expr
    (slots: list Loop.expr) (e: Instr.affine_expr) : Loop.expr :=
  Cleanup.simpl_expr (lower_affine_expr (simplified_slots slots) e).

Definition display_instr_expr
    (slots: list Loop.expr) (e: Instr.expr) : option Loop.expr :=
  match lower_instr_expr (simplified_slots slots) e with
  | Some le => Some (Cleanup.simpl_expr le)
  | None => None
  end.

Lemma eval_simplified_slots :
  forall env slots,
    map (Loop.eval_expr env) (simplified_slots slots) =
    map (Loop.eval_expr env) slots.
Proof.
  intros env slots.
  unfold simplified_slots.
  apply Cleanup.simpl_expr_list_correct.
Qed.

Lemma lower_affine_expr_correct :
  forall env slots e,
    Loop.eval_expr env (lower_affine_expr slots e) =
    eval_affine_expr e (map (Loop.eval_expr env) slots).
Proof.
  induction e; cbn [lower_affine_expr eval_affine_expr]; intros; try reflexivity.
  - apply slot_expr_correct.
  - rewrite Cleanup.simpl_expr_correct.
    cbn [Loop.eval_expr].
    rewrite IHe1, IHe2. reflexivity.
  - rewrite Cleanup.simpl_expr_correct.
    cbn [Loop.eval_expr].
    rewrite IHe1, IHe2. lia.
  - rewrite Cleanup.simpl_expr_correct.
    cbn [Loop.eval_expr].
    rewrite IHe. reflexivity.
Qed.

Lemma display_affine_expr_correct :
  forall env slots e,
    Loop.eval_expr env (display_affine_expr slots e) =
    eval_affine_expr e (map (Loop.eval_expr env) slots).
Proof.
  intros env slots e.
  unfold display_affine_expr.
  rewrite Cleanup.simpl_expr_correct.
  rewrite lower_affine_expr_correct.
  rewrite eval_simplified_slots.
  reflexivity.
Qed.

Lemma loop_add_correct :
  forall env a b,
    Loop.eval_expr env (loop_add a b) =
    Loop.eval_expr env a + Loop.eval_expr env b.
Proof.
  intros env a b.
  unfold loop_add.
  rewrite Cleanup.simpl_expr_correct.
  reflexivity.
Qed.

Lemma loop_sub_correct :
  forall env a b,
    Loop.eval_expr env (loop_sub a b) =
    Loop.eval_expr env a - Loop.eval_expr env b.
Proof.
  intros env a b.
  unfold loop_sub.
  rewrite Cleanup.simpl_expr_correct.
  simpl. lia.
Qed.

Lemma loop_mul_correct :
  forall env a b out,
    loop_mul a b = Some out ->
    Loop.eval_expr env out =
    Loop.eval_expr env a * Loop.eval_expr env b.
Proof.
  intros env a b out Hmul.
  unfold loop_mul in Hmul.
  destruct a; destruct b; try discriminate;
    inversion Hmul; subst; clear Hmul;
    rewrite Loop.make_mult_correct; simpl;
    try rewrite Z.mul_comm; reflexivity.
Qed.

Lemma loop_div_correct :
  forall env a b out,
    loop_div a b = Some out ->
    Loop.eval_expr env out =
    Loop.eval_expr env a / Loop.eval_expr env b.
Proof.
  intros env a b out Hdiv.
  unfold loop_div in Hdiv.
  destruct b; try discriminate.
  inversion Hdiv; subst; clear Hdiv.
  rewrite Loop.make_div_correct.
  reflexivity.
Qed.

Theorem lower_instr_expr_correct :
  forall env slots e out st,
    lower_instr_expr slots e = Some out ->
    Instr.eval_expr e (map (Loop.eval_expr env) slots) st =
    State.VInt (Loop.eval_expr env out).
Proof.
  induction e; simpl; intros out st Hlow; try discriminate.
  - inversion Hlow; subst. reflexivity.
  - inversion Hlow; subst.
    rewrite slot_expr_correct. reflexivity.
  - destruct (lower_instr_expr slots e1) as [l1|] eqn:H1; try discriminate.
    destruct (lower_instr_expr slots e2) as [l2|] eqn:H2; try discriminate.
    inversion Hlow; subst; clear Hlow.
    rewrite (IHe1 l1 st eq_refl), (IHe2 l2 st eq_refl).
    unfold Instr.value_add.
    f_equal. symmetry. apply loop_add_correct.
  - destruct (lower_instr_expr slots e1) as [l1|] eqn:H1; try discriminate.
    destruct (lower_instr_expr slots e2) as [l2|] eqn:H2; try discriminate.
    inversion Hlow; subst; clear Hlow.
    rewrite (IHe1 l1 st eq_refl), (IHe2 l2 st eq_refl).
    unfold Instr.value_sub.
    f_equal. symmetry. apply loop_sub_correct.
  - destruct (lower_instr_expr slots e1) as [l1|] eqn:H1; try discriminate.
    destruct (lower_instr_expr slots e2) as [l2|] eqn:H2; try discriminate.
    destruct (loop_mul l1 l2) as [lm|] eqn:Hm; try discriminate.
    inversion Hlow; subst; clear Hlow.
    rewrite (IHe1 l1 st eq_refl), (IHe2 l2 st eq_refl).
    unfold Instr.value_mul.
    f_equal. symmetry. eapply loop_mul_correct; eauto.
  - destruct (lower_instr_expr slots e1) as [l1|] eqn:H1; try discriminate.
    destruct (lower_instr_expr slots e2) as [l2|] eqn:H2; try discriminate.
    destruct (loop_div l1 l2) as [ld|] eqn:Hd; try discriminate.
    inversion Hlow; subst; clear Hlow.
    rewrite (IHe1 l1 st eq_refl), (IHe2 l2 st eq_refl).
    unfold Instr.value_div.
    f_equal. symmetry. eapply loop_div_correct; eauto.
Qed.

Theorem display_instr_expr_correct :
  forall env slots e out st,
    display_instr_expr slots e = Some out ->
    Instr.eval_expr e (map (Loop.eval_expr env) slots) st =
    State.VInt (Loop.eval_expr env out).
Proof.
  intros env slots e out st Hdisp.
  unfold display_instr_expr in Hdisp.
  destruct (lower_instr_expr (simplified_slots slots) e) as [le|] eqn:Hlow;
    try discriminate.
  inversion Hdisp; subst; clear Hdisp.
  rewrite Cleanup.simpl_expr_correct.
  rewrite <- (lower_instr_expr_correct env (simplified_slots slots) e le st Hlow).
  rewrite eval_simplified_slots.
  reflexivity.
Qed.
