Require Import Bool.
Require Import List.
Import ListNotations.

Require Import LoopSingletonCleanup.
Require Import LoopUnroll.
Require Import LoopJamNative.
Require Import PolIRs.

Module LoopJamLower (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module Instr := PolIRs.Instr.
Module State := Instr.State.
Module Subst := LoopSingletonCleanup PolIRs.
Module Unroll := LoopUnroll PolIRs.
Module Native := LoopJamNative PolIRs.

Definition seq2 := Native.seq2.
Definition jammed_two_loop := Native.jammed_two_loop.
Definition unjammed_two_loop := Native.unjammed_two_loop.

Definition same_loop_boundsb
    (lb1 ub1 lb2 ub2 : Loop.expr) : bool :=
  Subst.expr_eqb lb1 lb2 && Subst.expr_eqb ub1 ub2.

Definition try_jam_pair (st1 st2 : Loop.stmt) : option Loop.stmt :=
  match st1, st2 with
  | Loop.Loop lb1 ub1 body1, Loop.Loop lb2 ub2 body2 =>
      if same_loop_boundsb lb1 ub1 lb2 ub2
      then Some (jammed_two_loop lb1 ub1 body1 body2)
      else None
  | _, _ => None
  end.

Fixpoint stmt_size (st : Loop.stmt) : nat :=
  match st with
  | Loop.Loop _ _ body => S (stmt_size body)
  | Loop.Instr _ _ => 1
  | Loop.Seq sts => S (stmt_list_size sts)
  | Loop.Guard _ body => S (stmt_size body)
  end
with stmt_list_size (sts : Loop.stmt_list) : nat :=
  match sts with
  | Loop.SNil => 1
  | Loop.SCons st sts' => S (stmt_size st + stmt_list_size sts')
  end.

Fixpoint jam_stmt_fuel (fuel : nat) (st : Loop.stmt) {struct fuel}
    : Loop.stmt * bool :=
  match fuel with
  | O => (st, false)
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          let '(body', changed) := jam_stmt_fuel fuel' body in
          (Loop.Loop lb ub body', changed)
      | Loop.Instr _ _ => (st, false)
      | Loop.Seq sts =>
          let '(sts', changed) := jam_stmt_list_fuel fuel' sts in
          (Loop.Seq sts', changed)
      | Loop.Guard tst body =>
          let '(body', changed) := jam_stmt_fuel fuel' body in
          (Loop.Guard tst body', changed)
      end
  end
with jam_stmt_list_fuel (fuel : nat) (sts : Loop.stmt_list) {struct fuel}
    : Loop.stmt_list * bool :=
  match fuel with
  | O => (sts, false)
  | S fuel' =>
      match sts with
      | Loop.SNil => (Loop.SNil, false)
      | Loop.SCons st Loop.SNil =>
          let '(st', changed) := jam_stmt_fuel fuel' st in
          (Loop.SCons st' Loop.SNil, changed)
      | Loop.SCons st1 (Loop.SCons st2 rest) =>
          let '(st1', changed1) := jam_stmt_fuel fuel' st1 in
          let '(st2', changed2) := jam_stmt_fuel fuel' st2 in
          match try_jam_pair st1' st2' with
          | Some fused =>
              let '(sts', changed_rest) :=
                jam_stmt_list_fuel fuel' (Loop.SCons fused rest) in
              (sts', true || changed1 || changed2 || changed_rest)
          | None =>
              let '(tail', changed_tail) :=
                jam_stmt_list_fuel fuel' (Loop.SCons st2' rest) in
              (Loop.SCons st1' tail',
               changed1 || changed2 || changed_tail)
          end
      end
  end.

Definition jam_stmt (st : Loop.stmt) : Loop.stmt :=
  fst (jam_stmt_fuel (S (stmt_size st + stmt_size st)) st).

Definition jam_stmt_changed (st : Loop.stmt) : bool :=
  snd (jam_stmt_fuel (S (stmt_size st + stmt_size st)) st).

Definition jam_loop (prog : Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (jam_stmt st, ctxt, vars).

Definition jam_loop_changed (prog : Loop.t) : bool :=
  let '(st, _, _) := prog in
  jam_stmt_changed st.

Fixpoint unrolljam_stmt_fuel
    (fuel factor : nat) (st : Loop.stmt) {struct fuel} : Loop.stmt :=
  match fuel with
  | O => st
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          descend_unrolljam_stmt_fuel
            fuel' factor
            (jam_stmt (Unroll.block_unroll_stmt factor lb ub body))
      | Loop.Instr _ _ => st
      | Loop.Seq sts =>
          Loop.Seq (unrolljam_stmt_list_fuel fuel' factor sts)
      | Loop.Guard tst body =>
          Loop.Guard tst (unrolljam_stmt_fuel fuel' factor body)
      end
  end
with unrolljam_stmt_list_fuel
    (fuel factor : nat) (sts : Loop.stmt_list) {struct fuel}
    : Loop.stmt_list :=
  match fuel with
  | O => sts
  | S fuel' =>
      match sts with
      | Loop.SNil => Loop.SNil
      | Loop.SCons st sts' =>
          Loop.SCons
            (unrolljam_stmt_fuel fuel' factor st)
            (unrolljam_stmt_list_fuel fuel' factor sts')
      end
  end
with descend_unrolljam_stmt_fuel
    (fuel factor : nat) (st : Loop.stmt) {struct fuel} : Loop.stmt :=
  match fuel with
  | O => st
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          Loop.Loop lb ub (unrolljam_stmt_fuel fuel' factor body)
      | Loop.Instr _ _ => st
      | Loop.Seq sts =>
          Loop.Seq (descend_unrolljam_stmt_list_fuel fuel' factor sts)
      | Loop.Guard tst body =>
          Loop.Guard tst (descend_unrolljam_stmt_fuel fuel' factor body)
      end
  end
with descend_unrolljam_stmt_list_fuel
    (fuel factor : nat) (sts : Loop.stmt_list) {struct fuel}
    : Loop.stmt_list :=
  match fuel with
  | O => sts
  | S fuel' =>
      match sts with
      | Loop.SNil => Loop.SNil
      | Loop.SCons st sts' =>
          Loop.SCons
            (descend_unrolljam_stmt_fuel fuel' factor st)
            (descend_unrolljam_stmt_list_fuel fuel' factor sts')
      end
  end.

Definition unrolljam_stmt (factor : nat) (st : Loop.stmt) : Loop.stmt :=
  unrolljam_stmt_fuel (S (stmt_size st + stmt_size st + stmt_size st)) factor st.

Definition unrolljam_loop (factor : nat) (prog : Loop.t) : Loop.t :=
  let '(st, ctxt, vars) := prog in
  (unrolljam_stmt factor st, ctxt, vars).

Theorem try_jam_pair_exact_sound :
  forall lb ub body1 body2 fused env il mem1 mem2,
    try_jam_pair
      (Loop.Loop lb ub body1)
      (Loop.Loop lb ub body2) = Some fused ->
    Instr.NonAlias mem1 ->
    Native.trace_safe_stmt (unjammed_two_loop lb ub body1 body2) ->
    Loop.loop_instance_list_semantics fused env il mem1 mem2 ->
    Native.same_range_trace_cross_permutable lb ub body1 body2 env ->
    exists mem2',
      Loop.loop_semantics
        (unjammed_two_loop lb ub body1 body2) env mem1 mem2' /\
      State.eq mem2 mem2'.
Proof.
  intros lb ub body1 body2 fused env il mem1 mem2
    Hjam Hna Hsafe Hinst Hperm.
  unfold try_jam_pair, same_loop_boundsb in Hjam.
  rewrite !Unroll.expr_eqb_refl in Hjam.
  inversion Hjam; subst fused; clear Hjam.
  eapply Native.jammed_two_loop_instance_refines_unjammed; eauto.
Qed.

End LoopJamLower.
