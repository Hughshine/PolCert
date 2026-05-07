Require Import Bool.
Require Import List.
Require Import ZArith.
Import ListNotations.

Require Import ImpureAlarmConfig.
Require Import Result.
Require Import Vpl.Impure.
Require Import LoopSingletonCleanup.
Require Import LoopUnroll.
Require Import LoopJamNative.
Require Import LoopJamValidator.
Require Import PolIRs.

Module LoopJamLower (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module Instr := PolIRs.Instr.
Module Ty := PolIRs.Ty.
Module State := Instr.State.
Module Subst := LoopSingletonCleanup PolIRs.
Module Unroll := LoopUnroll PolIRs.
Module Native := LoopJamNative PolIRs.
Module Validator := LoopJamValidator PolIRs.

Definition seq2 := Native.seq2.
Definition jammed_two_loop := Native.jammed_two_loop.
Definition unjammed_two_loop := Native.unjammed_two_loop.

Definition same_loop_boundsb
    (lb1 ub1 lb2 ub2 : Loop.expr) : bool :=
  Subst.expr_eqb lb1 lb2 && Subst.expr_eqb ub1 ub2.

Fixpoint same_testb (t1 t2 : Loop.test) : bool :=
  match t1, t2 with
  | Loop.LE a1 b1, Loop.LE a2 b2 =>
      Subst.expr_eqb a1 a2 && Subst.expr_eqb b1 b2
  | Loop.EQ a1 b1, Loop.EQ a2 b2 =>
      Subst.expr_eqb a1 a2 && Subst.expr_eqb b1 b2
  | Loop.And a1 b1, Loop.And a2 b2 =>
      same_testb a1 a2 && same_testb b1 b2
  | Loop.Or a1 b1, Loop.Or a2 b2 =>
      same_testb a1 a2 && same_testb b1 b2
  | Loop.Not t1', Loop.Not t2' =>
      same_testb t1' t2'
  | Loop.TConstantTest b1, Loop.TConstantTest b2 =>
      Bool.eqb b1 b2
  | _, _ => false
  end.

Definition try_jam_pair (st1 st2 : Loop.stmt) : option Loop.stmt :=
  match st1, st2 with
  | Loop.Loop lb1 ub1 body1, Loop.Loop lb2 ub2 body2 =>
      if same_loop_boundsb lb1 ub1 lb2 ub2
      then Some (jammed_two_loop lb1 ub1 body1 body2)
      else None
  | Loop.Guard tst1 (Loop.Loop lb1 ub1 body1),
    Loop.Guard tst2 (Loop.Loop lb2 ub2 body2) =>
      if same_testb tst1 tst2 && same_loop_boundsb lb1 ub1 lb2 ub2
      then Some (Loop.Guard tst1 (jammed_two_loop lb1 ub1 body1 body2))
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

Record unrolljam_candidate : Type := {
  uj_depth : nat;
  uj_path : option (list nat)
}.

Definition unrolljam_plan : Type := list unrolljam_candidate.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Definition unrolljam_candidate_selects_loopb
    (depth : nat) (path : list nat) (cand : unrolljam_candidate) : bool :=
  Nat.eqb depth (uj_depth cand) &&
  match uj_path cand with
  | None => true
  | Some cand_path => nat_list_eqb path cand_path
  end.

Definition unrolljam_plan_selects_loopb
    (depth : nat) (path : list nat) (plan : unrolljam_plan) : bool :=
  existsb (unrolljam_candidate_selects_loopb depth path) plan.

Fixpoint unrolljam_depth_plan_from
    (fuel start : nat) : unrolljam_plan :=
  match fuel with
  | O => []
  | S fuel' =>
      {| uj_depth := start; uj_path := None |} ::
      unrolljam_depth_plan_from fuel' (S start)
  end.

Definition unrolljam_all_depths_plan (fuel : nat) : unrolljam_plan :=
  unrolljam_depth_plan_from fuel 0.

Example empty_unrolljam_plan_rejects_depth_example :
  unrolljam_plan_selects_loopb 0 [] [] = false.
Proof. reflexivity. Qed.

Example singleton_unrolljam_plan_accepts_depth_example :
  unrolljam_plan_selects_loopb
    2 [0; 1] [{| uj_depth := 2; uj_path := None |}] = true.
Proof. reflexivity. Qed.

Example path_unrolljam_plan_accepts_matching_path_example :
  unrolljam_plan_selects_loopb
    2 [0; 1] [{| uj_depth := 2; uj_path := Some [0; 1] |}] = true.
Proof. reflexivity. Qed.

Example path_unrolljam_plan_rejects_mismatched_path_example :
  unrolljam_plan_selects_loopb
    2 [1; 0] [{| uj_depth := 2; uj_path := Some [0; 1] |}] = false.
Proof. reflexivity. Qed.

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

Definition checked_pair_accepts
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (body1 body2 : Loop.stmt) : imp bool :=
  BIND cert_res <-
    Validator.checked_loop_jam_pair_at_depth
      varctxt vars depth body1 body2 -;
  match cert_res with
  | Okk _ => pure true
  | Err _ => pure false
  end.

Definition checked_try_jam_pair
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (st1 st2 : Loop.stmt) : imp (option Loop.stmt) :=
  match st1, st2 with
  | Loop.Loop lb1 ub1 body1, Loop.Loop lb2 ub2 body2 =>
      if same_loop_boundsb lb1 ub1 lb2 ub2
      then
        BIND ok <- checked_pair_accepts varctxt vars depth body1 body2 -;
        if ok
        then pure (Some (jammed_two_loop lb1 ub1 body1 body2))
        else pure None
      else pure None
  | Loop.Guard tst1 (Loop.Loop lb1 ub1 body1),
    Loop.Guard tst2 (Loop.Loop lb2 ub2 body2) =>
      if same_testb tst1 tst2 && same_loop_boundsb lb1 ub1 lb2 ub2
      then
        BIND ok <- checked_pair_accepts varctxt vars depth body1 body2 -;
        if ok
        then pure (Some (Loop.Guard tst1 (jammed_two_loop lb1 ub1 body1 body2)))
        else pure None
      else pure None
  | _, _ => pure None
  end.

Fixpoint checked_jam_stmt_fuel
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth fuel : nat) (st : Loop.stmt) {struct fuel}
    : imp (Loop.stmt * bool) :=
  match fuel with
  | O => pure (st, false)
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          BIND body_res <-
            checked_jam_stmt_fuel varctxt vars (S depth) fuel' body -;
          let '(body', changed) := body_res in
          pure (Loop.Loop lb ub body', changed)
      | Loop.Instr _ _ => pure (st, false)
      | Loop.Seq sts =>
          BIND sts_res <-
            checked_jam_stmt_list_fuel varctxt vars depth fuel' sts -;
          let '(sts', changed) := sts_res in
          pure (Loop.Seq sts', changed)
      | Loop.Guard tst body =>
          BIND body_res <-
            checked_jam_stmt_fuel varctxt vars depth fuel' body -;
          let '(body', changed) := body_res in
          pure (Loop.Guard tst body', changed)
      end
  end
with checked_jam_stmt_list_fuel
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth fuel : nat) (sts : Loop.stmt_list) {struct fuel}
    : imp (Loop.stmt_list * bool) :=
  match fuel with
  | O => pure (sts, false)
  | S fuel' =>
      match sts with
      | Loop.SNil => pure (Loop.SNil, false)
      | Loop.SCons st Loop.SNil =>
          BIND st_res <-
            checked_jam_stmt_fuel varctxt vars depth fuel' st -;
          let '(st', changed) := st_res in
          pure (Loop.SCons st' Loop.SNil, changed)
      | Loop.SCons st1 (Loop.SCons st2 rest) =>
          BIND st1_res <-
            checked_jam_stmt_fuel varctxt vars depth fuel' st1 -;
          let '(st1', changed1) := st1_res in
          BIND st2_res <-
            checked_jam_stmt_fuel varctxt vars depth fuel' st2 -;
          let '(st2', changed2) := st2_res in
          BIND fused_opt <-
            checked_try_jam_pair varctxt vars depth st1' st2' -;
          match fused_opt with
          | Some fused =>
              BIND rest_res <-
                checked_jam_stmt_list_fuel
                  varctxt vars depth fuel' (Loop.SCons fused rest) -;
              let '(sts', changed_rest) := rest_res in
              pure (sts', true || changed1 || changed2 || changed_rest)
          | None =>
              BIND tail_res <-
                checked_jam_stmt_list_fuel
                  varctxt vars depth fuel' (Loop.SCons st2' rest) -;
              let '(tail', changed_tail) := tail_res in
              pure (Loop.SCons st1' tail',
                    changed1 || changed2 || changed_tail)
          end
      end
  end.

Definition checked_jam_stmt
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (st : Loop.stmt) : imp (Loop.stmt * bool) :=
  checked_jam_stmt_fuel
    varctxt vars depth (S (stmt_size st + stmt_size st)) st.

Fixpoint checked_unrolljam_stmt_with_plan_fuel
    (plan : unrolljam_plan)
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (path : list nat) (fuel factor : nat)
    (st : Loop.stmt) {struct fuel}
    : imp Loop.stmt :=
  match fuel with
  | O => pure st
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          if unrolljam_plan_selects_loopb depth path plan
          then
            BIND jammed_res <-
              checked_jam_stmt
                varctxt vars depth
                (Unroll.block_unroll_stmt factor lb ub body) -;
            let '(jammed, _) := jammed_res in
            checked_descend_unrolljam_stmt_with_plan_fuel
              plan varctxt vars depth path fuel' factor jammed
          else
            BIND body' <-
              checked_unrolljam_stmt_with_plan_fuel
                plan varctxt vars (S depth) (path ++ [0]) fuel' factor body -;
            pure (Loop.Loop lb ub body')
      | Loop.Instr _ _ => pure st
      | Loop.Seq sts =>
          BIND sts' <-
            checked_unrolljam_stmt_list_with_plan_fuel
              plan varctxt vars depth path 0 fuel' factor sts -;
          pure (Loop.Seq sts')
      | Loop.Guard tst body =>
          BIND body' <-
            checked_unrolljam_stmt_with_plan_fuel
              plan varctxt vars depth (path ++ [0]) fuel' factor body -;
          pure (Loop.Guard tst body')
      end
  end
with checked_unrolljam_stmt_list_with_plan_fuel
    (plan : unrolljam_plan)
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (path : list nat) (index fuel factor : nat)
    (sts : Loop.stmt_list) {struct fuel}
    : imp Loop.stmt_list :=
  match fuel with
  | O => pure sts
  | S fuel' =>
      match sts with
      | Loop.SNil => pure Loop.SNil
      | Loop.SCons st sts' =>
          BIND st' <-
            checked_unrolljam_stmt_with_plan_fuel
              plan varctxt vars depth (path ++ [index]) fuel' factor st -;
          BIND sts'' <-
            checked_unrolljam_stmt_list_with_plan_fuel
              plan varctxt vars depth path (S index) fuel' factor sts' -;
          pure (Loop.SCons st' sts'')
      end
  end
with checked_descend_unrolljam_stmt_with_plan_fuel
    (plan : unrolljam_plan)
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (path : list nat) (fuel factor : nat)
    (st : Loop.stmt) {struct fuel}
    : imp Loop.stmt :=
  match fuel with
  | O => pure st
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          BIND body' <-
            checked_unrolljam_stmt_with_plan_fuel
              plan varctxt vars (S depth) (path ++ [0]) fuel' factor body -;
          pure (Loop.Loop lb ub body')
      | Loop.Instr _ _ => pure st
      | Loop.Seq sts =>
          BIND sts' <-
            checked_descend_unrolljam_stmt_list_with_plan_fuel
              plan varctxt vars depth path 0 fuel' factor sts -;
          pure (Loop.Seq sts')
      | Loop.Guard tst body =>
          BIND body' <-
            checked_descend_unrolljam_stmt_with_plan_fuel
              plan varctxt vars depth (path ++ [0]) fuel' factor body -;
          pure (Loop.Guard tst body')
      end
  end
with checked_descend_unrolljam_stmt_list_with_plan_fuel
    (plan : unrolljam_plan)
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (path : list nat) (index fuel factor : nat)
    (sts : Loop.stmt_list) {struct fuel}
    : imp Loop.stmt_list :=
  match fuel with
  | O => pure sts
  | S fuel' =>
      match sts with
      | Loop.SNil => pure Loop.SNil
      | Loop.SCons st sts' =>
          BIND st' <-
            checked_descend_unrolljam_stmt_with_plan_fuel
              plan varctxt vars depth (path ++ [index]) fuel' factor st -;
          BIND sts'' <-
            checked_descend_unrolljam_stmt_list_with_plan_fuel
              plan varctxt vars depth path (S index) fuel' factor sts' -;
          pure (Loop.SCons st' sts'')
      end
  end.

Definition checked_unrolljam_stmt_with_plan
    (plan : unrolljam_plan)
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (factor : nat) (st : Loop.stmt) : imp Loop.stmt :=
  checked_unrolljam_stmt_with_plan_fuel
    plan varctxt vars 0 []
    (S (stmt_size st + stmt_size st + stmt_size st))
    factor st.

Definition checked_unrolljam_loop_with_plan
    (plan : unrolljam_plan)
    (factor : nat) (prog : Loop.t) : imp Loop.t :=
  let '(st, ctxt, vars) := prog in
  BIND st' <- checked_unrolljam_stmt_with_plan plan ctxt vars factor st -;
  pure (st', ctxt, vars).

Fixpoint checked_unrolljam_stmt_fuel
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth fuel factor : nat) (st : Loop.stmt) {struct fuel}
    : imp Loop.stmt :=
  match fuel with
  | O => pure st
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          BIND jammed_res <-
            checked_jam_stmt
              varctxt vars depth
              (Unroll.block_unroll_stmt factor lb ub body) -;
          let '(jammed, _) := jammed_res in
          checked_descend_unrolljam_stmt_fuel
            varctxt vars depth fuel' factor jammed
      | Loop.Instr _ _ => pure st
      | Loop.Seq sts =>
          BIND sts' <-
            checked_unrolljam_stmt_list_fuel
              varctxt vars depth fuel' factor sts -;
          pure (Loop.Seq sts')
      | Loop.Guard tst body =>
          BIND body' <-
            checked_unrolljam_stmt_fuel
              varctxt vars depth fuel' factor body -;
          pure (Loop.Guard tst body')
      end
  end
with checked_unrolljam_stmt_list_fuel
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth fuel factor : nat) (sts : Loop.stmt_list) {struct fuel}
    : imp Loop.stmt_list :=
  match fuel with
  | O => pure sts
  | S fuel' =>
      match sts with
      | Loop.SNil => pure Loop.SNil
      | Loop.SCons st sts' =>
          BIND st' <-
            checked_unrolljam_stmt_fuel
              varctxt vars depth fuel' factor st -;
          BIND sts'' <-
            checked_unrolljam_stmt_list_fuel
              varctxt vars depth fuel' factor sts' -;
          pure (Loop.SCons st' sts'')
      end
  end
with checked_descend_unrolljam_stmt_fuel
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth fuel factor : nat) (st : Loop.stmt) {struct fuel}
    : imp Loop.stmt :=
  match fuel with
  | O => pure st
  | S fuel' =>
      match st with
      | Loop.Loop lb ub body =>
          BIND body' <-
            checked_unrolljam_stmt_fuel
              varctxt vars (S depth) fuel' factor body -;
          pure (Loop.Loop lb ub body')
      | Loop.Instr _ _ => pure st
      | Loop.Seq sts =>
          BIND sts' <-
            checked_descend_unrolljam_stmt_list_fuel
              varctxt vars depth fuel' factor sts -;
          pure (Loop.Seq sts')
      | Loop.Guard tst body =>
          BIND body' <-
            checked_descend_unrolljam_stmt_fuel
              varctxt vars depth fuel' factor body -;
          pure (Loop.Guard tst body')
      end
  end
with checked_descend_unrolljam_stmt_list_fuel
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth fuel factor : nat) (sts : Loop.stmt_list) {struct fuel}
    : imp Loop.stmt_list :=
  match fuel with
  | O => pure sts
  | S fuel' =>
      match sts with
      | Loop.SNil => pure Loop.SNil
      | Loop.SCons st sts' =>
          BIND st' <-
            checked_descend_unrolljam_stmt_fuel
              varctxt vars depth fuel' factor st -;
          BIND sts'' <-
            checked_descend_unrolljam_stmt_list_fuel
              varctxt vars depth fuel' factor sts' -;
          pure (Loop.SCons st' sts'')
      end
  end.

Definition checked_unrolljam_stmt
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (factor : nat) (st : Loop.stmt) : imp Loop.stmt :=
  checked_unrolljam_stmt_fuel
    varctxt vars 0
    (S (stmt_size st + stmt_size st + stmt_size st))
    factor st.

Definition checked_unrolljam_loop
    (factor : nat) (prog : Loop.t) : imp Loop.t :=
  let '(st, ctxt, vars) := prog in
  BIND st' <- checked_unrolljam_stmt ctxt vars factor st -;
  pure (st', ctxt, vars).

End LoopJamLower.
