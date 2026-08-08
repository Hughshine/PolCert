Require Import ZArith.
Require Import Bool.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import String.

Require Import PolIRs.

Require Import AST.
Require Import Base.
Require Import PolyBase.
Require Import List.
Require Import SetoidList.
Import ListNotations.

Require Import Linalg.
Require Import Lia.
Require Import LibTactics.
Require Import sflib.
Require Import Misc.
Require Import AffineValidator.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import PointWitness.

Module Extractor (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Module Loop := PolIRs.Loop.
Module Val := AffineValidator PolIRs.
Definition ident := Instr.ident.

(** * Proof map

    The executable half of this file translates affine expressions, tests,
    and structured statements into polyhedral instructions.  The proof half
    reconstructs the syntax-directed loop execution from the flattened list
    of extracted instances.  Its main technical steps split that sorted list
    at sequence boundaries and at successive loop-iterator values.

    [core_sched_stmt_stmts_constrs_prefix_mutual] is the structural induction.
    [extract_stmt_to_loop_semantics_core_sched_constrs] specializes it to an
    empty iterator prefix, and [extractor_correct] packages the result for
    complete loop and polyhedral programs. *)

(** * Affine frontend checks *)

(* Note: empty domain contains exactly one instance: [] (empty list) *)

(** The loop language already owns this conversion.  Keep the historical
    extractor path as an alias rather than maintaining a second implementation. *)
Definition expr_to_aff := Loop.expr_to_aff.

Fixpoint wf_affine_expr (e: PolIRs.Loop.expr): bool :=
    match e with
    | PolIRs.Loop.Constant _ => true
    | PolIRs.Loop.Var _ => true
    | PolIRs.Loop.Mult _ e' => wf_affine_expr e'
    | PolIRs.Loop.Sum e1 e2 => wf_affine_expr e1 && wf_affine_expr e2
    | _ => false
    end.

Fixpoint wf_affine_expr_list (es: list PolIRs.Loop.expr): bool :=
    match es with
    | [] => true
    | e :: es' => wf_affine_expr e && wf_affine_expr_list es'
    end.

Fixpoint wf_affine_test (tst: PolIRs.Loop.test): bool :=
    match tst with
    | PolIRs.Loop.LE e1 e2 => wf_affine_expr e1 && wf_affine_expr e2
    | PolIRs.Loop.EQ e1 e2 => wf_affine_expr e1 && wf_affine_expr e2
    | PolIRs.Loop.And t1 t2 => wf_affine_test t1 && wf_affine_test t2
    | _ => false
    end.

Fixpoint wf_scop_stmt (stmt: PolIRs.Loop.stmt): bool :=
    match stmt with
    | PolIRs.Loop.Instr _ es => wf_affine_expr_list es
    | PolIRs.Loop.Seq stmts => wf_scop_stmts stmts
    | PolIRs.Loop.Loop lb ub body =>
        wf_affine_expr lb && wf_affine_expr ub && wf_scop_stmt body
    | PolIRs.Loop.Guard test body =>
        wf_affine_test test && wf_scop_stmt body
    end
with wf_scop_stmts (stmts: PolIRs.Loop.stmt_list): bool :=
    match stmts with
    | PolIRs.Loop.SNil => true
    | PolIRs.Loop.SCons stmt stmts' => wf_scop_stmt stmt && wf_scop_stmts stmts'
    end.

Lemma andb_true_iff_local0:
    forall b1 b2, (b1 && b2)%bool = true <-> b1 = true /\ b2 = true.
Proof.
    exact andb_true_iff.
Qed.

Lemma wf_scop_seq_inv:
    forall stmts,
    wf_scop_stmt (PolIRs.Loop.Seq stmts) = true ->
    wf_scop_stmts stmts = true.
Proof.
    intros stmts Hwf.
    simpl in Hwf. exact Hwf.
Qed.

Lemma wf_scop_loop_inv:
    forall lb ub body,
    wf_scop_stmt (PolIRs.Loop.Loop lb ub body) = true ->
    wf_affine_expr lb = true /\
    wf_affine_expr ub = true /\
    wf_scop_stmt body = true.
Proof.
    intros lb ub body Hwf.
    simpl in Hwf.
    eapply andb_true_iff_local0 in Hwf.
    destruct Hwf as [Hlbub Hbody].
    eapply andb_true_iff_local0 in Hlbub.
    destruct Hlbub as [Hlb Hub].
    repeat split; auto.
Qed.

Lemma wf_scop_guard_inv:
    forall test body,
    wf_scop_stmt (PolIRs.Loop.Guard test body) = true ->
    wf_affine_test test = true /\
    wf_scop_stmt body = true.
Proof.
    intros test body Hwf.
    simpl in Hwf.
    eapply andb_true_iff_local0 in Hwf.
    exact Hwf.
Qed.

Lemma wf_scop_stmts_cons_inv:
    forall stmt stmts',
    wf_scop_stmts (PolIRs.Loop.SCons stmt stmts') = true ->
    wf_scop_stmt stmt = true /\
    wf_scop_stmts stmts' = true.
Proof.
    intros stmt stmts' Hwf.
    simpl in Hwf.
    eapply andb_true_iff_local0 in Hwf.
    exact Hwf.
Qed.

Lemma expr_to_aff_correct: 
    forall e env aff v z, expr_to_aff e = Okk aff -> 
    aff = (v, z) ->
    PolIRs.Loop.eval_expr env e = (dot_product env v) + z.
Proof.
    exact Loop.expr_to_aff_correct.
Qed.

Example test_expr_to_aff_1: 
    expr_to_aff (PolIRs.Loop.Constant 5%Z) = Okk ([], 5%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_2:
    (expr_to_aff (PolIRs.Loop.Var 3)) = Okk ([0%Z; 0%Z; 0%Z; 1%Z], 0%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_3:
    (expr_to_aff (PolIRs.Loop.Mult 2%Z (PolIRs.Loop.Var 4))) = Okk ([0%Z; 0%Z; 0%Z; 0%Z; 2%Z], 0%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_4: 
    (expr_to_aff (PolIRs.Loop.Sum (PolIRs.Loop.Var 3) (PolIRs.Loop.Constant 5%Z))) = Okk ([0%Z; 0%Z; 0%Z; 1%Z], 5%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_5: 
    (expr_to_aff (PolIRs.Loop.Sum 
                        (PolIRs.Loop.Var 3) 
                        (PolIRs.Loop.Mult 2%Z (PolIRs.Loop.Var 4))
                    )) 
    = Okk ([0%Z; 0%Z; 0%Z; 1%Z; 2%Z], 0%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_6: 
    (expr_to_aff (PolIRs.Loop.Sum 
                        (PolIRs.Loop.Var 3) 
                    (PolIRs.Loop.Sum 
                        (PolIRs.Loop.Mult 2%Z (PolIRs.Loop.Var 4))
                        (PolIRs.Loop.Constant 5%Z)
                    )))
    = Okk ([0%Z; 0%Z; 0%Z; 1%Z; 2%Z], 5%Z).
Proof. reflexivity. Qed.

Fixpoint exprlist_to_aff (es: list PolIRs.Loop.expr) (cols: nat): result (list (list Z * Z))
:= 
    match es with 
    | [] => Okk []
    | e :: es' => 
        match (expr_to_aff e) with 
        | Okk (v, c) =>
            let aff := (resize cols v, c) in
            match (exprlist_to_aff es' cols) with
            | Okk affs => Okk (aff :: affs)
            | Err msg => Err msg
            end
        | Err msg => Err msg
        end
    end.

Lemma exprlist_to_aff_correct:
    forall es env cols affs,
    exprlist_to_aff es cols = Okk affs ->
    Datatypes.length env = cols ->
    map (Loop.eval_expr env) es = affine_product affs env.
Proof.
    induction es as [|e es IH]; intros env cols affs Haff Hlen; simpl in Haff.
    - inversion Haff; clear Haff; subst affs. reflexivity.
    - destruct (expr_to_aff e) as [[v c]|msg] eqn:He; try discriminate.
      destruct (exprlist_to_aff es cols) as [affs'|msg'] eqn:Hes; try discriminate.
      pose proof Hlen as Hlen0.
      inversion Haff; clear Haff; subst affs. simpl.
      f_equal.
      + pose proof (expr_to_aff_correct e env (v, c) v c He eq_refl) as Heval.
        simpl.
        rewrite Heval.
        rewrite dot_product_commutative.
        assert (dot_product (resize cols v) env = dot_product v env) as Hdot.
        { rewrite <- Hlen0. rewrite dot_product_resize_left. reflexivity. }
        rewrite Hdot.
        reflexivity.
      + eapply IH; eauto.
Qed.

Definition normalize_affine (cols: nat) (aff: list Z * Z): (list Z * Z) :=
    let (v, c) := aff in (resize cols v, c).

Definition normalize_affine_list (cols: nat) (affs: list (list Z * Z)) :=
    map (normalize_affine cols) affs.

Definition normalize_access (cols: nat) (acc: AccessFunction): AccessFunction :=
    let (arrid, affs) := acc in (arrid, normalize_affine_list cols affs).

Definition normalize_access_list (cols: nat) (accs: list AccessFunction) :=
    map (normalize_access cols) accs.

Definition lift_affine (aff: list Z * Z): (list Z * Z) :=
    let (v, c) := aff in (0%Z :: v, c).

Definition lift_affine_list (affs: list (list Z * Z)) :=
    map lift_affine affs.

Fixpoint lift_affine_list_n (n: nat) (affs: list (list Z * Z)) :=
    match n with
    | O => affs
    | S n' => lift_affine_list (lift_affine_list_n n' affs)
    end.

Lemma lift_affine_list_app:
    forall l1 l2,
    lift_affine_list (l1 ++ l2) = lift_affine_list l1 ++ lift_affine_list l2.
Proof.
    intros l1 l2.
    unfold lift_affine_list.
    rewrite map_app.
    reflexivity.
Qed.

Lemma lift_affine_list_n_app:
    forall n l1 l2,
    lift_affine_list_n n (l1 ++ l2) =
    lift_affine_list_n n l1 ++ lift_affine_list_n n l2.
Proof.
    induction n as [|n IH]; intros l1 l2; simpl.
    - reflexivity.
    - rewrite IH.
      rewrite lift_affine_list_app.
      reflexivity.
Qed.

Lemma lift_affine_list_n_succ:
    forall n l,
    lift_affine_list_n n (lift_affine_list l) =
    lift_affine_list_n (S n) l.
Proof.
    induction n as [|n IH]; intros l; simpl.
    - reflexivity.
    - rewrite IH.
      reflexivity.
Qed.

Lemma lift_affine_satisfies_constraint:
    forall i env aff,
    satisfies_constraint (i :: env) (lift_affine aff) =
    satisfies_constraint env aff.
Proof.
    intros i env [v c].
    unfold lift_affine.
    unfold satisfies_constraint.
    simpl.
    rewrite Z.mul_0_r.
    reflexivity.
Qed.

Lemma lift_affine_list_satisfies_constraint:
    forall i env affs,
    forallb (satisfies_constraint (i :: env)) (lift_affine_list affs) =
    forallb (satisfies_constraint env) affs.
Proof.
    intros i env affs.
    induction affs as [|aff affs IH]; simpl.
    - reflexivity.
    - rewrite lift_affine_satisfies_constraint.
      rewrite IH.
      reflexivity.
Qed.

Lemma in_poly_lift_affine_list:
    forall i env affs,
    in_poly (i :: env) (lift_affine_list affs) = in_poly env affs.
Proof.
    intros i env affs.
    unfold in_poly.
    eapply lift_affine_list_satisfies_constraint.
Qed.

Lemma in_poly_lift_affine_list_n_app:
    forall prefix suffix affs,
    in_poly (prefix ++ suffix) (lift_affine_list_n (Datatypes.length prefix) affs) =
    in_poly suffix affs.
Proof.
    induction prefix as [|x prefix IH]; intros suffix affs; simpl.
    - reflexivity.
    - rewrite in_poly_lift_affine_list.
      eapply IH.
Qed.

Lemma lift_affine_eval:
    forall i env aff,
    dot_product (fst (lift_affine aff)) (i :: env) + snd (lift_affine aff) =
    dot_product (fst aff) env + snd aff.
Proof.
    intros i env [v c].
    unfold lift_affine.
    simpl.
    lia.
Qed.

Lemma lift_affine_list_affine_product:
    forall i env affs,
    affine_product (lift_affine_list affs) (i :: env) =
    affine_product affs env.
Proof.
    intros i env affs.
    induction affs as [|aff affs IH]; simpl.
    - reflexivity.
    - rewrite lift_affine_eval.
      rewrite IH.
      reflexivity.
Qed.

Lemma affine_product_lift_affine_list_n_app:
    forall prefix suffix affs,
    affine_product (lift_affine_list_n (Datatypes.length prefix) affs) (prefix ++ suffix) =
    affine_product affs suffix.
Proof.
    induction prefix as [|x prefix IH]; intros suffix affs; simpl.
    - reflexivity.
    - rewrite lift_affine_list_affine_product.
      rewrite IH.
      reflexivity.
Qed.

Lemma dot_product_repeat_zero_left:
    forall n l,
    dot_product (repeat 0%Z n) l = 0%Z.
Proof.
    exact Linalg.dot_product_repeat_zero_left.
Qed.

Lemma affine_product_loop_row:
    forall cols i env,
    affine_product [((1%Z :: repeat 0%Z cols), 0%Z)] (i :: env) = [i].
Proof.
    intros cols i env.
    simpl.
    rewrite dot_product_repeat_zero_left.
    f_equal.
    lia.
Qed.

Lemma affine_product_app:
    forall m1 m2 p,
    affine_product (m1 ++ m2) p = affine_product m1 p ++ affine_product m2 p.
Proof.
    intros m1 m2 p.
    unfold affine_product.
    rewrite map_app.
    reflexivity.
Qed.

Lemma affine_product_sched_prefix_seq:
    forall sched cols env pos,
    affine_product (sched ++ [(repeat 0%Z cols, pos)]) env =
    affine_product sched env ++ [pos].
Proof.
    intros sched cols env pos.
    rewrite affine_product_app.
    simpl.
    rewrite dot_product_repeat_zero_left.
    reflexivity.
Qed.

Lemma affine_product_sched_prefix_loop:
    forall sched cols i env,
    affine_product (lift_affine_list sched ++ [((1%Z :: repeat 0%Z cols), 0%Z)]) (i :: env) =
    affine_product sched env ++ [i].
Proof.
    intros sched cols i env.
    rewrite affine_product_app.
    rewrite lift_affine_list_affine_product.
    rewrite affine_product_loop_row.
    reflexivity.
Qed.

Lemma in_poly_lift_app_cons2_inv:
    forall i env constrs c1 c2,
    in_poly (i :: env) (lift_affine_list constrs ++ [c1; c2]) = true ->
    in_poly env constrs = true /\
    satisfies_constraint (i :: env) c1 = true /\
    satisfies_constraint (i :: env) c2 = true.
Proof.
    intros i env constrs c1 c2 Hin.
    unfold in_poly in Hin.
    rewrite forallb_app in Hin.
    eapply andb_prop in Hin.
    destruct Hin as [Hlift Htail].
    simpl in Htail.
    eapply andb_prop in Htail.
    destruct Htail as [Hc1 Hrest].
    eapply andb_prop in Hrest.
    destruct Hrest as [Hc2 _].
    split.
    - unfold in_poly.
      rewrite lift_affine_list_satisfies_constraint in Hlift.
      exact Hlift.
    - split; auto.
Qed.

Definition normalize_affine_rev (cols: nat) (aff: list Z * Z): (list Z * Z) :=
    let (v, c) := aff in (rev (resize cols v), c).

Definition normalize_affine_list_rev (cols: nat) (affs: list (list Z * Z)) :=
    map (normalize_affine_rev cols) affs.

Lemma normalize_affine_satisfies_constraint:
    forall cols env aff,
    Datatypes.length env = cols ->
    satisfies_constraint env (normalize_affine cols aff) =
    satisfies_constraint env aff.
Proof.
    intros cols env [v c] Hlen.
    unfold normalize_affine. simpl.
    unfold satisfies_constraint. simpl.
    rewrite <- Hlen.
    rewrite dot_product_resize_right.
    reflexivity.
Qed.

Lemma normalize_affine_list_satisfies_constraint:
    forall cols env affs,
    Datatypes.length env = cols ->
    forallb (satisfies_constraint env) (normalize_affine_list cols affs) =
    forallb (satisfies_constraint env) affs.
Proof.
    intros cols env affs Hlen.
    induction affs as [|aff affs IH]; simpl.
    - reflexivity.
    - rewrite normalize_affine_satisfies_constraint with (cols:=cols) (env:=env) (aff:=aff) by auto.
      f_equal. exact IH.
Qed.

Lemma dot_product_rev:
    forall xs ys,
    Datatypes.length xs = Datatypes.length ys ->
    dot_product (rev xs) (rev ys) = dot_product xs ys.
Proof.
    induction xs as [|x xs IH]; intros ys Hlen.
    - destruct ys; simpl in *; [reflexivity|lia].
    - destruct ys as [|y ys]; simpl in *; [lia|].
      inversion Hlen as [Hlen'].
      rewrite !dot_product_app.
      2: rewrite !rev_length; simpl; lia.
      simpl.
      rewrite IH; [lia|exact Hlen'].
Qed.

Lemma dot_product_env_rev_vec:
    forall env v,
    Datatypes.length env = Datatypes.length v ->
    dot_product env (rev v) = dot_product (rev env) v.
Proof.
    intros env v Hlen.
    pose proof (dot_product_rev env (rev v)) as Hrev.
    assert (Datatypes.length env = Datatypes.length (rev v)) as Hlen'.
    { rewrite rev_length; exact Hlen. }
    specialize (Hrev Hlen').
    rewrite rev_involutive in Hrev.
    symmetry.
    exact Hrev.
Qed.

Lemma normalize_affine_rev_eval:
    forall cols env aff,
    Datatypes.length env = cols ->
    dot_product (fst (normalize_affine_rev cols aff)) env + snd (normalize_affine_rev cols aff) =
    dot_product (fst aff) (rev env) + snd aff.
Proof.
    intros cols env [v c] Hlen.
    unfold normalize_affine_rev. simpl.
    rewrite dot_product_commutative.
    rewrite dot_product_env_rev_vec.
    2: rewrite resize_length; exact Hlen.
    rewrite dot_product_commutative.
    assert (Datatypes.length (rev env) = cols) as Hlenrev.
    { rewrite rev_length; exact Hlen. }
    rewrite <- Hlenrev at 1.
    rewrite dot_product_resize_left.
    lia.
Qed.

Lemma normalize_affine_list_rev_affine_product:
    forall cols env affs,
    Datatypes.length env = cols ->
    affine_product (normalize_affine_list_rev cols affs) env = affine_product affs (rev env).
Proof.
    intros cols env affs Hlen.
    induction affs as [|aff affs IH]; simpl.
    - reflexivity.
    - f_equal.
      + eapply normalize_affine_rev_eval; eauto.
      + exact IH.
Qed.

Lemma normalize_affine_rev_satisfies_constraint:
    forall cols env aff,
    Datatypes.length env = cols ->
    satisfies_constraint env (normalize_affine_rev cols aff) =
    satisfies_constraint (rev env) aff.
Proof.
    intros cols env [v c] Hlen.
    unfold normalize_affine_rev. simpl.
    unfold satisfies_constraint. simpl.
    rewrite dot_product_env_rev_vec.
    2: rewrite resize_length; exact Hlen.
    rewrite dot_product_commutative.
    assert (Datatypes.length (rev env) = cols) as Hlenrev.
    { rewrite rev_length; exact Hlen. }
    rewrite <- Hlenrev at 1.
    rewrite dot_product_resize_left.
    rewrite dot_product_commutative.
    reflexivity.
Qed.

Lemma normalize_affine_list_rev_satisfies_constraint:
    forall cols env affs,
    Datatypes.length env = cols ->
    forallb (satisfies_constraint env) (normalize_affine_list_rev cols affs) =
    forallb (satisfies_constraint (rev env)) affs.
Proof.
    intros cols env affs Hlen.
    induction affs as [|aff affs IH]; simpl.
    - reflexivity.
    - rewrite normalize_affine_rev_satisfies_constraint with (cols:=cols) (env:=env) (aff:=aff) by auto.
      f_equal. exact IH.
Qed.

Lemma exprlist_to_aff_rev_normalized_correct:
    forall es env cols tf,
    exprlist_to_aff es cols = Okk tf ->
    Datatypes.length env = cols ->
    affine_product (normalize_affine_list_rev cols tf) env = map (Loop.eval_expr (rev env)) es.
Proof.
    intros es env cols tf Htf Hlen.
    rewrite normalize_affine_list_rev_affine_product with (cols:=cols) (env:=env) (affs:=tf); auto.
    symmetry.
    eapply exprlist_to_aff_correct; eauto.
    rewrite rev_length; exact Hlen.
Qed.

Definition resolve_access_functions
    (instr: Instr.t) : option (list AccessFunction * list AccessFunction) :=
    let empty := (@nil AccessFunction) in
    match PolIRs.Instr.waccess instr, PolIRs.Instr.raccess instr with
    | Some w, Some r =>
        if PolIRs.Instr.access_function_checker w r instr
        then Some (w, r)
        else None
    | Some w, None =>
        if PolIRs.Instr.access_function_checker w empty instr
        then Some (w, empty)
        else None
    | None, Some r =>
        if PolIRs.Instr.access_function_checker empty r instr
        then Some (empty, r)
        else None
    | None, None =>
        if PolIRs.Instr.access_function_checker empty empty instr
        then Some (empty, empty)
        else None
    end.

Definition make_le_constr (aff1 aff2: list Z * Z): list Z * Z := 
    let (aff1, c1) := aff1 in 
    let (aff2, c2) := aff2 in 
    (add_vector aff1 (map Z.opp aff2), c2 - c1).

Example test_make_le_constr_1:
    make_le_constr ([1%Z; -1%Z], 10%Z) ([2%Z; -1%Z; 1%Z], 10%Z) 
    = ([-1%Z; 0%Z; -1%Z], 0%Z).
Proof. reflexivity. Qed.
 
Example test_make_le_constr_2:
    make_le_constr ([1%Z; -1%Z], 10%Z) ([2%Z; -1%Z; 1%Z], 20%Z) 
    = ([-1%Z; 0%Z; -1%Z], 10%Z).
Proof. reflexivity. Qed.

Definition make_ge_constr (aff1 aff2: list Z * Z): list Z * Z := 
    let (aff1, c1) := aff1 in 
    let (aff2, c2) := aff2 in 
    (add_vector (map Z.opp aff1) aff2, c1 - c2).

Example test_make_ge_constr:
    make_ge_constr ([1%Z; -1%Z], 10%Z) ([2%Z; -1%Z; 1%Z], 10%Z) 
    = ([1%Z; 0%Z; 1%Z], 0%Z).
Proof. reflexivity. Qed.

Lemma dot_product_opp_right:
    forall p v,
    dot_product p (map Z.opp v) = Z.opp (dot_product p v).
Proof.
  exact LinalgExt.dot_product_vector_opp_r.
Qed.

Lemma make_le_constr_correct:
    forall env aff1 aff2,
    satisfies_constraint env (make_le_constr aff1 aff2) = true <->
    let (v1, c1) := aff1 in
    let (v2, c2) := aff2 in
    (dot_product env v1 + c1 <= dot_product env v2 + c2)%Z.
Proof.
    intros env [v1 c1] [v2 c2]. simpl.
    unfold satisfies_constraint. simpl.
    rewrite add_vector_dot_product_distr_right.
    rewrite dot_product_opp_right.
    rewrite Z.leb_le.
    lia.
Qed.

Lemma make_ge_constr_correct:
    forall env aff1 aff2,
    satisfies_constraint env (make_ge_constr aff1 aff2) = true <->
    let (v1, c1) := aff1 in
    let (v2, c2) := aff2 in
    (dot_product env v2 + c2 <= dot_product env v1 + c1)%Z.
Proof.
    intros env [v1 c1] [v2 c2]. simpl.
    unfold satisfies_constraint. simpl.
    rewrite add_vector_dot_product_distr_right.
    rewrite dot_product_opp_right.
    rewrite Z.leb_le.
    lia.
Qed.

Lemma andb_true_r_local:
    forall b, (b && true)%bool = b.
Proof.
    exact andb_true_r.
Qed.

Lemma andb_true_iff_local:
    forall b1 b2, (b1 && b2)%bool = true <-> b1 = true /\ b2 = true.
Proof.
    exact andb_true_iff.
Qed.


(** test to constraint *)
Fixpoint test_to_aff (tst: PolIRs.Loop.test): result (list (list Z * Z)) := 
    match tst with 
    | PolIRs.Loop.LE e1 e2 => 
        match (expr_to_aff e1), (expr_to_aff e2) with 
        | Okk aff1, Okk aff2 => 
            Okk [make_le_constr aff1 aff2]
        | _, _ => Err "Test to aff failed"%string
        end
    | PolIRs.Loop.EQ e1 e2 => 
        match (expr_to_aff e1), (expr_to_aff e2) with 
        | Okk aff1, Okk aff2 => 
            Okk [make_le_constr aff1 aff2; make_ge_constr aff1 aff2]
        | _, _ => Err "Test to aff failed"%string
        end
    | PolIRs.Loop.And tst1 tst2 => 
        match (test_to_aff tst1), (test_to_aff tst2) with 
        | Okk aff1, Okk aff2 => 
            Okk (aff1 ++ aff2)
        | _, _ => Err "Test to aff failed"%string
        end
    | _ => Err "Test to aff failed"%string
    end.

Lemma test_to_aff_sound:
    forall tst env constrs,
    test_to_aff tst = Okk constrs ->
    Loop.eval_test env tst = true ->
    forallb (satisfies_constraint env) constrs = true.
Proof.
    induction tst as [e1 e2|e1 e2|tst1 IH1 tst2 IH2|tst1 IH1 tst2 IH2|tst IH|b];
      intros env constrs Htst Heval; simpl in *; try discriminate.
    - destruct (expr_to_aff e1) as [[v1 c1]|msg1] eqn:He1; try discriminate.
      destruct (expr_to_aff e2) as [[v2 c2]|msg2] eqn:He2; try discriminate.
      inv Htst.
      apply Z.leb_le in Heval.
      pose proof (expr_to_aff_correct e1 env (v1, c1) v1 c1 He1 eq_refl) as Hv1.
      pose proof (expr_to_aff_correct e2 env (v2, c2) v2 c2 He2 eq_refl) as Hv2.
      rewrite Hv1 in Heval. rewrite Hv2 in Heval.
      simpl. rewrite andb_true_r_local.
      eapply (proj2 (make_le_constr_correct env (v1, c1) (v2, c2))).
      lia.
    - destruct (expr_to_aff e1) as [[v1 c1]|msg1] eqn:He1; try discriminate.
      destruct (expr_to_aff e2) as [[v2 c2]|msg2] eqn:He2; try discriminate.
      inv Htst.
      apply Z.eqb_eq in Heval.
      pose proof (expr_to_aff_correct e1 env (v1, c1) v1 c1 He1 eq_refl) as Hv1.
      pose proof (expr_to_aff_correct e2 env (v2, c2) v2 c2 He2 eq_refl) as Hv2.
      rewrite Hv1 in Heval. rewrite Hv2 in Heval.
      simpl. rewrite andb_true_r_local.
      rewrite andb_true_iff_local. split.
      + eapply (proj2 (make_le_constr_correct env (v1, c1) (v2, c2))). lia.
      + eapply (proj2 (make_ge_constr_correct env (v1, c1) (v2, c2))). lia.
    - destruct (test_to_aff tst1) as [cs1|msg1] eqn:H1; try discriminate.
      destruct (test_to_aff tst2) as [cs2|msg2] eqn:H2; try discriminate.
      inv Htst.
      apply andb_true_iff_local in Heval. destruct Heval as [Hv1 Hv2].
      rewrite forallb_app. rewrite andb_true_iff_local. split.
      + eapply IH1; eauto.
      + eapply IH2; eauto.
Qed.

Lemma test_to_aff_complete:
    forall tst env constrs,
    test_to_aff tst = Okk constrs ->
    forallb (satisfies_constraint env) constrs = true ->
    Loop.eval_test env tst = true.
Proof.
    induction tst as [e1 e2|e1 e2|tst1 IH1 tst2 IH2|tst1 IH1 tst2 IH2|tst IH|b];
      intros env constrs Htst Hsat; simpl in *; try discriminate.
    - destruct (expr_to_aff e1) as [[v1 c1]|msg1] eqn:He1; try discriminate.
      destruct (expr_to_aff e2) as [[v2 c2]|msg2] eqn:He2; try discriminate.
      inv Htst.
      simpl in Hsat.
      rewrite andb_true_r_local in Hsat.
      eapply (proj1 (make_le_constr_correct env (v1, c1) (v2, c2))) in Hsat.
      eapply Z.leb_le.
      pose proof (expr_to_aff_correct e1 env (v1, c1) v1 c1 He1 eq_refl) as Hv1.
      pose proof (expr_to_aff_correct e2 env (v2, c2) v2 c2 He2 eq_refl) as Hv2.
      rewrite Hv1, Hv2.
      exact Hsat.
    - destruct (expr_to_aff e1) as [[v1 c1]|msg1] eqn:He1; try discriminate.
      destruct (expr_to_aff e2) as [[v2 c2]|msg2] eqn:He2; try discriminate.
      inv Htst.
      simpl in Hsat.
      rewrite andb_true_r_local in Hsat.
      eapply andb_true_iff_local in Hsat.
      destruct Hsat as [Hle Hge].
      eapply (proj1 (make_le_constr_correct env (v1, c1) (v2, c2))) in Hle.
      eapply (proj1 (make_ge_constr_correct env (v1, c1) (v2, c2))) in Hge.
      eapply Z.eqb_eq.
      pose proof (expr_to_aff_correct e1 env (v1, c1) v1 c1 He1 eq_refl) as Hv1.
      pose proof (expr_to_aff_correct e2 env (v2, c2) v2 c2 He2 eq_refl) as Hv2.
      rewrite Hv1, Hv2.
      lia.
    - destruct (test_to_aff tst1) as [cs1|msg1] eqn:H1; try discriminate.
      destruct (test_to_aff tst2) as [cs2|msg2] eqn:H2; try discriminate.
      inv Htst.
      rewrite forallb_app in Hsat.
      eapply andb_true_iff_local in Hsat.
      destruct Hsat as [Hs1 Hs2].
      simpl.
      specialize (IH1 env cs1 eq_refl Hs1).
      specialize (IH2 env cs2 eq_refl Hs2).
      rewrite IH1.
      rewrite IH2.
      reflexivity.
Qed.

Lemma test_to_aff_sound_normalized:
    forall tst env cols constrs,
    test_to_aff tst = Okk constrs ->
    Loop.eval_test env tst = true ->
    Datatypes.length env = cols ->
    forallb (satisfies_constraint env) (normalize_affine_list cols constrs) = true.
Proof.
    intros tst env cols constrs Htst Heval Hlen.
    rewrite normalize_affine_list_satisfies_constraint with (cols:=cols) (env:=env) (affs:=constrs); auto.
    eapply test_to_aff_sound; eauto.
Qed.

Lemma test_to_aff_complete_normalized:
    forall tst env cols constrs,
    test_to_aff tst = Okk constrs ->
    Datatypes.length env = cols ->
    forallb (satisfies_constraint env) (normalize_affine_list cols constrs) = true ->
    Loop.eval_test env tst = true.
Proof.
    intros tst env cols constrs Htst Hlen Hsat.
    rewrite normalize_affine_list_satisfies_constraint with (cols:=cols) (env:=env) (affs:=constrs) in Hsat; auto.
    eapply test_to_aff_complete; eauto.
Qed.

Lemma test_false_implies_not_in_poly_normalized:
    forall tst env cols constrs,
    test_to_aff tst = Okk constrs ->
    Datatypes.length env = cols ->
    Loop.eval_test env tst = false ->
    in_poly env (normalize_affine_list cols constrs) = false.
Proof.
    intros tst env cols constrs Htst Hlen Heval.
    unfold in_poly.
    destruct (forallb (satisfies_constraint env) (normalize_affine_list cols constrs)) eqn:HSat.
    - exfalso.
      eapply test_to_aff_complete_normalized in HSat; eauto.
      rewrite HSat in Heval.
      discriminate.
    - reflexivity.
Qed.

Lemma guard_constraints_sound:
    forall test env cols constrs test_constrs,
    test_to_aff test = Okk test_constrs ->
    Loop.eval_test env test = true ->
    Datatypes.length env = cols ->
    forallb (satisfies_constraint env) constrs = true ->
    forallb (satisfies_constraint env)
        (constrs ++ normalize_affine_list cols test_constrs) = true.
Proof.
    intros test env cols constrs test_constrs Htest Heval Hlen Hconstrs.
    rewrite forallb_app.
    rewrite andb_true_iff_local. split; auto.
    eapply test_to_aff_sound_normalized; eauto.
Qed.

Lemma guard_constraints_sound_in_poly:
    forall test env cols constrs test_constrs,
    test_to_aff test = Okk test_constrs ->
    Loop.eval_test env test = true ->
    Datatypes.length env = cols ->
    in_poly env constrs = true ->
    in_poly env (constrs ++ normalize_affine_list cols test_constrs) = true.
Proof.
    intros test env cols constrs test_constrs Htest Heval Hlen Hin.
    unfold in_poly in *.
    eapply guard_constraints_sound; eauto.
Qed.

Definition lb_to_constr (lb: PolIRs.Loop.expr) (depth: nat): result (list Z * Z) := 
    match (expr_to_aff lb) with 
    | Okk (aff, c) => Okk ((-1%Z) :: (resize depth aff), Z.opp c) 
    | Err msg => Err msg
    end
.

(** $3 + 5 <= $4  ==> -$4 + $3 <= -5 *)
Example test_lb_to_constr_1:
    lb_to_constr (PolIRs.Loop.Sum (PolIRs.Loop.Var 3) (PolIRs.Loop.Constant 5%Z)) 4
    = Okk ([-1%Z; 0%Z; 0%Z; 0%Z; 1%Z], -5%Z).
Proof. reflexivity. Qed.

Lemma lb_to_constr_sound:
    forall lb env depth constr i,
    Datatypes.length env = depth ->
    lb_to_constr lb depth = Okk constr ->
    satisfies_constraint (i :: env) constr = true <->
    (Loop.eval_expr env lb <= i)%Z.
Proof.
    intros lb env depth constr i Hlen Hlb.
    unfold lb_to_constr in Hlb.
    destruct (expr_to_aff lb) as [[v c]|msg] eqn:He; try discriminate.
    pose proof Hlen as Hlen0.
    inversion Hlb; subst; clear Hlb.
    split; intro Hsat.
    - unfold satisfies_constraint in Hsat. simpl in Hsat.
      rewrite Z.leb_le in Hsat.
      rewrite dot_product_resize_right in Hsat.
      simpl in Hsat.
      pose proof (expr_to_aff_correct lb env (v, c) v c He eq_refl) as Heval.
      rewrite Heval.
      lia.
    - pose proof (expr_to_aff_correct lb env (v, c) v c He eq_refl) as Heval.
      rewrite Heval in Hsat.
      unfold satisfies_constraint. simpl.
      rewrite Z.leb_le.
      rewrite dot_product_resize_right.
      simpl.
      lia.
Qed.

Definition ub_to_constr (ub: PolIRs.Loop.expr) (depth: nat): result (list Z * Z) := 
    match (expr_to_aff ub) with
    | Okk (aff, c) => Okk ((1%Z) :: (resize depth (map Z.opp aff)), c-1)    (** < => <= -1*)
    | Err msg => Err msg 
    end
.

(** $3 + 5 > $4 => $4 - $3 < 5 *)
Example test_ub_to_constr_1:
    ub_to_constr (PolIRs.Loop.Sum (PolIRs.Loop.Var 3) (PolIRs.Loop.Constant 5%Z)) 4
    = Okk ([1%Z; 0%Z; 0%Z; 0%Z; -1%Z], 4%Z).
Proof. reflexivity. Qed.

Lemma ub_to_constr_sound:
    forall ub env depth constr i,
    Datatypes.length env = depth ->
    ub_to_constr ub depth = Okk constr ->
    satisfies_constraint (i :: env) constr = true <->
    (i < Loop.eval_expr env ub)%Z.
Proof.
    intros ub env depth constr i Hlen Hub.
    unfold ub_to_constr in Hub.
    destruct (expr_to_aff ub) as [[v c]|msg] eqn:He; try discriminate.
    pose proof Hlen as Hlen0.
    inversion Hub; subst; clear Hub.
    split; intro Hsat.
    - unfold satisfies_constraint in Hsat. simpl in Hsat.
      rewrite Z.leb_le in Hsat.
      rewrite dot_product_resize_right in Hsat.
      rewrite dot_product_opp_right in Hsat.
      simpl in Hsat.
      pose proof (expr_to_aff_correct ub env (v, c) v c He eq_refl) as Heval.
      rewrite Heval.
      lia.
    - pose proof (expr_to_aff_correct ub env (v, c) v c He eq_refl) as Heval.
      rewrite Heval in Hsat.
      unfold satisfies_constraint. simpl.
      rewrite Z.leb_le.
      rewrite dot_product_resize_right.
      rewrite dot_product_opp_right.
      simpl.
      lia.
Qed.

Lemma loop_bounds_sound:
    forall lb ub env depth lbc ubc i,
    Datatypes.length env = depth ->
    lb_to_constr lb depth = Okk lbc ->
    ub_to_constr ub depth = Okk ubc ->
    (satisfies_constraint (i :: env) lbc = true /\
     satisfies_constraint (i :: env) ubc = true) <->
    (Loop.eval_expr env lb <= i < Loop.eval_expr env ub)%Z.
Proof.
    intros lb ub env depth lbc ubc i Hlen Hlb Hub.
    rewrite lb_to_constr_sound with (lb:=lb) (env:=env) (depth:=depth) (constr:=lbc) (i:=i); auto.
    rewrite ub_to_constr_sound with (ub:=ub) (env:=env) (depth:=depth) (constr:=ubc) (i:=i); auto.
Qed.

Lemma loop_constraints_complete_lifted:
    forall lb ub env depth constrs lbc ubc i,
    Datatypes.length env = depth ->
    lb_to_constr lb depth = Okk lbc ->
    ub_to_constr ub depth = Okk ubc ->
    in_poly (i :: env) (lift_affine_list constrs ++ [lbc; ubc]) = true ->
    in_poly env constrs = true /\
    (Loop.eval_expr env lb <= i < Loop.eval_expr env ub)%Z.
Proof.
    intros lb ub env depth constrs lbc ubc i Hlen Hlb Hub Hin.
    eapply in_poly_lift_app_cons2_inv in Hin.
    destruct Hin as [Hbase [Hlbc Hubc]].
    split; auto.
    eapply loop_bounds_sound; eauto.
Qed.

Lemma loop_constraints_sound_lifted:
    forall lb ub env depth constrs lbc ubc i,
    Datatypes.length env = depth ->
    lb_to_constr lb depth = Okk lbc ->
    ub_to_constr ub depth = Okk ubc ->
    in_poly env constrs = true ->
    (Loop.eval_expr env lb <= i < Loop.eval_expr env ub)%Z ->
    in_poly (i :: env) (lift_affine_list constrs ++ [lbc; ubc]) = true.
Proof.
    intros lb ub env depth constrs lbc ubc i Hlen Hlb Hub Hconstr Hbounds.
    unfold in_poly in *.
    rewrite forallb_app.
    apply andb_true_iff_local.
    split.
    - rewrite lift_affine_list_satisfies_constraint.
      exact Hconstr.
    - simpl.
      apply andb_true_iff_local.
      split.
      + eapply (proj2 (lb_to_constr_sound lb env depth lbc i Hlen Hlb)); lia.
      + apply andb_true_iff_local.
        split.
        * eapply (proj2 (ub_to_constr_sound ub env depth ubc i Hlen Hub)); lia.
        * reflexivity.
Qed.

Lemma in_poly_guard_split:
    forall p constrs cols test_constrs,
    in_poly p (constrs ++ normalize_affine_list cols test_constrs) = true ->
    in_poly p constrs = true /\
    forallb (satisfies_constraint p) (normalize_affine_list cols test_constrs) = true.
Proof.
    intros p constrs cols test_constrs Hin.
    unfold in_poly in *.
    rewrite forallb_app in Hin.
    eapply andb_true_iff_local in Hin.
    exact Hin.
Qed.

Lemma in_poly_normalize_affine_list_rev_app_inv:
    forall cols env pol1 pol2,
    Datatypes.length env = cols ->
    in_poly env (normalize_affine_list_rev cols (pol1 ++ pol2)) = true ->
    in_poly (rev env) pol1 = true /\
    in_poly (rev env) pol2 = true.
Proof.
    intros cols env pol1 pol2 Hlen Hin.
    unfold in_poly in *.
    rewrite normalize_affine_list_rev_satisfies_constraint in Hin; auto.
    rewrite forallb_app in Hin.
    eapply andb_true_iff_local in Hin.
    exact Hin.
Qed.

Lemma firstn_length_decompose:
    forall (envv idx: list Z) d,
    firstn (Datatypes.length envv) idx = envv ->
    Datatypes.length idx = (Datatypes.length envv + d)%nat ->
    exists suf,
      idx = envv ++ suf /\ Datatypes.length suf = d.
Proof.
    intros envv idx d Hprefix Hlen.
    exists (skipn (Datatypes.length envv) idx).
    split.
    - rewrite <- firstn_skipn with (n:=Datatypes.length envv) (l:=idx) at 1.
      rewrite Hprefix.
      reflexivity.
    - rewrite skipn_length.
      rewrite Hlen.
      lia.
Qed.

Lemma skipn_length_S_singleton:
    forall (k: nat) (l: list Z),
    Datatypes.length l = S k ->
    exists x, skipn k l = [x].
Proof.
    intros k l Hlen.
    assert (Datatypes.length (skipn k l) = 1%nat) as Hsk.
    {
      rewrite skipn_length.
      rewrite Hlen.
      lia.
    }
    destruct (skipn k l) as [|x xs] eqn:Hskip.
    - simpl in Hsk. lia.
    - exists x.
      simpl in Hsk.
      destruct xs as [|y ys].
      + reflexivity.
      + simpl in Hsk. lia.
Qed.

Fixpoint extract_stmt
    (stmt: PolIRs.Loop.stmt)
    (constrs: Domain)
    (env_dim iter_depth: nat)
    (sched_prefix: Schedule)
    {struct stmt}: result (list PolIRs.PolyLang.PolyInstr) :=
    let cols := (env_dim + iter_depth)%nat in
    match stmt with
    | PolIRs.Loop.Instr instr es =>
        match exprlist_to_aff es cols with
        | Okk tf =>
            match resolve_access_functions instr with
            | Some (w, r) =>
                Okk [{|
                    PolIRs.PolyLang.pi_depth := iter_depth;
                    PolIRs.PolyLang.pi_instr := instr;
                    PolIRs.PolyLang.pi_poly := normalize_affine_list_rev cols constrs;
                    PolIRs.PolyLang.pi_schedule := normalize_affine_list_rev cols sched_prefix;
                    PolIRs.PolyLang.pi_point_witness := PSWIdentity iter_depth;
                    PolIRs.PolyLang.pi_transformation := normalize_affine_list_rev cols tf;
                    PolIRs.PolyLang.pi_access_transformation := normalize_affine_list_rev cols tf;
                    PolIRs.PolyLang.pi_waccess := normalize_access_list cols w;
                    PolIRs.PolyLang.pi_raccess := normalize_access_list cols r;
                |}]
            | None => Err "Instr access extraction/check failed"%string
            end
        | Err msg => Err msg
        end
    | PolIRs.Loop.Seq stmts =>
        extract_stmts stmts constrs env_dim iter_depth sched_prefix 0
    | PolIRs.Loop.Loop lb ub stmt =>
        let lb_constr := lb_to_constr lb cols in
        let ub_constr := ub_to_constr ub cols in
        match lb_constr, ub_constr with
        | Okk lb_constr', Okk ub_constr' =>
            let constrs' := lift_affine_list constrs ++ [lb_constr'; ub_constr'] in
            let sched_prefix' := lift_affine_list sched_prefix ++ [((1%Z :: repeat 0%Z cols), 0%Z)] in
            extract_stmt stmt constrs' env_dim (S iter_depth) sched_prefix'
        | _, _ => Err "Loop bound to aff failed"%string
        end
    | PolIRs.Loop.Guard test stmt =>
        let test_constrs := test_to_aff test in
        match test_constrs with
        | Okk test_constrs' =>
            let constrs' := constrs ++ normalize_affine_list cols test_constrs' in
            extract_stmt stmt constrs' env_dim iter_depth sched_prefix
        | Err msg => Err msg
        end
    end
with extract_stmts
    (stmts: PolIRs.Loop.stmt_list)
    (constrs: Domain)
    (env_dim iter_depth: nat)
    (sched_prefix: Schedule)
    (pos: nat)
    {struct stmts}: result (list PolIRs.PolyLang.PolyInstr) :=
    let cols := (env_dim + iter_depth)%nat in
    match stmts with
    | PolIRs.Loop.SNil => Okk nil
    | PolIRs.Loop.SCons stmt stmts' =>
        let sched_prefix' := sched_prefix ++ [(repeat 0%Z cols, Z.of_nat pos)] in
        match extract_stmt stmt constrs env_dim iter_depth sched_prefix' with
        | Okk pis =>
            match extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) with
            | Okk pis' => Okk (pis ++ pis')
            | Err msg => Err msg
            end
        | Err msg => Err msg
        end
    end.

Lemma extract_stmt_instr_success_inv:
    forall instr es constrs env_dim iter_depth sched_prefix pis,
    extract_stmt (PolIRs.Loop.Instr instr es) constrs env_dim iter_depth sched_prefix = Okk pis ->
    exists tf w r,
      exprlist_to_aff es (env_dim + iter_depth)%nat = Okk tf /\
      resolve_access_functions instr = Some (w, r) /\
      pis =
      [{|
        PolIRs.PolyLang.pi_depth := iter_depth;
        PolIRs.PolyLang.pi_instr := instr;
        PolIRs.PolyLang.pi_poly := normalize_affine_list_rev (env_dim + iter_depth)%nat constrs;
        PolIRs.PolyLang.pi_schedule := normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix;
        PolIRs.PolyLang.pi_point_witness := PSWIdentity iter_depth;
        PolIRs.PolyLang.pi_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolIRs.PolyLang.pi_access_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolIRs.PolyLang.pi_waccess := normalize_access_list (env_dim + iter_depth)%nat w;
        PolIRs.PolyLang.pi_raccess := normalize_access_list (env_dim + iter_depth)%nat r;
      |}].
Proof.
    intros instr es constrs env_dim iter_depth sched_prefix pis Hext.
    simpl in Hext.
    remember (exprlist_to_aff es (env_dim + iter_depth)%nat) as Tf.
    destruct Tf as [tf|msg]; try discriminate.
    remember (resolve_access_functions instr) as Access.
    destruct Access as [[w r]|]; try discriminate.
    inv Hext.
    do 3 eexists.
    repeat split; eauto.
Qed.

Lemma extract_stmt_seq_success_inv:
    forall stmts constrs env_dim iter_depth sched_prefix pis,
    extract_stmt (PolIRs.Loop.Seq stmts) constrs env_dim iter_depth sched_prefix = Okk pis ->
    extract_stmts stmts constrs env_dim iter_depth sched_prefix 0 = Okk pis.
Proof.
    intros stmts constrs env_dim iter_depth sched_prefix pis Hext.
    simpl in Hext. exact Hext.
Qed.

Lemma extract_stmt_loop_success_inv:
    forall lb ub body constrs env_dim iter_depth sched_prefix pis,
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs env_dim iter_depth sched_prefix = Okk pis ->
    exists lbc ubc,
      lb_to_constr lb (env_dim + iter_depth)%nat = Okk lbc /\
      ub_to_constr ub (env_dim + iter_depth)%nat = Okk ubc /\
      extract_stmt body (lift_affine_list constrs ++ [lbc; ubc]) env_dim (S iter_depth)
        (lift_affine_list sched_prefix ++ [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)]) = Okk pis.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix pis Hext.
    simpl in Hext.
    remember (lb_to_constr lb (env_dim + iter_depth)%nat) as Lb.
    remember (ub_to_constr ub (env_dim + iter_depth)%nat) as Ub.
    destruct Lb as [lbc|msg1]; destruct Ub as [ubc|msg2]; try discriminate.
    eexists; eexists.
    repeat split; eauto.
Qed.

Lemma extract_stmt_guard_success_inv:
    forall test body constrs env_dim iter_depth sched_prefix pis,
    extract_stmt (PolIRs.Loop.Guard test body) constrs env_dim iter_depth sched_prefix = Okk pis ->
    exists test_constrs,
      test_to_aff test = Okk test_constrs /\
      extract_stmt body
        (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs)
        env_dim iter_depth sched_prefix = Okk pis.
Proof.
    intros test body constrs env_dim iter_depth sched_prefix pis Hext.
    simpl in Hext.
    remember (test_to_aff test) as Tst.
    destruct Tst as [test_constrs|msg]; try discriminate.
    eexists.
    split; eauto.
Qed.

Lemma extract_stmts_cons_success_inv:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix pos pis,
    extract_stmts (PolIRs.Loop.SCons stmt stmts') constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    exists pis1 pis2,
      extract_stmt stmt constrs env_dim iter_depth
        (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 /\
      extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 /\
      pis = pis1 ++ pis2.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix pos pis Hext.
    simpl in Hext.
    remember (extract_stmt stmt constrs env_dim iter_depth
      (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)])) as S1.
    destruct S1 as [pis1|msg1]; try discriminate.
    remember (extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos)) as S2.
    destruct S2 as [pis2|msg2]; try discriminate.
    inv Hext.
    exists pis1.
    exists pis2.
    repeat split; eauto.
Qed.

Lemma extract_stmts_nil_success_inv:
    forall constrs env_dim iter_depth sched_prefix pos pis,
    extract_stmts PolIRs.Loop.SNil constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    pis = [].
Proof.
    intros constrs env_dim iter_depth sched_prefix pos pis Hext.
    simpl in Hext. inv Hext. reflexivity.
Qed.

Definition pi_has_lifted_prefix
    (env_dim iter_depth: nat)
    (constrs: Domain)
    (pi: PolyLang.PolyInstr): Prop :=
    exists k tail,
      PolyLang.pi_depth pi = (iter_depth + k)%nat /\
      PolyLang.pi_poly pi =
        normalize_affine_list_rev (env_dim + PolyLang.pi_depth pi)%nat
          (lift_affine_list_n k constrs ++ tail).

Definition pi_has_lifted_sched_prefix
    (env_dim iter_depth: nat)
    (sched_prefix: Schedule)
    (pi: PolyLang.PolyInstr): Prop :=
    exists k tail,
      PolyLang.pi_depth pi = (iter_depth + k)%nat /\
      PolyLang.pi_schedule pi =
        normalize_affine_list_rev (env_dim + PolyLang.pi_depth pi)%nat
          (lift_affine_list_n k sched_prefix ++ tail).

Lemma extract_stmt_has_lifted_prefix:
    forall stmt constrs env_dim iter_depth sched_prefix pis,
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    forall pi, In pi pis ->
    pi_has_lifted_prefix env_dim iter_depth constrs pi
with extract_stmts_has_lifted_prefix:
    forall stmts constrs env_dim iter_depth sched_prefix pos pis,
    extract_stmts stmts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    forall pi, In pi pis ->
    pi_has_lifted_prefix env_dim iter_depth constrs pi.
Proof.
    - induction stmt as [lb ub body IHbody|i es|stmts|test body IHbody];
        intros constrs env_dim iter_depth sched_prefix pis Hext pi Hin.
      + eapply extract_stmt_loop_success_inv in Hext.
        destruct Hext as (lbc & ubc & Hlb & Hub & Hbody).
        eapply IHbody in Hbody; eauto.
        destruct Hbody as (k & tail & Hdepth & Hpoly).
        unfold pi_has_lifted_prefix.
        exists (S k).
        exists (lift_affine_list_n k [lbc; ubc] ++ tail).
        split.
        * lia.
        * rewrite Hpoly.
          f_equal.
          rewrite lift_affine_list_n_app.
          rewrite lift_affine_list_n_succ.
          rewrite app_assoc.
          reflexivity.
      + eapply extract_stmt_instr_success_inv in Hext.
        destruct Hext as (tf & w & r & Htf & Hacc & Hpis).
        subst pis.
        simpl in Hin.
        destruct Hin as [Hin|Hin]; [|contradiction].
        subst pi.
        unfold pi_has_lifted_prefix.
        exists 0%nat.
        exists ([]: list (list Z * Z)).
        split.
        * rewrite Nat.add_0_r.
          reflexivity.
        * simpl.
          rewrite app_nil_r.
          reflexivity.
      + eapply extract_stmt_seq_success_inv in Hext.
        eapply extract_stmts_has_lifted_prefix; eauto.
      + eapply extract_stmt_guard_success_inv in Hext.
        destruct Hext as (test_constrs & Htest & Hbody).
        eapply IHbody in Hbody; eauto.
        destruct Hbody as (k & tail & Hdepth & Hpoly).
        unfold pi_has_lifted_prefix.
        exists k.
        exists (lift_affine_list_n k (normalize_affine_list (env_dim + iter_depth)%nat test_constrs) ++ tail).
        split; auto.
        rewrite Hpoly.
        f_equal.
        rewrite lift_affine_list_n_app.
        rewrite app_assoc.
        reflexivity.
    - induction stmts as [|stmt stmts' IHstmts']; intros constrs env_dim iter_depth sched_prefix pos pis Hext pi Hin.
      + eapply extract_stmts_nil_success_inv in Hext.
        subst pis.
        contradiction.
      + eapply extract_stmts_cons_success_inv in Hext.
        destruct Hext as (pis1 & pis2 & Hstmt & Htl & Hpis).
        subst pis.
        eapply in_app_or in Hin.
        destruct Hin as [Hin1|Hin2].
        * eapply extract_stmt_has_lifted_prefix; eauto.
        * eapply IHstmts'; eauto.
Qed.

Lemma extract_stmt_has_lifted_sched_prefix:
    forall stmt constrs env_dim iter_depth sched_prefix pis,
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    forall pi, In pi pis ->
    pi_has_lifted_sched_prefix env_dim iter_depth sched_prefix pi
with extract_stmts_has_lifted_sched_prefix:
    forall stmts constrs env_dim iter_depth sched_prefix pos pis,
    extract_stmts stmts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    forall pi, In pi pis ->
    pi_has_lifted_sched_prefix env_dim iter_depth sched_prefix pi.
Proof.
    - induction stmt as [lb ub body IHbody|i es|stmts|test body IHbody];
        intros constrs env_dim iter_depth sched_prefix pis Hext pi Hin.
      + eapply extract_stmt_loop_success_inv in Hext.
        destruct Hext as (lbc & ubc & Hlb & Hub & Hbody).
        eapply IHbody in Hbody; eauto.
        destruct Hbody as (k & tail & Hdepth & Hsched).
        unfold pi_has_lifted_sched_prefix.
        exists (S k).
        exists (lift_affine_list_n k
          [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)] ++ tail).
        split.
        * lia.
        * rewrite Hsched.
          f_equal.
          rewrite lift_affine_list_n_app.
          rewrite lift_affine_list_n_succ.
          rewrite app_assoc.
          reflexivity.
      + eapply extract_stmt_instr_success_inv in Hext.
        destruct Hext as (tf & w & r & Htf & Hacc & Hpis).
        subst pis.
        simpl in Hin.
        destruct Hin as [Hin|Hin]; [|contradiction].
        subst pi.
        unfold pi_has_lifted_sched_prefix.
        exists 0%nat.
        exists ([]: list (list Z * Z)).
        split.
        * rewrite Nat.add_0_r.
          reflexivity.
        * simpl.
          rewrite app_nil_r.
          reflexivity.
      + eapply extract_stmt_seq_success_inv in Hext.
        eapply extract_stmts_has_lifted_sched_prefix; eauto.
      + eapply extract_stmt_guard_success_inv in Hext.
        destruct Hext as (test_constrs & Htest & Hbody).
        eapply IHbody in Hbody; eauto.
    - induction stmts as [|stmt stmts' IHstmts']; intros constrs env_dim iter_depth sched_prefix pos pis Hext pi Hin.
      + eapply extract_stmts_nil_success_inv in Hext.
        subst pis.
        contradiction.
      + eapply extract_stmts_cons_success_inv in Hext.
        destruct Hext as (pis1 & pis2 & Hstmt & Htl & Hpis).
        subst pis.
        eapply in_app_or in Hin.
        destruct Hin as [Hin1|Hin2].
        * eapply extract_stmt_has_lifted_sched_prefix in Hstmt; eauto.
          destruct Hstmt as (k & tail & Hdepth & Hsched).
          unfold pi_has_lifted_sched_prefix.
          exists k.
          exists (lift_affine_list_n k
            [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)] ++ tail).
          split; auto.
          rewrite Hsched.
          f_equal.
          rewrite lift_affine_list_n_app.
          rewrite app_assoc.
          reflexivity.
        * eapply IHstmts'; eauto.
Qed.

Definition check_extracted_wf
    (pis: list PolyLang.PolyInstr)
    (varctxt: list ident)
    (vars: list (ident * Ty.t)) : bool :=
    Nat.leb (length varctxt) (length vars) &&
    forallb (fun pi => Val.check_wf_polyinstr pi varctxt vars) pis.

Lemma check_extracted_wf_spec:
    forall pis varctxt vars,
    check_extracted_wf pis varctxt vars = true ->
    Nat.leb (length varctxt) (length vars) = true /\
    forallb (fun pi => Val.check_wf_polyinstr pi varctxt vars) pis = true.
Proof.
    intros pis varctxt vars H.
    unfold check_extracted_wf in H.
    destruct (Nat.leb (length varctxt) (length vars)) eqn:Hlen; simpl in H; try discriminate.
    destruct (forallb (fun pi : PolyLang.PolyInstr => Val.check_wf_polyinstr pi varctxt vars) pis) eqn:Hpis; simpl in H; try discriminate.
    split; auto.
Qed.

Definition extractor (loop: PolIRs.Loop.t): result PolIRs.PolyLang.t :=
    let '(stmt, varctxt, vars) := loop in
    if wf_scop_stmt stmt then
      let pol := extract_stmt stmt [] (length varctxt) 0 [] in
      match pol with
      | Okk pis =>
          if check_extracted_wf pis varctxt vars
          then Okk (pis, varctxt, vars)
          else Err "Extractor generated ill-formed poly program"%string
      | Err msg => Err msg
      end
    else Err "Extractor rejected non-affine SCoP fragment"%string.

Lemma extractor_success_implies_wf_scop:
    forall stmt varctxt vars pol,
    extractor (stmt, varctxt, vars) = Okk pol ->
    wf_scop_stmt stmt = true.
Proof.
    intros stmt varctxt vars pol Hext.
    unfold extractor in Hext. simpl in Hext.
    remember (wf_scop_stmt stmt) as WfScop.
    destruct WfScop; try discriminate.
    reflexivity.
Qed.

Lemma extractor_success_implies_wf_check:
    forall loop pol,
    extractor loop = Okk pol ->
    let '(pis, varctxt, vars) := pol in
    check_extracted_wf pis varctxt vars = true.
Proof.
    intros [[stmt varctxt] vars] [[pis varctxt_out] vars_out] Hext.
    unfold extractor in Hext.
    destruct (wf_scop_stmt stmt) eqn:WfScop; try discriminate.
    remember (extract_stmt stmt [] (Datatypes.length varctxt) 0 []) as Extract.
    destruct Extract as [pis0|msg]; try discriminate.
    destruct (check_extracted_wf pis0 varctxt vars) eqn:Hwf; try discriminate.
    inversion Hext; subst.
    exact Hwf.
Qed.

Lemma extractor_success_inv:
    forall stmt varctxt vars pol,
    extractor (stmt, varctxt, vars) = Okk pol ->
    exists pis,
    extract_stmt stmt [] (Datatypes.length varctxt) 0 [] = Okk pis /\
    check_extracted_wf pis varctxt vars = true /\
    pol = (pis, varctxt, vars).
Proof.
    intros stmt varctxt vars pol Hext.
    unfold extractor in Hext.
    destruct (wf_scop_stmt stmt) eqn:WfScop; try discriminate.
    destruct (extract_stmt stmt [] (Datatypes.length varctxt) 0 []) as [pis|msg] eqn:Hextract;
      try discriminate.
    destruct (check_extracted_wf pis varctxt vars) eqn:Hwf; try discriminate.
    inversion Hext; subst.
    exists pis.
    repeat split; auto.
Qed.

Lemma extractor_success_implies_varctxt_le_vars:
    forall loop pis varctxt vars,
    extractor loop = Okk (pis, varctxt, vars) ->
    (Datatypes.length varctxt <= Datatypes.length vars)%nat.
Proof.
    intros loop pis varctxt vars Hext.
    pose proof (extractor_success_implies_wf_check loop (pis, varctxt, vars) Hext) as Hwf.
    simpl in Hwf.
    apply check_extracted_wf_spec in Hwf.
    destruct Hwf as [Hlen _].
    eapply Nat.leb_le; eauto.
Qed.

(** * Flattened-instance witnesses *)

Lemma flatten_instrs_in_intro:
    forall envv pis ipl ip pi,
    PolyLang.flatten_instrs envv pis ipl ->
    firstn (Datatypes.length envv) (PolyLang.ip_index ip) = envv ->
    nth_error pis (PolyLang.ip_nth ip) = Some pi ->
    PolyLang.belongs_to ip pi ->
    Datatypes.length (PolyLang.ip_index ip) = (Datatypes.length envv + PolyLang.pi_depth pi)%nat ->
    In ip ipl.
Proof.
    intros envv pis ipl ip pi Hflat Hpre Hnth Hbel Hlen.
    destruct Hflat as (_ & Hchar & _ & _).
    apply (proj2 (Hchar ip)).
    exists pi.
    split; [exact Hnth|].
    split; [exact Hpre|].
    split; [exact Hbel| exact Hlen].
Qed.

Definition flatten_instrs_prefix_slice
    (envv prefix: list Z)
    (pis: list PolyLang.PolyInstr)
    (ipl: list PolyLang.InstrPoint) : Prop :=
  (forall ip,
      In ip ipl <->
      exists pi suf,
        nth_error pis (PolyLang.ip_nth ip) = Some pi /\
        PolyLang.belongs_to ip pi /\
        (Datatypes.length prefix <= PolyLang.pi_depth pi)%nat /\
        PolyLang.ip_index ip = envv ++ prefix ++ suf /\
        Datatypes.length suf = (PolyLang.pi_depth pi - Datatypes.length prefix)%nat) /\
  NoDup ipl /\
  Sorted PolyLang.np_lt ipl.

Lemma flatten_instrs_prefix_slice_nil:
    forall envv pis ipl,
    PolyLang.flatten_instrs envv pis ipl ->
    flatten_instrs_prefix_slice envv [] pis ipl.
Proof.
    intros envv pis ipl Hflat.
    destruct Hflat as [Hprefix [Hchar [Hnodup Hsorted]]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        pose proof (proj1 (Hchar ip) Hin) as Hmem.
        destruct Hmem as [pi [Hnth [_ [Hbel Hlenidx]]]].
        pose proof (Hprefix ip Hin) as Hpre.
        pose proof (firstn_length_decompose envv (PolyLang.ip_index ip) (PolyLang.pi_depth pi) Hpre Hlenidx)
          as Hsplit.
        destruct Hsplit as [suf [Hidx Hsuflen]].
        exists pi.
        exists suf.
        split; [exact Hnth|].
        split; [exact Hbel|].
        split.
        * simpl. lia.
        * split; [exact Hidx|].
          { simpl.
            rewrite Nat.sub_0_r.
            exact Hsuflen. }
      + intros (pi & suf & Hnth & Hbel & _ & Hidx & Hsuflen).
        simpl in Hidx.
        assert (firstn (Datatypes.length envv) (PolyLang.ip_index ip) = envv) as Hpre.
        {
          rewrite Hidx.
          rewrite firstn_app.
          rewrite firstn_all.
          replace ((Datatypes.length envv - Datatypes.length envv)%nat) with 0%nat by lia.
          simpl.
          rewrite app_nil_r.
          reflexivity.
        }
        apply (proj2 (Hchar ip)).
        exists pi.
        split; [exact Hnth|].
        split; [exact Hpre|].
        split; [exact Hbel|].
        rewrite Hidx.
        rewrite app_length.
        simpl.
        rewrite Hsuflen.
        rewrite Nat.sub_0_r.
        reflexivity.
    - split; auto.
Qed.

Lemma flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice:
    forall lb ub body constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists i suf tsuf,
      PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf /\
      (Loop.eval_expr (rev (envv ++ prefix)) lb <= i < Loop.eval_expr (rev (envv ++ prefix)) ub)%Z /\
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [i] ++ tsuf.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    eapply extract_stmt_loop_success_inv in Hext.
    destruct Hext as (lbc & ubc & Hlb & Hub & Hbodyext).
    pose proof Hbodyext as Hbodyext_sched.
    pose proof Hbodyext as Hbodyext_dom.
    destruct Hslice as [Hchar [_ _]].
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & suf0 & Hnth & Hbel & Hgepref & Hidx & Hsuflen).
    assert (In pi pis) as Hpin.
    { eapply nth_error_In; eauto. }
    eapply extract_stmt_has_lifted_sched_prefix in Hbodyext_sched.
    2: { exact Hpin. }
    destruct Hbodyext_sched as (ks & tail_sched & Hdepth_sched & Hsched).
    eapply extract_stmt_has_lifted_prefix in Hbodyext_dom.
    2: { exact Hpin. }
    destruct Hbodyext_dom as (kd & tail_dom & Hdepth_dom & Hpoly).
    assert (kd = ks) as Hk by lia.
    subst kd.
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (Hindom & _ & Hts & _ & _).
    assert (Hlenidx_var:
      Datatypes.length (PolyLang.ip_index ip) =
      (env_dim + PolyLang.pi_depth pi)%nat).
    {
      rewrite Hidx.
      repeat rewrite app_length.
      simpl.
      rewrite Hprefixlen, Hlenenv, Hsuflen.
      lia.
    }
    rewrite Hdepth_sched in Hsuflen.
    rewrite Hprefixlen in Hsuflen.
    replace ((S iter_depth + ks - iter_depth)%nat) with (S ks)%nat in Hsuflen by lia.
    assert (Datatypes.length (rev suf0) = S ks)%nat as Hlenrev.
    { rewrite rev_length. exact Hsuflen. }
    assert (
      rev suf0 ++ rev prefix ++ rev envv =
      firstn ks (rev suf0) ++ (skipn ks (rev suf0) ++ rev prefix ++ rev envv)
    ) as Hsplit.
    {
      replace (rev suf0) with (firstn ks (rev suf0) ++ skipn ks (rev suf0)) at 1 by
        (eapply firstn_skipn).
      repeat rewrite app_assoc.
      reflexivity.
    }
    assert (Datatypes.length (firstn ks (rev suf0)) = ks)%nat as Hlenfirst.
    {
      rewrite firstn_length.
      lia.
    }
    eapply skipn_length_S_singleton in Hlenrev.
    destruct Hlenrev as [i Hskip].

    rewrite Hsched in Hts.
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: { exact Hlenidx_var. }
    rewrite Hidx in Hts.
    repeat rewrite rev_app_distr in Hts.
    rewrite <- app_assoc in Hts.
    rewrite affine_product_app in Hts.
    rewrite Hsplit in Hts.
    assert (Hlift_sched:
      affine_product
        (lift_affine_list_n ks
          (lift_affine_list sched_prefix ++
           [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)]))
        (firstn ks (rev suf0) ++
         (skipn ks (rev suf0) ++ rev prefix ++ rev envv)) =
      affine_product
        (lift_affine_list sched_prefix ++
         [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)])
        (skipn ks (rev suf0) ++ rev prefix ++ rev envv)).
    {
      replace ks with (Datatypes.length (firstn ks (rev suf0))) at 1
        by (symmetry; exact Hlenfirst).
      eapply affine_product_lift_affine_list_n_app.
    }
    rewrite Hlift_sched in Hts.
    rewrite Hskip in Hts.
    simpl in Hts.
    rewrite affine_product_sched_prefix_loop in Hts.
    replace (rev prefix ++ rev envv) with (rev (envv ++ prefix)) in Hts.
    2: { rewrite rev_app_distr. reflexivity. }
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=(env_dim + iter_depth)%nat)
           (env:=envv ++ prefix)
           (affs:=sched_prefix) in Hts.
    2: {
      rewrite app_length.
      rewrite Hlenenv, Hprefixlen.
      lia.
    }
    rewrite <- app_assoc in Hts.

    rewrite Hpoly in Hindom.
    eapply in_poly_normalize_affine_list_rev_app_inv
      with (cols:=(env_dim + PolyLang.pi_depth pi)%nat)
           (env:=PolyLang.ip_index ip)
           (pol1:=lift_affine_list_n ks (lift_affine_list constrs ++ [lbc; ubc]))
           (pol2:=tail_dom) in Hindom.
    2: { exact Hlenidx_var. }
    destruct Hindom as [Hbase _].
    rewrite Hidx in Hbase.
    repeat rewrite rev_app_distr in Hbase.
    rewrite <- app_assoc in Hbase.
    rewrite Hsplit in Hbase.
    set (pref := firstn ks (rev suf0)) in *.
    set (suff := skipn ks (rev suf0) ++ rev prefix ++ rev envv) in *.
    assert (Datatypes.length pref = ks)%nat as Hlenpref.
    {
      unfold pref.
      exact Hlenfirst.
    }
    change (in_poly (pref ++ suff)
      (lift_affine_list_n ks (lift_affine_list constrs ++ [lbc; ubc])) = true) in Hbase.
    rewrite <- Hlenpref in Hbase.
    rewrite in_poly_lift_affine_list_n_app in Hbase.
    unfold suff in Hbase.
    rewrite Hskip in Hbase.
    simpl in Hbase.
    assert (Hlenrevprefix:
      Datatypes.length (rev prefix ++ rev envv) = (env_dim + iter_depth)%nat).
    {
      rewrite app_length.
      repeat rewrite rev_length.
      rewrite Hprefixlen, Hlenenv.
      lia.
    }
    eapply loop_constraints_complete_lifted in Hbase.
    2: { exact Hlenrevprefix. }
    2: { exact Hlb. }
    2: { exact Hub. }
    destruct Hbase as [_ Hbounds].
    assert (Hrevsuf:
      rev suf0 = pref ++ [i]).
    {
      rewrite <- Hskip.
      symmetry.
      eapply firstn_skipn.
    }
    assert (Hsuf0:
      suf0 = [i] ++ rev pref).
    {
      apply (f_equal (@rev Z)) in Hrevsuf.
      rewrite rev_involutive in Hrevsuf.
      rewrite rev_app_distr in Hrevsuf.
      simpl in Hrevsuf.
      exact Hrevsuf.
    }
    assert (Hbounds':
      (Loop.eval_expr (rev (envv ++ prefix)) lb <= i <
       Loop.eval_expr (rev (envv ++ prefix)) ub)%Z).
    {
      replace (rev (envv ++ prefix)) with (rev prefix ++ rev envv).
      2: { rewrite rev_app_distr. reflexivity. }
      exact Hbounds.
    }
    exists i.
    exists (rev pref).
    exists (affine_product tail_sched (pref ++ i :: rev (envv ++ prefix))).
    split.
    - rewrite Hidx.
      rewrite Hsuf0.
      rewrite app_assoc.
      reflexivity.
    - split.
      + exact Hbounds'.
      + exact Hts.
Qed.

Lemma loop_slice_point_fixed_prefix_slice:
    forall lb ub body constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip i,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip
      (filter
        (fun ip =>
          Z.eqb
            (nth
              (Datatypes.length
                (affine_product
                  (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                  (envv ++ prefix)))
              (PolyLang.ip_time_stamp ip) 0%Z)
            i)
        ipl) ->
    exists suf tsuf,
      PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf /\
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [i] ++ tsuf.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip i Hprefixlen Hext Hslice Hlenenv Hin.
    apply filter_In in Hin.
    destruct Hin as [Hip Hheq].
    destruct (
      flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
        lb ub body constrs env_dim iter_depth sched_prefix prefix
        pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip
    ) as [j [suf [tsuf [Hidx [_ Hts]]]]].
    replace (PolyLang.ip_time_stamp ip)
      with
        (affine_product
           (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
           (envv ++ prefix) ++ [j] ++ tsuf) in Hheq by exact Hts.
    assert (
      nth
        (Datatypes.length
          (affine_product
            (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
            (envv ++ prefix)))
        (affine_product
           (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
           (envv ++ prefix) ++ [j] ++ tsuf) 0%Z = j) as Hnthj.
    {
      clear.
      induction (affine_product
        (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
        (envv ++ prefix)) as [|z zs IH]; simpl.
      - reflexivity.
      - exact IH.
    }
    rewrite Hnthj in Hheq.
    apply Z.eqb_eq in Hheq.
    subst j.
    exists suf.
    exists tsuf.
    split; auto.
Qed.

Lemma flattened_point_loop_fixed_prefix_implies_timestamp_head_slice:
    forall lb ub body constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip i suf,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [i] ++ tsuf.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip i suf Hprefixlen Hext Hslice Hlenenv Hip Hidxi.
    destruct (
      flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
        lb ub body constrs env_dim iter_depth sched_prefix prefix
        pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip
    ) as [j [suf' [tsuf [Hidx [_ Hts]]]]].
    assert (Hidx':
      (envv ++ prefix) ++ [j] ++ suf' =
      (envv ++ prefix) ++ [i] ++ suf).
    {
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      rewrite <- Hidx.
      exact Hidxi.
    }
    apply app_inv_head in Hidx'.
    inversion Hidx'; subst.
    exists tsuf.
    exact Hts.
Qed.

Lemma loop_slice_filter_prefix_slice_gen:
    forall lb ub body constrs sched_prefix env_dim iter_depth prefix
           pis envv ipl i,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    flatten_instrs_prefix_slice envv (prefix ++ [i]) pis
      (filter
        (fun ip =>
          Z.eqb
            (nth
              (Datatypes.length
                (affine_product
                  (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                  (envv ++ prefix)))
              (PolyLang.ip_time_stamp ip) 0%Z)
            i)
        ipl).
Proof.
    intros lb ub body constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl i Hprefixlen Hext Hslice Hlenenv.
    destruct Hslice as [Hchar [Hnodup Hsorted]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        apply filter_In in Hin.
        destruct Hin as [Hip Hpred].
        pose proof (proj1 (Hchar ip) Hip) as Hmem.
        destruct Hmem as (pi & suf0 & Hnth & Hbel & Hge0 & Hidx0 & Hlen0).
        assert (Hin_filter:
          In ip
            (filter
              (fun ip =>
                Z.eqb
                  (nth
                    (Datatypes.length
                      (affine_product
                        (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                        (envv ++ prefix)))
                    (PolyLang.ip_time_stamp ip) 0%Z)
                  i) ipl)).
        {
          apply filter_In.
          split; assumption.
        }
        destruct (
          loop_slice_point_fixed_prefix_slice
            lb ub body constrs env_dim iter_depth sched_prefix prefix
            pis envv ipl ip i Hprefixlen Hext
            ((conj Hchar (conj Hnodup Hsorted))) Hlenenv
            Hin_filter
        ) as [suf [tsuf [Hidx Hts]]].
        assert (Htail: suf0 = [i] ++ suf).
        {
          assert ((envv ++ prefix) ++ suf0 = (envv ++ prefix) ++ [i] ++ suf) as Heq.
          {
            rewrite <- app_assoc.
            rewrite <- app_assoc.
            rewrite <- Hidx0.
            exact Hidx.
          }
          apply app_inv_head in Heq.
          exact Heq.
        }
        exists pi.
        exists suf.
        split.
        * exact Hnth.
        * split; [exact Hbel|].
          split.
          { rewrite Htail in Hlen0.
            simpl in Hlen0.
            rewrite Hprefixlen in Hlen0.
            rewrite app_length.
            simpl.
            rewrite Hprefixlen.
            lia. }
          split.
          { rewrite <- app_assoc. exact Hidx. }
          { rewrite Htail in Hlen0.
            simpl in Hlen0.
            rewrite Hprefixlen in Hlen0.
            assert (Hlen_suf:
              Datatypes.length suf = Nat.pred (PolyLang.pi_depth pi - iter_depth)%nat).
            {
              remember (PolyLang.pi_depth pi - iter_depth)%nat as d.
              destruct d as [|d'].
              - simpl in Hlen0. lia.
              - simpl.
                inversion Hlen0.
                reflexivity.
            }
            rewrite app_length.
            simpl.
            rewrite Hprefixlen.
            replace (PolyLang.pi_depth pi - (iter_depth + 1))%nat
              with (Nat.pred (PolyLang.pi_depth pi - iter_depth)) by lia.
            exact Hlen_suf. }
      + intros (pi & suf & Hnth & Hbel & Hge & Hidx & Hlen).
        apply filter_In.
        split.
        * apply (proj2 (Hchar ip)).
          exists pi.
          exists ([i] ++ suf).
          split.
          { exact Hnth. }
          split.
          { exact Hbel. }
          split.
          { rewrite app_length in Hge. simpl in Hge. lia. }
          split.
          { rewrite <- app_assoc in Hidx.
            exact Hidx. }
          { simpl.
            rewrite Hlen.
            rewrite app_length.
            simpl.
            rewrite Hprefixlen.
            rewrite app_length in Hge.
            simpl in Hge.
            rewrite Hprefixlen in Hge.
            replace (PolyLang.pi_depth pi - iter_depth)%nat
              with (S (PolyLang.pi_depth pi - (iter_depth + 1))) by lia.
            reflexivity. }
        * assert (Hip_plain: In ip ipl).
          {
            apply (proj2 (Hchar ip)).
            exists pi.
            exists ([i] ++ suf).
            split.
            { exact Hnth. }
            split.
            { exact Hbel. }
            split.
            { rewrite app_length in Hge. simpl in Hge. lia. }
            split.
            { rewrite <- app_assoc in Hidx.
              exact Hidx. }
            { simpl.
              rewrite Hlen.
              rewrite app_length.
              simpl.
              rewrite Hprefixlen.
              rewrite app_length in Hge.
              simpl in Hge.
              rewrite Hprefixlen in Hge.
              replace (PolyLang.pi_depth pi - iter_depth)%nat
                with (S (PolyLang.pi_depth pi - (iter_depth + 1))) by lia.
              reflexivity. }
          }
          assert (Hidx_plain:
            PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf).
          {
            rewrite <- app_assoc in Hidx.
            exact Hidx.
          }
          destruct (
            flattened_point_loop_fixed_prefix_implies_timestamp_head_slice
              lb ub body constrs env_dim iter_depth sched_prefix prefix
              pis envv ipl ip i suf Hprefixlen Hext
              ((conj Hchar (conj Hnodup Hsorted))) Hlenenv
              Hip_plain Hidx_plain
          ) as [tsuf Hts].
          replace (PolyLang.ip_time_stamp ip)
            with
              (affine_product
                 (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                 (envv ++ prefix) ++ [i] ++ tsuf) by exact Hts.
          assert (
            nth
              (Datatypes.length
                (affine_product
                  (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                  (envv ++ prefix)))
              (affine_product
                 (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                 (envv ++ prefix) ++ [i] ++ tsuf) 0%Z = i) as Hnthi.
          {
            clear.
            induction (affine_product
              (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
              (envv ++ prefix)) as [|z zs IH]; simpl.
            - reflexivity.
            - exact IH.
          }
          rewrite Hnthi.
          apply Z.eqb_eq.
          reflexivity.
    - split.
      + eapply NoDup_filter.
        exact Hnodup.
      + eapply filter_sort; eauto.
        * eapply PolyLang.np_eq_equivalence.
        * eapply PolyLang.np_lt_strict.
        * eapply PolyLang.np_lt_proper.
Qed.

Lemma flatten_instrs_prefix_slice_filter_left:
    forall envv prefix pis1 pis2 ipl,
    flatten_instrs_prefix_slice envv prefix (pis1 ++ pis2) ipl ->
    flatten_instrs_prefix_slice envv prefix pis1
      (filter (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)) ipl).
Proof.
    intros envv prefix pis1 pis2 ipl Hslice.
    destruct Hslice as [Hchar [Hnodup Hsorted]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        apply filter_In in Hin.
        destruct Hin as [Hip Hlt].
        pose proof (proj1 (Hchar ip) Hip) as Hmem.
        destruct Hmem as (pi & suf & Hnth & Hbel & Hge & Hidx & Hsuflen).
        exists pi.
        exists suf.
        split.
        * rewrite nth_error_app1 in Hnth.
          2: { apply Nat.ltb_lt in Hlt; exact Hlt. }
          exact Hnth.
        * split; [exact Hbel|].
          split; [exact Hge|].
          split; [exact Hidx|exact Hsuflen].
      + intros (pi & suf & Hnth & Hbel & Hge & Hidx & Hsuflen).
        apply filter_In.
        split.
        * apply (proj2 (Hchar ip)).
          exists pi.
          exists suf.
          split.
          { rewrite nth_error_app1.
            - exact Hnth.
            - eapply nth_error_Some.
              rewrite Hnth.
              discriminate. }
          split; [exact Hbel|].
          split; [exact Hge|].
          split; [exact Hidx|exact Hsuflen].
        * apply Nat.ltb_lt.
          eapply nth_error_Some.
          rewrite Hnth.
          discriminate.
    - split.
      + eapply NoDup_filter.
        exact Hnodup.
      + eapply filter_sort; eauto.
        * eapply PolyLang.np_eq_equivalence.
        * eapply PolyLang.np_lt_strict.
        * eapply PolyLang.np_lt_proper.
Qed.


Lemma flattened_point_schedule_has_top_prefix_slice:
    forall stmt constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ tsuf.
Proof.
    intros stmt constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    destruct Hslice as [Hchar [_ _]].
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & suf & Hnth & Hbel & Hgeprefix & Hidx & Hsuflen).
    eapply extract_stmt_has_lifted_sched_prefix in Hext.
    2: { eapply nth_error_In; eauto. }
    destruct Hext as (k & tail & Hdepth & Hsched).
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (_ & _ & Hts & _ & _).
    rewrite Hsched in Hts.
    assert (Hlenidx:
      Datatypes.length (PolyLang.ip_index ip) =
      (env_dim + PolyLang.pi_depth pi)%nat).
    {
      rewrite Hdepth in Hsuflen.
      rewrite Hprefixlen in Hsuflen.
      replace ((iter_depth + k - iter_depth)%nat) with k in Hsuflen by lia.
      rewrite Hidx.
      repeat rewrite app_length.
      simpl.
      rewrite Hsuflen.
      rewrite Hdepth.
      rewrite Hprefixlen.
      rewrite <- Hlenenv.
      lia.
    }
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: { exact Hlenidx. }
    assert (Hidx_app: PolyLang.ip_index ip = (envv ++ prefix) ++ suf).
    { rewrite <- app_assoc. exact Hidx. }
    rewrite Hidx_app in Hts.
    rewrite rev_app_distr in Hts.
    assert (Datatypes.length (rev suf) = k)%nat as Hlenrev.
    { rewrite rev_length. lia. }
    rewrite affine_product_app in Hts.
    rewrite <- Hlenrev in Hts.
    rewrite affine_product_lift_affine_list_n_app in Hts.
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=(env_dim + iter_depth)%nat) (env:=envv ++ prefix) (affs:=sched_prefix) in Hts.
    2: {
      rewrite app_length.
      rewrite Hprefixlen.
      rewrite Hlenenv.
      lia.
    }
    exists (affine_product tail (rev suf ++ rev (envv ++ prefix))).
    exact Hts.
Qed.

Lemma flattened_point_satisfies_top_constraints_slice:
    forall stmt constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    in_poly (rev (envv ++ prefix)) constrs = true.
Proof.
    intros stmt constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    destruct Hslice as [Hchar [_ _]].
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & suf & Hnth & Hbel & Hgeprefix & Hidx & Hsuflen).
    eapply extract_stmt_has_lifted_prefix in Hext.
    2: { eapply nth_error_In; eauto. }
    destruct Hext as (k & tail & Hdepth & Hpoly).
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (Hindom & _ & _ & _ & _).
    rewrite Hpoly in Hindom.
    assert (Hlenidx:
      Datatypes.length (PolyLang.ip_index ip) =
      (env_dim + PolyLang.pi_depth pi)%nat).
    {
      rewrite Hdepth in Hsuflen.
      rewrite Hprefixlen in Hsuflen.
      rewrite Hidx.
      repeat rewrite app_length.
      simpl.
      rewrite Hsuflen.
      rewrite Hdepth.
      rewrite Hprefixlen.
      lia.
    }
    eapply in_poly_normalize_affine_list_rev_app_inv
      with (cols:=(env_dim + PolyLang.pi_depth pi)%nat)
           (env:=PolyLang.ip_index ip)
           (pol1:=lift_affine_list_n k constrs)
           (pol2:=tail) in Hindom.
    2: { exact Hlenidx. }
    destruct Hindom as [Hbase _].
    rewrite Hdepth in Hsuflen.
    rewrite Hprefixlen in Hsuflen.
    replace ((iter_depth + k - iter_depth)%nat) with k in Hsuflen by lia.
    assert (Hidx_app: PolyLang.ip_index ip = (envv ++ prefix) ++ suf).
    { rewrite <- app_assoc. exact Hidx. }
    rewrite Hidx_app in Hbase.
    rewrite rev_app_distr in Hbase.
    assert (Datatypes.length (rev suf) = k)%nat as Hlenrev.
    { rewrite rev_length. exact Hsuflen. }
    rewrite <- Hlenrev in Hbase.
    rewrite in_poly_lift_affine_list_n_app in Hbase.
    exact Hbase.
Qed.

Lemma flattened_point_seq_pos_timestamp_with_prefix_slice:
    forall stmt constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth
      (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, pos)]) = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [pos] ++ tsuf.
Proof.
    intros stmt constrs env_dim iter_depth sched_prefix prefix pos
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    eapply flattened_point_schedule_has_top_prefix_slice
      with (ip:=ip) in Hext; eauto.
    destruct Hext as [tsuf Hts].
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: {
      rewrite app_length.
      rewrite Hprefixlen.
      rewrite Hlenenv.
      lia.
    }
    rewrite affine_product_sched_prefix_seq in Hts.
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=(env_dim + iter_depth)%nat) (env:=envv ++ prefix) (affs:=sched_prefix) in Hts.
    2: {
      rewrite app_length.
      rewrite Hprefixlen.
      rewrite Hlenenv.
      lia.
    }
    rewrite <- app_assoc in Hts.
    exists tsuf.
    exact Hts.
Qed.

Lemma lex_compare_cons_head_lt:
    forall h1 h2 t1 t2,
    (h1 < h2)%Z ->
    lex_compare (h1 :: t1) (h2 :: t2) = Lt.
Proof.
    intros h1 h2 t1 t2 Hlt.
    simpl.
    destruct (h1 ?= h2) eqn:Hcmp; simpl.
    - eapply Z.compare_eq_iff in Hcmp. lia.
    - reflexivity.
    - eapply Z.compare_gt_iff in Hcmp. lia.
Qed.

Lemma lex_compare_prefix_cons_head_lt:
    forall pref h1 h2 t1 t2,
    (h1 < h2)%Z ->
    lex_compare (pref ++ (h1 :: t1)) (pref ++ (h2 :: t2)) = Lt.
Proof.
    induction pref as [|p pref IH]; intros h1 h2 t1 t2 Hlt; simpl.
    - eapply lex_compare_cons_head_lt; eauto.
    - rewrite Z.compare_refl.
      eapply IH; eauto.
Qed.

Lemma filter_all_false_nil:
    forall A (f: A -> bool) l,
    (forall x, In x l -> f x = false) ->
    filter f l = [].
Proof.
    intros A f l Hall.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; left; reflexivity).
      apply IH.
      intros x Hin.
      eapply Hall.
      simpl. right. exact Hin.
Qed.

Lemma filter_all_true_id:
    forall A (f: A -> bool) l,
    (forall x, In x l -> f x = true) ->
    filter f l = l.
Proof.
    intros A f l Hall.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; left; reflexivity).
      f_equal.
      apply IH.
      intros x Hin.
      eapply Hall.
      simpl. right. exact Hin.
Qed.

Lemma filter_andb:
    forall A (f g: A -> bool) l,
    filter (fun x => andb (f x) (g x)) l = filter g (filter f l).
Proof.
    intros A f g l.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - destruct (f a) eqn:Hfa; simpl.
      + destruct (g a); simpl; rewrite IH; reflexivity.
      + rewrite IH; reflexivity.
Qed.

Lemma filter_negb_all_false_id:
    forall A (f: A -> bool) l,
    (forall x, In x l -> f x = false) ->
    filter (fun x => negb (f x)) l = l.
Proof.
    intros A f l Hall.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; left; reflexivity).
      simpl.
      f_equal.
      apply IH.
      intros x Hin.
      eapply Hall.
      simpl. right. exact Hin.
Qed.

Lemma sched_lt_not_sched_le_rev:
    forall ip1 ip2,
    lex_compare (PolyLang.ip_time_stamp ip1) (PolyLang.ip_time_stamp ip2) = Lt ->
    ~ PolyLang.instr_point_sched_le ip2 ip1.
Proof.
    intros ip1 ip2 Hlt Hle.
    unfold PolyLang.instr_point_sched_le in Hle.
    destruct Hle as [Hrevlt|Hreveq].
    - rewrite lex_compare_antisym in Hrevlt.
      rewrite Hlt in Hrevlt.
      discriminate.
    - rewrite lex_compare_antisym in Hreveq.
      rewrite Hlt in Hreveq.
      discriminate.
Qed.

Lemma sorted_sched_head_le_all:
    forall a l x,
    Sorted PolyLang.instr_point_sched_le (a :: l) ->
    In x l ->
    PolyLang.instr_point_sched_le a x.
Proof.
    intros a l x Hsorted Hin.
    pose proof (Sorted_extends PolyLang.instr_point_sched_le_trans Hsorted) as Hall.
    eapply Forall_forall in Hall; eauto.
Qed.

Lemma sorted_sched_filter_split_if_cross_lt:
    forall l (f: PolyLang.InstrPoint -> bool),
    Sorted PolyLang.instr_point_sched_le l ->
    (forall x y,
      In x l ->
      In y l ->
      f x = true ->
      f y = false ->
      lex_compare (PolyLang.ip_time_stamp x) (PolyLang.ip_time_stamp y) = Lt) ->
    l = filter f l ++ filter (fun x => negb (f x)) l.
Proof.
    intros l f Hsorted Hcross.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - inversion Hsorted as [|a0 l0 Hsorted_tl Hhd]; subst.
      destruct (f a) eqn:Hfa.
      + simpl.
        f_equal.
        eapply IH.
        * exact Hsorted_tl.
        * intros x y Hinx Hiny Hfx Hfy.
          eapply Hcross.
          -- simpl. right. exact Hinx.
          -- simpl. right. exact Hiny.
          -- exact Hfx.
          -- exact Hfy.
      + assert (forall x, In x l -> f x = false) as Hallfalse.
        {
          intros x Hinx.
          destruct (f x) eqn:Hfx; auto.
          exfalso.
          pose proof (Hcross x a) as Hlt.
          specialize (Hlt (or_intror Hinx) (or_introl eq_refl) Hfx Hfa).
          pose proof (sorted_sched_head_le_all a l x) as Hleax.
          specialize (Hleax).
          assert (Sorted PolyLang.instr_point_sched_le (a :: l)) as Hsorted_cons.
          { constructor; assumption. }
          specialize (Hleax Hsorted_cons Hinx).
          eapply (sched_lt_not_sched_le_rev x a) in Hlt.
          contradiction.
        }
        assert (filter f l = []) as Hnil.
        { eapply filter_all_false_nil; eauto. }
        assert (filter (fun x => negb (f x)) l = l) as Hnegb_id.
        { eapply filter_negb_all_false_id; eauto. }
        rewrite Hnil.
        rewrite Hnegb_id.
        reflexivity.
Qed.

Lemma sorted_filter_trans:
    forall A (R: A -> A -> Prop) (f: A -> bool) l,
    Transitive R ->
    Sorted R l ->
    Sorted R (filter f l).
Proof.
    intros A R f l Htrans Hsorted.
    induction Hsorted as [|a l Hsorted_tl IH Hhd].
    - simpl. constructor.
    - simpl.
      destruct (f a) eqn:Hfa.
      + constructor.
        * exact IH.
        * destruct (filter f l) as [|b l'] eqn:Hfilter.
          { constructor. }
          { apply HdRel_cons.
            assert (Forall (R a) l) as Hforall.
            {
              eapply Sorted_extends.
              - exact Htrans.
              - constructor; eauto.
            }
            assert (In b (filter f l)) as Hin_filter.
            { rewrite Hfilter. simpl. left. reflexivity. }
            apply filter_In in Hin_filter.
            destruct Hin_filter as [Hin_l _].
            eapply Forall_forall; eauto.
          }
      + exact IH.
Qed.

Lemma sorted_sched_filter:
    forall l (f: PolyLang.InstrPoint -> bool),
    Sorted PolyLang.instr_point_sched_le l ->
    Sorted PolyLang.instr_point_sched_le (filter f l).
Proof.
    intros l f Hsorted.
    eapply sorted_filter_trans.
    intros x y z Hxy Hyz.
    eapply PolyLang.instr_point_sched_le_trans; eauto.
    exact Hsorted.
Qed.

Lemma nth_after_prefix_singleton:
    forall (pfx tsuf: list Z) (i d: Z),
    nth (Datatypes.length pfx) (pfx ++ [i] ++ tsuf) d = i.
Proof.
    intros pfx tsuf i d.
    change (nth (Datatypes.length pfx) (pfx ++ i :: tsuf) d = i).
    apply nth_middle.
Qed.

Lemma sorted_sched_filter_split_by_prefix_head_eq:
    forall l pfx v,
    Sorted PolyLang.instr_point_sched_le l ->
    (forall ip, In ip l ->
      exists i tsuf, PolyLang.ip_time_stamp ip = pfx ++ [i] ++ tsuf) ->
    l =
      filter (fun ip => Z.ltb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) v) l ++
      filter (fun ip => Z.eqb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) v) l ++
      filter (fun ip => Z.ltb v (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z)) l.
Proof.
    intros l pfx v Hsorted Hhead.
    set (head := fun ip : PolyLang.InstrPoint =>
      nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z).
    pose proof (
      sorted_sched_filter_split_if_cross_lt
        l
        (fun ip => Z.ltb (head ip) v)
        Hsorted
    ) as Hsplit_lt.
    assert (Hcross_lt:
      forall x y,
      In x l ->
      In y l ->
      Z.ltb (head x) v = true ->
      Z.ltb (head y) v = false ->
      lex_compare (PolyLang.ip_time_stamp x) (PolyLang.ip_time_stamp y) = Lt).
    {
      intros x y Hinx Hiny Hfx Hfy.
      destruct (Hhead x Hinx) as [ix [tx Htsx]].
      destruct (Hhead y Hiny) as [iy [ty Htsy]].
      unfold head in Hfx, Hfy.
      rewrite Htsx in Hfx.
      rewrite Htsy in Hfy.
      rewrite nth_after_prefix_singleton in Hfx.
      rewrite nth_after_prefix_singleton in Hfy.
      eapply Z.ltb_lt in Hfx.
      eapply Z.ltb_ge in Hfy.
      assert ((ix < iy)%Z) as Hlt by lia.
      rewrite Htsx, Htsy.
      replace (pfx ++ [ix] ++ tx) with (pfx ++ (ix :: tx)) by reflexivity.
      replace (pfx ++ [iy] ++ ty) with (pfx ++ (iy :: ty)) by reflexivity.
      eapply lex_compare_prefix_cons_head_lt.
      exact Hlt.
    }
    specialize (Hsplit_lt Hcross_lt).
    set (l_ge :=
      filter (fun ip => negb (Z.ltb (head ip) v)) l).
    assert (Hsorted_ge:
      Sorted PolyLang.instr_point_sched_le l_ge).
    {
      unfold l_ge.
      eapply sorted_sched_filter.
      exact Hsorted.
    }
    pose proof (
      sorted_sched_filter_split_if_cross_lt
        l_ge
        (fun ip => Z.eqb (head ip) v)
        Hsorted_ge
    ) as Hsplit_eq_in_ge.
    assert (Hcross_eq:
      forall x y,
      In x l_ge ->
      In y l_ge ->
      Z.eqb (head x) v = true ->
      Z.eqb (head y) v = false ->
      lex_compare (PolyLang.ip_time_stamp x) (PolyLang.ip_time_stamp y) = Lt).
    {
      intros x y Hinx Hiny Hfx Hfy.
      apply filter_In in Hinx.
      apply filter_In in Hiny.
      destruct Hinx as [Hinx Hxge].
      destruct Hiny as [Hiny Hyge].
      destruct (Hhead x Hinx) as [ix [tx Htsx]].
      destruct (Hhead y Hiny) as [iy [ty Htsy]].
      unfold head in Hfx, Hfy, Hxge, Hyge.
      rewrite Htsx in Hfx.
      rewrite Htsy in Hfy.
      rewrite Htsx in Hxge.
      rewrite Htsy in Hyge.
      rewrite nth_after_prefix_singleton in Hfx.
      rewrite nth_after_prefix_singleton in Hfy.
      rewrite nth_after_prefix_singleton in Hxge.
      rewrite nth_after_prefix_singleton in Hyge.
      eapply Z.eqb_eq in Hfx.
      eapply Z.eqb_neq in Hfy.
      eapply Bool.negb_true_iff in Hxge.
      eapply Bool.negb_true_iff in Hyge.
      eapply Z.ltb_ge in Hxge.
      eapply Z.ltb_ge in Hyge.
      assert ((ix < iy)%Z) as Hlt by lia.
      rewrite Htsx, Htsy.
      replace (pfx ++ [ix] ++ tx) with (pfx ++ (ix :: tx)) by reflexivity.
      replace (pfx ++ [iy] ++ ty) with (pfx ++ (iy :: ty)) by reflexivity.
      eapply lex_compare_prefix_cons_head_lt.
      exact Hlt.
    }
    specialize (Hsplit_eq_in_ge Hcross_eq).
    unfold l_ge in Hsplit_eq_in_ge.
    rewrite Hsplit_lt at 1.
    rewrite Hsplit_eq_in_ge at 1.
    repeat rewrite app_assoc.
    f_equal.
    - f_equal.
      rewrite <- filter_andb.
      eapply filter_ext_in.
      intros ip Hin.
      destruct (Z.eqb (head ip) v) eqn:Heq; simpl.
      + eapply Z.eqb_eq in Heq.
        subst.
        rewrite Z.ltb_irrefl.
        rewrite Z.eqb_refl.
        simpl.
        reflexivity.
      + unfold head in Heq.
        rewrite Heq.
        rewrite andb_false_r.
        reflexivity.
    - rewrite <- filter_andb.
      eapply filter_ext_in.
      intros ip Hin.
      destruct (Z.ltb (head ip) v) eqn:Hltv; simpl.
      + eapply Z.ltb_lt in Hltv.
        assert ((v <? head ip)%Z = false) as Hn.
        { eapply Z.ltb_ge. lia. }
        unfold head in Hn |- *.
        rewrite Hn.
        reflexivity.
      + destruct (Z.eqb (head ip) v) eqn:Heq; simpl.
        * eapply Z.eqb_eq in Heq.
          subst.
          rewrite Z.ltb_irrefl.
          reflexivity.
        * eapply Z.ltb_ge in Hltv.
          eapply Z.eqb_neq in Heq.
          assert ((v < head ip)%Z) as Hgt by lia.
          assert ((v <? head ip)%Z = true) as Hv.
          { eapply Z.ltb_lt. exact Hgt. }
          unfold head in Hv |- *.
          rewrite Hv.
          reflexivity.
Qed.

Lemma sorted_sched_filter_ltb_succ_by_prefix_head:
    forall l pfx i,
    Sorted PolyLang.instr_point_sched_le l ->
    (forall ip, In ip l ->
      exists j tsuf, PolyLang.ip_time_stamp ip = pfx ++ [j] ++ tsuf) ->
    filter (fun ip => Z.ltb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) (i + 1)) l =
      filter (fun ip => Z.ltb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) i) l ++
      filter (fun ip => Z.eqb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) i) l.
Proof.
    intros l pfx i Hsorted Hhead.
    set (head := fun ip : PolyLang.InstrPoint =>
      nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z).
    set (flt_succ := fun ip : PolyLang.InstrPoint => Z.ltb (head ip) (i + 1)).
    set (flt_lt := fun ip : PolyLang.InstrPoint => Z.ltb (head ip) i).
    set (flt_eq := fun ip : PolyLang.InstrPoint => Z.eqb (head ip) i).
    set (flt_gt := fun ip : PolyLang.InstrPoint => Z.ltb i (head ip)).
    pose proof (sorted_sched_filter_split_by_prefix_head_eq l pfx i Hsorted Hhead) as Hsplit.
    unfold head in Hsplit.
    rewrite Hsplit at 1.
    repeat rewrite filter_app.
    change (
      filter flt_succ (filter flt_lt l) ++
      filter flt_succ (filter flt_eq l) ++
      filter flt_succ (filter flt_gt l) =
      filter flt_lt l ++ filter flt_eq l).
    assert (Hsucc_lt:
      filter flt_succ (filter flt_lt l) = filter flt_lt l).
    {
      eapply filter_all_true_id.
      intros ip Hin.
      apply filter_In in Hin.
      destruct Hin as [_ Hlt].
      unfold flt_succ, flt_lt in *.
      eapply Z.ltb_lt in Hlt.
      eapply Z.ltb_lt.
      lia.
    }
    assert (Hsucc_eq:
      filter flt_succ (filter flt_eq l) = filter flt_eq l).
    {
      eapply filter_all_true_id.
      intros ip Hin.
      apply filter_In in Hin.
      destruct Hin as [_ Heq].
      unfold flt_succ, flt_eq in *.
      eapply Z.eqb_eq in Heq.
      subst.
      eapply Z.ltb_lt.
      lia.
    }
    assert (Hsucc_gt_nil:
      filter flt_succ (filter flt_gt l) = []).
    {
      eapply filter_all_false_nil.
      intros ip Hin.
      apply filter_In in Hin.
      destruct Hin as [_ Hgt].
      unfold flt_succ, flt_gt in *.
      eapply Z.ltb_lt in Hgt.
      eapply Z.ltb_ge.
      lia.
    }
    rewrite Hsucc_lt.
    rewrite Hsucc_eq.
    rewrite Hsucc_gt_nil.
    rewrite app_nil_r.
    reflexivity.
Qed.


Lemma permutation_singleton:
    forall A (x: A) l,
    Permutation [x] l ->
    l = [x].
Proof.
    exact Permutation_length_1_inv.
Qed.

Lemma instr_point_list_semantics_singleton_inv:
    forall ip st1 st2,
    PolyLang.instr_point_list_semantics [ip] st1 st2 ->
    exists stmid,
      PolyLang.instr_point_sema ip st1 stmid /\
      State.eq stmid st2.
Proof.
  exact PolyLang.ILSema.instr_point_list_semantics_singleton_decompose.
Qed.

Lemma instr_point_list_semantics_nil_inv:
    forall st1 st2,
    PolyLang.instr_point_list_semantics [] st1 st2 ->
    State.eq st1 st2.
Proof.
  exact PolyLang.ILSema.instr_point_list_semantics_nil_inv.
Qed.

Lemma instr_point_list_semantics_app_inv:
    forall l1 l2 st1 st3,
    PolyLang.instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      PolyLang.instr_point_list_semantics l1 st1 st2 /\
      PolyLang.instr_point_list_semantics l2 st2 st3.
Proof.
  exact PolyLang.ILSema.instr_point_list_semantics_app_inv.
Qed.

(** * Statement-number rebasing *)

Definition rebase_ip_nth (base: nat) (ip: PolyLang.InstrPoint): PolyLang.InstrPoint :=
  {|
    PolyLang.ip_nth := (PolyLang.ip_nth ip - base)%nat;
    PolyLang.ip_index := PolyLang.ip_index ip;
    PolyLang.ip_transformation := PolyLang.ip_transformation ip;
    PolyLang.ip_time_stamp := PolyLang.ip_time_stamp ip;
    PolyLang.ip_instruction := PolyLang.ip_instruction ip;
    PolyLang.ip_depth := PolyLang.ip_depth ip;
  |}.

Lemma rebase_ip_nth_injective_ge:
    forall base ip1 ip2,
    (base <= PolyLang.ip_nth ip1)%nat ->
    (base <= PolyLang.ip_nth ip2)%nat ->
    rebase_ip_nth base ip1 = rebase_ip_nth base ip2 ->
    ip1 = ip2.
Proof.
    intros base ip1 ip2 Hge1 Hge2 Heq.
    destruct ip1 as [n1 idx1 tf1 ts1 instr1 d1].
    destruct ip2 as [n2 idx2 tf2 ts2 instr2 d2].
    simpl in *.
    inversion Heq; subst.
    assert (Hnsub: (n1 - base)%nat = (n2 - base)%nat) by exact H0.
    assert (Hnadd: ((n1 - base + base)%nat = (n2 - base + base)%nat)).
    { now rewrite Hnsub. }
    rewrite Nat.sub_add in Hnadd by exact Hge1.
    rewrite Nat.sub_add in Hnadd by exact Hge2.
    subst.
    f_equal; auto.
Qed.

Lemma np_lt_rebase_ip_nth_iff:
    forall base ip1 ip2,
    (base <= PolyLang.ip_nth ip1)%nat ->
    (base <= PolyLang.ip_nth ip2)%nat ->
    PolyLang.np_lt (rebase_ip_nth base ip1) (rebase_ip_nth base ip2) <->
    PolyLang.np_lt ip1 ip2.
Proof.
    intros base ip1 ip2 Hge1 Hge2.
    unfold PolyLang.np_lt.
    split; intro Hlt.
    - destruct Hlt as [Hlt|[Heq Hlex]].
      + left.
        simpl in Hlt.
        assert (Hplus: ((PolyLang.ip_nth ip1 - base + base < PolyLang.ip_nth ip2 - base + base)%nat)).
        { apply (proj1 (Nat.add_lt_mono_r _ _ base)); exact Hlt. }
        rewrite Nat.sub_add in Hplus by exact Hge1.
        rewrite Nat.sub_add in Hplus by exact Hge2.
        exact Hplus.
      + right. split.
        * simpl in Heq.
          assert (Hplus: ((PolyLang.ip_nth ip1 - base + base)%nat = (PolyLang.ip_nth ip2 - base + base)%nat)).
          { now rewrite Heq. }
          rewrite Nat.sub_add in Hplus by exact Hge1.
          rewrite Nat.sub_add in Hplus by exact Hge2.
          exact Hplus.
        * exact Hlex.
    - destruct Hlt as [Hlt|[Heq Hlex]].
      + left.
        assert (Hplus: ((PolyLang.ip_nth ip1 - base + base < PolyLang.ip_nth ip2 - base + base)%nat)).
        { rewrite Nat.sub_add by exact Hge1.
          rewrite Nat.sub_add by exact Hge2.
          exact Hlt. }
        apply (proj2 (Nat.add_lt_mono_r _ _ base)).
        exact Hplus.
      + right. split.
        * simpl. now rewrite Heq.
        * exact Hlex.
Qed.

Lemma instr_point_sema_rebase_ip_nth:
    forall base ip st1 st2,
    PolyLang.instr_point_sema (rebase_ip_nth base ip) st1 st2 <->
    PolyLang.instr_point_sema ip st1 st2.
Proof.
    intros base ip st1 st2.
    split; intro Hsema.
    - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
      econstructor.
      simpl in *.
      exact Hsem.
    - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
      econstructor.
      simpl in *.
      exact Hsem.
Qed.

Lemma instr_point_sched_le_rebase_ip_nth:
    forall base ip1 ip2,
    PolyLang.instr_point_sched_le (rebase_ip_nth base ip1) (rebase_ip_nth base ip2) <->
    PolyLang.instr_point_sched_le ip1 ip2.
Proof.
    intros base ip1 ip2.
    unfold PolyLang.instr_point_sched_le.
    simpl.
    tauto.
Qed.

Lemma sorted_sched_le_map_rebase_ip_nth:
    forall base ipl,
    Sorted PolyLang.instr_point_sched_le ipl ->
    Sorted PolyLang.instr_point_sched_le (map (rebase_ip_nth base) ipl).
Proof.
    intros base ipl Hsorted.
    induction Hsorted.
    - simpl. constructor.
    - simpl. constructor.
      + exact IHHsorted.
      + destruct H as [|b l0 Hle].
        * constructor.
        * constructor.
          eapply (proj2 (instr_point_sched_le_rebase_ip_nth base a b)).
          exact Hle.
Qed.

Lemma instr_point_list_semantics_map_rebase_ip_nth:
    forall base ipl st1 st2,
    PolyLang.instr_point_list_semantics (map (rebase_ip_nth base) ipl) st1 st2 <->
    PolyLang.instr_point_list_semantics ipl st1 st2.
Proof.
    intros base ipl.
    induction ipl as [|ip ipl IH]; intros st1 st2; split; intro Hsema.
    - inversion Hsema; subst.
      constructor.
      exact H.
    - inversion Hsema; subst.
      constructor.
      exact H.
    - simpl in Hsema.
      inversion Hsema; subst.
      econstructor.
      + eapply (proj1 (instr_point_sema_rebase_ip_nth base ip st1 st3)); eauto.
      + eapply (proj1 (IH st3 st2)); eauto.
    - simpl.
      inversion Hsema; subst.
      econstructor.
      + eapply (proj2 (instr_point_sema_rebase_ip_nth base ip st1 st3)); eauto.
      + eapply (proj2 (IH st3 st2)); eauto.
Qed.

Lemma instr_point_list_semantics_split_by_eq_app:
    forall l1 l2 l st1 st2,
    l = l1 ++ l2 ->
    PolyLang.instr_point_list_semantics l st1 st2 ->
    exists stmid,
      PolyLang.instr_point_list_semantics l1 st1 stmid /\
      PolyLang.instr_point_list_semantics l2 stmid st2.
Proof.
    intros l1 l2 l st1 st2 Heq Hsema.
    subst l.
    eapply instr_point_list_semantics_app_inv in Hsema.
    exact Hsema.
Qed.

Lemma instr_point_list_semantics_split_by_eq_app_rebase_right:
    forall base l1 l2 l st1 st2,
    l = l1 ++ l2 ->
    PolyLang.instr_point_list_semantics l st1 st2 ->
    exists stmid,
      PolyLang.instr_point_list_semantics l1 st1 stmid /\
      PolyLang.instr_point_list_semantics (map (rebase_ip_nth base) l2) stmid st2.
Proof.
    intros base l1 l2 l st1 st2 Heq Hsema.
    pose proof (
      instr_point_list_semantics_split_by_eq_app
        l1 l2 l st1 st2 Heq Hsema
    ) as Hsplit.
    destruct Hsplit as [stmid [Hleft Hright]].
    exists stmid.
    split.
    - exact Hleft.
    - eapply (proj2 (instr_point_list_semantics_map_rebase_ip_nth base l2 stmid st2)).
      exact Hright.
Qed.

Lemma sorted_np_lt_map_rebase_ip_nth:
    forall base ipl,
    (forall ip, In ip ipl -> (base <= PolyLang.ip_nth ip)%nat) ->
    Sorted PolyLang.np_lt ipl ->
    Sorted PolyLang.np_lt (map (rebase_ip_nth base) ipl).
Proof.
    intros base ipl Hge Hsorted.
    induction Hsorted.
    - simpl. constructor.
    - simpl. constructor.
      + eapply IHHsorted.
        intros ip Hin.
        eapply Hge.
        simpl. right. exact Hin.
      + destruct H as [|b l0 Hlt].
        * constructor.
        * constructor.
          assert ((base <= PolyLang.ip_nth a)%nat) as Hgea.
          { eapply Hge. simpl. left. reflexivity. }
          assert ((base <= PolyLang.ip_nth b)%nat) as Hgeb.
          { eapply Hge. simpl. right. left. reflexivity. }
          eapply (proj2 (np_lt_rebase_ip_nth_iff base a b Hgea Hgeb)).
          exact Hlt.
Qed.

Lemma nodup_map_rebase_ip_nth:
    forall base ipl,
    (forall ip, In ip ipl -> (base <= PolyLang.ip_nth ip)%nat) ->
    NoDup ipl ->
    NoDup (map (rebase_ip_nth base) ipl).
Proof.
    intros base ipl Hge Hnodup.
    induction Hnodup as [|x l Hnin Hnodup IH].
    - simpl. constructor.
    - simpl. constructor.
      + intro Hin.
        eapply in_map_iff in Hin.
        destruct Hin as (y & Heq & Hyin).
        assert ((base <= PolyLang.ip_nth y)%nat) as Hgey.
        { eapply Hge. simpl. right. exact Hyin. }
        assert ((base <= PolyLang.ip_nth x)%nat) as Hgex.
        { eapply Hge. simpl. left. reflexivity. }
        assert (y = x).
        { eapply rebase_ip_nth_injective_ge; eauto. }
        subst.
        eapply Hnin.
        exact Hyin.
      + eapply IH.
        intros ip Hin.
        eapply Hge.
        simpl. right. exact Hin.
Qed.

Lemma flatten_instrs_prefix_slice_filter_right_rebase:
    forall envv prefix pis1 pis2 ipl,
    flatten_instrs_prefix_slice envv prefix (pis1 ++ pis2) ipl ->
    flatten_instrs_prefix_slice envv prefix pis2
      (map (rebase_ip_nth (Datatypes.length pis1))
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)).
Proof.
    intros envv prefix pis1 pis2 ipl Hslice.
    destruct Hslice as [Hchar [Hnodup Hsorted]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        eapply in_map_iff in Hin.
        destruct Hin as (ip0 & Hip & Hip0in).
        subst ip.
        apply filter_In in Hip0in.
        destruct Hip0in as [Hip0in Hge0].
        apply negb_true_iff in Hge0.
        apply Nat.ltb_ge in Hge0.
        pose proof (proj1 (Hchar ip0) Hip0in) as Hmem.
        destruct Hmem as (pi & suf & Hnth & Hbel & Hgepref & Hidx & Hsuflen).
        exists pi.
        exists suf.
        split.
        * rewrite nth_error_app2 in Hnth by exact Hge0.
          exact Hnth.
        * split.
          { exact Hbel. }
          split.
          { exact Hgepref. }
          split.
          { exact Hidx. }
          { exact Hsuflen. }
      + intros (pi & suf & Hnth & Hbel & Hgepref & Hidx & Hsuflen).
        set (base := Datatypes.length pis1).
        set (ip0 := {|
          PolyLang.ip_nth := (PolyLang.ip_nth ip + base)%nat;
          PolyLang.ip_index := PolyLang.ip_index ip;
          PolyLang.ip_transformation := PolyLang.ip_transformation ip;
          PolyLang.ip_time_stamp := PolyLang.ip_time_stamp ip;
          PolyLang.ip_instruction := PolyLang.ip_instruction ip;
          PolyLang.ip_depth := PolyLang.ip_depth ip;
        |}).
        assert (Hip0in : In ip0 ipl).
        {
          apply (proj2 (Hchar ip0)).
          exists pi.
          exists suf.
          split.
	          { subst base ip0.
	            destruct ip.
	            simpl in *.
	            rewrite nth_error_app2 by lia.
	            replace
	              (ip_nth + Datatypes.length pis1 - Datatypes.length pis1)%nat
	              with ip_nth by lia.
	            exact Hnth. }
          split.
          { exact Hbel. }
          split.
          { exact Hgepref. }
          split.
          { exact Hidx. }
          { exact Hsuflen. }
        }
        eapply in_map_iff.
	        exists ip0.
	        split.
	        * subst base ip0.
	          destruct ip.
	          unfold rebase_ip_nth.
	          simpl.
	          replace
	            (ip_nth + Datatypes.length pis1 - Datatypes.length pis1)%nat
	            with ip_nth by lia.
	          reflexivity.
        * apply filter_In.
          split.
          { exact Hip0in. }
          { apply negb_true_iff.
            apply Nat.ltb_ge.
            subst base ip0.
            destruct ip.
            simpl.
            lia. }
    - split.
      + assert (Hgeall:
          forall ip,
            In
              ip
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl) ->
            (Datatypes.length pis1 <= PolyLang.ip_nth ip)%nat).
        {
          intros ip Hin.
          apply filter_In in Hin.
          destruct Hin as [_ Hge].
          apply negb_true_iff in Hge.
          apply Nat.ltb_ge in Hge.
          exact Hge.
        }
        eapply nodup_map_rebase_ip_nth.
        * exact Hgeall.
        * eapply NoDup_filter.
          exact Hnodup.
      + assert (Hsorted_filter:
          Sorted PolyLang.np_lt
            (filter
              (fun ip : PolyLang.InstrPoint =>
                negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
              ipl)).
        {
          eapply filter_sort; eauto.
          - eapply PolyLang.np_eq_equivalence.
          - eapply PolyLang.np_lt_strict.
          - eapply PolyLang.np_lt_proper.
        }
        assert (Hgeall:
          forall ip,
            In
              ip
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl) ->
            (Datatypes.length pis1 <= PolyLang.ip_nth ip)%nat).
        {
          intros ip Hin.
          apply filter_In in Hin.
          destruct Hin as [_ Hge].
          apply negb_true_iff in Hge.
          apply Nat.ltb_ge in Hge.
          exact Hge.
        }
        eapply sorted_np_lt_map_rebase_ip_nth.
        * exact Hgeall.
        * exact Hsorted_filter.
Qed.

Lemma flattened_stmts_pos_ge_with_prefix_slice:
    forall stmts constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmts stmts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists h tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [h] ++ tsuf /\
      (Z.of_nat pos <= h)%Z.
Proof.
    induction stmts as [|stmt stmts' IH];
      intros constrs env_dim iter_depth sched_prefix prefix pos
        pis envv ipl ip Hprefixlen Hext Hslice Hlen Hip.
    - eapply extract_stmts_nil_success_inv in Hext.
      subst pis.
      destruct Hslice as [Hchar _].
      exfalso.
      pose proof (proj1 (Hchar ip) Hip) as Hmem.
      destruct Hmem as (pi & suf & Hnth & _).
      destruct (PolyLang.ip_nth ip); simpl in Hnth; inversion Hnth.
    - eapply extract_stmts_cons_success_inv in Hext.
      destruct Hext as (pis1 & pis2 & Hhdext & Htlext & Hpis).
      subst pis.
      destruct (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)) eqn:Hlt.
      + assert (Hin_left:
          In ip
            (filter
              (fun ip0 : PolyLang.InstrPoint =>
                Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1))
              ipl)).
        {
          apply filter_In.
          split; auto.
        }
        assert (Hhdslice:
          flatten_instrs_prefix_slice envv prefix pis1
            (filter
              (fun ip0 : PolyLang.InstrPoint =>
                Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1))
              ipl)).
        {
          eapply flatten_instrs_prefix_slice_filter_left.
          exact Hslice.
        }
        assert (Hhdext0:
          extract_stmt stmt constrs env_dim iter_depth
            (sched_prefix ++
             [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1).
        { exact Hhdext. }
        eapply flattened_point_seq_pos_timestamp_with_prefix_slice
          with (ip:=ip) in Hhdext0; eauto.
        destruct Hhdext0 as [tsuf Hts].
        exists (Z.of_nat pos).
        exists tsuf.
        split; [exact Hts|lia].
      + assert (Hin_right:
          In ip
            (filter
              (fun ip0 : PolyLang.InstrPoint =>
                negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
              ipl)).
        {
          apply filter_In.
          split; auto.
          apply negb_true_iff.
          exact Hlt.
        }
        assert (Hin_right_map:
          In (rebase_ip_nth (Datatypes.length pis1) ip)
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl))).
        {
          eapply in_map.
          exact Hin_right.
        }
        assert (Htlslice:
          flatten_instrs_prefix_slice envv prefix pis2
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl))).
        {
          eapply flatten_instrs_prefix_slice_filter_right_rebase.
          exact Hslice.
        }
        eapply IH
          with (sched_prefix:=sched_prefix)
               (pos:=S pos)
               (pis:=pis2)
               (envv:=envv)
               (ipl:=map (rebase_ip_nth (Datatypes.length pis1))
                      (filter
                        (fun ip0 : PolyLang.InstrPoint =>
                          negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                        ipl))
               (ip:=rebase_ip_nth (Datatypes.length pis1) ip)
          in Htlext; eauto.
        destruct Htlext as [h [tsuf [Hts Hge]]].
        exists h.
        exists tsuf.
        split.
        * simpl in Hts.
          exact Hts.
        * lia.
Qed.

Lemma seq_cons_cross_lt_by_nth_with_prefix_slice:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
           pis1 pis2 envv ipl1 ipl2 ip1 ip2,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth
      (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 ->
    extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 ->
    flatten_instrs_prefix_slice envv prefix pis1 ipl1 ->
    flatten_instrs_prefix_slice envv prefix pis2
      (map (rebase_ip_nth (Datatypes.length pis1)) ipl2) ->
    Datatypes.length envv = env_dim ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    lex_compare (PolyLang.ip_time_stamp ip1) (PolyLang.ip_time_stamp ip2) = Lt.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
      pis1 pis2 envv ipl1 ipl2 ip1 ip2
      Hprefixlen Hhdext Htlext Hflat1 Hflat2 Hlen Hip1 Hip2.
    eapply flattened_point_seq_pos_timestamp_with_prefix_slice
      with (ip:=ip1) in Hhdext; eauto.
    destruct Hhdext as [tsuf1 Hts1].
    assert (Hin2':
      In (rebase_ip_nth (Datatypes.length pis1) ip2)
        (map (rebase_ip_nth (Datatypes.length pis1)) ipl2)).
    {
      eapply in_map.
      exact Hip2.
    }
    eapply flattened_stmts_pos_ge_with_prefix_slice
      with (ip:=rebase_ip_nth (Datatypes.length pis1) ip2) in Htlext;
      eauto.
    destruct Htlext as [h [tsuf2 [Hts2 Hge]]].
    simpl in Hts2.
    rewrite Hts1, Hts2.
    eapply lex_compare_prefix_cons_head_lt.
    lia.
Qed.

Lemma permutation_filter:
    forall A (f: A -> bool) l1 l2,
    Permutation l1 l2 ->
    Permutation (filter f l1) (filter f l2).
Proof.
    intros A f l1 l2 Hperm.
    induction Hperm; simpl.
    - constructor.
    - destruct (f x); simpl.
      + apply perm_skip. exact IHHperm.
      + exact IHHperm.
    - destruct (f x), (f y); simpl.
      + apply perm_swap.
      + apply Permutation_refl.
      + apply Permutation_refl.
      + apply Permutation_refl.
    - eapply Permutation_trans; eauto.
Qed.

Lemma extract_stmts_cons_sorted_split_by_nth_prefix_slice:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl sorted_ipl,
    Datatypes.length prefix = iter_depth ->
    extract_stmts (PolIRs.Loop.SCons stmt stmts') constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    exists pis1 pis2,
      extract_stmt stmt constrs env_dim iter_depth
        (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 /\
      extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 /\
      pis = pis1 ++ pis2 /\
      flatten_instrs_prefix_slice envv prefix pis1
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl) /\
      flatten_instrs_prefix_slice envv prefix pis2
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl)) /\
      Permutation
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl) /\
      Permutation
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl) /\
      sorted_ipl =
        filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl ++
        filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
      pis envv ipl sorted_ipl Hprefixlen Hext Hslice Hlen Hperm Hsorted.
    eapply extract_stmts_cons_success_inv in Hext.
    destruct Hext as (pis1 & pis2 & Hhdext & Htlext & Hpis).
    subst pis.
    assert (Hhdslice:
      flatten_instrs_prefix_slice envv prefix pis1
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)).
    {
      eapply flatten_instrs_prefix_slice_filter_left.
      exact Hslice.
    }
    assert (Htlslice:
      flatten_instrs_prefix_slice envv prefix pis2
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl))).
    {
      eapply flatten_instrs_prefix_slice_filter_right_rebase.
      exact Hslice.
    }
    assert (HpermL:
      Permutation
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    assert (HpermR:
      Permutation
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    assert (Hsplit_sorted:
      sorted_ipl =
        filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl ++
        filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl).
    {
      eapply sorted_sched_filter_split_if_cross_lt; eauto.
      intros x y Hinx Hiny Hfx Hfy.
      assert (HxinF:
        In x
          (filter
            (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
            sorted_ipl)).
	      {
	        apply filter_In.
	        split.
	        - exact Hinx.
	        - exact Hfx.
	      }
      assert (HyinF:
        In y
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl)).
	      {
	        apply filter_In.
	        split.
	        - exact Hiny.
	        - rewrite Hfy.
	          reflexivity.
	      }
      assert (Hxin1:
        In x
          (filter
            (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
            ipl)).
      {
        eapply Permutation_in.
        2: { exact HxinF. }
        exact (Permutation_sym HpermL).
      }
      assert (Hyin2:
        In y
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl)).
      {
        eapply Permutation_in.
        2: { exact HyinF. }
        exact (Permutation_sym HpermR).
      }
      eapply seq_cons_cross_lt_by_nth_with_prefix_slice
        with (stmt:=stmt) (stmts':=stmts') (constrs:=constrs)
             (env_dim:=env_dim) (iter_depth:=iter_depth)
             (sched_prefix:=sched_prefix) (prefix:=prefix) (pos:=pos)
             (pis1:=pis1) (pis2:=pis2)
             (envv:=envv)
             (ipl1:=filter
                (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
                ipl)
             (ipl2:=filter
                (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
                ipl).
      - exact Hprefixlen.
      - exact Hhdext.
      - exact Htlext.
      - exact Hhdslice.
      - exact Htlslice.
      - exact Hlen.
      - exact Hxin1.
      - exact Hyin2.
    }
    exists pis1.
    exists pis2.
    split.
    - exact Hhdext.
    - split.
      + exact Htlext.
      + split.
        * reflexivity.
        * split.
          { exact Hhdslice. }
          split.
          { exact Htlslice. }
          split.
          { exact HpermL. }
          split.
          { exact HpermR. }
          { exact Hsplit_sorted. }
Qed.

Lemma extract_stmts_cons_semantics_split_by_nth_prefix_slice:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl sorted_ipl st1 st2,
    Datatypes.length prefix = iter_depth ->
    extract_stmts (PolIRs.Loop.SCons stmt stmts') constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    exists pis1 pis2 stmid,
      extract_stmt stmt constrs env_dim iter_depth
        (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 /\
      extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 /\
      pis = pis1 ++ pis2 /\
      flatten_instrs_prefix_slice envv prefix pis1
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl) /\
      flatten_instrs_prefix_slice envv prefix pis2
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl)) /\
      PolyLang.instr_point_list_semantics
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)
        st1 stmid /\
      PolyLang.instr_point_list_semantics
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))
        stmid st2.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hext Hslice Hlen Hperm Hsorted Hipls.
    pose proof (
      extract_stmts_cons_sorted_split_by_nth_prefix_slice
        stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
        pis envv ipl sorted_ipl
        Hprefixlen Hext Hslice Hlen Hperm Hsorted
    ) as Hsplit.
    destruct Hsplit as
      (pis1 & pis2 & Hhdext & Htlext & Hpis &
       Hflat1 & Hflat2 & Hperm1 & Hperm2 & Hsplit_sorted).
    pose proof (
      instr_point_list_semantics_split_by_eq_app_rebase_right
        (Datatypes.length pis1)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)
        sorted_ipl st1 st2 Hsplit_sorted Hipls
    ) as Hsemsplit.
    destruct Hsemsplit as [stmid [Hsem1 Hsem2]].
    exists pis1.
    exists pis2.
    exists stmid.
    split.
    - exact Hhdext.
    - split.
      + exact Htlext.
      + split.
        * exact Hpis.
        * split.
          { exact Hflat1. }
          split.
          { exact Hflat2. }
          split.
          { exact Hsem1. }
          { exact Hsem2. }
Qed.

Lemma nodup_all_eq_singleton:
    forall A (x: A) l,
    NoDup l ->
    (forall y, In y l -> y = x) ->
    In x l ->
    l = [x].
Proof.
    intros A x l Hnd Hall Hin.
    destruct l as [|a l']; [contradiction|].
    assert (a = x) as Ha.
    { eapply Hall. simpl. left. reflexivity. }
    subst a.
    destruct l' as [|b l''].
    - reflexivity.
    - exfalso.
      assert (b = x) as Hb.
      { eapply Hall. simpl. right. left. reflexivity. }
      subst b.
      inversion Hnd; subst.
      eapply H1.
      simpl. left. reflexivity.
Qed.

Lemma instance_list_semantics_inv:
    forall pprog st1 st2,
    PolyLang.instance_list_semantics pprog st1 st2 ->
    exists pis varctxt vars envv,
      pprog = (pis, varctxt, vars) /\
      Instr.Compat vars st1 /\
      Instr.NonAlias st1 /\
      Instr.InitEnv varctxt envv st1 /\
      PolyLang.poly_instance_list_semantics envv pprog st1 st2.
Proof.
    intros pprog st1 st2 Hsem.
    destruct Hsem as [pprog' pis varctxt vars envv st1' st2' Hpprog Hcompat Hnonalias Hinit Hpoly].
    subst.
    exists pis.
    exists varctxt.
    exists vars.
    exists envv.
    repeat split; auto.
Qed.

Lemma poly_instance_list_semantics_inv:
    forall envv pprog st1 st2,
    PolyLang.poly_instance_list_semantics envv pprog st1 st2 ->
    exists pis varctxt vars ipl sorted_ipl,
      pprog = (pis, varctxt, vars) /\
      PolyLang.flatten_instrs envv pis ipl /\
      Permutation ipl sorted_ipl /\
      Sorted PolyLang.instr_point_sched_le sorted_ipl /\
      PolyLang.instr_point_list_semantics sorted_ipl st1 st2.
Proof.
    intros envv pprog st1 st2 Hsem.
    inversion Hsem; subst; clear Hsem.
    exists pis.
    exists varctxt.
    exists vars.
    exists ipl.
    exists sorted_ipl.
    split.
    - reflexivity.
    - split.
      + exact H0.
      + split.
        * exact H1.
        * split.
          { exact H2. }
          { exact H3. }
Qed.

Lemma loop_semantics_intro_from_envv:
    forall stmt varctxt vars envv st1 st2,
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    Loop.loop_semantics stmt (rev envv) st1 st2 ->
    Loop.semantics (stmt, varctxt, vars) st1 st2.
Proof.
    intros stmt varctxt vars envv st1 st2 Hcompat Hnonalias Hinit Hloop.
    eapply Loop.LSemaIntro
      with (loop:=stmt) (ctxt:=varctxt) (vars:=vars) (env:=rev envv).
    - reflexivity.
    - exact Hcompat.
    - exact Hnonalias.
    - replace (rev (rev envv)) with envv.
      + exact Hinit.
      + symmetry; eapply rev_involutive.
    - exact Hloop.
Qed.

Lemma iter_semantics_app:
    forall A (P: A -> State.t -> State.t -> Prop)
           xs ys st1 st2 st3,
    Instr.IterSem.iter_semantics P xs st1 st2 ->
    Instr.IterSem.iter_semantics P ys st2 st3 ->
    Instr.IterSem.iter_semantics P (xs ++ ys) st1 st3.
Proof.
    intros A P xs ys st1 st2 st3 Hxs Hys.
    induction Hxs.
    - simpl.
      exact Hys.
    - simpl.
      econstructor.
      + exact H.
      + eapply IHHxs.
        exact Hys.
Qed.

Lemma seq_cons_semantics_with_eq:
    forall st sts env st1 st2 st3 st3',
    Loop.loop_semantics st env st1 st2 ->
    Loop.loop_semantics (PolIRs.Loop.Seq sts) env st2 st3 ->
    State.eq st3' st3 ->
    exists stmid,
      Loop.loop_semantics (PolIRs.Loop.Seq (PolIRs.Loop.SCons st sts)) env st1 stmid /\
      State.eq st3' stmid.
Proof.
    intros st sts env st1 st2 st3 st3' Hhd Htl Heq.
    exists st3.
    split.
    - eapply Loop.LSeq; eauto.
    - exact Heq.
Qed.

Lemma flatten_instr_prefix_slice_singleton_if_in_poly:
    forall envv prefix pi ipl,
    Datatypes.length prefix = PolyLang.pi_depth pi ->
    in_poly (envv ++ prefix) (PolyLang.pi_poly pi) = true ->
    flatten_instrs_prefix_slice envv prefix [pi] ipl ->
    exists ip0,
      ipl = [ip0] /\
      PolyLang.ip_nth ip0 = 0%nat /\
      PolyLang.ip_index ip0 = envv ++ prefix /\
      PolyLang.ip_transformation ip0 = PolyLang.current_transformation_of pi (envv ++ prefix) /\
      PolyLang.ip_time_stamp ip0 = affine_product (PolyLang.pi_schedule pi) (envv ++ prefix) /\
      PolyLang.ip_instruction ip0 = PolyLang.pi_instr pi /\
      PolyLang.ip_depth ip0 = PolyLang.pi_depth pi.
Proof.
    intros envv prefix pi ipl Hprefixlen Hpolyin Hslice.
    destruct Hslice as [Hchar [Hnodup _]].
    set (ip0 := {|
      PolyLang.ip_nth := 0%nat;
      PolyLang.ip_index := envv ++ prefix;
      PolyLang.ip_transformation :=
        PolyLang.current_transformation_of pi (envv ++ prefix);
      PolyLang.ip_time_stamp := affine_product (PolyLang.pi_schedule pi) (envv ++ prefix);
      PolyLang.ip_instruction := PolyLang.pi_instr pi;
      PolyLang.ip_depth := PolyLang.pi_depth pi;
    |}).
    assert (Hin0: In ip0 ipl).
    {
      eapply (proj2 (Hchar ip0)).
      exists pi.
      exists ([]: list Z).
      split; [reflexivity|].
      split.
      - unfold PolyLang.belongs_to.
        simpl.
        rewrite Hpolyin.
        repeat split; reflexivity.
      - split; [lia|].
        split.
        + rewrite app_nil_r.
          reflexivity.
        + rewrite Hprefixlen.
          simpl.
          lia.
    }
    assert (Hall: forall ip, In ip ipl -> ip = ip0).
    {
      intros ip Hin.
      pose proof (proj1 (Hchar ip) Hin) as Hm.
      destruct Hm as (pi' & suf & Hnth & Hbel & _ & Hidx & Hsuflen).
      assert (Hnth_some: nth_error [pi] (PolyLang.ip_nth ip) <> None).
      { rewrite Hnth. discriminate. }
      eapply nth_error_Some in Hnth_some.
      simpl in Hnth_some.
      assert (Hnth0: PolyLang.ip_nth ip = 0%nat) by lia.
      rewrite Hnth0 in Hnth.
      simpl in Hnth.
      inversion Hnth; subst pi'; clear Hnth.
      rewrite Hprefixlen in Hsuflen.
      destruct suf as [|z suf'] eqn:Hsuf; simpl in Hsuflen; try lia.
      rewrite app_nil_r in Hidx.
      unfold PolyLang.belongs_to in Hbel.
      destruct Hbel as (_ & Htf & Hts & Hinstr & Hdepth).
      destruct ip as [n' idx tf ts instr depth].
      simpl in *.
      subst.
      reflexivity.
    }
    exists ip0.
    split.
    - eapply nodup_all_eq_singleton; eauto.
    - repeat split; reflexivity.
Qed.

Local Lemma instr_branch_core_prefix:
    forall i es constrs sched_prefix env_dim iter_depth prefix envv
           ipl sorted_ipl st1 st2 tf w r,
    Datatypes.length prefix = iter_depth ->
    exprlist_to_aff es (env_dim + iter_depth)%nat = Okk tf ->
    resolve_access_functions i = Some (w, r) ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix
      [{|
        PolyLang.pi_depth := iter_depth;
        PolyLang.pi_instr := i;
        PolyLang.pi_poly := normalize_affine_list_rev (env_dim + iter_depth)%nat constrs;
        PolyLang.pi_schedule := normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix;
        PolyLang.pi_point_witness := PSWIdentity iter_depth;
        PolyLang.pi_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_access_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_waccess := normalize_access_list (env_dim + iter_depth)%nat w;
        PolyLang.pi_raccess := normalize_access_list (env_dim + iter_depth)%nat r;
      |}] ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics (Loop.Instr i es) (rev (envv ++ prefix)) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros i es constrs sched_prefix env_dim iter_depth prefix envv
      ipl sorted_ipl st1 st2 tf w r
      Hprefixlen Htf Hacc Hconstr Hflat Hperm _ Hipls Hlenenv.
    assert (Hlenenvprefix:
      Datatypes.length (envv ++ prefix) = (env_dim + iter_depth)%nat).
    {
      rewrite app_length, Hlenenv, Hprefixlen.
      lia.
    }
    assert (Hdom:
      in_poly (envv ++ prefix)
        (normalize_affine_list_rev (env_dim + iter_depth)%nat constrs) = true).
    {
      unfold in_poly in *.
      rewrite normalize_affine_list_rev_satisfies_constraint
        with (cols := (env_dim + iter_depth)%nat)
             (env := envv ++ prefix)
             (affs := constrs).
      - exact Hconstr.
      - exact Hlenenvprefix.
    }
    assert (Haff:
      affine_product
        (normalize_affine_list_rev (env_dim + iter_depth)%nat tf)
        (envv ++ prefix) =
      map (Loop.eval_expr (rev (envv ++ prefix))) es).
    {
      eapply exprlist_to_aff_rev_normalized_correct; eauto.
    }
    eapply flatten_instr_prefix_slice_singleton_if_in_poly in Hflat.
    2: { simpl. exact Hprefixlen. }
    2: { exact Hdom. }
    destruct Hflat as (ip0 & Hipl & _ & Hidx & Htr & _ & Hinstr & _).
    subst ipl.
    eapply permutation_singleton in Hperm.
    subst sorted_ipl.
    eapply instr_point_list_semantics_singleton_inv in Hipls.
    destruct Hipls as (stmid & Hipsema & Heq).
    inversion Hipsema as [wcs rcs Hipinstr]; clear Hipsema.
    assert (Hargs:
      affine_product (PolyLang.ip_transformation ip0) (PolyLang.ip_index ip0) =
      map (Loop.eval_expr (rev (envv ++ prefix))) es).
    {
      rewrite Htr, Hidx.
      exact Haff.
    }
    rewrite Hargs, Hinstr in Hipinstr.
    exists stmid.
    split.
    - eapply Loop.LInstr.
      exact Hipinstr.
    - eapply State.eq_sym.
      exact Heq.
Qed.

Lemma flatten_instrs_prefix_slice_nil_implies_nil:
    forall envv prefix ipl,
    flatten_instrs_prefix_slice envv prefix [] ipl ->
    ipl = [].
Proof.
    intros envv prefix ipl Hslice.
    destruct Hslice as [Hchar [_ _]].
    destruct ipl as [|ip ipl'].
    - reflexivity.
    - exfalso.
      pose proof (proj1 (Hchar ip) (or_introl eq_refl)) as Hm.
      destruct Hm as (pi & suf & Hnth & _).
      destruct (PolyLang.ip_nth ip); simpl in Hnth; discriminate.
Qed.

Lemma instr_branch_core_with_constrs_prefix_len:
    forall i es constrs sched_prefix env_dim iter_depth prefix envv
           ipl sorted_ipl st1 st2 tf w r,
    Datatypes.length prefix = iter_depth ->
    exprlist_to_aff es (env_dim + iter_depth)%nat = Okk tf ->
    resolve_access_functions i = Some (w, r) ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix
      [{|
        PolyLang.pi_depth := iter_depth;
        PolyLang.pi_instr := i;
        PolyLang.pi_poly := normalize_affine_list_rev (env_dim + iter_depth)%nat constrs;
        PolyLang.pi_schedule := normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix;
        PolyLang.pi_point_witness := PSWIdentity iter_depth;
        PolyLang.pi_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_access_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_waccess := normalize_access_list (env_dim + iter_depth)%nat w;
        PolyLang.pi_raccess := normalize_access_list (env_dim + iter_depth)%nat r;
      |}] ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics (Loop.Instr i es) (rev (envv ++ prefix)) st1 st2' /\ State.eq st2 st2'.
Proof.
    exact instr_branch_core_prefix.
Qed.

Lemma iter_semantics_shift_start_with_state_eq:
    forall A (P: A -> State.t -> State.t -> Prop),
    (forall x st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      P x st1 st2 ->
      P x st1' st2') ->
    forall xs st1 st2 st1',
      Instr.IterSem.iter_semantics P xs st1 st2 ->
      State.eq st1 st1' ->
      exists st2',
        Instr.IterSem.iter_semantics P xs st1' st2' /\
        State.eq st2 st2'.
Proof.
    intros A P Hstable xs st1 st2 st1' Hiter.
    revert st1'.
    induction Hiter; intros st1' Heqstart.
    - exists st1'.
      split.
      + constructor.
      + exact Heqstart.
    - assert (HP':
          P x st1' st2).
      {
        eapply Hstable with (st1 := st1) (st2 := st2).
        - exact Heqstart.
        - eapply State.eq_refl.
        - exact H.
      }
      destruct (IHHiter st2 (State.eq_refl st2)) as [st3' [Htail' Heq3]].
      exists st3'.
      split.
      + econstructor; eauto.
      + exact Heq3.
Qed.

Lemma iter_semantics_refine_with_state_eq:
    forall A (P Q: A -> State.t -> State.t -> Prop),
    (forall x st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      P x st1 st2 ->
      P x st1' st2') ->
    forall xs st1 st2,
      Instr.IterSem.iter_semantics P xs st1 st2 ->
      (forall x stA stB, In x xs -> P x stA stB ->
        exists stB', Q x stA stB' /\ State.eq stB stB') ->
      exists st2',
        Instr.IterSem.iter_semantics Q xs st1 st2' /\
        State.eq st2 st2'.
Proof.
    intros A P Q Hstable xs.
    induction xs as [|x xs IH]; intros st1 st2 Hiter Hbridge.
    - inversion Hiter; subst; clear Hiter.
      eexists.
      split.
      + constructor.
      + eapply State.eq_refl.
    - inversion Hiter as [|x' xs' st1a st2a st3a HP Htail]; subst; clear Hiter.
      destruct (Hbridge x st1 st2a (or_introl eq_refl) HP)
        as [st2' [HQx Heq2']].
      destruct (
        iter_semantics_shift_start_with_state_eq
          A P Hstable xs st2a st2 st2' Htail Heq2'
      ) as [st3' [HtailP' Heq3']].
      destruct (IH st2' st3' HtailP')
        as [st3'' [HtailQ Heq3'']].
      {
        intros y stA stB Hyin HyP.
        eapply Hbridge.
        - right. exact Hyin.
        - exact HyP.
      }
      exists st3''.
      split.
      + econstructor; eauto.
      + eapply State.eq_trans.
        * exact Heq3'.
        * exact Heq3''.
Qed.

Scheme loop_stmt_mutind_prefix := Induction for PolIRs.Loop.stmt Sort Prop
with loop_stmts_mutind_prefix := Induction for PolIRs.Loop.stmt_list Sort Prop.
Combined Scheme loop_stmt_stmts_mutind_prefix
  from loop_stmt_mutind_prefix, loop_stmts_mutind_prefix.

Definition stmt_constrs_prefix_goal (stmt: PolIRs.Loop.stmt): Prop :=
  forall constrs sched_prefix env_dim iter_depth prefix
         pis envv ipl sorted_ipl st1 st2,
    Datatypes.length prefix = iter_depth ->
    wf_scop_stmt stmt = true ->
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics stmt (rev (envv ++ prefix)) st1 st2' /\ State.eq st2 st2'.

Definition stmts_constrs_prefix_goal (stmts: PolIRs.Loop.stmt_list): Prop :=
  forall constrs sched_prefix env_dim iter_depth prefix pos
         pis envv ipl sorted_ipl st1 st2,
    Datatypes.length prefix = iter_depth ->
    wf_scop_stmts stmts = true ->
    extract_stmts stmts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics (PolIRs.Loop.Seq stmts) (rev (envv ++ prefix)) st1 st2' /\
      State.eq st2 st2'.

Lemma core_sched_stmt_stmts_constrs_prefix_mutual:
  (forall stmt, stmt_constrs_prefix_goal stmt) /\
  (forall stmts, stmts_constrs_prefix_goal stmts).
Proof.
  apply
    (loop_stmt_stmts_mutind_prefix
       stmt_constrs_prefix_goal stmts_constrs_prefix_goal).
  - (* Loop *)
    intros lb ub body IHbody constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    pose proof Hextract as Hextract_loop.
    eapply extract_stmt_loop_success_inv in Hextract.
    destruct Hextract as (lbc & ubc & Hlb & Hub & Hbodyext).
    eapply wf_scop_loop_inv in Hwf.
    destruct Hwf as (_ & _ & Hwf_body).
    assert (Hpoint_ts_head:
      forall ip, In ip sorted_ipl ->
      exists i tsuf,
        PolyLang.ip_time_stamp ip =
          affine_product
            (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
            (envv ++ prefix) ++ [i] ++ tsuf).
    {
      intros ip Hin.
      eapply Permutation_in in Hin.
      2: { exact (Permutation_sym Hperm). }
      destruct (
        flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
          lb ub body constrs env_dim iter_depth sched_prefix prefix
          pis envv ipl ip Hprefixlen Hextract_loop Hflat Hlenenv Hin
      ) as [i [suf [tsuf [_ [_ Hts]]]]].
      exists i.
      exists tsuf.
      exact Hts.
    }
    set (pfx :=
      affine_product
        (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
        (envv ++ prefix)).
    set (head_ts := fun ip : PolyLang.InstrPoint =>
      nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z).
    set (lbv := Loop.eval_expr (rev (envv ++ prefix)) lb).
    set (ubv := Loop.eval_expr (rev (envv ++ prefix)) ub).
    assert (Hpoint_head_in_bounds:
      forall ip, In ip sorted_ipl ->
      (lbv <= head_ts ip < ubv)%Z).
    {
      intros ip Hin.
      eapply Permutation_in in Hin.
      2: { exact (Permutation_sym Hperm). }
      destruct (
        flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
          lb ub body constrs env_dim iter_depth sched_prefix prefix
          pis envv ipl ip Hprefixlen Hextract_loop Hflat Hlenenv Hin
      ) as [i [suf [tsuf [_ [Hbounds Hts]]]]].
      unfold head_ts.
      rewrite Hts.
      unfold pfx.
      rewrite nth_after_prefix_singleton.
      exact Hbounds.
    }
    assert (Hlt_lb_nil:
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) lbv) sorted_ipl = []).
    {
      eapply filter_all_false_nil.
      intros ip Hin.
      pose proof (Hpoint_head_in_bounds ip Hin) as Hbounds.
      eapply Z.ltb_ge.
      lia.
    }
    assert (Hlt_ub_eq_sorted:
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) ubv) sorted_ipl = sorted_ipl).
    {
      assert (Halltrue:
        forall ip, In ip sorted_ipl ->
          Z.ltb (head_ts ip) ubv = true).
      {
        intros ip Hin.
        pose proof (Hpoint_head_in_bounds ip Hin) as Hbounds.
        eapply Z.ltb_lt.
        lia.
      }
      eapply filter_all_true_id.
      exact Halltrue.
    }
    assert (Hlt_succ_split:
      forall i,
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (i + 1)) sorted_ipl =
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl ++
      filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) i) sorted_ipl).
    {
      intros i.
      unfold head_ts.
      eapply sorted_sched_filter_ltb_succ_by_prefix_head.
      - exact Hsorted.
      - intros ip Hin.
        destruct (Hpoint_ts_head ip Hin) as [j [tsuf Hts]].
        exists j.
        exists tsuf.
        rewrite Hts.
        unfold pfx.
        reflexivity.
    }
    assert (Hsem_prefix_step:
      forall i st_next,
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (i + 1)) sorted_ipl)
        st1 st_next ->
      exists st_prev,
        PolyLang.instr_point_list_semantics
          (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl)
          st1 st_prev /\
        PolyLang.instr_point_list_semantics
          (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) i) sorted_ipl)
          st_prev st_next).
    {
      intros i st_next Hsem_next.
      pose proof (Hlt_succ_split i) as Hsplit_succ.
      eapply instr_point_list_semantics_split_by_eq_app
        with
          (l1 := filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl)
          (l2 := filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) i) sorted_ipl)
          (l := filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (i + 1)) sorted_ipl)
          (st1 := st1) (st2 := st_next)
        in Hsem_next.
      2: { exact Hsplit_succ. }
      exact Hsem_next.
    }
    assert (Hpref_lb_eq_st1:
      forall st_lb,
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) lbv) sorted_ipl)
        st1 st_lb ->
      State.eq st1 st_lb).
    {
      intros st_lb Hsem_lb.
      rewrite Hlt_lb_nil in Hsem_lb.
      eapply instr_point_list_semantics_nil_inv in Hsem_lb.
      exact Hsem_lb.
    }

    assert (Hsem_pref_ub:
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) ubv) sorted_ipl)
        st1 st2).
    {
      rewrite Hlt_ub_eq_sorted.
      exact Hipls.
    }
    assert (Hiter_prefix_eq:
      forall i st_i,
      (lbv <= i <= ubv)%Z ->
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl)
        st1 st_i ->
      exists st_i',
        Instr.IterSem.iter_semantics
          (fun x stA stB =>
            PolyLang.instr_point_list_semantics
              (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
              stA stB)
          (Zrange lbv i) st1 st_i' /\
        State.eq st_i st_i').
    {
      intros i st_i Hrange Hpref_i.
      remember (Z.to_nat (i - lbv)) as n eqn:Hn.
      assert (Hi: i = lbv + Z.of_nat n).
      {
        subst n.
        rewrite Z2Nat.id; lia.
      }
      clear Hn.
      revert i st_i Hrange Hpref_i Hi.
      induction n as [|n IH]; intros i st_i Hrange Hpref_i Hi.
      - rewrite Hi in Hpref_i.
        replace (lbv + Z.of_nat 0)%Z with lbv in Hpref_i by lia.
        exists st1.
        split.
        + rewrite Zrange_empty by lia.
          constructor.
        + pose proof (Hpref_lb_eq_st1 st_i Hpref_i) as Heq.
          eapply State.eq_sym.
          exact Heq.
      - assert (Hlt_i: (lbv < i)%Z) by lia.
        set (iprev := (i - 1)%Z).
        assert (Hiprev_range: (lbv <= iprev <= ubv)%Z) by (unfold iprev; lia).
        assert (Hpref_prev_input:
          PolyLang.instr_point_list_semantics
            (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (iprev + 1)) sorted_ipl)
            st1 st_i).
        {
          unfold iprev.
          replace (i - 1 + 1)%Z with i by lia.
          exact Hpref_i.
        }
        destruct (Hsem_prefix_step iprev st_i Hpref_prev_input)
          as [st_prev [Hpref_prev Heq_prev]].
        assert (Hiprev_eq: iprev = lbv + Z.of_nat n).
        { unfold iprev. lia. }
        specialize (IH iprev st_prev Hiprev_range Hpref_prev Hiprev_eq).
        destruct IH as [st_prev' [Hiter_prev Heq_prev_state]].
        assert (Heq_prev_from_prev':
          PolyLang.instr_point_list_semantics
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) iprev) sorted_ipl)
            st_prev' st_i).
        {
          eapply PolyLang.instr_point_list_sema_stable_under_state_eq
            with (st1:=st_prev) (st2:=st_i) (st1':=st_prev') (st2':=st_i) in Heq_prev.
          2: { exact Heq_prev_state. }
          2: { eapply State.eq_refl. }
          exact Heq_prev.
        }
        assert (Hiter_single:
          Instr.IterSem.iter_semantics
            (fun x stA stB =>
              PolyLang.instr_point_list_semantics
                (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
                stA stB)
            [iprev] st_prev' st_i).
        {
          econstructor.
          - exact Heq_prev_from_prev'.
          - constructor.
        }
        exists st_i.
        split.
        + assert (Hiter_cat:
            Instr.IterSem.iter_semantics
              (fun x stA stB =>
                PolyLang.instr_point_list_semantics
                  (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
                  stA stB)
              (Zrange lbv iprev ++ [iprev]) st1 st_i).
          {
            eapply iter_semantics_app; eauto.
          }
          unfold iprev in Hiter_cat.
          replace (Zrange lbv i) with (Zrange lbv (i - 1) ++ [(i - 1)%Z]) by
            (symmetry; eapply Zrange_end; exact Hlt_i).
          exact Hiter_cat.
        + eapply State.eq_refl.
    }
    assert (Hiter_eq_range_from_st1:
      (lbv <= ubv)%Z ->
      exists st2',
        Instr.IterSem.iter_semantics
          (fun x stA stB =>
            PolyLang.instr_point_list_semantics
              (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
              stA stB)
          (Zrange lbv ubv) st1 st2' /\
        State.eq st2 st2').
    {
      intros Hle.
      eapply Hiter_prefix_eq.
      - split; lia.
      - exact Hsem_pref_ub.
    }
    destruct (Z_lt_ge_dec lbv ubv) as [Hlb_lt_ub | Hlb_ge_ub].
    2: {
      assert (sorted_ipl = []) as Hsorted_nil.
      {
        destruct sorted_ipl as [|ip tl].
        + reflexivity.
        + exfalso.
          pose proof (Hpoint_head_in_bounds ip (or_introl eq_refl)) as Hb.
          lia.
      }
      subst sorted_ipl.
      assert (State.eq st1 st2) as Heq12.
      { eapply instr_point_list_semantics_nil_inv; eauto. }
      exists st1.
      split.
      + eapply Loop.LLoop.
        rewrite Zrange_empty by lia.
        constructor.
      + eapply State.eq_sym.
        exact Heq12.
    }
    assert (Hiter_loop_refined:
      forall stA stB,
      Instr.IterSem.iter_semantics
        (fun x stX stY =>
          PolyLang.instr_point_list_semantics
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
            stX stY)
        (Zrange lbv ubv) stA stB ->
      exists stB',
        Instr.IterSem.iter_semantics
          (fun x stX stY =>
            Loop.loop_semantics body (x :: rev (envv ++ prefix)) stX stY)
          (Zrange lbv ubv) stA stB' /\
        State.eq stB stB').
    {
      intros stA stB Hiter.
      eapply iter_semantics_refine_with_state_eq
        with
          (P := fun x stX stY =>
                  PolyLang.instr_point_list_semantics
                    (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
                    stX stY)
          (Q := fun x stX stY =>
                  Loop.loop_semantics body (x :: rev (envv ++ prefix)) stX stY)
          (xs := Zrange lbv ubv) (st1 := stA) (st2 := stB).
      - intros x stX stY stX' stY' HeqX HeqY Hslice0.
        eapply PolyLang.instr_point_list_sema_stable_under_state_eq; eauto.
      - exact Hiter.
      - intros x stX stY Hin Hslice0.
        eapply Zrange_in in Hin.
        assert (Hprefixlen':
          Datatypes.length (prefix ++ [x]) = S iter_depth).
        {
          rewrite app_length.
          simpl.
          rewrite Hprefixlen.
          lia.
        }
        assert (Hconstr_body:
          in_poly (rev (envv ++ (prefix ++ [x])))
            (lift_affine_list constrs ++ [lbc; ubc]) = true).
        {
          replace (rev (envv ++ (prefix ++ [x]))) with (x :: rev (envv ++ prefix)).
          2: {
            symmetry.
            rewrite app_assoc.
            apply rev_unit.
          }
          eapply loop_constraints_sound_lifted
            with (lb:=lb) (ub:=ub) (depth:=(env_dim + iter_depth)%nat).
          - rewrite rev_length.
            rewrite app_length, Hlenenv, Hprefixlen.
            lia.
          - exact Hlb.
          - exact Hub.
          - exact Hconstr.
          - exact Hin.
        }
        assert (Hslice_flat:
          flatten_instrs_prefix_slice envv (prefix ++ [x]) pis
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) ipl)).
        {
          eapply loop_slice_filter_prefix_slice_gen
            with (lb:=lb) (ub:=ub) (body:=body) (constrs:=constrs)
                 (sched_prefix:=sched_prefix) (env_dim:=env_dim)
                 (iter_depth:=iter_depth) (prefix:=prefix) (pis:=pis); eauto.
        }
        assert (Hperm_slice:
          Permutation
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) ipl)
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)).
        {
          eapply permutation_filter.
          exact Hperm.
        }
        assert (Hsorted_slice:
          Sorted PolyLang.instr_point_sched_le
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)).
        {
          eapply sorted_sched_filter.
          exact Hsorted.
        }
        destruct (
          IHbody
            (lift_affine_list constrs ++ [lbc; ubc])
            (lift_affine_list sched_prefix ++
             [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat)%list, 0%Z)])
            env_dim (S iter_depth) (prefix ++ [x])
            pis envv
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) ipl)
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
            stX stY
            Hprefixlen'
            Hwf_body
            Hbodyext
            Hconstr_body
            Hslice_flat
            Hperm_slice
            Hsorted_slice
            Hslice0
            Hlenenv
        ) as [stY' [Hbody_loop HeqY']].
        replace (rev (envv ++ (prefix ++ [x]))) with (x :: rev (envv ++ prefix)) in Hbody_loop.
        2: {
          symmetry.
          rewrite app_assoc.
          apply rev_unit.
        }
        exists stY'.
        split.
        + exact Hbody_loop.
        + exact HeqY'.
    }
    destruct (Hiter_eq_range_from_st1 (ltac:(lia))) as [st2_mid [Hiter_range Heq2_mid]].
    destruct (Hiter_loop_refined st1 st2_mid Hiter_range)
      as [st2' [Hiter_loop Heq2']].
    exists st2'.
    split.
    + eapply Loop.LLoop.
      exact Hiter_loop.
    + eapply State.eq_trans.
      * exact Heq2_mid.
      * exact Heq2'.
  - (* Instr *)
    intros i es constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply extract_stmt_instr_success_inv in Hextract.
    destruct Hextract as (tf & w & r & Htf & Hacc & Hpis).
    subst pis.
    eapply instr_branch_core_with_constrs_prefix_len
      with (tf:=tf) (w:=w) (r:=r); eauto.
  - (* Seq *)
    intros stmts IHstmts constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply wf_scop_seq_inv in Hwf.
    eapply extract_stmt_seq_success_inv in Hextract.
    exact (
      IHstmts constrs sched_prefix env_dim iter_depth prefix 0%nat
              pis envv ipl sorted_ipl st1 st2
              Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv
    ).
  - (* Guard *)
    intros test body IHbody constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply extract_stmt_guard_success_inv in Hextract.
    destruct Hextract as (test_constrs & Htest & Hbodyext).
    eapply wf_scop_guard_inv in Hwf.
    destruct Hwf as [_ Hwf_body].
    destruct (Loop.eval_test (rev (envv ++ prefix)) test) eqn:Heval.
    + assert (Hconstr_body:
        in_poly (rev (envv ++ prefix))
          (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs) = true).
      {
        eapply guard_constraints_sound_in_poly
          with (test:=test) (cols:=(env_dim + iter_depth)%nat); eauto.
        rewrite rev_length.
        rewrite app_length, Hlenenv, Hprefixlen.
        lia.
      }
      pose proof (
        IHbody
          (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs)
          sched_prefix env_dim iter_depth prefix
          pis envv ipl sorted_ipl st1 st2
          Hprefixlen Hwf_body Hbodyext Hconstr_body Hflat Hperm Hsorted Hipls Hlenenv
      ) as Hbody_sem.
      destruct Hbody_sem as [st2' [Hloop_body Heq_body]].
      exists st2'.
      split.
      * eapply Loop.LGuardTrue.
        -- exact Hloop_body.
        -- exact Heval.
      * exact Heq_body.
    + assert (Hnil: ipl = []).
      {
        replace (rev prefix ++ rev envv) with (rev (envv ++ prefix)) in Heval.
        2: { rewrite rev_app_distr. reflexivity. }
        destruct ipl as [|ip ipl'].
        - reflexivity.
        - exfalso.
          assert (Hguardall:
            in_poly (rev (envv ++ prefix))
              (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs) = true).
          {
            eapply flattened_point_satisfies_top_constraints_slice
              with (stmt:=body)
                   (env_dim:=env_dim)
                   (iter_depth:=iter_depth)
                   (sched_prefix:=sched_prefix)
                   (prefix:=prefix)
                   (pis:=pis)
                   (envv:=envv)
                   (ipl:=ip :: ipl')
                   (ip:=ip); eauto.
            simpl. left. reflexivity.
          }
          eapply in_poly_guard_split in Hguardall.
          destruct Hguardall as [_ Hguardnorm].
          assert (Hguardin:
            in_poly (rev (envv ++ prefix))
              (normalize_affine_list (env_dim + iter_depth)%nat test_constrs) = true).
          {
            unfold in_poly.
            exact Hguardnorm.
          }
          assert (Hlenrevprefix:
            Datatypes.length (rev (envv ++ prefix)) = (env_dim + iter_depth)%nat).
          {
            rewrite rev_length.
            rewrite app_length, Hlenenv, Hprefixlen.
            lia.
          }
          pose proof
            (test_false_implies_not_in_poly_normalized
               test
               (rev (envv ++ prefix))
               (env_dim + iter_depth)%nat
               test_constrs
               Htest
               Hlenrevprefix
               Heval) as Hguardfalse.
          rewrite Hguardin in Hguardfalse.
          discriminate.
      }
      subst ipl.
      eapply Permutation_nil in Hperm.
      subst sorted_ipl.
      assert (State.eq st1 st2) as Heq12.
      { eapply instr_point_list_semantics_nil_inv; eauto. }
      exists st1.
      split.
      * eapply Loop.LGuardFalse.
        exact Heval.
      * eapply State.eq_sym.
        exact Heq12.
  - (* SNil *)
    intros constrs sched_prefix env_dim iter_depth prefix pos
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply extract_stmts_nil_success_inv in Hextract.
    subst pis.
    eapply flatten_instrs_prefix_slice_nil_implies_nil in Hflat.
    subst ipl.
    eapply Permutation_nil in Hperm.
    subst sorted_ipl.
    assert (State.eq st1 st2) as Heq12.
    { eapply instr_point_list_semantics_nil_inv; eauto. }
    exists st1.
    split.
    + constructor.
    + eapply State.eq_sym.
      exact Heq12.
  - (* SCons *)
    intros st IHstmt sts IHsts
      constrs sched_prefix env_dim iter_depth prefix pos
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply wf_scop_stmts_cons_inv in Hwf.
    destruct Hwf as [Hwf_hd Hwf_tl].
    pose proof (
      extract_stmts_cons_semantics_split_by_nth_prefix_slice
        st sts constrs env_dim iter_depth sched_prefix prefix pos
        pis envv ipl sorted_ipl st1 st2
        Hprefixlen Hextract Hflat Hlenenv Hperm Hsorted Hipls
    ) as Hsplit.
    destruct Hsplit as
      (pis1 & pis2 & stmid &
       Hhdext & Htlext & _ &
       Hflat1 & Hflat2 & Hsem1 & Hsem2).
    assert (Hperm1:
      Permutation
        (filter
          (fun ip : PolyLang.InstrPoint =>
            Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    pose proof (
      IHstmt constrs
             (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)])
             env_dim iter_depth prefix
             pis1 envv
             (filter
               (fun ip : PolyLang.InstrPoint =>
                 Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
               ipl)
             (filter
               (fun ip : PolyLang.InstrPoint =>
                 Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
               sorted_ipl)
             st1 stmid
             Hprefixlen Hwf_hd Hhdext Hconstr
             Hflat1
             Hperm1
             (sorted_sched_filter _ _ Hsorted)
             Hsem1 Hlenenv
    ) as Hhead.
    destruct Hhead as [sth [Hloop_hd Heq_mid_h]].
    assert (Hsem2_from_sth:
      PolyLang.instr_point_list_semantics
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))
        sth st2).
    {
      eapply PolyLang.instr_point_list_sema_stable_under_state_eq
        with (st1:=stmid) (st2:=st2) (st1':=sth) (st2':=st2) in Hsem2.
      2: { exact Heq_mid_h. }
      2: { eapply State.eq_refl. }
      exact Hsem2.
    }
    assert (Hsorted2_base:
      Sorted PolyLang.instr_point_sched_le
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)).
    { eapply sorted_sched_filter; eauto. }
    assert (Hsorted2:
      Sorted PolyLang.instr_point_sched_le
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))).
    {
      eapply sorted_sched_le_map_rebase_ip_nth.
      exact Hsorted2_base.
    }
    assert (Hperm2:
      Permutation
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    assert (Hperm2_map:
      Permutation
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl))
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))).
    {
      eapply Permutation_map.
      exact Hperm2.
    }
    pose proof (
      IHsts constrs sched_prefix env_dim iter_depth prefix (S pos)
            pis2 envv
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
                ipl))
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
                sorted_ipl))
            sth st2
            Hprefixlen Hwf_tl Htlext Hconstr
            Hflat2
            Hperm2_map
            Hsorted2 Hsem2_from_sth Hlenenv
    ) as Htail.
    destruct Htail as [stt [Hloop_tl Heq_tl]].
    eapply seq_cons_semantics_with_eq
      with (st:=st) (sts:=sts) (env:=rev (envv ++ prefix))
           (st1:=st1) (st2:=sth) (st3:=stt) (st3':=st2); eauto.
Qed.

(** Empty-prefix specializations of the mutual reconstruction theorem.  These
    two private bridges are the only way the compatibility layer below enters
    the main proof. *)
Local Lemma extracted_stmt_core_from_prefix:
    forall stmt constrs sched_prefix (varctxt: list ident) (vars: list (ident * Ty.t))
           pis (envv: list Z) (ipl sorted_ipl: list PolyLang.InstrPoint) st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt constrs (Datatypes.length varctxt) 0 sched_prefix = Okk pis ->
    in_poly (rev envv) constrs = true ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = Datatypes.length varctxt ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros stmt constrs sched_prefix varctxt vars pis envv ipl sorted_ipl st1 st2
      Hwf Hextract Hconstr _ Hflat Hperm Hsorted Hipls Hlenenv.
    pose proof (flatten_instrs_prefix_slice_nil envv pis ipl Hflat) as Hslice.
    assert (Hconstr_nil : in_poly (rev (envv ++ [])) constrs = true).
    { rewrite app_nil_r. exact Hconstr. }
    destruct core_sched_stmt_stmts_constrs_prefix_mutual as [Hstmt _].
    specialize
      (Hstmt stmt constrs sched_prefix
         (Datatypes.length varctxt) 0%nat []
         pis envv ipl sorted_ipl st1 st2
         eq_refl Hwf Hextract Hconstr_nil Hslice Hperm Hsorted Hipls Hlenenv).
    repeat rewrite app_nil_r in Hstmt.
    exact Hstmt.
Qed.

Lemma extract_stmt_to_loop_semantics_core_sched_constrs:
    forall stmt constrs sched_prefix (varctxt: list ident) (vars: list (ident * Ty.t))
           pis (envv: list Z) (ipl sorted_ipl: list PolyLang.InstrPoint) st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt constrs (Datatypes.length varctxt) 0 sched_prefix = Okk pis ->
    in_poly (rev envv) constrs = true ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = Datatypes.length varctxt ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    exact extracted_stmt_core_from_prefix.
Qed.

Lemma extract_stmt_to_loop_semantics_core_sched:
    forall stmt sched_prefix varctxt vars pis envv ipl sorted_ipl st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt [] (Datatypes.length varctxt) 0 sched_prefix = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros stmt sched_prefix varctxt vars pis envv ipl sorted_ipl st1 st2
      Hwf Hextract Hchk Hflat Hperm Hsorted Hipls _ _ Hinit.
    assert (Hlenenv : Datatypes.length envv = Datatypes.length varctxt).
    {
      symmetry.
      eapply Instr.init_env_samelen.
      exact Hinit.
    }
    eapply extract_stmt_to_loop_semantics_core_sched_constrs
      with (constrs:=[]) (sched_prefix:=sched_prefix)
           (varctxt:=varctxt) (vars:=vars) (pis:=pis)
           (envv:=envv) (ipl:=ipl) (sorted_ipl:=sorted_ipl)
           (st1:=st1) (st2:=st2); eauto.
Qed.

Lemma extract_stmt_to_loop_semantics_core:
    forall stmt varctxt vars pis envv ipl sorted_ipl st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt [] (Datatypes.length varctxt) 0 [] = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros.
    eapply extract_stmt_to_loop_semantics_core_sched with (sched_prefix:=[]); eauto.
Qed.


(* Lemma extract_stmt_correct: 
    forall stmt constrs depth sched_prefix, 
        extract_stmt stmt constrs depth sched_prefix = Okk [] ->
        PolyLang.instance_list_semantics constrs [] []. *)

Theorem extractor_correct: 
  forall loop pol st1 st2, 
    extractor loop = Okk pol ->
    PolyLang.instance_list_semantics pol st1 st2 -> 
    exists st2',
    Loop.semantics loop st1 st2' /\ State.eq st2 st2'.
Proof.
    intros loop pol st1 st2 Hext Hsema.
    destruct loop as [[stmt varctxt] vars].
    assert (Hscop: wf_scop_stmt stmt = true).
    { eapply extractor_success_implies_wf_scop; eauto. }
    eapply extractor_success_inv in Hext.
    destruct Hext as [pis [Hextract [Hwf Hpol]]].
    subst pol.
    eapply instance_list_semantics_inv in Hsema.
    destruct Hsema as (pis0 & varctxt0 & vars0 & envv &
      Hpprog & Hcompat & Hnonalias & Hinitenv & Hpolysema).
    inversion Hpprog; subst; clear Hpprog.
    eapply poly_instance_list_semantics_inv in Hpolysema.
    destruct Hpolysema as (pis1 & varctxt1 & vars1 & ipl & sorted_ipl &
      Hpprog' & Hflatten & Hperm & Hsorted & Hipls).
    inversion Hpprog'; subst; clear Hpprog'.
    pose proof (
      extract_stmt_to_loop_semantics_core
        _ _ _ _ _ _ _ _ _
        Hscop Hextract Hwf Hflatten Hperm Hsorted Hipls
        Hcompat Hnonalias Hinitenv
    ) as Hcore.
    destruct Hcore as (st2' & Hloop & Heq).
    exists st2'.
    split.
    - eapply loop_semantics_intro_from_envv; eauto.
    - exact Heq.
Qed.


End Extractor.
