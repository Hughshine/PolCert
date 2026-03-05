Require Import ZArith.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import String.

Require Import PolIRs.

Require Import AST.
Require Import Base.
Require Import PolyBase.
Require Import List.
Import ListNotations.

Require Import Linalg.
Require Import Lia.
Require Import LibTactics.
Require Import sflib.
Require Import Misc.
Require Import Validator.
Require Import Permutation.
Require Import Sorting.Sorted.

Module Extractor (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Module Loop := PolIRs.Loop.
Module Val := Validator PolIRs.
Definition ident := Instr.ident.

(* Note: empty domain contains exactly one instance: [] (empty list) *)

(** generate aff from the deepest *)
(** cur_dim, from 0 to depth *)
Fixpoint expr_to_aff (e: PolIRs.Loop.expr): result (list Z * Z) := 
    match e with 
    (* base case, c*)
    | PolIRs.Loop.Constant z => Okk (nil, z)
    (* base case, xni + c / xni *)
    | PolIRs.Loop.Var n => Okk (V0 n ++ [1%Z] , 0%Z)
    (* base case, anixni + c / anixni*)
    | PolIRs.Loop.Mult z e2 => 
        match expr_to_aff e2 with
        | Okk (aff2, c2) => 
                Okk (mult_vector z aff2, z * c2)
        | Err msg => Err "Expr to aff failed, mult."%string
        end
    (* recursive case *)
    | PolIRs.Loop.Sum e1 e2 =>
        match expr_to_aff e1, expr_to_aff e2 with
        | Okk (aff1, c1), Okk (aff2, c2) => 
            Okk (add_vector aff1 aff2, c1 + c2)
        | Err msg, _ => Err msg
        | _, Err msg => Err msg
        end
    | _ => Err "Expr to aff failed."%string
    end.

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
    intros b1 b2. destruct b1, b2; simpl; tauto.
Qed.

Lemma wf_scop_instr_inv:
    forall instr es,
    wf_scop_stmt (PolIRs.Loop.Instr instr es) = true ->
    wf_affine_expr_list es = true.
Proof.
    intros instr es Hwf.
    simpl in Hwf. exact Hwf.
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
    induction e; intros; simpl in *; try discriminate. 
    - inv H; eauto. inv H2; eauto.
        rewrite dot_product_nil_right. lia.
    - destruct (expr_to_aff e1) eqn: H1 in H; try discriminate.
        destruct p as [v1 z1] eqn: H2 in H; try discriminate.
        destruct (expr_to_aff e2) eqn: H3 in H; try discriminate.
        destruct p0 as [v2 z2] eqn: H4 in H; try discriminate.
        inv H; eauto. inv H6.
        eapply IHe1 with (env:=env) in H1; eauto.
        eapply IHe2 with (env:=env) in H3; eauto.
        rewrite H1. rewrite H3. 
        rewrite add_vector_dot_product_distr_right. lia.
    - destruct (expr_to_aff e) eqn: H1 in H; try discriminate.
        destruct p as [v1 z1] eqn: H2 in H; try discriminate.
        inv H; eauto. inv H4; eauto.
        eapply IHe with (env:=env) in H1; eauto.
        rewrite H1.
        rewrite dot_product_mult_right. lia.
    - inv H. inv H2.
        (* TODO: extract new lib lemma*)
        remember (nth_error env n) as nth.
        destruct nth; try discriminate.
        + symmetry in Heqnth.
        pose proof Heqnth as Heqnth0. 
        eapply v0_n_app_1_dot_product_p_is_nth_p in Heqnth; eauto. 
        rewrite dot_product_commutative.
        rewrite Heqnth.
        eapply nth_error_nth with (d:=0) in Heqnth0. lia. 
        + symmetry in Heqnth.    
        rewrite nth_error_None in Heqnth. pose proof Heqnth as Heqnth0.
        eapply nth_overflow with (d:=0) in Heqnth. rewrite Heqnth.
        eapply dot_product_v0_with_shorter_is_0 with (l:=[1]) in Heqnth0; eauto.
        rewrite Heqnth0. lia.
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

Lemma exprlist_to_aff_length:
    forall es cols affs,
    exprlist_to_aff es cols = Okk affs ->
    Datatypes.length affs = Datatypes.length es.
Proof.
    induction es; intros cols affs H; simpl in H.
    - inv H. auto.
    - destruct (expr_to_aff a) as [[v c]|msg] eqn:Ha; try discriminate.
      destruct (exprlist_to_aff es cols) as [affs'|msg'] eqn:Hes; try discriminate.
      inv H. simpl.
      eapply IHes in Hes.
      lia.
Qed.

Lemma exprlist_to_aff_rows_cols:
    forall es cols affs,
    exprlist_to_aff es cols = Okk affs ->
    Forall (fun aff => Datatypes.length (fst aff) = cols) affs.
Proof.
    induction es; intros cols affs H; simpl in H.
    - inv H. constructor.
    - destruct (expr_to_aff a) as [[v c]|msg] eqn:Ha; try discriminate.
      destruct (exprlist_to_aff es cols) as [affs'|msg'] eqn:Hes; try discriminate.
      inv H.
      constructor.
      + simpl. eapply resize_length.
      + eapply IHes; eauto.
Qed.

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
    induction n as [|n IH]; intros l; simpl.
    - destruct l; reflexivity.
    - destruct l as [|x l']; simpl.
      + reflexivity.
      + rewrite IH.
        lia.
Qed.

Lemma affine_product_seq_row:
    forall cols env pos,
    affine_product [(repeat 0%Z cols, pos)] env = [pos].
Proof.
    intros cols env pos.
    simpl.
    rewrite dot_product_repeat_zero_left.
    reflexivity.
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

Definition normalize_access_rev (cols: nat) (acc: AccessFunction): AccessFunction :=
    let (arrid, affs) := acc in (arrid, normalize_affine_list_rev cols affs).

Definition normalize_access_list_rev (cols: nat) (accs: list AccessFunction) :=
    map (normalize_access_rev cols) accs.

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

Lemma normalize_affine_eval:
    forall cols env aff,
    Datatypes.length env = cols ->
    dot_product (fst (normalize_affine cols aff)) env + snd (normalize_affine cols aff) =
    dot_product (fst aff) env + snd aff.
Proof.
    intros cols env [v c] Hlen.
    unfold normalize_affine. simpl.
    rewrite <- Hlen.
    rewrite dot_product_resize_left.
    lia.
Qed.

Lemma normalize_affine_list_affine_product:
    forall cols env affs,
    Datatypes.length env = cols ->
    affine_product (normalize_affine_list cols affs) env = affine_product affs env.
Proof.
    intros cols env affs Hlen.
    induction affs as [|aff affs IH]; simpl.
    - reflexivity.
    - f_equal.
      + eapply normalize_affine_eval; eauto.
      + exact IH.
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

Lemma exprlist_to_aff_normalized_correct:
    forall es env cols tf,
    exprlist_to_aff es cols = Okk tf ->
    Datatypes.length env = cols ->
    affine_product (normalize_affine_list cols tf) env = map (Loop.eval_expr env) es.
Proof.
    intros es env cols tf Htf Hlen.
    rewrite normalize_affine_list_affine_product with (cols:=cols) (env:=env) (affs:=tf); auto.
    symmetry.
    eapply exprlist_to_aff_correct; eauto.
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

Lemma resolve_access_functions_sound:
    forall instr w r,
    resolve_access_functions instr = Some (w, r) ->
    Instr.valid_access_function w r instr.
Proof.
    intros instr w r Hres.
    unfold resolve_access_functions in Hres.
    remember (PolIRs.Instr.waccess instr) as wopt.
    remember (PolIRs.Instr.raccess instr) as ropt.
    destruct wopt as [w0|]; destruct ropt as [r0|]; simpl in Hres.
    - destruct (PolIRs.Instr.access_function_checker w0 r0 instr) eqn:Hcheck; try discriminate.
      inv Hres.
      eapply PolIRs.Instr.access_function_checker_correct; eauto.
    - destruct (PolIRs.Instr.access_function_checker w0 [] instr) eqn:Hcheck; try discriminate.
      inv Hres.
      eapply PolIRs.Instr.access_function_checker_correct; eauto.
    - destruct (PolIRs.Instr.access_function_checker [] r0 instr) eqn:Hcheck; try discriminate.
      inv Hres.
      eapply PolIRs.Instr.access_function_checker_correct; eauto.
    - destruct (PolIRs.Instr.access_function_checker [] [] instr) eqn:Hcheck; try discriminate.
      inv Hres.
      eapply PolIRs.Instr.access_function_checker_correct; eauto.
Qed.

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
    induction p as [|x p IH]; intros v; destruct v as [|y v']; simpl; try lia.
    rewrite IH. lia.
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
    destruct b; reflexivity.
Qed.

Lemma andb_true_iff_local:
    forall b1 b2, (b1 && b2)%bool = true <-> b1 = true /\ b2 = true.
Proof.
    intros b1 b2. destruct b1, b2; simpl; tauto.
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

Lemma guard_constraints_complete:
    forall test env cols constrs test_constrs,
    test_to_aff test = Okk test_constrs ->
    Datatypes.length env = cols ->
    forallb (satisfies_constraint env)
      (constrs ++ normalize_affine_list cols test_constrs) = true ->
    forallb (satisfies_constraint env) constrs = true /\
    Loop.eval_test env test = true.
Proof.
    intros test env cols constrs test_constrs Htest Hlen Hall.
    rewrite forallb_app in Hall.
    eapply andb_true_iff_local in Hall.
    destruct Hall as [Hconstrs Hguard].
    split; auto.
    eapply test_to_aff_complete_normalized; eauto.
Qed.

Lemma guard_constraints_complete_in_poly:
    forall test env cols constrs test_constrs,
    test_to_aff test = Okk test_constrs ->
    Datatypes.length env = cols ->
    in_poly env (constrs ++ normalize_affine_list cols test_constrs) = true ->
    in_poly env constrs = true /\
    Loop.eval_test env test = true.
Proof.
    intros test env cols constrs test_constrs Htest Hlen Hin.
    unfold in_poly in *.
    eapply guard_constraints_complete in Hin; eauto.
Qed.

Lemma wf_affine_expr_true_expr_to_aff_success:
    forall e,
    wf_affine_expr e = true ->
    exists aff, expr_to_aff e = Okk aff.
Proof.
    induction e as
      [z
      |e1 IHe1 e2 IHe2
      |k e IHe
      |e k
      |e k
      |n
      |e1 IHe1 e2 IHe2
      |e1 IHe1 e2 IHe2];
      intros Hwf; simpl in Hwf; try discriminate.
    - eexists. reflexivity.
    - simpl.
      eapply andb_true_iff_local in Hwf. destruct Hwf as [H1 H2].
      destruct (IHe1 H1) as [aff1 He1].
      destruct (IHe2 H2) as [aff2 He2].
      rewrite He1, He2.
      destruct aff1 as [v1 c1].
      destruct aff2 as [v2 c2].
      simpl. eexists. reflexivity.
    - simpl.
      destruct (IHe Hwf) as [aff He].
      rewrite He.
      destruct aff as [v c].
      simpl. eexists. reflexivity.
    - eexists. reflexivity.
Qed.

Lemma wf_affine_expr_list_true_exprlist_to_aff_success:
    forall es cols,
    wf_affine_expr_list es = true ->
    exists affs, exprlist_to_aff es cols = Okk affs.
Proof.
    induction es as [|e es IH]; intros cols Hwf; simpl in Hwf.
    - eexists. reflexivity.
    - eapply andb_true_iff_local in Hwf. destruct Hwf as [He Hes].
      destruct (wf_affine_expr_true_expr_to_aff_success e He) as [aff Heaff].
      destruct (IH cols Hes) as [affs Haffs].
      destruct aff as [v c].
      simpl in *.
      rewrite Heaff, Haffs.
      eexists. reflexivity.
Qed.

Lemma wf_affine_test_true_test_to_aff_success:
    forall tst,
    wf_affine_test tst = true ->
    exists constrs, test_to_aff tst = Okk constrs.
Proof.
    induction tst as [e1 e2|e1 e2|t1 IH1 t2 IH2|t1 IH1 t2 IH2|t IH|b];
      intros Hwf; simpl in Hwf; try discriminate.
    - eapply andb_true_iff_local in Hwf. destruct Hwf as [He1 He2].
      destruct (wf_affine_expr_true_expr_to_aff_success e1 He1) as [aff1 Haff1].
      destruct (wf_affine_expr_true_expr_to_aff_success e2 He2) as [aff2 Haff2].
      simpl. rewrite Haff1, Haff2. eexists. reflexivity.
    - eapply andb_true_iff_local in Hwf. destruct Hwf as [He1 He2].
      destruct (wf_affine_expr_true_expr_to_aff_success e1 He1) as [aff1 Haff1].
      destruct (wf_affine_expr_true_expr_to_aff_success e2 He2) as [aff2 Haff2].
      simpl. rewrite Haff1, Haff2. eexists. reflexivity.
    - eapply andb_true_iff_local in Hwf. destruct Hwf as [Ht1 Ht2].
      destruct (IH1 Ht1) as [cs1 Hcs1].
      destruct (IH2 Ht2) as [cs2 Hcs2].
      simpl. rewrite Hcs1, Hcs2. eexists. reflexivity.
Qed.

(** depth is the loop's depth (counting ctxt), from zero *)
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

Lemma loop_constraints_complete:
    forall lb ub env depth constrs lbc ubc i,
    Datatypes.length env = depth ->
    lb_to_constr lb depth = Okk lbc ->
    ub_to_constr ub depth = Okk ubc ->
    forallb (satisfies_constraint (i :: env)) (constrs ++ [lbc; ubc]) = true ->
    forallb (satisfies_constraint (i :: env)) constrs = true /\
    (Loop.eval_expr env lb <= i < Loop.eval_expr env ub)%Z.
Proof.
    intros lb ub env depth constrs lbc ubc i Hlen Hlb Hub Hall.
    rewrite forallb_app in Hall.
    eapply andb_true_iff_local in Hall.
    destruct Hall as [Hconstrs Hbounds].
    simpl in Hbounds.
    eapply andb_true_iff_local in Hbounds.
    destruct Hbounds as [Hlbc Hrest].
    eapply andb_true_iff_local in Hrest.
    destruct Hrest as [Hubc _].
    split; auto.
    eapply loop_bounds_sound; eauto.
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

Lemma in_poly_app_inv:
    forall p pol1 pol2,
    in_poly p (pol1 ++ pol2) = true ->
    in_poly p pol1 = true /\ in_poly p pol2 = true.
Proof.
    intros p pol1 pol2 Hin.
    rewrite in_poly_app in Hin.
    eapply andb_true_iff_local in Hin.
    exact Hin.
Qed.

Lemma in_poly_app_cons2_inv:
    forall p pol c1 c2,
    in_poly p (pol ++ [c1; c2]) = true ->
    in_poly p pol = true /\
    satisfies_constraint p c1 = true /\
    satisfies_constraint p c2 = true.
Proof.
    intros p pol c1 c2 Hin.
    apply in_poly_app_inv in Hin.
    destruct Hin as [Hpol Htail].
    simpl in Htail.
    eapply andb_true_iff_local in Htail.
    destruct Htail as [Hc1 Hrest].
    eapply andb_true_iff_local in Hrest.
    destruct Hrest as [Hc2 _].
    repeat split; auto.
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

Lemma dot_product_firstn_right:
    forall v l n,
    Datatypes.length v = n ->
    dot_product v l = dot_product v (firstn n l).
Proof.
    induction v as [|x v IH]; intros l n Hlen; simpl in *.
    - destruct n; simpl in *; [destruct l; reflexivity|lia].
    - destruct n; simpl in Hlen; [lia|].
      destruct l as [|y l']; simpl.
      + reflexivity.
      + inversion Hlen as [Hlen'].
        simpl.
        f_equal.
        eapply IH; eauto.
Qed.

Lemma dot_product_firstn_left:
    forall l v n,
    Datatypes.length v = n ->
    dot_product l v = dot_product (firstn n l) v.
Proof.
    intros l v n Hlen.
    rewrite dot_product_commutative.
    rewrite dot_product_firstn_right with (n:=n) (v:=v) (l:=l); auto.
    rewrite dot_product_commutative.
    reflexivity.
Qed.

Lemma satisfies_constraint_prefix:
    forall cols env idx aff,
    Datatypes.length env = cols ->
    firstn cols idx = env ->
    Datatypes.length (fst aff) = cols ->
    satisfies_constraint idx aff = satisfies_constraint env aff.
Proof.
    intros cols env idx [v c] Henv Hprefix Hlenv.
    unfold satisfies_constraint. simpl.
    rewrite dot_product_firstn_left with (n:=cols) (v:=v) (l:=idx); auto.
Qed.

Lemma in_poly_prefix:
    forall cols env idx constrs,
    Datatypes.length env = cols ->
    firstn cols idx = env ->
    Forall (fun aff => Datatypes.length (fst aff) = cols) constrs ->
    in_poly idx constrs = in_poly env constrs.
Proof.
    intros cols env idx constrs Henv Hprefix Hcols.
    induction constrs as [|aff constrs IH]; simpl in *.
    - reflexivity.
    - inversion Hcols as [|aff' constrs' Haff Hrest]; subst.
      assert (Hs: satisfies_constraint idx aff = satisfies_constraint env aff).
      { eapply satisfies_constraint_prefix; eauto. }
      rewrite Hs.
      rewrite IH; auto.
Qed.

Lemma normalize_affine_list_rev_rows_cols:
    forall cols affs,
    Forall (fun aff => Datatypes.length (fst aff) = cols) (normalize_affine_list_rev cols affs).
Proof.
    intros cols affs.
    induction affs as [|[v c] affs IH]; simpl.
    - constructor.
    - constructor.
      + simpl. rewrite rev_length. eapply resize_length.
      + exact IH.
Qed.

(** $3 + 5 >= $4 => -$3 + $4 <= 5 *)


(** `env_dim` is fixed symbolic context dimension. *)
(** `iter_depth` is the number of surrounding loop iterators. *)
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
                    PolIRs.PolyLang.pi_transformation := normalize_affine_list_rev cols tf;
                    PolIRs.PolyLang.pi_waccess := normalize_access_list_rev cols w;
                    PolIRs.PolyLang.pi_raccess := normalize_access_list_rev cols r;
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
        PolIRs.PolyLang.pi_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolIRs.PolyLang.pi_waccess := normalize_access_list_rev (env_dim + iter_depth)%nat w;
        PolIRs.PolyLang.pi_raccess := normalize_access_list_rev (env_dim + iter_depth)%nat r;
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

(* Extraction examples are kept in instance-level test files (e.g. CPolIRs/TPolIRs)
   because generic functor-level examples become brittle after strengthening
   access-function resolution with checker-dependent branches. *)

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
    intros [[stmt varctxt] vars] [[pis varctxt'] vars'] Hext.
    simpl in *.
    unfold extractor in Hext. simpl in Hext.
    remember (wf_scop_stmt stmt) as WfScop.
    destruct WfScop; try discriminate.
    remember (extract_stmt stmt [] (Datatypes.length varctxt) 0 []) as Extract.
    destruct Extract as [l|msg]; try discriminate.
    destruct (check_extracted_wf l varctxt vars) eqn: Hwf; try discriminate.
    inv Hext. simpl. exact Hwf.
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
    unfold extractor in Hext. simpl in Hext.
    remember (wf_scop_stmt stmt) as WfScop.
    destruct WfScop; try discriminate.
    remember (extract_stmt stmt [] (Datatypes.length varctxt) 0 []) as Extract.
    destruct Extract as [pis|msg]; try discriminate.
    destruct (check_extracted_wf pis varctxt vars) eqn:Hwf; try discriminate.
    inv Hext.
    exists pis.
    repeat split; auto.
Qed.

Lemma extractor_success_inv_full:
    forall stmt varctxt vars pis varctxt' vars',
    extractor (stmt, varctxt, vars) = Okk (pis, varctxt', vars') ->
    varctxt' = varctxt /\
    vars' = vars /\
    extract_stmt stmt [] (Datatypes.length varctxt) 0 [] = Okk pis /\
    check_extracted_wf pis varctxt vars = true.
Proof.
    intros stmt varctxt vars pis varctxt' vars' Hext.
    eapply extractor_success_inv in Hext.
    destruct Hext as [pis' [Hextract [Hwf Hpol]]].
    inversion Hpol; subst.
    repeat split; auto.
Qed.

Lemma extractor_success_implies_wf_pinstrs:
    forall loop pis varctxt vars,
    extractor loop = Okk (pis, varctxt, vars) ->
    Forall (fun pi => PolyLang.wf_pinstr varctxt vars pi) pis.
Proof.
    intros [[stmt varctxt0] vars0] pis varctxt vars Hext.
    unfold extractor in Hext. simpl in Hext.
    remember (wf_scop_stmt stmt) as WfScop.
    destruct WfScop; try discriminate.
    remember (extract_stmt stmt [] (Datatypes.length varctxt0) 0 []) as Extract.
    destruct Extract as [pis0|msg]; try discriminate.
    destruct (check_extracted_wf pis0 varctxt0 vars0) eqn:Hwf; try discriminate.
    inv Hext.
    apply check_extracted_wf_spec in Hwf.
    destruct Hwf as [_ Hall].
    eapply Forall_forall.
    intros pi Hin.
    eapply forallb_forall in Hall; eauto.
    eapply Val.check_wf_polyinstr_correct; eauto.
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

Lemma flatten_instrs_singleton_inv:
    forall envv pi ipl,
    PolyLang.flatten_instrs envv [pi] ipl ->
    PolyLang.flatten_instr_nth envv 0 pi ipl.
Proof.
    intros envv pi ipl Hflat.
    change [pi] with ([] ++ [pi]) in Hflat.
    eapply PolyLang.flatten_instrs_app_singleton_inv in Hflat.
    destruct Hflat as (ipl0 & ipl' & Hflat0 & Hflat1 & Heq).
    eapply PolyLang.flatten_instrs_nil_implies_nil in Hflat0.
    subst ipl0.
    simpl in Heq.
    subst ipl.
    replace (Datatypes.length []) with 0%nat in Hflat1 by reflexivity.
    exact Hflat1.
Qed.

Lemma flatten_instr_nth_in_inv:
    forall envv n pi ipl ip,
    PolyLang.flatten_instr_nth envv n pi ipl ->
    In ip ipl ->
    PolyLang.belongs_to ip pi /\
    PolyLang.ip_nth ip = n /\
    Datatypes.length (PolyLang.ip_index ip) = (Datatypes.length envv + PolyLang.pi_depth pi)%nat.
Proof.
    intros envv n pi ipl ip Hflat Hin.
    destruct Hflat as (_ & Hbel & _ & _).
    eapply Hbel in Hin.
    exact Hin.
Qed.

Lemma flatten_instr_nth_index_split:
    forall envv n pi ipl ip,
    PolyLang.flatten_instr_nth envv n pi ipl ->
    In ip ipl ->
    exists suf,
      PolyLang.ip_index ip = envv ++ suf /\
      Datatypes.length suf = PolyLang.pi_depth pi.
Proof.
    intros envv n pi ipl ip Hflat Hin.
    destruct Hflat as (Hprefix & Hbel & _ & _).
    pose proof (Hprefix ip Hin) as Hpre.
    pose proof (proj1 (Hbel ip) Hin) as Htmp.
    destruct Htmp as (_ & _ & Hlen).
    eapply firstn_length_decompose with (d:=PolyLang.pi_depth pi) in Hpre; eauto.
Qed.

Lemma flatten_instrs_in_inv:
    forall envv pis ipl ip,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    exists pi,
      In pi pis /\
      PolyLang.belongs_to ip pi /\
      Datatypes.length (PolyLang.ip_index ip) = (Datatypes.length envv + PolyLang.pi_depth pi)%nat.
Proof.
    intros envv pis ipl ip Hflat Hin.
    destruct Hflat as (_ & Hchar & _ & _).
    specialize (Hchar ip).
    eapply Hchar in Hin.
    destruct Hin as (pi & Hnth & Hbel & Hlen).
    exists pi.
    split.
    - eapply nth_error_In; eauto.
    - split; auto.
Qed.

Lemma flattened_point_satisfies_top_constraints:
    forall stmt constrs env_dim sched_prefix pis envv ipl ip,
    extract_stmt stmt constrs env_dim 0%nat sched_prefix = Okk pis ->
    PolyLang.flatten_instrs envv pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    in_poly (rev envv) constrs = true.
Proof.
    intros stmt constrs env_dim sched_prefix pis envv ipl ip
      Hext Hflat Hlenenv Hip.
    destruct Hflat as (Hprefix & Hchar & Hnodup & Hsortednp).
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & Hnth & Hbel & Hlenidx).
    pose proof Hlenidx as Hlenidx0.
    eapply extract_stmt_has_lifted_prefix in Hext.
    2: { eapply nth_error_In; eauto. }
    destruct Hext as (k & tail & Hdepth & Hpoly).
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (Hindom & Htf & Hts & Hinst & Hdep).
    rewrite Hpoly in Hindom.
    rewrite Hlenenv in Hlenidx.
    eapply in_poly_normalize_affine_list_rev_app_inv
      with (cols:=(env_dim + PolyLang.pi_depth pi)%nat)
           (env:=PolyLang.ip_index ip)
           (pol1:=lift_affine_list_n k constrs)
           (pol2:=tail) in Hindom.
    2: { exact Hlenidx. }
    destruct Hindom as [Hbase _].
    pose proof (Hprefix ip Hip) as Hpre.
    eapply firstn_length_decompose with (d:=PolyLang.pi_depth pi) in Hpre.
    2: { exact Hlenidx0. }
    destruct Hpre as (suf & Hidx & Hsuflen).
    rewrite Hidx in Hbase.
    rewrite rev_app_distr in Hbase.
    rewrite Hdepth in Hsuflen.
    simpl in Hsuflen.
    assert (Datatypes.length (rev suf) = k)%nat as Hlenrev.
    { rewrite rev_length. lia. }
    rewrite <- Hlenrev in Hbase.
    rewrite in_poly_lift_affine_list_n_app in Hbase.
    exact Hbase.
Qed.

Lemma flattened_point_schedule_has_top_prefix:
    forall stmt constrs env_dim sched_prefix pis envv ipl ip,
    extract_stmt stmt constrs env_dim 0%nat sched_prefix = Okk pis ->
    PolyLang.flatten_instrs envv pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product (normalize_affine_list_rev env_dim sched_prefix) envv ++ tsuf.
Proof.
    intros stmt constrs env_dim sched_prefix pis envv ipl ip
      Hext Hflat Hlenenv Hip.
    destruct Hflat as (Hprefix & Hchar & Hnodup & Hsortednp).
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & Hnth & Hbel & Hlenidx).
    pose proof Hlenidx as Hlenidx0.
    eapply extract_stmt_has_lifted_sched_prefix in Hext.
    2: { eapply nth_error_In; eauto. }
    destruct Hext as (k & tail & Hdepth & Hsched).
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (Hindom & Htf & Hts & Hinst & Hdep).
    rewrite Hsched in Hts.
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: { rewrite Hlenenv in Hlenidx. exact Hlenidx. }
    pose proof (Hprefix ip Hip) as Hpre.
    eapply firstn_length_decompose with (d:=PolyLang.pi_depth pi) in Hpre.
    2: { exact Hlenidx0. }
    destruct Hpre as (suf & Hidx & Hsuflen).
    rewrite Hidx in Hts.
    rewrite rev_app_distr in Hts.
    rewrite Hdepth in Hsuflen.
    simpl in Hsuflen.
    assert (Datatypes.length (rev suf) = k)%nat as Hlenrev.
    { rewrite rev_length. lia. }
    rewrite affine_product_app in Hts.
    rewrite <- Hlenrev in Hts.
    rewrite affine_product_lift_affine_list_n_app in Hts.
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=env_dim) (env:=envv) (affs:=sched_prefix) in Hts.
    2: { exact Hlenenv. }
    exists (affine_product tail (rev suf ++ rev envv)).
    exact Hts.
Qed.

Lemma flattened_point_seq_pos_timestamp:
    forall stmt constrs env_dim pos pis envv ipl ip,
    extract_stmt stmt constrs env_dim 0%nat [(repeat 0%Z env_dim, pos)] = Okk pis ->
    PolyLang.flatten_instrs envv pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists tsuf,
      PolyLang.ip_time_stamp ip = [pos] ++ tsuf.
Proof.
    intros stmt constrs env_dim pos pis envv ipl ip
      Hext Hflat Hlenenv Hip.
    eapply flattened_point_schedule_has_top_prefix
      with (ip:=ip) in Hext; eauto.
    destruct Hext as [tsuf Hts].
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: { exact Hlenenv. }
    assert (affine_product [(repeat 0%Z env_dim, pos)] (rev envv) = [pos]) as Hrow.
    { eapply affine_product_seq_row. }
    rewrite Hrow in Hts.
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

Lemma instr_point_sched_le_from_cons_head_lt:
    forall ip1 ip2 h1 h2 t1 t2,
    PolyLang.ip_time_stamp ip1 = h1 :: t1 ->
    PolyLang.ip_time_stamp ip2 = h2 :: t2 ->
    (h1 < h2)%Z ->
    PolyLang.instr_point_sched_le ip1 ip2.
Proof.
    intros ip1 ip2 h1 h2 t1 t2 Hts1 Hts2 Hlt.
    unfold PolyLang.instr_point_sched_le.
    left.
    rewrite Hts1, Hts2.
    eapply lex_compare_cons_head_lt; eauto.
Qed.

Lemma flattened_guard_false_implies_nil:
    forall test body varctxt vars envv pis ipl st1,
    wf_scop_stmt (PolIRs.Loop.Guard test body) = true ->
    extract_stmt (PolIRs.Loop.Guard test body) [] (Datatypes.length varctxt) 0%nat [] = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Instr.InitEnv varctxt envv st1 ->
    Loop.eval_test (rev envv) test = false ->
    ipl = [].
Proof.
    intros test body varctxt vars envv pis ipl st1
      Hwf Hext Hchk Hflat Hinit Hevalfalse.
    eapply extract_stmt_guard_success_inv in Hext.
    destruct Hext as (test_constrs & Htest & Hbodyext).
    pose proof (Instr.init_env_samelen varctxt envv st1 Hinit) as Hlenenv.
    simpl in Hbodyext.
    replace (Datatypes.length varctxt + 0)%nat with (Datatypes.length varctxt) in Hbodyext by lia.
    destruct ipl as [|ip ipl'].
    - reflexivity.
    - exfalso.
      assert (in_poly (rev envv)
        (normalize_affine_list (Datatypes.length varctxt) test_constrs) = true) as Hguardin.
      {
        eapply flattened_point_satisfies_top_constraints
          with (stmt:=body)
               (constrs:=normalize_affine_list (Datatypes.length varctxt) test_constrs)
               (env_dim:=Datatypes.length varctxt)
               (sched_prefix:=[])
               (pis:=pis)
               (envv:=envv)
               (ipl:=ip :: ipl')
               (ip:=ip); eauto.
        simpl. left. reflexivity.
      }
      eapply test_false_implies_not_in_poly_normalized in Hevalfalse; eauto.
      assert (in_poly (rev envv)
        (normalize_affine_list (Datatypes.length (rev envv)) test_constrs) = true) as Hguardin'.
      {
        rewrite rev_length.
        rewrite <- Hlenenv.
        exact Hguardin.
      }
      rewrite Hguardin' in Hevalfalse.
      discriminate.
Qed.

Lemma flattened_guard_nonempty_implies_true:
    forall test body varctxt vars envv pis ip ipl' st1,
    wf_scop_stmt (PolIRs.Loop.Guard test body) = true ->
    extract_stmt (PolIRs.Loop.Guard test body) [] (Datatypes.length varctxt) 0%nat [] = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis (ip :: ipl') ->
    Instr.InitEnv varctxt envv st1 ->
    Loop.eval_test (rev envv) test = true.
Proof.
    intros test body varctxt vars envv pis ip ipl' st1
      Hwf Hext Hchk Hflat Hinit.
    eapply extract_stmt_guard_success_inv in Hext.
    destruct Hext as (test_constrs & Htest & Hbodyext).
    pose proof (Instr.init_env_samelen varctxt envv st1 Hinit) as Hlenenv.
    simpl in Hbodyext.
    replace (Datatypes.length varctxt + 0)%nat with (Datatypes.length varctxt) in Hbodyext by lia.
    assert (in_poly (rev envv)
      (normalize_affine_list (Datatypes.length varctxt) test_constrs) = true) as Hguardin.
    {
      eapply flattened_point_satisfies_top_constraints
        with (stmt:=body)
             (constrs:=normalize_affine_list (Datatypes.length varctxt) test_constrs)
             (env_dim:=Datatypes.length varctxt)
             (sched_prefix:=[])
             (pis:=pis)
             (envv:=envv)
             (ipl:=ip :: ipl')
             (ip:=ip); eauto.
      simpl. left. reflexivity.
    }
    assert (in_poly (rev envv)
      ([] ++ normalize_affine_list (Datatypes.length varctxt) test_constrs) = true) as Hguardin_app.
    { simpl. exact Hguardin. }
    assert (Datatypes.length (rev envv) = Datatypes.length varctxt) as Hlenrev.
    { rewrite rev_length. symmetry. exact Hlenenv. }
    pose proof (
      guard_constraints_complete_in_poly
        test (rev envv) (Datatypes.length varctxt) [] test_constrs
        Htest Hlenrev Hguardin_app
    ) as Hguardtrue.
    destruct Hguardtrue as [_ Heval].
    exact Heval.
Qed.

Lemma guard_false_core_case:
    forall test body varctxt vars pis envv ipl sorted_ipl st1 st2,
    wf_scop_stmt (PolIRs.Loop.Guard test body) = true ->
    extract_stmt (PolIRs.Loop.Guard test body) [] (Datatypes.length varctxt) 0%nat [] = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    Loop.eval_test (rev envv) test = false ->
    exists st2',
      Loop.loop_semantics (PolIRs.Loop.Guard test body) (rev envv) st1 st2' /\
      State.eq st2 st2'.
Proof.
    intros test body varctxt vars pis envv ipl sorted_ipl st1 st2
      Hwf Hext Hchk Hflat Hperm Hsorted Hipls Hcompat Hnonalias Hinit Hevalfalse.
    assert (Hnil: ipl = []).
    {
      eapply flattened_guard_false_implies_nil
        with (test:=test) (body:=body) (varctxt:=varctxt) (vars:=vars) (st1:=st1); eauto.
    }
    subst ipl.
    eapply Permutation_nil in Hperm.
    subst sorted_ipl.
    assert (State.eq st1 st2) as Heq12.
    { inversion Hipls; subst; auto. }
    exists st1.
    split.
    - eapply Loop.LGuardFalse.
      exact Hevalfalse.
    - eapply State.eq_sym.
      exact Heq12.
Qed.

Lemma permutation_singleton:
    forall A (x: A) l,
    Permutation [x] l ->
    l = [x].
Proof.
    intros A x l Hperm.
    assert (Datatypes.length l = 1)%nat as Hlen.
    { eapply Permutation_length in Hperm. simpl in Hperm. lia. }
    destruct l as [|y l']; simpl in Hlen; try lia.
    destruct l' as [|z l'']; simpl in Hlen; try lia.
    eapply Permutation_length_1 in Hperm.
    subst y. reflexivity.
Qed.

Lemma instr_point_list_semantics_singleton_inv:
    forall ip st1 st2,
    PolyLang.instr_point_list_semantics [ip] st1 st2 ->
    exists stmid,
      PolyLang.instr_point_sema ip st1 stmid /\
      State.eq stmid st2.
Proof.
    intros ip st1 st2 Hsema.
    inversion Hsema; subst; clear Hsema.
    inversion H4; subst; clear H4.
    exists st3.
    split; auto.
Qed.

Lemma instr_point_list_semantics_nil_inv:
    forall st1 st2,
    PolyLang.instr_point_list_semantics [] st1 st2 ->
    State.eq st1 st2.
Proof.
    intros st1 st2 Hsema.
    inversion Hsema; subst; auto.
Qed.

Lemma instr_point_list_semantics_app_inv:
    forall l1 l2 st1 st3,
    PolyLang.instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      PolyLang.instr_point_list_semantics l1 st1 st2 /\
      PolyLang.instr_point_list_semantics l2 st2 st3.
Proof.
    induction l1 as [|ip l1 IH]; intros l2 st1 st3 Hsema.
    - simpl in Hsema.
      exists st1.
      split.
      + constructor.
        eapply State.eq_refl.
      + exact Hsema.
    - simpl in Hsema.
      inversion Hsema; subst; clear Hsema.
      eapply IH in H4.
      destruct H4 as (stmid & Hleft & Hright).
      exists stmid.
      split.
      + econstructor; eauto.
      + exact Hright.
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

Lemma flatten_instr_nth_depth0_emptydom_singleton:
    forall envv n pi ipl,
    PolyLang.pi_depth pi = 0%nat ->
    PolyLang.pi_poly pi = [] ->
    PolyLang.flatten_instr_nth envv n pi ipl ->
    exists ip0,
      ipl = [ip0] /\
      PolyLang.ip_nth ip0 = n /\
      PolyLang.ip_index ip0 = envv /\
      PolyLang.ip_transformation ip0 = PolyLang.pi_transformation pi /\
      PolyLang.ip_time_stamp ip0 = affine_product (PolyLang.pi_schedule pi) envv /\
      PolyLang.ip_instruction ip0 = PolyLang.pi_instr pi /\
      PolyLang.ip_depth ip0 = PolyLang.pi_depth pi.
Proof.
    intros envv n pi ipl Hdepth Hpoly Hflat.
    subst.
    destruct Hflat as (Hprefix & Hchar & Hnodup & _).
    set (ip0 := {|
      PolyLang.ip_nth := n;
      PolyLang.ip_index := envv;
      PolyLang.ip_transformation := PolyLang.pi_transformation pi;
      PolyLang.ip_time_stamp := affine_product (PolyLang.pi_schedule pi) envv;
      PolyLang.ip_instruction := PolyLang.pi_instr pi;
      PolyLang.ip_depth := PolyLang.pi_depth pi;
    |}).
    assert (In ip0 ipl) as Hin0.
    {
      eapply (proj2 (Hchar ip0)).
      split.
      - unfold PolyLang.belongs_to.
        simpl.
        rewrite Hpoly.
        simpl.
        repeat split; reflexivity.
      - split.
        + reflexivity.
        + rewrite Hdepth. simpl. lia.
    }
    assert (forall ip, In ip ipl -> ip = ip0) as Hall.
    {
      intros ip Hin.
      pose proof (proj1 (Hchar ip) Hin) as Hmem.
      destruct Hmem as (Hbel & Hnth & Hlen).
      pose proof (Hprefix ip Hin) as Hpre.
      pose proof (firstn_length_decompose envv (PolyLang.ip_index ip) 0 Hpre) as Hsplit.
      assert (Datatypes.length (PolyLang.ip_index ip) = Datatypes.length envv + 0)%nat as Hlen0 by lia.
      specialize (Hsplit Hlen0).
      destruct Hsplit as (suf & Hidx & Hsuflen).
      assert (suf = []).
      { destruct suf; simpl in Hsuflen; try lia; reflexivity. }
      subst suf.
      rewrite app_nil_r in Hidx.
      subst.
      unfold PolyLang.belongs_to in Hbel.
      destruct Hbel as (_ & Htf & Hts & Hinst & Hdep).
      destruct ip.
      simpl in *.
      subst.
      reflexivity.
    }
    exists ip0.
    split.
    - eapply nodup_all_eq_singleton; eauto.
    - repeat split; reflexivity.
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

Lemma loop_semantics_aux_implies_loop_semantics:
    forall stmt env st1 st2,
    Loop.loop_semantics_aux stmt env st1 st2 ->
    Loop.loop_semantics stmt env st1 st2.
Proof.
    intros stmt env st1 st2 Haux.
    induction Haux using Loop.loop_semantics_aux_mutual_ind
      with (P0 := fun zs stmt env st1 st2 Hlist =>
                  Instr.IterSem.iter_semantics
                    (fun x => Loop.loop_semantics stmt (x :: env)) zs st1 st2).
    - econstructor; eauto.
    - constructor.
    - econstructor; eauto.
    - eapply Loop.LGuardTrue; eauto.
    - eapply Loop.LGuardFalse; eauto.
    - eapply Loop.LLoop; eauto.
    - constructor.
    - econstructor; eauto.
Qed.

Lemma loop_instance_list_semantics_implies_loop_semantics:
    forall stmt env il st1 st2,
    Loop.loop_instance_list_semantics stmt env il st1 st2 ->
    Loop.loop_semantics stmt env st1 st2.
Proof.
    intros stmt env il st1 st2 Hlil.
    eapply loop_semantics_aux_implies_loop_semantics.
    eapply Loop.instance_list_implies_loop_semantics_aux; eauto.
Qed.

Lemma guard_true_semantics_with_eq:
    forall test body env st1 st2 st2',
    Loop.loop_semantics body env st1 st2' ->
    Loop.eval_test env test = true ->
    State.eq st2 st2' ->
    exists stmid,
      Loop.loop_semantics (PolIRs.Loop.Guard test body) env st1 stmid /\
      State.eq st2 stmid.
Proof.
    intros test body env st1 st2 st2' Hbody Heval Heq.
    exists st2'.
    split.
    - eapply Loop.LGuardTrue; eauto.
    - exact Heq.
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

Lemma instr_branch_core:
    forall i es varctxt envv ipl sorted_ipl st1 st2 tf w r,
    exprlist_to_aff es (Datatypes.length varctxt) = Okk tf ->
    resolve_access_functions i = Some (w, r) ->
    PolyLang.flatten_instrs envv
      [{|
        PolyLang.pi_depth := 0;
        PolyLang.pi_instr := i;
        PolyLang.pi_poly := normalize_affine_list_rev (Datatypes.length varctxt) [];
        PolyLang.pi_schedule := normalize_affine_list_rev (Datatypes.length varctxt) [];
        PolyLang.pi_transformation := normalize_affine_list_rev (Datatypes.length varctxt) tf;
        PolyLang.pi_waccess := normalize_access_list_rev (Datatypes.length varctxt) w;
        PolyLang.pi_raccess := normalize_access_list_rev (Datatypes.length varctxt) r;
      |}] ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Instr.InitEnv varctxt envv st1 ->
    exists st2',
      Loop.loop_semantics (Loop.Instr i es) (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros i es varctxt envv ipl sorted_ipl st1 st2 tf w r
      Htf Hacc Hflat Hperm Hsorted Hipls Hinit.
    pose proof (Instr.init_env_samelen varctxt envv st1 Hinit) as Hlen.
    assert (affine_product (normalize_affine_list_rev (Datatypes.length varctxt) tf) envv =
            map (Loop.eval_expr (rev envv)) es) as Haff.
    {
      eapply exprlist_to_aff_rev_normalized_correct; eauto.
    }
    eapply flatten_instrs_singleton_inv in Hflat.
    eapply flatten_instr_nth_depth0_emptydom_singleton in Hflat.
    2: reflexivity.
    2: simpl; reflexivity.
    destruct Hflat as (ip0 & Hipl & Hnth & Hidx & Htr & Hts & Hinstr & Hdep).
    subst ipl.
    eapply permutation_singleton in Hperm.
    subst sorted_ipl.
    eapply instr_point_list_semantics_singleton_inv in Hipls.
    destruct Hipls as (stmid & Hipsema & Heq).
    inversion Hipsema as [wcs rcs Hipinstr]; clear Hipsema.
    assert (affine_product (PolyLang.ip_transformation ip0) (PolyLang.ip_index ip0) =
            map (Loop.eval_expr (rev envv)) es) as Hargs_rev.
    {
      rewrite Htr.
      rewrite Hidx.
      replace (Datatypes.length varctxt + 0)%nat with (Datatypes.length varctxt) by lia.
      exact Haff.
    }
    rewrite Hargs_rev in Hipinstr.
    rewrite Hinstr in Hipinstr.
    exists stmid.
    split.
    - eapply Loop.LInstr.
      eauto.
    - eapply State.eq_sym.
      exact Heq.
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
    intros stmt varctxt vars pis envv ipl sorted_ipl st1 st2
      Hwf Hextract Hchk Hflat Hperm Hsorted Hipls Hcompat Hnonalias Hinit.
    destruct stmt as [lb ub body | i es | stmts | test body].
    2:{
      eapply extract_stmt_instr_success_inv in Hextract.
      destruct Hextract as (tf & w & r & Htf & Hacc & Hpis).
      subst pis.
      replace (Datatypes.length varctxt + 0)%nat with (Datatypes.length varctxt) in Htf by lia.
      replace (Datatypes.length varctxt + 0)%nat with (Datatypes.length varctxt) in Hflat by lia.
      replace (Datatypes.length varctxt + 0)%nat with (Datatypes.length varctxt) in Hchk by lia.
      eapply (instr_branch_core i es varctxt envv ipl sorted_ipl st1 st2 tf w r); eauto.
    }
Admitted.


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
