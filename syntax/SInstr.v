Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import StateTy.
Require Import TyTy.
Require Import InstrTy.
Require Import IterSemantics.
Require Import ImpureAlarmConfig.
Require Import Base.
Require Import PolyBase.
Require Import AST.
Require Import OpenScop.
Require Import Coqlib.
Require Import Linalg.
Import List.ListNotations.
Open Scope Z_scope.

Module Ty <: TY.
  Definition t := unit.
  Definition dummy := tt.
  Definition eqb (_ _ : t) := true.
  Lemma eqb_eq : forall t1 t2, eqb t1 t2 = true <-> t1 = t2.
  Proof. intros. split; intros; destruct t1, t2; reflexivity. Qed.
End Ty.

Module State <: STATE.
  Definition t := unit.
  Definition non_alias (_ : t) := True.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_trans := @eq_trans t.
  Definition eq_sym := @eq_sym t.
  Definition dummy_state := tt.
End State.

Module SInstr <: INSTR.
  Module State := State.
  Module Ty := Ty.
  Module IterSem := IterSem State.
  Module IterSemImpure := IterSem.IterImpureSemantics(CoreAlarmed).

  Definition ident := AST.ident.
  Definition ident_eqb := Pos.eqb.
  Definition ident_eqb_eq := Pos.eqb_eq.
  Definition ident_eq_dec : forall i1 i2 : ident, {i1 = i2} + {i1 <> i2} := Pos.eq_dec.
  Definition ident_to_openscop_ident (id : ident) := id.
  Definition openscop_ident_to_ident (id : AST.ident) := id.
  Definition ident_to_varname := AST.ident_to_varname.
  Definition varname_to_ident := AST.varname_to_ident.
  Definition bind_ident_varname := AST.bind_ident_varname.
  Definition iterator_to_varname := AST.iterator_to_varname.

  Inductive affine_expr : Type :=
  | AeConst (z : Z)
  | AeVar (n : nat)
  | AeAdd (e1 e2 : affine_expr)
  | AeSub (e1 e2 : affine_expr)
  | AeMul (z : Z) (e : affine_expr).

  Inductive access : Type :=
  | AcVar (id : ident)
  | AcArr (id : ident) (indices : list affine_expr).

  Inductive expr : Type :=
  | ExConst (z : Z)
  | ExVar (n : nat)
  | ExAccess (a : access)
  | ExAdd (e1 e2 : expr)
  | ExSub (e1 e2 : expr)
  | ExMul (e1 e2 : expr).

  Inductive lang : Type :=
  | SSkip
  | SAssign (lhs : access) (rhs : expr).

  Definition t := lang.
  Definition dummy_instr := SSkip.

  Inductive sema : t -> list Z -> list MemCell -> list MemCell -> State.t -> State.t -> Prop := .
  Definition instr_semantics := sema.

  Fixpoint affine_expr_eq_dec (e1 e2 : affine_expr) : {e1 = e2} + {e1 <> e2}.
  Proof. decide equality; try apply Z.eq_dec; try apply Nat.eq_dec. Defined.

  Definition access_eq_dec (a1 a2 : access) : {a1 = a2} + {a1 <> a2}.
  Proof.
    destruct a1 as [id1|id1 idx1], a2 as [id2|id2 idx2].
    - destruct (ident_eq_dec id1 id2) as [Heq|Hneq].
      + subst. left. reflexivity.
      + right. intros H. inversion H. contradiction.
    - right. discriminate.
    - right. discriminate.
    - destruct (ident_eq_dec id1 id2) as [Heq|Hneq].
      + subst. destruct (list_eq_dec affine_expr_eq_dec idx1 idx2) as [Hidx|Hidx].
        * subst. left. reflexivity.
        * right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
  Defined.

  Fixpoint expr_eq_dec (e1 e2 : expr) : {e1 = e2} + {e1 <> e2}.
  Proof. decide equality; try apply access_eq_dec; try apply Z.eq_dec; try apply Nat.eq_dec. Defined.

  Fixpoint lang_eq_dec (i1 i2 : lang) : {i1 = i2} + {i1 <> i2}.
  Proof. decide equality; try apply expr_eq_dec; try apply access_eq_dec. Defined.

  Definition eqb (i1 i2 : t) : bool :=
    if lang_eq_dec i1 i2 then true else false.

  Lemma eqb_eq : forall i1 i2, eqb i1 i2 = true <-> i1 = i2.
  Proof.
    intros i1 i2. unfold eqb.
    destruct (lang_eq_dec i1 i2); split; intro H; auto; discriminate.
  Qed.

  Definition NonAlias (_ : State.t) : Prop := True.

  Lemma sema_prsv_nonalias :
    forall i p wcs rcs st1 st2,
      NonAlias st1 ->
      instr_semantics i p wcs rcs st1 st2 ->
      NonAlias st2.
  Proof. intros; firstorder. Qed.

  Lemma instr_semantics_stable_under_state_eq :
    forall i p wcs rcs st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      instr_semantics i p wcs rcs st1 st2 ->
      instr_semantics i p wcs rcs st1' st2'.
  Proof. intros; firstorder. Qed.

  Definition InitEnv (env : list ident) (envv : list Z) (_ : State.t) : Prop :=
    length env = length envv.

  Definition Compat (_ : list (ident * Ty.t)) (_ : State.t) : Prop := True.

  Lemma init_env_samelen :
    forall env envv st,
      InitEnv env envv st ->
      length env = length envv.
  Proof. auto. Qed.

  Definition coeff_of_var (n : nat) : list Z :=
    assign n 1%Z (V0 (S n)).

  Fixpoint affine_expr_to_affine (e : affine_expr) : (list Z * Z) :=
    match e with
    | AeConst z => ([], z)
    | AeVar n => (coeff_of_var n, 0%Z)
    | AeAdd e1 e2 =>
        let '(v1, c1) := affine_expr_to_affine e1 in
        let '(v2, c2) := affine_expr_to_affine e2 in
        (add_vector v1 v2, (c1 + c2)%Z)
    | AeSub e1 e2 =>
        let '(v1, c1) := affine_expr_to_affine e1 in
        let '(v2, c2) := affine_expr_to_affine e2 in
        (add_vector v1 (mult_vector (-1)%Z v2), (c1 - c2)%Z)
    | AeMul z e =>
        let '(v, c) := affine_expr_to_affine e in
        (mult_vector z v, (z * c)%Z)
    end.

  Definition access_to_function (a : access) : AccessFunction :=
    match a with
    | AcVar id => (id, [])
    | AcArr id indices => (id, map affine_expr_to_affine indices)
    end.

  Definition access_ident (a : access) : ident :=
    match a with
    | AcVar id => id
    | AcArr id _ => id
    end.

  Fixpoint read_accesses_expr (e : expr) : list AccessFunction :=
    match e with
    | ExConst _ => []
    | ExVar _ => []
    | ExAccess a => [access_to_function a]
    | ExAdd e1 e2 => read_accesses_expr e1 ++ read_accesses_expr e2
    | ExSub e1 e2 => read_accesses_expr e1 ++ read_accesses_expr e2
    | ExMul e1 e2 => read_accesses_expr e1 ++ read_accesses_expr e2
    end.

  Definition waccess (i : t) : option (list AccessFunction) :=
    match i with
    | SSkip => Some []
    | SAssign lhs _ => Some [access_to_function lhs]
    end.

  Definition raccess (i : t) : option (list AccessFunction) :=
    match i with
    | SSkip => Some []
    | SAssign _ rhs => Some (read_accesses_expr rhs)
    end.

  Definition valid_access_function (wl rl : list AccessFunction) (i : t) : Prop :=
    forall p st st' wcells rcells,
      instr_semantics i p wcells rcells st st' ->
      valid_access_cells p wcells wl /\ valid_access_cells p rcells rl.

  Definition check_never_written (ctxt : list ident) (i : t) : bool :=
    match i with
    | SSkip => true
    | SAssign lhs _ => negb (existsb (ident_eqb (access_ident lhs)) ctxt)
    end.

  Definition normalize_affine_rev (cols : nat) (aff : list Z * Z) : (list Z * Z) :=
    let '(v, c) := aff in
    (rev (resize cols v), c).

  Definition normalize_affine_list_rev (cols : nat) (affs : list (list Z * Z)) :=
    map (normalize_affine_rev cols) affs.

  Definition normalize_access_rev (cols : nat) (acc : AccessFunction) : AccessFunction :=
    let '(arrid, affs) := acc in
    (arrid, normalize_affine_list_rev cols affs).

  Definition access_cols (acc : AccessFunction) : nat :=
    let '(_, affs) := acc in
    list_max (map (fun aff => let '(zs, _) := aff in length zs) affs).

  Definition access_function_checker_access
      (al : list AccessFunction) (a : access) : bool :=
    let acc := access_to_function a in
    existsb
      (fun target =>
        access_strict_eqb acc target ||
        access_strict_eqb
          (normalize_access_rev (access_cols target) acc)
          target)
      al.

  Fixpoint access_function_checker_expr
      (rl : list AccessFunction) (e : expr) : bool :=
    match e with
    | ExConst _ => true
    | ExVar _ => true
    | ExAccess a => access_function_checker_access rl a
    | ExAdd e1 e2 =>
        access_function_checker_expr rl e1 &&
        access_function_checker_expr rl e2
    | ExSub e1 e2 =>
        access_function_checker_expr rl e1 &&
        access_function_checker_expr rl e2
    | ExMul e1 e2 => access_function_checker_expr rl e1 && access_function_checker_expr rl e2
    end.

  Definition access_function_checker (wl rl : list AccessFunction) (i : t) : bool :=
    match i with
    | SSkip => true
    | SAssign lhs rhs =>
        access_function_checker_access wl lhs &&
        access_function_checker_expr rl rhs
    end.

  Lemma access_function_checker_correct :
    forall wl rl i,
      access_function_checker wl rl i = true ->
      valid_access_function wl rl i.
  Proof.
    intros wl rl i _. unfold valid_access_function. intros.
    inversion H.
  Qed.

  Definition fallback_name (names : list varname) (n : nat) : varname :=
    nth n names (ident_to_varname (free_ident tt)).

  Fixpoint affine_expr_to_openscop (e : affine_expr) (names : list varname) : AffineExpr :=
    match e with
    | AeConst z => AfInt z
    | AeVar n => AfVar (fallback_name names n)
    | AeAdd e1 e2 => AfAdd (affine_expr_to_openscop e1 names) (affine_expr_to_openscop e2 names)
    | AeSub e1 e2 => AfMinus (affine_expr_to_openscop e1 names) (affine_expr_to_openscop e2 names)
    | AeMul z e => AfMulti (AfInt z) (affine_expr_to_openscop e names)
    end.

  Definition access_to_openscop (a : access) (names : list varname) : ArrayAccess :=
    match a with
    | AcVar id => ArrAccess (ident_to_varname id) []
    | AcArr id indices => ArrAccess (ident_to_varname id) (map (fun e => affine_expr_to_openscop e names) indices)
    end.

  Fixpoint expr_to_openscop (e : expr) (names : list varname) : ArrayExpr :=
    match e with
    | ExConst z => ArrAtom (AInt z)
    | ExVar n => ArrAtom (AVar (fallback_name names n))
    | ExAccess a => ArrAccessAtom (access_to_openscop a names)
    | ExAdd e1 e2 => ArrAdd (expr_to_openscop e1 names) (expr_to_openscop e2 names)
    | ExSub e1 e2 => ArrMinus (expr_to_openscop e1 names) (expr_to_openscop e2 names)
    | ExMul e1 e2 => ArrMulti (expr_to_openscop e1 names) (expr_to_openscop e2 names)
    end.

  Definition to_openscop (i : t) (names : list varname) : option OpenScop.ArrayStmt :=
    match i with
    | SSkip => Some ArrSkip
    | SAssign lhs rhs => Some (ArrAssign (access_to_openscop lhs names) (expr_to_openscop rhs names))
    end.

  Lemma bc_condition_implie_permutbility :
    forall i1 p1 wcs1 rcs1 st1 st2 st3 i2 p2 wcs2 rcs2,
      NonAlias st1 ->
      (instr_semantics i1 p1 wcs1 rcs1 st1 st2 /\ instr_semantics i2 p2 wcs2 rcs2 st2 st3) ->
      (Forall (fun wc2 => Forall (fun wc1 => cell_neq wc1 wc2) wcs1) wcs2) /\
      (Forall (fun rc2 => Forall (fun wc1 => cell_neq wc1 rc2) wcs1) rcs2) /\
      (Forall (fun wc2 => Forall (fun rc1 => cell_neq rc1 wc2) rcs1) wcs2) ->
      exists st2' st3',
        instr_semantics i2 p2 wcs2 rcs2 st1 st2' /\
        instr_semantics i1 p1 wcs1 rcs1 st2' st3' /\
        State.eq st3 st3'.
  Proof.
    intros. destruct H0 as [H12 _]. inversion H12.
  Qed.
End SInstr.
