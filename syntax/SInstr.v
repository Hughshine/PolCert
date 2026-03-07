Require Import List.
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import Lia.
Require Import FunctionalExtensionality.
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
  Definition t := MemCell -> Z.
  Definition non_alias (_ : t) := True.
  Definition eq (st1 st2 : t) : Prop := forall c, st1 c = st2 c.

  Lemma eq_refl : forall s, eq s s.
  Proof. intros s c. reflexivity. Qed.

  Lemma eq_sym : forall s1 s2, eq s1 s2 -> eq s2 s1.
  Proof. intros s1 s2 Heq c. symmetry. apply Heq. Qed.

  Lemma eq_trans : forall s1 s2 s3, eq s1 s2 -> eq s2 s3 -> eq s1 s3.
  Proof. intros s1 s2 s3 H12 H23 c. rewrite H12, H23. reflexivity. Qed.

  Definition dummy_state : t := fun _ => 0%Z.
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

  Definition normalize_affine (cols : nat) (aff : list Z * Z) : (list Z * Z) :=
    let '(v, c) := aff in
    (resize cols v, c).

  Definition normalize_affine_list (cols : nat) (affs : list (list Z * Z)) :=
    map (normalize_affine cols) affs.

  Definition normalize_access (cols : nat) (acc : AccessFunction) : AccessFunction :=
    let '(arrid, affs) := acc in
    (arrid, normalize_affine_list cols affs).

  Definition access_cols (acc : AccessFunction) : nat :=
    let '(_, affs) := acc in
    list_max (map (fun aff => let '(zs, _) := aff in length zs) affs).

  Definition access_cell (a : access) (p : list Z) : MemCell :=
    exact_cell (access_to_function a) p.

  Definition memcell_eq_dec (c1 c2 : MemCell) : {cell_eq c1 c2} + {~ cell_eq c1 c2}.
  Proof.
    destruct c1 as [id1 idx1], c2 as [id2 idx2].
    destruct (ident_eq_dec id1 id2) as [Hid|Hid].
    - subst. destruct (veq_eq_dec idx1 idx2) as [Hidx|Hidx].
      + left. split; auto.
      + right. intros [Heq Hveq]. contradiction.
    - right. intros [Heq _]. contradiction.
  Defined.

  Definition state_write (st : State.t) (cell : MemCell) (v : Z) : State.t :=
    fun c => if memcell_eq_dec c cell then v else st c.

  Fixpoint eval_expr (e : expr) (p : list Z) (st : State.t) : Z :=
    match e with
    | ExConst z => z
    | ExVar n => nth n p 0%Z
    | ExAccess a => st (access_cell a p)
    | ExAdd e1 e2 => (eval_expr e1 p st + eval_expr e2 p st)%Z
    | ExSub e1 e2 => (eval_expr e1 p st - eval_expr e2 p st)%Z
    | ExMul e1 e2 => (eval_expr e1 p st * eval_expr e2 p st)%Z
    end.

  Fixpoint read_cells_expr (e : expr) (p : list Z) : list MemCell :=
    match e with
    | ExConst _ => []
    | ExVar _ => []
    | ExAccess a => [access_cell a p]
    | ExAdd e1 e2 => read_cells_expr e1 p ++ read_cells_expr e2 p
    | ExSub e1 e2 => read_cells_expr e1 p ++ read_cells_expr e2 p
    | ExMul e1 e2 => read_cells_expr e1 p ++ read_cells_expr e2 p
    end.

  Inductive sema : t -> list Z -> list MemCell -> list MemCell -> State.t -> State.t -> Prop :=
  | SemaSkip : forall p st1 st2,
      State.eq st2 st1 ->
      sema SSkip p [] [] st1 st2
  | SemaAssign : forall lhs rhs p st1 st2 cell val,
      cell = access_cell lhs p ->
      val = eval_expr rhs p st1 ->
      State.eq st2 (state_write st1 cell val) ->
      sema (SAssign lhs rhs) p [cell] (read_cells_expr rhs p) st1 st2.

  Definition instr_semantics := sema.

  Lemma cell_eq_refl : forall c, cell_eq c c.
  Proof. intros [id idx]; split; auto; apply veq_refl. Qed.

  Lemma cell_eq_trans : forall c1 c2 c3, cell_eq c1 c2 -> cell_eq c2 c3 -> cell_eq c1 c3.
  Proof.
    intros [id1 idx1] [id2 idx2] [id3 idx3] [H12id H12idx] [H23id H23idx].
    simpl in *. subst. split; [reflexivity|].
    eapply veq_transitive; eauto.
  Qed.

  Lemma state_write_same : forall st cell v,
    state_write st cell v cell = v.
  Proof.
    intros. unfold state_write.
    destruct (memcell_eq_dec cell cell); [reflexivity|exfalso; apply n; apply cell_eq_refl].
  Qed.

  Lemma state_write_other : forall st cell1 cell2 v,
    cell_neq cell2 cell1 ->
    state_write st cell1 v cell2 = st cell2.
  Proof.
    intros. unfold state_write.
    destruct (memcell_eq_dec cell2 cell1) as [Heq|Hneq]; [|reflexivity].
    exfalso. destruct H as [Hid|Hidx]; destruct Heq as [Heqid Heqidx].
    - exact (Hid Heqid).
    - exact (Hidx Heqidx).
  Qed.

  Lemma state_write_proper : forall st1 st2 cell v,
    State.eq st1 st2 ->
    State.eq (state_write st1 cell v) (state_write st2 cell v).
  Proof.
    intros st1 st2 cell v Heq c. unfold state_write.
    destruct (memcell_eq_dec c cell); auto.
  Qed.

  Lemma state_write_value_eq : forall st cell v1 v2,
    v1 = v2 ->
    State.eq (state_write st cell v1) (state_write st cell v2).
  Proof.
    intros st cell v1 v2 Heq c. unfold state_write.
    destruct (memcell_eq_dec c cell); subst; reflexivity.
  Qed.

  Lemma state_write_commute : forall st cell1 cell2 v1 v2,
    cell_neq cell1 cell2 ->
    State.eq (state_write (state_write st cell1 v1) cell2 v2)
             (state_write (state_write st cell2 v2) cell1 v1).
  Proof.
    intros st cell1 cell2 v1 v2 Hneq c.
    unfold state_write.
    destruct (memcell_eq_dec c cell2) as [Hc2|Hc2].
    - destruct (memcell_eq_dec c cell1) as [Hc1|Hc1].
      + exfalso.
        destruct Hneq as [Hid|Hidx].
        * destruct Hc1 as [Hid1 _]. destruct Hc2 as [Hid2 _].
          apply Hid. transitivity (arr_id c); auto.
        * destruct Hc1 as [_ Hidx1]. destruct Hc2 as [_ Hidx2].
          apply Hidx. eapply veq_transitive; [apply veq_sym; exact Hidx1|exact Hidx2].
      + reflexivity.
    - destruct (memcell_eq_dec c cell1) as [Hc1|Hc1]; reflexivity.
  Qed.

  Lemma eval_expr_state_eq : forall e p st1 st2,
    State.eq st1 st2 ->
    eval_expr e p st1 = eval_expr e p st2.
  Proof.
    induction e; intros; simpl; try reflexivity.
    - apply H.
    - rewrite (IHe1 p st1 st2 H). rewrite (IHe2 p st1 st2 H). reflexivity.
    - rewrite (IHe1 p st1 st2 H). rewrite (IHe2 p st1 st2 H). reflexivity.
    - rewrite (IHe1 p st1 st2 H). rewrite (IHe2 p st1 st2 H). reflexivity.
  Qed.

  Lemma valid_access_cells_nil : forall p al,
    valid_access_cells p [] al.
  Proof.
    unfold valid_access_cells. intros. contradiction.
  Qed.

  Lemma valid_access_cells_app : forall p c1 c2 al,
    valid_access_cells p c1 al ->
    valid_access_cells p c2 al ->
    valid_access_cells p (c1 ++ c2) al.
  Proof.
    unfold valid_access_cells. intros p c1 c2 al H1 H2 c Hin.
    apply in_app_or in Hin. destruct Hin; auto.
  Qed.

  Lemma listzzs_eqb_affine_product_eq :
    forall affs1 affs2 p,
      listzzs_eqb affs1 affs2 = true ->
      affine_product affs1 p = affine_product affs2 p.
  Proof.
    induction affs1 as [|[v1 c1] affs1 IH]; intros [|[v2 c2] affs2] p Heq; simpl in *; try discriminate; auto.
    apply andb_true_iff in Heq as [Hlen Hfor].
    apply Nat.eqb_eq in Hlen. inversion Hlen. subst.
    apply andb_true_iff in Hfor as [Hhead Htail].
    apply andb_true_iff in Hhead as [Hv Hc].
    apply Z.eqb_eq in Hc. simpl. f_equal.
    - rewrite Hc. f_equal. apply dot_product_eq_compat_left. exact Hv.
    - apply IH. apply andb_true_iff. split.
      + apply Nat.eqb_eq. assumption.
      + exact Htail.
  Qed.

  Lemma access_eqb_cell_eq : forall a1 a2 p,
    access_eqb a1 a2 = true ->
    cell_eq (exact_cell a2 p) (exact_cell a1 p).
  Proof.
    intros [id1 affs1] [id2 affs2] p Heq. simpl in *.
    apply andb_true_iff in Heq as [Hid Haff].
    apply Pos.eqb_eq in Hid. split; auto.
    pose proof (listzzs_eqb_affine_product_eq affs1 affs2 p Haff) as Heval.
    rewrite <- Heval. apply veq_refl.
  Qed.

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

  Definition access_function_checker_access
      (al : list AccessFunction) (a : access) : bool :=
    existsb (fun target => access_eqb (access_to_function a) target) al.

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

  Lemma access_function_checker_access_correct :
    forall al a p,
      access_function_checker_access al a = true ->
      valid_access_cells p [access_cell a p] al.
  Proof.
    intros al a p Hchk. unfold access_function_checker_access in Hchk.
    unfold valid_access_cells. intros c Hin. simpl in Hin. destruct Hin as [Heq|[]]. subst c.
    apply existsb_exists in Hchk. destruct Hchk as [target [Hin Hacc]].
    exists target. split; auto. apply access_eqb_cell_eq. exact Hacc.
  Qed.

  Lemma access_function_checker_expr_correct :
    forall rl e p,
      access_function_checker_expr rl e = true ->
      valid_access_cells p (read_cells_expr e p) rl.
  Proof.
    induction e; intros p Hchk; simpl in *.
    - apply valid_access_cells_nil.
    - apply valid_access_cells_nil.
    - apply access_function_checker_access_correct; exact Hchk.
    - apply andb_true_iff in Hchk as [H1 H2].
      eapply valid_access_cells_app; [apply IHe1|apply IHe2]; eauto.
    - apply andb_true_iff in Hchk as [H1 H2].
      eapply valid_access_cells_app; [apply IHe1|apply IHe2]; eauto.
    - apply andb_true_iff in Hchk as [H1 H2].
      eapply valid_access_cells_app; [apply IHe1|apply IHe2]; eauto.
  Qed.

  Lemma access_function_checker_correct :
    forall wl rl i,
      access_function_checker wl rl i = true ->
      valid_access_function wl rl i.
  Proof.
    intros wl rl i Hchk p st st' wcells rcells Hsem.
    inversion Hsem; subst; simpl in *.
    - split; apply valid_access_cells_nil.
    - apply andb_true_iff in Hchk as [Hwl Hrl].
      split.
      + apply access_function_checker_access_correct. exact Hwl.
      + apply access_function_checker_expr_correct. exact Hrl.
  Qed.

  Lemma eval_expr_write_irrelevant : forall e p st cell val,
    Forall (fun rc => cell_neq rc cell) (read_cells_expr e p) ->
    eval_expr e p (state_write st cell val) = eval_expr e p st.
  Proof.
    induction e; intros p st cell val Hneq; simpl in *; auto.
    - inversion Hneq as [|? ? Hc _].
      rewrite state_write_other; auto.
    - apply Forall_app in Hneq as [H1 H2].
      rewrite IHe1 by exact H1. rewrite IHe2 by exact H2. reflexivity.
    - apply Forall_app in Hneq as [H1 H2].
      rewrite IHe1 by exact H1. rewrite IHe2 by exact H2. reflexivity.
    - apply Forall_app in Hneq as [H1 H2].
      rewrite IHe1 by exact H1. rewrite IHe2 by exact H2. reflexivity.
  Qed.

  Lemma instr_semantics_stable_under_state_eq :
    forall i p wcs rcs st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      instr_semantics i p wcs rcs st1 st2 ->
      instr_semantics i p wcs rcs st1' st2'.
  Proof.
    intros i p wcs rcs st1 st2 st1' st2' Heq1 Heq2 Hsem.
    destruct Hsem as
        [p0 st10 st20 Heqskip
        | lhs rhs p0 st10 st20 cell val Hcell Hval Hstate].
    - econstructor.
      eapply State.eq_trans.
      + apply State.eq_sym. exact Heq2.
      + eapply State.eq_trans; [exact Heqskip|exact Heq1].
    - subst cell val. econstructor.
      + reflexivity.
      + symmetry. apply eval_expr_state_eq. apply State.eq_sym. exact Heq1.
      + eapply State.eq_trans.
        * apply State.eq_sym. exact Heq2.
        * eapply State.eq_trans.
          -- exact Hstate.
          -- apply state_write_proper. exact Heq1.
  Qed.

  Lemma sema_prsv_nonalias :
    forall i p wcs rcs st1 st2,
      NonAlias st1 ->
      instr_semantics i p wcs rcs st1 st2 ->
      NonAlias st2.
  Proof. intros; exact I. Qed.

  Definition is_iterator_varname (name : varname) : bool :=
    match name with
    | String "$"%char (String "i"%char _) => true
    | _ => false
    end.

  (* Syntax instruction slots are laid out directly in PolyLang point order:
     params first, then outer-to-inner iterators. OpenScop names arrive in the
     same order, so no reordering is needed here. *)
  Definition syntax_slot_names (names : list varname) : list varname :=
    names.

  Definition fallback_name (names : list varname) (n : nat) : varname :=
    nth n (syntax_slot_names names) (ident_to_varname (free_ident tt)).

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
    intros i1 p1 wcs1 rcs1 st1 st2 st3 i2 p2 wcs2 rcs2 _ [Hsem1 Hsem2] [Hww [Hwr Hrw]].
    destruct Hsem1 as
        [p1' st10 st20 Heq12
        | lhs1 rhs1 p1' st10 st20 cell1 val1 Hcell1 Hval1 Hstate1];
    destruct Hsem2 as
        [p2' st21 st30 Heq23
        | lhs2 rhs2 p2' st21 st30 cell2 val2 Hcell2 Hval2 Hstate2].
    - exists st10, st10.
      split.
      + constructor. apply State.eq_refl.
      + split.
        * constructor. apply State.eq_refl.
        * eapply State.eq_trans; eauto.
    - exists st30, st30.
      split.
      + eapply SemaAssign with (cell := cell2) (val := val2).
        * exact Hcell2.
        * rewrite Hval2. apply eval_expr_state_eq. exact Heq12.
        * eapply State.eq_trans; [exact Hstate2|].
          apply state_write_proper. exact Heq12.
      + split.
        * constructor. apply State.eq_refl.
        * apply State.eq_refl.
    - exists st10, st21.
      split.
      + constructor. apply State.eq_refl.
      + split.
        * eapply SemaAssign with (cell := cell1) (val := val1); eauto.
        * exact Heq23.
    - assert (Hneq12 : cell_neq cell1 cell2).
      {
        inversion Hww as [| ? ? Hcell _]; subst.
        inversion Hcell as [| ? ? Hneq _]; subst.
        exact Hneq.
      }
      assert (Hrhs2 : Forall (fun rc => cell_neq rc cell1) (read_cells_expr rhs2 p2')).
      {
        induction Hwr as [|rc rcs Hhead Htail IH]; constructor.
        - inversion Hhead as [| ? ? Hneq _]; subst.
          rewrite cell_neq_symm. exact Hneq.
        - exact IH.
      }
      assert (Hrhs1 : Forall (fun rc => cell_neq rc cell2) (read_cells_expr rhs1 p1')).
      {
        inversion Hrw as [| ? ? Hhead _]; subst.
        exact Hhead.
      }
      exists (state_write st10 cell2 val2),
             (state_write (state_write st10 cell2 val2) cell1 val1).
      split.
      + eapply SemaAssign with (cell := cell2) (val := val2).
        * exact Hcell2.
        * rewrite Hval2.
          rewrite (eval_expr_state_eq rhs2 p2' st21 (state_write st10 cell1 val1) Hstate1).
          apply eval_expr_write_irrelevant. exact Hrhs2.
        * apply State.eq_refl.
      + split.
        * eapply SemaAssign with (cell := cell1) (val := val1).
          -- exact Hcell1.
          -- rewrite Hval1.
             symmetry. apply eval_expr_write_irrelevant. exact Hrhs1.
          -- apply State.eq_refl.
        * eapply State.eq_trans.
          -- exact Hstate2.
          -- eapply State.eq_trans.
             ++ apply state_write_proper. exact Hstate1.
             ++ apply state_write_commute. exact Hneq12.
  Qed.
End SInstr.
