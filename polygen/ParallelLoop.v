Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Psatz.
Require Import Result.
Import ListNotations.

Require Import InstrTy.
Require Import Loop.
Require Import Misc.
Require Import Linalg.
Require Import LibTactics.

Open Scope Z_scope.
Open Scope list_scope.

Module ParallelLoop (IInstr : INSTR).

Module Instr := IInstr.
Module BaseLoop := Loop IInstr.
Module ILSema := BaseLoop.ILSema.
Module Ty := IInstr.Ty.

Definition ident := IInstr.ident.
Definition instr := IInstr.t.
Definition mem := IInstr.State.t.
Definition expr := BaseLoop.expr.
Definition test := BaseLoop.test.
Definition InstrPoint := ILSema.InstrPoint.

Inductive loop_mode :=
| SeqMode
| ParMode
| VecMode.

Inductive stmt :=
| Loop : loop_mode -> option nat -> expr -> expr -> stmt -> stmt
| Instr : instr -> list expr -> stmt
| Seq : stmt_list -> stmt
| Guard : test -> stmt -> stmt
with stmt_list :=
| SNil : stmt_list
| SCons : stmt -> stmt_list -> stmt_list.

Definition t := (stmt * list ident * list (ident * Ty.t))%type.

Fixpoint erase_stmt (s : stmt) : BaseLoop.stmt :=
  match s with
  | Loop _ _ lb ub body => BaseLoop.Loop lb ub (erase_stmt body)
  | Instr i es => BaseLoop.Instr i es
  | Seq ss => BaseLoop.Seq (erase_stmt_list ss)
  | Guard tst body => BaseLoop.Guard tst (erase_stmt body)
  end
with erase_stmt_list (ss : stmt_list) : BaseLoop.stmt_list :=
  match ss with
  | SNil => BaseLoop.SNil
  | SCons s ss' => BaseLoop.SCons (erase_stmt s) (erase_stmt_list ss')
  end.

Definition erase_parallel (p : t) : BaseLoop.t :=
  let '(s, ctxt, vars) := p in
  (erase_stmt s, ctxt, vars).

Fixpoint parallelize_dim_stmt (d : nat) (s : stmt) : stmt :=
  match s with
  | Loop SeqMode (Some d') lb ub body =>
      Loop (if Nat.eqb d d' then ParMode else SeqMode)
           (Some d')
           lb
           ub
           (parallelize_dim_stmt d body)
  | Loop mode od lb ub body =>
      Loop mode od lb ub (parallelize_dim_stmt d body)
  | Instr i es => Instr i es
  | Seq ss => Seq (parallelize_dim_stmts d ss)
  | Guard tst body => Guard tst (parallelize_dim_stmt d body)
  end
with parallelize_dim_stmts (d : nat) (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' => SCons (parallelize_dim_stmt d s) (parallelize_dim_stmts d ss')
  end.

Definition parallelize_dim (d : nat) (p : t) : t :=
  let '(s, ctxt, vars) := p in
  (parallelize_dim_stmt d s, ctxt, vars).

Fixpoint vectorize_dim_stmt (d : nat) (s : stmt) : stmt :=
  match s with
  | Loop SeqMode (Some d') lb ub body =>
      Loop (if Nat.eqb d d' then VecMode else SeqMode)
           (Some d')
           lb
           ub
           (vectorize_dim_stmt d body)
  | Loop mode od lb ub body =>
      Loop mode od lb ub (vectorize_dim_stmt d body)
  | Instr i es => Instr i es
  | Seq ss => Seq (vectorize_dim_stmts d ss)
  | Guard tst body => Guard tst (vectorize_dim_stmt d body)
  end
with vectorize_dim_stmts (d : nat) (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' => SCons (vectorize_dim_stmt d s) (vectorize_dim_stmts d ss')
  end.

Definition vectorize_dim (d : nat) (p : t) : t :=
  let '(s, ctxt, vars) := p in
  (vectorize_dim_stmt d s, ctxt, vars).

Fixpoint has_loopb_stmt (s : stmt) : bool
with has_loopb_stmts (ss : stmt_list) : bool.
Proof.
  - destruct s.
    + exact true.
    + exact false.
    + exact (has_loopb_stmts s).
    + exact (has_loopb_stmt s).
  - destruct ss.
    + exact false.
    + exact (has_loopb_stmt s || has_loopb_stmts ss).
Defined.

Fixpoint has_vector_modeb_stmt (s : stmt) : bool
with has_vector_modeb_stmts (ss : stmt_list) : bool.
Proof.
  - destruct s.
    + destruct l.
      * exact (has_vector_modeb_stmt s).
      * exact (has_vector_modeb_stmt s).
      * exact true.
    + exact false.
    + exact (has_vector_modeb_stmts s).
    + exact (has_vector_modeb_stmt s).
  - destruct ss.
    + exact false.
    + exact (has_vector_modeb_stmt s || has_vector_modeb_stmts ss).
Defined.

Fixpoint vector_modes_innermostb_stmt (s : stmt) : bool
with vector_modes_innermostb_stmts (ss : stmt_list) : bool.
Proof.
  - destruct s.
    + destruct l.
      * exact (vector_modes_innermostb_stmt s).
      * exact (vector_modes_innermostb_stmt s).
      * exact (negb (has_loopb_stmt s)).
    + exact true.
    + exact (vector_modes_innermostb_stmts s).
    + exact (vector_modes_innermostb_stmt s).
  - destruct ss.
    + exact true.
    + exact (vector_modes_innermostb_stmt s && vector_modes_innermostb_stmts ss).
Defined.

(** A vector annotation is useful only when at least one loop is annotated, and
    it is backend-safe only when every annotated loop is structurally
    innermost. *)
Definition vector_annotations_innermostb (p : t) : bool :=
  let '(s, _, _) := p in
  vector_modes_innermostb_stmt s && has_vector_modeb_stmt s.

Fixpoint of_loop_stmt (s : BaseLoop.stmt) : stmt :=
  match s with
  | BaseLoop.Loop lb ub body => Loop SeqMode None lb ub (of_loop_stmt body)
  | BaseLoop.Instr i es => Instr i es
  | BaseLoop.Seq ss => Seq (of_loop_stmt_list ss)
  | BaseLoop.Guard tst body => Guard tst (of_loop_stmt body)
  end
with of_loop_stmt_list (ss : BaseLoop.stmt_list) : stmt_list :=
  match ss with
  | BaseLoop.SNil => SNil
  | BaseLoop.SCons s ss' => SCons (of_loop_stmt s) (of_loop_stmt_list ss')
  end.

Definition of_loop (p : BaseLoop.t) : t :=
  let '(s, ctxt, vars) := p in
  (of_loop_stmt s, ctxt, vars).

Fixpoint all_origin_none_stmt (s : stmt) : Prop :=
  match s with
  | Loop _ od _ _ body => od = None /\ all_origin_none_stmt body
  | Instr _ _ => True
  | Seq ss => all_origin_none_stmts ss
  | Guard _ body => all_origin_none_stmt body
  end
with all_origin_none_stmts (ss : stmt_list) : Prop :=
  match ss with
  | SNil => True
  | SCons s ss' => all_origin_none_stmt s /\ all_origin_none_stmts ss'
  end.

Definition all_origin_none (p : t) : Prop :=
  let '(s, _, _) := p in all_origin_none_stmt s.

Inductive seq_trace : stmt -> list Z -> list InstrPoint -> Prop :=
| STInstr : forall i es env,
    seq_trace (Instr i es) env [BaseLoop.mk_instr_point i es env]
| STSeqStmt : forall env sts tr,
    seq_traces sts env tr ->
    seq_trace (Seq sts) env tr
| STGuardTrue : forall env tst st tr,
    BaseLoop.eval_test env tst = true ->
    seq_trace st env tr ->
    seq_trace (Guard tst st) env tr
| STGuardFalse : forall env tst st,
    BaseLoop.eval_test env tst = false ->
    seq_trace (Guard tst st) env []
| STLoop : forall mode od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    seq_trace (Loop mode od lb ub body) env tr
with seq_traces : stmt_list -> list Z -> list InstrPoint -> Prop :=
| STTracesNil : forall env,
    seq_traces SNil env []
| STTracesCons : forall env st sts tr1 tr2,
    seq_trace st env tr1 ->
    seq_traces sts env tr2 ->
    seq_traces (SCons st sts) env (tr1 ++ tr2).

Inductive interleave_family : list (list InstrPoint) -> list InstrPoint -> Prop :=
| IF_nil :
    interleave_family [] []
| IF_skip_nil : forall trs out,
    interleave_family trs out ->
    interleave_family ([] :: trs) out
| IF_take : forall pre x xs post out,
    interleave_family (pre ++ xs :: post) out ->
    interleave_family (pre ++ (x :: xs) :: post) (x :: out).

Definition family_ordered_permutable (trs : list (list InstrPoint)) : Prop :=
  forall pre1 tr1 pre2 tr2 post ip1 ip2,
    trs = pre1 ++ tr1 :: pre2 ++ tr2 :: post ->
    In ip1 tr1 ->
    In ip2 tr2 ->
    ILSema.Permutable ip1 ip2.

Lemma family_ordered_permutable_tail :
  forall tr trs,
    family_ordered_permutable (tr :: trs) ->
    family_ordered_permutable trs.
Proof.
  intros tr trs Hordered pre1 tr1 pre2 tr2 post ip1 ip2 Hshape Hin1 Hin2.
  eapply Hordered with
      (pre1 := tr :: pre1) (tr1 := tr1) (pre2 := pre2)
      (tr2 := tr2) (post := post); eauto.
  simpl. now rewrite Hshape.
Qed.

Fixpoint family_ordered_permutable_rec
  (trs : list (list InstrPoint)) : Prop :=
  match trs with
  | [] => True
  | tr :: trs' =>
      (forall ip1 ip2,
          In ip1 tr ->
          In ip2 (concat trs') ->
          ILSema.Permutable ip1 ip2) /\
      family_ordered_permutable_rec trs'
  end.

Lemma family_ordered_permutable_rec_of_ordered :
  forall trs,
    family_ordered_permutable trs ->
    family_ordered_permutable_rec trs.
Proof.
  induction trs as [|tr trs IH]; intros Hordered; simpl.
  - exact I.
  - split.
    + intros ip1 ip2 Hin1 Hin2.
      apply in_concat in Hin2.
      destruct Hin2 as [tr2 [Htr2 Hin2]].
      apply in_split in Htr2.
      destruct Htr2 as [pre2 [post Hshape]].
      eapply Hordered with
          (pre1 := []) (tr1 := tr) (pre2 := pre2)
          (tr2 := tr2) (post := post); eauto.
      simpl. now rewrite Hshape.
    + apply IH.
      eapply family_ordered_permutable_tail; eauto.
Qed.

Lemma family_ordered_permutable_ordered_of_rec :
  forall trs,
    family_ordered_permutable_rec trs ->
    family_ordered_permutable trs.
Proof.
  induction trs as [|tr trs IH];
    intros Hrec pre1 tr1 pre2 tr2 post ip1 ip2 Hshape Hin1 Hin2.
  - destruct pre1; discriminate.
  - simpl in Hrec.
    destruct Hrec as [Hhead Htail].
    destruct pre1 as [|tr0 pre1].
    + simpl in Hshape.
      inversion Hshape; subst tr1.
      apply Hhead with (ip1 := ip1) (ip2 := ip2); auto.
      apply in_concat.
      exists tr2.
      split; auto.
      rewrite H1.
      apply in_or_app.
      right. simpl. auto.
    + simpl in Hshape.
      inversion Hshape; subst tr0.
      eapply IH; eauto.
Qed.

Lemma concat_pop_in :
  forall (pre : list (list InstrPoint)) (x : InstrPoint) xs post ip,
    In ip (concat (pre ++ xs :: post)) ->
    In ip (concat (pre ++ (x :: xs) :: post)).
Proof.
  induction pre as [|tr pre IH]; intros x xs post ip Hin; simpl in *.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + right. apply in_or_app. left. exact Hin.
    + right. apply in_or_app. right. exact Hin.
  - apply in_app_or in Hin.
    apply in_or_app.
    destruct Hin as [Hin | Hin].
    + left. exact Hin.
    + right. eapply IH; eauto.
Qed.

Lemma family_ordered_permutable_rec_pop :
  forall pre x xs post,
    family_ordered_permutable_rec (pre ++ (x :: xs) :: post) ->
    family_ordered_permutable_rec (pre ++ xs :: post).
Proof.
  induction pre as [|tr pre IH]; intros x xs post Hordered; simpl in *.
  - destruct Hordered as [Hhead Htail].
    split.
    + intros ip1 ip2 Hin1 Hin2.
      eapply Hhead.
      * right. exact Hin1.
      * exact Hin2.
    + exact Htail.
  - destruct Hordered as [Hhead Htail].
    split.
    + intros ip1 ip2 Hin1 Hin2.
      eapply Hhead.
      * exact Hin1.
      * eapply concat_pop_in; eauto.
    + eapply IH; eauto.
Qed.

Lemma family_ordered_permutable_pop :
  forall pre x xs post,
    family_ordered_permutable (pre ++ (x :: xs) :: post) ->
    family_ordered_permutable (pre ++ xs :: post).
Proof.
  intros pre x xs post Hordered.
  apply family_ordered_permutable_ordered_of_rec.
  eapply family_ordered_permutable_rec_pop with (x := x).
  apply family_ordered_permutable_rec_of_ordered.
  exact Hordered.
Qed.

Lemma family_ordered_permutable_before :
  forall pre x xs post,
    family_ordered_permutable (pre ++ (x :: xs) :: post) ->
    forall y,
      In y (concat pre) ->
      ILSema.Permutable y x.
Proof.
  induction pre as [|tr pre IH]; intros x xs post Hordered y Hin; simpl in Hin.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + eapply (Hordered [] tr pre (x :: xs) post y x); simpl; eauto.
    + eapply IH; eauto.
      eapply family_ordered_permutable_tail; eauto.
Qed.

Inductive interleave_safe : list (list InstrPoint) -> list InstrPoint -> Prop :=
| IS_nil :
    interleave_safe [] []
| IS_skip_nil : forall trs out,
    interleave_safe trs out ->
    interleave_safe ([] :: trs) out
| IS_take : forall pre x xs post out,
    (forall y, In y (concat pre) -> ILSema.Permutable y x) ->
    interleave_safe (pre ++ xs :: post) out ->
    interleave_safe (pre ++ (x :: xs) :: post) (x :: out).

Theorem family_ordered_interleave_safe :
  forall trs out,
    family_ordered_permutable trs ->
    interleave_family trs out ->
    interleave_safe trs out.
Proof.
  intros trs out Hordered Hinter.
  revert Hordered.
  induction Hinter; intros Hordered.
  - constructor.
  - constructor.
    apply IHHinter.
    eapply family_ordered_permutable_tail; eauto.
  - econstructor.
    + eapply family_ordered_permutable_before; eauto.
    + apply IHHinter.
      eapply family_ordered_permutable_pop; eauto.
Qed.

Inductive par_trace : stmt -> list Z -> list InstrPoint -> Prop :=
| PTInstr : forall i es env,
    par_trace (Instr i es) env [BaseLoop.mk_instr_point i es env]
| PTSeqStmt : forall env sts tr,
    par_traces sts env tr ->
    par_trace (Seq sts) env tr
| PTGuardTrue : forall env tst st tr,
    BaseLoop.eval_test env tst = true ->
    par_trace st env tr ->
    par_trace (Guard tst st) env tr
| PTGuardFalse : forall env tst st,
    BaseLoop.eval_test env tst = false ->
    par_trace (Guard tst st) env []
| PTLoopSeq : forall od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    par_trace (Loop SeqMode od lb ub body) env tr
| PTLoopVec : forall od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    par_trace (Loop VecMode od lb ub body) env tr
| PTLoopPar : forall d lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    interleave_family trs tr ->
    par_trace (Loop ParMode (Some d) lb ub body) env tr
with par_traces : stmt_list -> list Z -> list InstrPoint -> Prop :=
| PTTracesNil : forall env,
    par_traces SNil env []
| PTTracesCons : forall env st sts tr1 tr2,
    par_trace st env tr1 ->
    par_traces sts env tr2 ->
    par_traces (SCons st sts) env (tr1 ++ tr2).

(** A derivation-specific ordering certificate for a parallel trace.  The raw
    trace relation above continues to accept every interleaving.  This companion
    records exactly the recursive ordering facts needed to refine one concrete
    trace to sequential execution.  The raw [Forall2] premises make forgetting
    the certificate independent of the nested proof structure. *)
Inductive ordered_par_trace : stmt -> list Z -> list InstrPoint -> Prop :=
| OPTInstr : forall i es env,
    ordered_par_trace (Instr i es) env [BaseLoop.mk_instr_point i es env]
| OPTSeqStmt : forall env sts tr,
    ordered_par_traces sts env tr ->
    ordered_par_trace (Seq sts) env tr
| OPTGuardTrue : forall env tst st tr,
    BaseLoop.eval_test env tst = true ->
    ordered_par_trace st env tr ->
    ordered_par_trace (Guard tst st) env tr
| OPTGuardFalse : forall env tst st,
    BaseLoop.eval_test env tst = false ->
    ordered_par_trace (Guard tst st) env []
| OPTLoopSeq : forall od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    Forall2 (fun z tri => ordered_par_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    ordered_par_trace (Loop SeqMode od lb ub body) env tr
| OPTLoopVec : forall od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    Forall2 (fun z tri => ordered_par_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    ordered_par_trace (Loop VecMode od lb ub body) env tr
| OPTLoopPar : forall d lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    Forall2 (fun z tri => ordered_par_trace body (z :: env) tri) zs trs ->
    family_ordered_permutable trs ->
    interleave_family trs tr ->
    ordered_par_trace (Loop ParMode (Some d) lb ub body) env tr
with ordered_par_traces : stmt_list -> list Z -> list InstrPoint -> Prop :=
| OPTTracesNil : forall env,
    ordered_par_traces SNil env []
| OPTTracesCons : forall env st sts tr1 tr2,
    ordered_par_trace st env tr1 ->
    ordered_par_traces sts env tr2 ->
    ordered_par_traces (SCons st sts) env (tr1 ++ tr2).

Lemma ordered_par_trace_forget :
  forall s env tr,
    ordered_par_trace s env tr ->
    par_trace s env tr
with ordered_par_traces_forget :
  forall ss env tr,
    ordered_par_traces ss env tr ->
    par_traces ss env tr.
Proof.
  - intros s env tr Hordered.
    destruct Hordered.
    + constructor.
    + constructor. eapply ordered_par_traces_forget; eauto.
    + eapply PTGuardTrue; eauto.
    + eapply PTGuardFalse; eauto.
    + eapply PTLoopSeq; eauto.
    + eapply PTLoopVec; eauto.
    + eapply PTLoopPar; eauto.
  - intros ss env tr Hordered.
    destruct Hordered.
    + constructor.
    + econstructor.
      * eapply ordered_par_trace_forget; eauto.
      * eapply ordered_par_traces_forget; eauto.
Qed.

Fixpoint parallel_families_ordered_stmt (s : stmt) : Prop :=
  match s with
  | Loop ParMode (Some _) lb ub body =>
      parallel_families_ordered_stmt body /\
      (forall env zs trs,
          zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
          Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
          family_ordered_permutable trs)
  | Loop _ _ _ _ body => parallel_families_ordered_stmt body
  | Instr _ _ => True
  | Seq ss => parallel_families_ordered_stmts ss
  | Guard _ body => parallel_families_ordered_stmt body
  end
with parallel_families_ordered_stmts (ss : stmt_list) : Prop :=
  match ss with
  | SNil => True
  | SCons s ss' =>
      parallel_families_ordered_stmt s /\
      parallel_families_ordered_stmts ss'
  end.

Definition parallel_families_ordered (p : t) : Prop :=
  let '(s, _, _) := p in parallel_families_ordered_stmt s.

Definition loop_semantics (s : stmt) (env : list Z) (mem1 mem2 : mem) : Prop :=
  exists tr,
    par_trace s env tr /\
    ILSema.instr_point_list_semantics tr mem1 mem2.

Inductive semantics : t -> mem -> mem -> Prop :=
| PLSemaIntro : forall loop_ext loop ctxt vars env mem1 mem2,
    loop_ext = (loop, ctxt, vars) ->
    IInstr.Compat vars mem1 ->
    IInstr.NonAlias mem1 ->
    IInstr.InitEnv ctxt (rev env) mem1 ->
    loop_semantics loop env mem1 mem2 ->
    semantics loop_ext mem1 mem2.

(** The raw semantics remains the executable meaning of a parallel program.
    [ordered_semantics] is a proof companion for a particular execution; it is
    constructed only after the chosen trace has been justified. *)
Definition ordered_loop_semantics
    (s : stmt) (env : list Z) (mem1 mem2 : mem) : Prop :=
  exists tr,
    ordered_par_trace s env tr /\
    ILSema.instr_point_list_semantics tr mem1 mem2.

Inductive ordered_semantics : t -> mem -> mem -> Prop :=
| OPLSemaIntro : forall loop_ext loop ctxt vars env mem1 mem2,
    loop_ext = (loop, ctxt, vars) ->
    IInstr.Compat vars mem1 ->
    IInstr.NonAlias mem1 ->
    IInstr.InitEnv ctxt (rev env) mem1 ->
    ordered_loop_semantics loop env mem1 mem2 ->
    ordered_semantics loop_ext mem1 mem2.

Lemma ordered_loop_semantics_forget :
  forall s env mem1 mem2,
    ordered_loop_semantics s env mem1 mem2 ->
    loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2 [tr [Hordered Hsem]].
  exists tr. split; auto.
  eapply ordered_par_trace_forget; eauto.
Qed.

Lemma ordered_semantics_forget :
  forall p mem1 mem2,
    ordered_semantics p mem1 mem2 ->
    semantics p mem1 mem2.
Proof.
  intros p mem1 mem2 Hordered.
  inversion Hordered; subst.
  econstructor; eauto.
  eapply ordered_loop_semantics_forget; eauto.
Qed.

(** Compatibility bridge for clients that already establish the stronger
    program-wide invariant.  New checked code-generation paths can instead
    construct [ordered_par_trace] directly for the execution at hand. *)
Lemma ordered_par_trace_forall2_of_global :
  forall body env,
    (forall env' tr,
        parallel_families_ordered_stmt body ->
        par_trace body env' tr ->
        ordered_par_trace body env' tr) ->
    parallel_families_ordered_stmt body ->
    forall zs trs,
      Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
      Forall2 (fun z tri => ordered_par_trace body (z :: env) tri) zs trs.
Proof.
  intros body env Hbody Hglobal zs trs Hfor.
  induction Hfor as [|z tr zs' trs' Htrace Hfor IH].
  - apply Forall2_nil.
  - eapply Forall2_cons.
    + eapply Hbody; eauto.
    + exact IH.
Qed.

Lemma ordered_par_trace_of_global :
  forall s env tr,
    parallel_families_ordered_stmt s ->
    par_trace s env tr ->
    ordered_par_trace s env tr
with ordered_par_traces_of_global :
  forall ss env tr,
    parallel_families_ordered_stmts ss ->
    par_traces ss env tr ->
    ordered_par_traces ss env tr.
Proof.
  - intros s.
    induction s as [mode od lb ub body IHbody|i es|ss _|t body IHbody];
      intros env tr Hglobal Htrace.
    + inversion Htrace as
          [| | | |od' lb' ub' body' env' zs trs tr' Hzs Hfor Hconcat
           |od' lb' ub' body' env' zs trs tr' Hzs Hfor Hconcat
           |d lb' ub' body' env' zs trs tr' Hzs Hfor Hinter];
        subst.
      * simpl in Hglobal.
        lazymatch goal with
        | Hfor0 :
            Forall2 (fun z tri => par_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
            pose proof
              (ordered_par_trace_forall2_of_global
                 body env IHbody Hglobal zs0 trs0 Hfor0) as Hordered_for
        end.
        eapply OPTLoopSeq; eauto.
      * simpl in Hglobal.
        lazymatch goal with
        | Hfor0 :
            Forall2 (fun z tri => par_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
            pose proof
              (ordered_par_trace_forall2_of_global
                 body env IHbody Hglobal zs0 trs0 Hfor0) as Hordered_for
        end.
        eapply OPTLoopVec; eauto.
      * simpl in Hglobal.
        destruct Hglobal as [Hglobal_body Hglobal_family].
        lazymatch goal with
        | Hfor0 :
            Forall2 (fun z tri => par_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
            pose proof
              (ordered_par_trace_forall2_of_global
                 body env IHbody Hglobal_body zs0 trs0 Hfor0) as Hordered_for
        end.
        eapply OPTLoopPar; eauto.
    + inversion Htrace; constructor.
    + inversion Htrace; subst.
      simpl in Hglobal.
      constructor. eapply ordered_par_traces_of_global; eauto.
    + inversion Htrace as
          [| |env' tst st tr' Heval Hbody |env' tst st Heval | | |];
        subst; simpl in Hglobal.
      * eapply OPTGuardTrue; eauto.
      * eapply OPTGuardFalse; eauto.
  - intros ss.
    induction ss as [|s ss IHss]; intros env tr Hglobal Htrace.
    + inversion Htrace. constructor.
    + inversion Htrace as [|env' st sts tr1 tr2 Hst Hsts]; subst.
      simpl in Hglobal.
      destruct Hglobal as [Hglobal_s Hglobal_ss].
      econstructor.
      * eapply ordered_par_trace_of_global; eauto.
      * eapply IHss; eauto.
Qed.

Lemma ordered_loop_semantics_of_global :
  forall s env mem1 mem2,
    parallel_families_ordered_stmt s ->
    loop_semantics s env mem1 mem2 ->
    ordered_loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2 Hglobal [tr [Htrace Hsem]].
  exists tr. split; auto.
  eapply ordered_par_trace_of_global; eauto.
Qed.

Lemma ordered_semantics_of_global :
  forall p mem1 mem2,
    parallel_families_ordered p ->
    semantics p mem1 mem2 ->
    ordered_semantics p mem1 mem2.
Proof.
  intros [[s ctxt] vars] mem1 mem2 Hglobal Hsem.
  inversion Hsem as
    [loop_ext loop ctxt' vars' env mem1' mem2' Heq Hcompat Hna Hinit Hloop];
    subst.
  inversion Heq; subst.
  econstructor; eauto.
  eapply ordered_loop_semantics_of_global; eauto.
Qed.

Fixpoint trace_safe_stmt (s : stmt) : Prop :=
  match s with
  | Loop _ _ _ _ body => trace_safe_stmt body
  | Instr _ es => exists affs, BaseLoop.exprlist_to_aff es = Okk affs
  | Seq ss => trace_safe_stmts ss
  | Guard _ body => trace_safe_stmt body
  end
with trace_safe_stmts (ss : stmt_list) : Prop :=
  match ss with
  | SNil => True
  | SCons s ss' => trace_safe_stmt s /\ trace_safe_stmts ss'
  end.

Definition trace_safe (p : t) : Prop :=
  let '(s, _, _) := p in trace_safe_stmt s.

Fixpoint erase_parallelize_dim_stmt_eq_rec
  (d : nat) (s : stmt) {struct s}
  : erase_stmt (parallelize_dim_stmt d s) = erase_stmt s
with erase_parallelize_dim_stmts_eq_rec
  (d : nat) (ss : stmt_list) {struct ss}
  : erase_stmt_list (parallelize_dim_stmts d ss) = erase_stmt_list ss.
Proof.
  - destruct s; simpl.
    + destruct l; destruct o as [n|]; simpl; rewrite erase_parallelize_dim_stmt_eq_rec; reflexivity.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmts_eq_rec. reflexivity.
    + rewrite erase_parallelize_dim_stmt_eq_rec. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmt_eq_rec, erase_parallelize_dim_stmts_eq_rec.
      reflexivity.
Qed.

Fixpoint erase_vectorize_dim_stmt_eq_rec
  (d : nat) (s : stmt) {struct s}
  : erase_stmt (vectorize_dim_stmt d s) = erase_stmt s
with erase_vectorize_dim_stmts_eq_rec
  (d : nat) (ss : stmt_list) {struct ss}
  : erase_stmt_list (vectorize_dim_stmts d ss) = erase_stmt_list ss.
Proof.
  - destruct s; simpl.
    + destruct l; destruct o as [n|]; simpl; rewrite erase_vectorize_dim_stmt_eq_rec; reflexivity.
    + reflexivity.
    + rewrite erase_vectorize_dim_stmts_eq_rec. reflexivity.
    + rewrite erase_vectorize_dim_stmt_eq_rec. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_vectorize_dim_stmt_eq_rec, erase_vectorize_dim_stmts_eq_rec.
      reflexivity.
Qed.

Lemma erase_vectorize_dim_stmt_eq :
  forall d s,
    erase_stmt (vectorize_dim_stmt d s) = erase_stmt s
with erase_vectorize_dim_stmts_eq :
  forall d ss,
    erase_stmt_list (vectorize_dim_stmts d ss) = erase_stmt_list ss.
Proof.
  - intros d s.
    apply erase_vectorize_dim_stmt_eq_rec.
  - intros d ss.
    apply erase_vectorize_dim_stmts_eq_rec.
Qed.

Lemma erase_vectorize_dim_eq :
  forall d p,
    erase_parallel (vectorize_dim d p) = erase_parallel p.
Proof.
  intros d [[s ctxt] vars]; simpl.
  rewrite erase_vectorize_dim_stmt_eq.
  reflexivity.
Qed.

Lemma erase_parallelize_dim_stmt_eq :
  forall d s,
    erase_stmt (parallelize_dim_stmt d s) = erase_stmt s
with erase_parallelize_dim_stmts_eq :
  forall d ss,
    erase_stmt_list (parallelize_dim_stmts d ss) = erase_stmt_list ss.
Proof.
  - intros d s.
    apply erase_parallelize_dim_stmt_eq_rec.
  - intros d ss.
    apply erase_parallelize_dim_stmts_eq_rec.
Qed.

Lemma erase_parallelize_dim_eq :
  forall d p,
    erase_parallel (parallelize_dim d p) = erase_parallel p.
Proof.
  intros d [[s ctxt] vars]; simpl.
  rewrite erase_parallelize_dim_stmt_eq.
  reflexivity.
Qed.

Fixpoint erase_of_loop_stmt_eq_rec
  (s : BaseLoop.stmt) {struct s}
  : erase_stmt (of_loop_stmt s) = s
with erase_of_loop_stmt_list_eq_rec
  (ss : BaseLoop.stmt_list) {struct ss}
  : erase_stmt_list (of_loop_stmt_list ss) = ss.
Proof.
  - destruct s; simpl.
    + rewrite erase_of_loop_stmt_eq_rec. reflexivity.
    + reflexivity.
    + rewrite erase_of_loop_stmt_list_eq_rec. reflexivity.
    + rewrite erase_of_loop_stmt_eq_rec. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_of_loop_stmt_eq_rec, erase_of_loop_stmt_list_eq_rec. reflexivity.
Qed.

Lemma erase_of_loop_stmt_eq :
  forall s,
    erase_stmt (of_loop_stmt s) = s
with erase_of_loop_stmt_list_eq :
  forall ss,
    erase_stmt_list (of_loop_stmt_list ss) = ss.
Proof.
  - intros s.
    apply erase_of_loop_stmt_eq_rec.
  - intros ss.
    apply erase_of_loop_stmt_list_eq_rec.
Qed.

Lemma erase_of_loop_eq :
  forall p,
    erase_parallel (of_loop p) = p.
Proof.
  intros [[s ctxt] vars]; simpl.
  rewrite erase_of_loop_stmt_eq.
  reflexivity.
Qed.

Fixpoint of_loop_stmt_all_origin_none_rec
  (s : BaseLoop.stmt) {struct s}
  : all_origin_none_stmt (of_loop_stmt s)
with of_loop_stmt_list_all_origin_none_rec
  (ss : BaseLoop.stmt_list) {struct ss}
  : all_origin_none_stmts (of_loop_stmt_list ss).
Proof.
  - destruct s; simpl.
    + split; auto.
    + auto.
    + apply of_loop_stmt_list_all_origin_none_rec.
    + apply of_loop_stmt_all_origin_none_rec.
  - destruct ss; simpl.
    + auto.
    + split.
      * apply of_loop_stmt_all_origin_none_rec.
      * apply of_loop_stmt_list_all_origin_none_rec.
Qed.

Lemma of_loop_stmt_all_origin_none :
  forall s,
    all_origin_none_stmt (of_loop_stmt s)
with of_loop_stmt_list_all_origin_none :
  forall ss,
    all_origin_none_stmts (of_loop_stmt_list ss).
Proof.
  - intros s.
    apply of_loop_stmt_all_origin_none_rec.
  - intros ss.
    apply of_loop_stmt_list_all_origin_none_rec.
Qed.

Lemma of_loop_all_origin_none :
  forall p,
    all_origin_none (of_loop p).
Proof.
  intros [[s ctxt] vars]; simpl.
  apply of_loop_stmt_all_origin_none.
Qed.

Lemma instr_point_sema_stable_under_state_eq :
  forall ip st1 st2 st1' st2',
    Instr.State.eq st1 st1' ->
    Instr.State.eq st2 st2' ->
    ILSema.instr_point_sema ip st1 st2 ->
    ILSema.instr_point_sema ip st1' st2'.
Proof.
  intros ip st1 st2 st1' st2' Heq1 Heq2 Hsem.
  inversion Hsem as [wcs rcs Hinstr]; subst.
  econstructor.
  eapply Instr.instr_semantics_stable_under_state_eq; eauto.
Qed.

Lemma instr_point_sema_preserve_nonalias :
  forall ip st1 st2,
    Instr.NonAlias st1 ->
    ILSema.instr_point_sema ip st1 st2 ->
    Instr.NonAlias st2.
Proof.
  intros ip st1 st2 Hna Hsem.
  inversion Hsem as [wcs rcs Hinstr]; subst.
  eapply Instr.sema_prsv_nonalias; eauto.
Qed.

Lemma instr_point_list_semantics_nil_inv :
  forall st1 st2,
    ILSema.instr_point_list_semantics [] st1 st2 ->
    Instr.State.eq st1 st2.
Proof.
  intros st1 st2 Hsem.
  inversion Hsem; subst; assumption.
Qed.

Lemma instr_point_list_semantics_singleton_inv :
  forall ip st1 st2,
    ILSema.instr_point_list_semantics [ip] st1 st2 ->
    ILSema.instr_point_sema ip st1 st2.
Proof.
  intros ip st1 st2 Hsem.
  inversion Hsem as [|st1' stmid st2' ip' il Hip Hnil]; subst.
  simpl in *.
  inversion Hnil; subst.
  eapply instr_point_sema_stable_under_state_eq; eauto using Instr.State.eq_refl.
Qed.

Lemma instr_point_list_semantics_app_inv :
  forall l1 l2 st1 st3,
    ILSema.instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      ILSema.instr_point_list_semantics l1 st1 st2 /\
      ILSema.instr_point_list_semantics l2 st2 st3.
Proof.
  induction l1 as [|ip l1 IH]; intros l2 st1 st3 Hsem.
  - exists st1.
    split.
    + constructor. apply Instr.State.eq_refl.
    + simpl in Hsem. exact Hsem.
  - simpl in Hsem.
    inversion Hsem as [|st1' stmid st3' ip' il Hip Htail]; subst.
    specialize (IH l2 stmid st3 Htail) as [st2 [Hleft Hright]].
    exists st2.
    split.
    + econstructor; eauto.
    + exact Hright.
Qed.

Lemma base_loop_semantics_aux_implies_loop_semantics :
  forall s env mem1 mem2,
    BaseLoop.loop_semantics_aux s env mem1 mem2 ->
    BaseLoop.loop_semantics s env mem1 mem2.
Proof.
  refine
    (BaseLoop.loop_semantics_aux_mutual_ind
       (fun s env mem1 mem2 _ => BaseLoop.loop_semantics s env mem1 mem2)
       (fun zs s env mem1 mem2 _ =>
          Instr.IterSem.iter_semantics
            (fun x => BaseLoop.loop_semantics s (x :: env))
            zs mem1 mem2)
       _ _ _ _ _ _ _ _).
  - intros i es env mem1 mem2 wcs rcs Hinstr.
    eapply BaseLoop.LInstr; eauto.
  - intros env mem.
    apply BaseLoop.LSeqEmpty.
  - intros env st sts mem1 mem2 mem3 l Hst l0 Hsts.
    eapply BaseLoop.LSeq; eauto.
  - intros env t st mem1 mem2 Heval l Hst.
    eapply BaseLoop.LGuardTrue; eauto.
  - intros env t st mem Heval.
    eapply BaseLoop.LGuardFalse; eauto.
  - intros env lb ub st mem1 mem2 l Hiter.
    eapply BaseLoop.LLoop; eauto.
  - intros st env mem.
    apply Instr.IterSem.IDone.
  - intros x xs st env mem1 mem2 mem3 l Hhead l0 Htail.
    econstructor; eauto.
Qed.

Lemma base_loop_semantics_aux_list_implies_iter :
  forall zs s env mem1 mem2,
    BaseLoop.loop_semantics_aux_list zs s env mem1 mem2 ->
    Instr.IterSem.iter_semantics
      (fun x => BaseLoop.loop_semantics s (x :: env))
      zs mem1 mem2.
Proof.
  refine
    (BaseLoop.loop_semantics_aux_list_mutual_ind
       (fun s env mem1 mem2 _ => BaseLoop.loop_semantics s env mem1 mem2)
       (fun zs s env mem1 mem2 _ =>
          Instr.IterSem.iter_semantics
            (fun x => BaseLoop.loop_semantics s (x :: env))
            zs mem1 mem2)
       _ _ _ _ _ _ _ _).
  - intros i es env mem1 mem2 wcs rcs Hinstr.
    eapply BaseLoop.LInstr; eauto.
  - intros env mem.
    apply BaseLoop.LSeqEmpty.
  - intros env st sts mem1 mem2 mem3 l Hst l0 Hsts.
    eapply BaseLoop.LSeq; eauto.
  - intros env t st mem1 mem2 Heval l Hst.
    eapply BaseLoop.LGuardTrue; eauto.
  - intros env t st mem Heval.
    eapply BaseLoop.LGuardFalse; eauto.
  - intros env lb ub st mem1 mem2 l Hiter.
    eapply BaseLoop.LLoop; eauto.
  - intros st env mem.
    apply Instr.IterSem.IDone.
  - intros x xs st env mem1 mem2 mem3 l Hhead l0 Htail.
    econstructor; eauto.
Qed.

Lemma base_loop_instance_list_implies_loop_semantics :
  forall s env il mem1 mem2,
    BaseLoop.loop_instance_list_semantics s env il mem1 mem2 ->
    BaseLoop.loop_semantics s env mem1 mem2.
Proof.
  intros s env il mem1 mem2 Hinst.
  eapply base_loop_semantics_aux_implies_loop_semantics.
  eapply BaseLoop.instance_list_implies_loop_semantics_aux; eauto.
Qed.

Lemma seq_trace_forall2_refines_erased :
  forall body env,
    (forall env' tr mem1 mem2,
       trace_safe_stmt body ->
       seq_trace body env' tr ->
       ILSema.instr_point_list_semantics tr mem1 mem2 ->
       exists mem2',
         BaseLoop.loop_semantics (erase_stmt body) env' mem1 mem2' /\
         Instr.State.eq mem2 mem2') ->
    forall zs trs mem1 mem2,
      trace_safe_stmt body ->
      Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
      ILSema.instr_point_list_semantics (concat trs) mem1 mem2 ->
      exists mem2',
        Instr.IterSem.iter_semantics
          (fun z => BaseLoop.loop_semantics (erase_stmt body) (z :: env))
          zs mem1 mem2' /\
        Instr.State.eq mem2 mem2'.
Proof.
  intros body env Hbody zs trs mem1 mem2 Hsafe_body Hfor.
  revert mem1 mem2 Hsafe_body.
  induction Hfor as [|z tr zs' trs' Htri Hfor' IHfor'];
    intros mem1 mem2 Hsafe_body Hsem_concat.
  - simpl in Hsem_concat.
    exists mem1.
    split.
    + constructor.
    + eapply Instr.State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem_concat.
    eapply instr_point_list_semantics_app_inv in Hsem_concat.
    destruct Hsem_concat as [mem_mid [Hsem_head Hsem_tail]].
    pose proof
      (Hbody (z :: env) tr mem1 mem_mid Hsafe_body Htri Hsem_head)
      as [mem_mid' [Hbody_sem Heq_mid]].
    pose proof
      (ILSema.instr_point_list_sema_stable_under_state_eq
         (concat trs') mem_mid mem2 mem_mid' mem2
         Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
      as Hsem_tail'.
    pose proof (IHfor' mem_mid' mem2 Hsafe_body Hsem_tail')
      as [mem2' [Hrest_sem Heq_tail]].
    exists mem2'.
    split.
    + eapply Instr.IterSem.IProgress.
      * exact Hbody_sem.
      * exact Hrest_sem.
    + exact Heq_tail.
Qed.

Lemma seq_trace_refines_erased_stmt :
  forall s env tr mem1 mem2,
    trace_safe_stmt s ->
    seq_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'
with seq_trace_refines_erased_stmts :
  forall ss env tr mem1 mem2,
    trace_safe_stmts ss ->
    seq_traces ss env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (BaseLoop.Seq (erase_stmt_list ss)) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  - intros s.
    induction s as [mode od lb ub body IHbody|i es|ss _|t body IHbody];
      intros env tr mem1 mem2 Hsafe Htrace Hsem.
    + inversion Htrace as
          [| | | | mode' od' lb' ub' body' env' zs trs tr' Hzs Hfor Hconcat];
        subst.
      match goal with
      | Hfor0 :
          Forall2 (fun z tri => seq_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
          pose proof
            (seq_trace_forall2_refines_erased
               body env IHbody zs0 trs0 mem1 mem2 Hsafe Hfor0 Hsem)
            as [mem2' [Hloop_sem Heq]]
      end.
      exists mem2'. split.
      * econstructor. exact Hloop_sem.
      * exact Heq.
    + inversion Htrace; subst.
      simpl in Hsafe.
      pose proof (instr_point_list_semantics_singleton_inv _ _ _ Hsem) as Hip.
      inversion Hip as [wcs rcs Hinstr]; subst.
      unfold BaseLoop.mk_instr_point in Hinstr.
      destruct Hsafe as [affs Haff].
      rewrite Haff in Hinstr.
      simpl in Hinstr.
      pose proof (BaseLoop.exprlist_to_aff_correct es env affs Haff) as Haff_ok.
      exists mem2.
      split.
      * eapply BaseLoop.LInstr with (wcs := wcs) (rcs := rcs).
        rewrite <- Haff_ok in Hinstr.
        exact Hinstr.
      * apply Instr.State.eq_refl.
    + inversion Htrace; subst.
      eapply seq_trace_refines_erased_stmts; eauto.
    + inversion Htrace as
          [| | env' tst st tr' Heval Hbodytrace | env' tst st Heval |];
        subst; simpl in Hsafe.
      * pose proof (IHbody env tr mem1 mem2 Hsafe Hbodytrace Hsem)
          as [mem2' [Hbody_sem Heq]].
        exists mem2'.
        split; [eapply BaseLoop.LGuardTrue; eauto | exact Heq].
      * exists mem1.
        split;
          [eapply BaseLoop.LGuardFalse; eauto
          | eapply Instr.State.eq_sym;
            eapply instr_point_list_semantics_nil_inv; eauto].
  - intros ss.
    induction ss as [|s ss IHss']; intros env tr mem1 mem2 Hsafe Htrace Hsem.
    + inversion Htrace; subst.
      exists mem1.
      split;
        [constructor
        | eapply Instr.State.eq_sym;
          eapply instr_point_list_semantics_nil_inv; eauto].
    + inversion Htrace as [|env' st sts tr1 tr2 Hst Hsts]; subst.
      simpl in Hsafe.
      destruct Hsafe as [Hsafe_s Hsafe_ss].
      eapply instr_point_list_semantics_app_inv in Hsem.
      destruct Hsem as [mem_mid [Hsem_head Hsem_tail]].
      pose proof
        (seq_trace_refines_erased_stmt
           s env tr1 mem1 mem_mid Hsafe_s Hst Hsem_head)
        as [mem_mid' [Hs_sem Heq_mid]].
      pose proof
        (ILSema.instr_point_list_sema_stable_under_state_eq
           tr2 mem_mid mem2 mem_mid' mem2
           Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
        as Hsem_tail'.
      pose proof
        (IHss' env tr2 mem_mid' mem2 Hsafe_ss Hsts Hsem_tail')
        as [mem2' [Hss_sem Heq_tail]].
      exists mem2'.
      split.
      * econstructor; eauto.
      * eapply Instr.State.eq_trans.
        -- exact Heq_tail.
        -- apply Instr.State.eq_refl.
Qed.

Lemma seq_trace_refines_erased :
  forall s env tr mem1 mem2,
    trace_safe_stmt s ->
    seq_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros. eapply seq_trace_refines_erased_stmt; eauto.
Qed.

Lemma instr_point_list_semantics_swap_adj :
  forall ip1 ip2 rest st1 st4,
    Instr.NonAlias st1 ->
    ILSema.Permutable ip1 ip2 ->
    ILSema.instr_point_list_semantics (ip1 :: ip2 :: rest) st1 st4 ->
    exists st4',
      ILSema.instr_point_list_semantics (ip2 :: ip1 :: rest) st1 st4' /\
      Instr.State.eq st4 st4'.
Proof.
  intros ip1 ip2 rest st1 st4 Hna Hperm Hsem.
  inversion Hsem as [|st1' st2 st4' ip1' l1 Hip1 Htail]; subst.
  inversion Htail as [|st2' st3 st4'' ip2' l2 Hip2 Hrest]; subst.
  unfold ILSema.Permutable in Hperm.
  specialize (Hperm st1 Hna).
  destruct Hperm as [Hfwd _].
  destruct (Hfwd _ _ Hip1 Hip2) as (st2'' & st3' & Hip2' & Hip1' & Heq3).
  pose proof
    (ILSema.instr_point_list_sema_stable_under_state_eq
       rest st3 st4 st3' st4
       Hrest Heq3 (Instr.State.eq_refl st4))
    as Hrest'.
  exists st4.
  split.
  - econstructor.
    + exact Hip2'.
    + econstructor.
      * exact Hip1'.
      * exact Hrest'.
  - apply Instr.State.eq_refl.
Qed.

Lemma move_front_permutable :
  forall prefix x rest st1 st2,
    Instr.NonAlias st1 ->
    (forall y, In y prefix -> ILSema.Permutable y x) ->
    ILSema.instr_point_list_semantics (prefix ++ x :: rest) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (x :: prefix ++ rest) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  induction prefix as [|y prefix IH]; intros x rest st1 st2 Hna Hperm Hsem.
  - simpl in *.
    exists st2.
    split; [exact Hsem | apply Instr.State.eq_refl].
  - simpl in Hsem.
    inversion Hsem as [|st1' stmid st2' ip' il Hip Htail]; subst.
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    assert (Hperm_tail : forall y0, In y0 prefix -> ILSema.Permutable y0 x).
    {
      intros y0 Hin.
      apply Hperm.
      right; exact Hin.
    }
    pose proof (IH x rest stmid st2 Hna_mid Hperm_tail Htail)
      as (st2' & Htail_moved & Heq_tail).
    assert
      (Hyx :
         ILSema.instr_point_list_semantics (y :: x :: prefix ++ rest) st1 st2').
    {
      econstructor.
      - exact Hip.
      - exact Htail_moved.
    }
    pose proof
      (instr_point_list_semantics_swap_adj
         y x (prefix ++ rest) st1 st2'
         Hna (Hperm y (or_introl eq_refl)) Hyx)
      as (st2'' & Hswapped & Heq_swap).
    exists st2''.
    split.
    + exact Hswapped.
    + eapply Instr.State.eq_trans; eauto.
Qed.

Lemma move_back_permutable :
  forall x prefix rest st1 st2,
    Instr.NonAlias st1 ->
    (forall y, In y prefix -> ILSema.Permutable y x) ->
    ILSema.instr_point_list_semantics (x :: prefix ++ rest) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (prefix ++ x :: rest) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  induction prefix as [|y prefix IH]; intros rest st1 st2 Hna Hperm Hsem.
  - simpl in *.
    exists st2.
    split; [exact Hsem | apply Instr.State.eq_refl].
  - simpl in Hsem.
    assert (Hyx : ILSema.Permutable x y).
    {
      eapply ILSema.Permutable_symm.
      apply Hperm.
      left; reflexivity.
    }
    pose proof
      (instr_point_list_semantics_swap_adj
         x y (prefix ++ rest) st1 st2 Hna Hyx Hsem)
      as [st2' [Hswapped Heq_swap]].
    inversion Hswapped as [|st1' stmid st2'' ip' il Hy Htail]; subst.
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    assert (Hperm_tail : forall y0, In y0 prefix -> ILSema.Permutable y0 x).
    {
      intros y0 Hin.
      apply Hperm.
      right; exact Hin.
    }
    destruct (IH rest stmid st2' Hna_mid Hperm_tail Htail)
      as [st2'' [Hmoved Heq_tail]].
    exists st2''.
    split.
    + econstructor; eauto.
    + eapply Instr.State.eq_trans; eauto.
Qed.

Lemma instr_point_list_semantics_cons_inv :
  forall ip rest st1 st2,
    ILSema.instr_point_list_semantics (ip :: rest) st1 st2 ->
    exists stmid,
      ILSema.instr_point_sema ip st1 stmid /\
      ILSema.instr_point_list_semantics rest stmid st2.
Proof.
  intros ip rest st1 st2 Hsem.
  inversion Hsem as [|st1' stmid st2' ip' il Hip Htail]; subst.
  exists stmid.
  split; assumption.
Qed.

Lemma iter_semantics_preserve_nonalias :
  forall A (P : A -> mem -> mem -> Prop),
    (forall x mem1 mem2,
        P x mem1 mem2 ->
        Instr.NonAlias mem1 ->
        Instr.NonAlias mem2) ->
    forall xs mem1 mem2,
      Instr.IterSem.iter_semantics P xs mem1 mem2 ->
      Instr.NonAlias mem1 ->
      Instr.NonAlias mem2.
Proof.
  intros A P Hstep xs mem1 mem2 Hiter.
  induction Hiter; intros Hna.
  - exact Hna.
  - apply IHHiter.
    eapply Hstep; eauto.
Qed.

Scheme base_stmt_mutind := Induction for BaseLoop.stmt Sort Prop
with base_stmts_mutind := Induction for BaseLoop.stmt_list Sort Prop.
Combined Scheme base_stmt_stmts_mutind from base_stmt_mutind, base_stmts_mutind.

Definition base_stmt_preserve_nonalias_goal (s : BaseLoop.stmt) : Prop :=
  forall env mem1 mem2,
    BaseLoop.loop_semantics s env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.

Definition base_stmts_preserve_nonalias_goal (ss : BaseLoop.stmt_list) : Prop :=
  forall env mem1 mem2,
    BaseLoop.loop_semantics (BaseLoop.Seq ss) env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.

Lemma base_loop_semantics_preserve_nonalias_mutual :
  (forall s,
      base_stmt_preserve_nonalias_goal s) /\
  (forall ss,
      base_stmts_preserve_nonalias_goal ss).
Proof.
  apply
    (base_stmt_stmts_mutind
       base_stmt_preserve_nonalias_goal
       base_stmts_preserve_nonalias_goal).
  - intros lb ub body IHbody env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    lazymatch goal with
    | Hiter : Instr.IterSem.iter_semantics _ _ _ _ |- _ =>
        eapply
          (iter_semantics_preserve_nonalias
             Z
             (fun x mem1 mem2 => BaseLoop.loop_semantics body (x :: env) mem1 mem2));
          [intros x mem1' mem2' Hbody_sem Hna'; eapply IHbody; eauto
          | exact Hiter
          | exact Hna]
    end.
  - intros i es env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    eauto using Instr.sema_prsv_nonalias.
  - intros ss IHss env mem1 mem2 Hsem Hna.
    eapply IHss; eauto.
  - intros test body IHbody env mem1 mem2 Hsem Hna.
    inversion Hsem; subst; eauto.
  - intros env mem1 mem2 Hsem Hna.
    inversion Hsem; subst; eauto.
  - intros s IHs ss IHss env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    eapply IHss.
    + eauto.
    + eapply IHs; eauto.
Qed.

Lemma base_loop_semantics_preserve_nonalias_stmt :
  forall s,
    base_stmt_preserve_nonalias_goal s.
Proof.
  exact (proj1 base_loop_semantics_preserve_nonalias_mutual).
Qed.

Lemma base_loop_semantics_preserve_nonalias_stmts :
  forall ss,
    base_stmts_preserve_nonalias_goal ss.
Proof.
  exact (proj2 base_loop_semantics_preserve_nonalias_mutual).
Qed.

Lemma base_loop_semantics_preserve_nonalias :
  forall s env mem1 mem2,
    BaseLoop.loop_semantics s env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.
Proof.
  intros s.
  apply base_loop_semantics_preserve_nonalias_stmt.
Qed.

Lemma interleave_safe_refines_concat :
  forall trs out st1 st2,
    Instr.NonAlias st1 ->
    interleave_safe trs out ->
    ILSema.instr_point_list_semantics out st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (concat trs) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros trs out st1 st2 Hna Hsafe.
  revert st1 st2 Hna.
  induction Hsafe; intros st1 st2 Hna Hsem.
  - simpl in Hsem.
    exists st1.
    split.
    + constructor. apply Instr.State.eq_refl.
    + eapply Instr.State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem.
    eapply IHHsafe; eauto.
  - destruct (instr_point_list_semantics_cons_inv _ _ _ _ Hsem)
      as [stmid [Hx Htail]].
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    destruct (IHHsafe stmid st2 Hna_mid Htail)
      as [st2' [Hconcat_tail Heq_tail]].
    assert
      (Hshape_rest :
         concat (pre ++ xs :: post) =
         concat pre ++ concat (xs :: post)).
    {
      rewrite concat_app.
      reflexivity.
    }
    assert
      (Hcons :
         ILSema.instr_point_list_semantics
           (x :: concat pre ++ concat (xs :: post)) st1 st2').
    {
      econstructor.
      - exact Hx.
      - rewrite <- Hshape_rest.
        exact Hconcat_tail.
    }
    assert
      (Hshape :
         concat (pre ++ (x :: xs) :: post) =
         concat pre ++ x :: concat (xs :: post)).
    {
      rewrite concat_app.
      simpl.
      reflexivity.
    }
    destruct
      (move_back_permutable
         x (concat pre) (concat (xs :: post)) st1 st2'
         Hna H Hcons)
      as [st2'' [Hconcat_full Heq_move]].
    assert
      (Hconcat_full' :
         ILSema.instr_point_list_semantics
           (concat (pre ++ (x :: xs) :: post)) st1 st2'').
    {
      rewrite Hshape.
      exact Hconcat_full.
    }
    exists st2''.
    split.
    + exact Hconcat_full'.
    + eapply Instr.State.eq_trans.
      * exact Heq_tail.
      * exact Heq_move.
Qed.

Lemma ordered_par_trace_forall2_refines_erased :
  forall body env,
    (forall env' tr mem1 mem2,
        Instr.NonAlias mem1 ->
        trace_safe_stmt body ->
        ordered_par_trace body env' tr ->
        ILSema.instr_point_list_semantics tr mem1 mem2 ->
        exists mem2',
          BaseLoop.loop_semantics (erase_stmt body) env' mem1 mem2' /\
          Instr.State.eq mem2 mem2') ->
    forall zs trs mem1 mem2,
      Instr.NonAlias mem1 ->
      trace_safe_stmt body ->
      Forall2 (fun z tri => ordered_par_trace body (z :: env) tri) zs trs ->
      ILSema.instr_point_list_semantics (concat trs) mem1 mem2 ->
      exists mem2',
        Instr.IterSem.iter_semantics
          (fun z => BaseLoop.loop_semantics (erase_stmt body) (z :: env))
          zs mem1 mem2' /\
        Instr.State.eq mem2 mem2'.
Proof.
  intros body env Hbody zs trs mem1 mem2 Hna Hsafe_body Hfor.
  revert mem1 mem2 Hna Hsafe_body.
  induction Hfor as [|z tr zs' trs' Htri Hfor' IHfor'];
    intros mem1 mem2 Hna Hsafe_body Hsem_concat.
  - simpl in Hsem_concat.
    exists mem1.
    split.
    + constructor.
    + eapply Instr.State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem_concat.
    eapply instr_point_list_semantics_app_inv in Hsem_concat.
    destruct Hsem_concat as [mem_mid [Hsem_head Hsem_tail]].
    pose proof
      (Hbody
         (z :: env) tr mem1 mem_mid Hna Hsafe_body Htri Hsem_head)
      as [mem_mid' [Hbody_sem Heq_mid]].
    assert (Hna_mid' : Instr.NonAlias mem_mid').
    {
      eapply base_loop_semantics_preserve_nonalias; eauto.
    }
    pose proof
      (ILSema.instr_point_list_sema_stable_under_state_eq
         (concat trs') mem_mid mem2 mem_mid' mem2
         Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
      as Hsem_tail'.
    pose proof
      (IHfor' mem_mid' mem2 Hna_mid' Hsafe_body Hsem_tail')
      as [mem2' [Hrest_sem Heq_tail]].
    exists mem2'.
    split.
    + eapply Instr.IterSem.IProgress.
      * exact Hbody_sem.
      * exact Hrest_sem.
    + exact Heq_tail.
Qed.

Lemma ordered_par_trace_refines_erased_stmt :
  forall s env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt s ->
    ordered_par_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'
with ordered_par_traces_refines_erased_stmts :
  forall ss env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmts ss ->
    ordered_par_traces ss env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (BaseLoop.Seq (erase_stmt_list ss)) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  - intros s.
    induction s as [mode od lb ub body IHbody|i es|ss _|t body IHbody];
      intros env tr mem1 mem2 Hna Hsafe Htrace Hsem.
    + inversion Htrace as
          [| | | |od' lb' ub' body' env' zs trs tr' Hzs Hfor Hordered_for Hconcat
           |od' lb' ub' body' env' zs trs tr' Hzs Hfor Hordered_for Hconcat
           |d lb' ub' body' env' zs trs tr' Hzs Hfor Hordered_for Hfamily Hinter];
        subst.
      * simpl in Hsafe.
        match goal with
        | Hfor0 :
            Forall2
              (fun z tri => ordered_par_trace body (z :: env) tri)
              ?zs0 ?trs0 |- _ =>
            pose proof
              (ordered_par_trace_forall2_refines_erased
                 body env IHbody zs0 trs0 mem1 mem2
                 Hna Hsafe Hfor0 Hsem)
              as [mem2' [Hloop_sem Heq]]
        end.
        exists mem2'. split.
        -- econstructor. exact Hloop_sem.
        -- exact Heq.
      * simpl in Hsafe.
        match goal with
        | Hfor0 :
            Forall2
              (fun z tri => ordered_par_trace body (z :: env) tri)
              ?zs0 ?trs0 |- _ =>
            pose proof
              (ordered_par_trace_forall2_refines_erased
                 body env IHbody zs0 trs0 mem1 mem2
                 Hna Hsafe Hfor0 Hsem)
              as [mem2' [Hloop_sem Heq]]
        end.
        exists mem2'. split.
        -- econstructor. exact Hloop_sem.
        -- exact Heq.
      * simpl in Hsafe.
        lazymatch goal with
        | Hfor0 :
            Forall2
              (fun z tri => ordered_par_trace body (z :: env) tri)
              ?zs0 ?trs0 |- _ =>
            lazymatch goal with
            | Hinter0 : interleave_family trs0 ?tr0 |- _ =>
                pose proof
                  (family_ordered_interleave_safe
                     trs0 tr0 Hfamily Hinter0) as Hinter_safe;
                pose proof
                  (interleave_safe_refines_concat
                     trs0 tr0 mem1 mem2 Hna Hinter_safe Hsem)
                  as [mem2a [Hconcat_sem Heq_concat]];
                pose proof
                  (ordered_par_trace_forall2_refines_erased
                     body env IHbody zs0 trs0 mem1 mem2a
                     Hna Hsafe Hfor0 Hconcat_sem)
                  as [mem2' [Hloop_sem Heq_seq]]
            end
        end.
        exists mem2'. split.
        -- econstructor. exact Hloop_sem.
        -- eapply Instr.State.eq_trans; eauto.
    + inversion Htrace; subst.
      simpl in Hsafe.
      pose proof (instr_point_list_semantics_singleton_inv _ _ _ Hsem) as Hip.
      inversion Hip as [wcs rcs Hinstr]; subst.
      unfold BaseLoop.mk_instr_point in Hinstr.
      destruct Hsafe as [affs Haff].
      rewrite Haff in Hinstr.
      simpl in Hinstr.
      pose proof (BaseLoop.exprlist_to_aff_correct es env affs Haff) as Haff_ok.
      exists mem2.
      split.
      * eapply BaseLoop.LInstr with (wcs := wcs) (rcs := rcs).
        rewrite <- Haff_ok in Hinstr.
        exact Hinstr.
      * apply Instr.State.eq_refl.
    + inversion Htrace; subst.
      eapply ordered_par_traces_refines_erased_stmts; eauto.
    + inversion Htrace as
          [| | env' tst st tr' Heval Hbodytrace | env' tst st Heval | | |];
        subst; simpl in Hsafe.
      * pose proof
          (IHbody env tr mem1 mem2 Hna Hsafe Hbodytrace Hsem)
          as [mem2' [Hbody_sem Heq]].
        exists mem2'.
        split; [eapply BaseLoop.LGuardTrue; eauto | exact Heq].
      * exists mem1.
        split;
          [eapply BaseLoop.LGuardFalse; eauto
          | eapply Instr.State.eq_sym;
            eapply instr_point_list_semantics_nil_inv; eauto].
  - intros ss.
    induction ss as [|s ss IHss'];
      intros env tr mem1 mem2 Hna Hsafe Htrace Hsem.
    + inversion Htrace; subst.
      exists mem1.
      split;
        [constructor
        | eapply Instr.State.eq_sym;
          eapply instr_point_list_semantics_nil_inv; eauto].
    + inversion Htrace as [|env' st sts tr1 tr2 Hst Hsts]; subst.
      simpl in Hsafe.
      destruct Hsafe as [Hsafe_s Hsafe_ss].
      eapply instr_point_list_semantics_app_inv in Hsem.
      destruct Hsem as [mem_mid [Hsem_head Hsem_tail]].
      pose proof
        (ordered_par_trace_refines_erased_stmt
           s env tr1 mem1 mem_mid Hna Hsafe_s Hst Hsem_head)
        as [mem_mid' [Hs_sem Heq_mid]].
      assert (Hna_mid' : Instr.NonAlias mem_mid').
      {
        eapply base_loop_semantics_preserve_nonalias; eauto.
      }
      pose proof
        (ILSema.instr_point_list_sema_stable_under_state_eq
           tr2 mem_mid mem2 mem_mid' mem2
           Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
        as Hsem_tail'.
      pose proof
        (IHss'
           env tr2 mem_mid' mem2 Hna_mid' Hsafe_ss Hsts Hsem_tail')
        as [mem2' [Hss_sem Heq_tail]].
      exists mem2'.
      split.
      * econstructor; eauto.
      * exact Heq_tail.
Qed.

Lemma ordered_par_trace_refines_erased :
  forall s env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt s ->
    ordered_par_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros. eapply ordered_par_trace_refines_erased_stmt; eauto.
Qed.

Lemma ordered_loop_semantics_refines_erased :
  forall s env mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt s ->
    ordered_loop_semantics s env mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros s env mem1 mem2 Hna Hsafe [tr [Htrace Hsem]].
  eapply ordered_par_trace_refines_erased; eauto.
Qed.

Lemma semantics_refines_erased :
  forall p mem1 mem2,
    trace_safe p ->
    ordered_semantics p mem1 mem2 ->
    exists mem2',
      BaseLoop.semantics (erase_parallel p) mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros [[s ctxt] vars] mem1 mem2 Hsafe Hsem.
  inversion Hsem as [loop_ext loop ctxt' vars' env mem1' mem2' Heq Hcompat Hna Hinit Hloop];
    subst.
  inversion Heq; subst.
  simpl in Hsafe.
  destruct
    (ordered_loop_semantics_refines_erased
       loop env mem1 mem2 Hna Hsafe Hloop)
    as [mem2'' [Hloop' Heq_loop]].
  exists mem2''.
  split.
  - econstructor; eauto.
    reflexivity.
  - exact Heq_loop.
Qed.

(** Legacy wrapper for proofs that still establish the stronger invariant.
    Checked endpoints should prefer [semantics_refines_erased] with a
    trace-specific [ordered_semantics] derivation. *)
Lemma semantics_refines_erased_global :
  forall p mem1 mem2,
    trace_safe p ->
    parallel_families_ordered p ->
    semantics p mem1 mem2 ->
    exists mem2',
      BaseLoop.semantics (erase_parallel p) mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros p mem1 mem2 Hsafe Hglobal Hsem.
  eapply semantics_refines_erased.
  - exact Hsafe.
  - eapply ordered_semantics_of_global; eauto.
Qed.

(** Metadata-preserving singleton cleanup for annotated parallel loops. *)
Fixpoint expr_eqb (e1 e2 : BaseLoop.expr) : bool :=
  match e1, e2 with
  | BaseLoop.Constant z1, BaseLoop.Constant z2 => Z.eqb z1 z2
  | BaseLoop.Sum a1 b1, BaseLoop.Sum a2 b2 =>
      expr_eqb a1 a2 && expr_eqb b1 b2
  | BaseLoop.Mult k1 e1, BaseLoop.Mult k2 e2 =>
      Z.eqb k1 k2 && expr_eqb e1 e2
  | BaseLoop.Div e1 k1, BaseLoop.Div e2 k2 =>
      expr_eqb e1 e2 && Z.eqb k1 k2
  | BaseLoop.Mod e1 k1, BaseLoop.Mod e2 k2 =>
      expr_eqb e1 e2 && Z.eqb k1 k2
  | BaseLoop.Var n1, BaseLoop.Var n2 => Nat.eqb n1 n2
  | BaseLoop.Max a1 b1, BaseLoop.Max a2 b2 =>
      expr_eqb a1 a2 && expr_eqb b1 b2
  | BaseLoop.Min a1 b1, BaseLoop.Min a2 b2 =>
      expr_eqb a1 a2 && expr_eqb b1 b2
  | _, _ => false
  end.

Lemma expr_eqb_correct :
  forall e1 e2,
    expr_eqb e1 e2 = true ->
    forall env, BaseLoop.eval_expr env e1 = BaseLoop.eval_expr env e2.
Proof.
  induction e1; destruct e2; simpl; try discriminate; intros Heq env;
    try reflexivity.
  - apply Z.eqb_eq in Heq. subst. reflexivity.
  - apply andb_true_iff in Heq as [Ha Hb].
    rewrite (IHe1_1 _ Ha env), (IHe1_2 _ Hb env). reflexivity.
  - apply andb_true_iff in Heq as [Hk He].
    apply Z.eqb_eq in Hk. subst. rewrite (IHe1 _ He env). reflexivity.
  - apply andb_true_iff in Heq as [He Hk].
    apply Z.eqb_eq in Hk. subst. rewrite (IHe1 _ He env). reflexivity.
  - apply andb_true_iff in Heq as [He Hk].
    apply Z.eqb_eq in Hk. subst. rewrite (IHe1 _ He env). reflexivity.
  - apply Nat.eqb_eq in Heq. subst. reflexivity.
  - apply andb_true_iff in Heq as [Ha Hb].
    rewrite (IHe1_1 _ Ha env), (IHe1_2 _ Hb env). reflexivity.
  - apply andb_true_iff in Heq as [Ha Hb].
    rewrite (IHe1_1 _ Ha env), (IHe1_2 _ Hb env). reflexivity.
Qed.

Fixpoint lift_expr (e : BaseLoop.expr) : BaseLoop.expr :=
  match e with
  | BaseLoop.Constant c => BaseLoop.Constant c
  | BaseLoop.Sum e1 e2 => BaseLoop.Sum (lift_expr e1) (lift_expr e2)
  | BaseLoop.Mult k e1 => BaseLoop.Mult k (lift_expr e1)
  | BaseLoop.Div e1 k => BaseLoop.Div (lift_expr e1) k
  | BaseLoop.Mod e1 k => BaseLoop.Mod (lift_expr e1) k
  | BaseLoop.Var n => BaseLoop.Var (S n)
  | BaseLoop.Max e1 e2 => BaseLoop.Max (lift_expr e1) (lift_expr e2)
  | BaseLoop.Min e1 e2 => BaseLoop.Min (lift_expr e1) (lift_expr e2)
  end.

Fixpoint subst_expr_at
    (k : nat) (rep : BaseLoop.expr) (e : BaseLoop.expr) : BaseLoop.expr :=
  match e with
  | BaseLoop.Constant c => BaseLoop.Constant c
  | BaseLoop.Sum e1 e2 =>
      BaseLoop.Sum (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | BaseLoop.Mult n e1 => BaseLoop.Mult n (subst_expr_at k rep e1)
  | BaseLoop.Div e1 n => BaseLoop.Div (subst_expr_at k rep e1) n
  | BaseLoop.Mod e1 n => BaseLoop.Mod (subst_expr_at k rep e1) n
  | BaseLoop.Var n =>
      if Nat.ltb n k then BaseLoop.Var n
      else if Nat.eqb n k then rep
      else BaseLoop.Var (Nat.pred n)
  | BaseLoop.Max e1 e2 =>
      BaseLoop.Max (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | BaseLoop.Min e1 e2 =>
      BaseLoop.Min (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  end.

Fixpoint subst_test_at
    (k : nat) (rep : BaseLoop.expr) (t : BaseLoop.test) : BaseLoop.test :=
  match t with
  | BaseLoop.LE e1 e2 =>
      BaseLoop.LE (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | BaseLoop.EQ e1 e2 =>
      BaseLoop.EQ (subst_expr_at k rep e1) (subst_expr_at k rep e2)
  | BaseLoop.And t1 t2 =>
      BaseLoop.And (subst_test_at k rep t1) (subst_test_at k rep t2)
  | BaseLoop.Or t1 t2 =>
      BaseLoop.Or (subst_test_at k rep t1) (subst_test_at k rep t2)
  | BaseLoop.Not t1 => BaseLoop.Not (subst_test_at k rep t1)
  | BaseLoop.TConstantTest b => BaseLoop.TConstantTest b
  end.

Lemma nth_insert_middle :
  forall (A : Type) pre suf (x d : A),
    nth (length pre) (pre ++ x :: suf) d = x.
Proof.
  induction pre; intros; simpl; auto.
Qed.

Lemma nth_insert_before :
  forall (A : Type) pre suf (x d : A) n,
    (n < length pre)%nat ->
    nth n (pre ++ x :: suf) d = nth n (pre ++ suf) d.
Proof.
  induction pre; intros; simpl in *; [lia|].
  destruct n; simpl; auto. apply IHpre. lia.
Qed.

Lemma nth_insert_after :
  forall (A : Type) pre suf (x d : A) n,
    (length pre < n)%nat ->
    nth n (pre ++ x :: suf) d = nth (Nat.pred n) (pre ++ suf) d.
Proof.
  induction pre; intros; simpl in *.
  - destruct n; [lia|]. reflexivity.
  - destruct n as [|n']; [lia|].
    destruct n' as [|m]; [lia|]. simpl. apply IHpre. lia.
Qed.

Lemma lift_expr_correct :
  forall env x e,
    BaseLoop.eval_expr (x :: env) (lift_expr e) =
    BaseLoop.eval_expr env e.
Proof.
  induction e; simpl; intros; try reflexivity;
    try rewrite IHe; try rewrite IHe1, IHe2; reflexivity.
Qed.

Lemma subst_expr_at_correct :
  forall pre suf rep e,
    BaseLoop.eval_expr (pre ++ suf)
      (subst_expr_at (length pre) rep e) =
    BaseLoop.eval_expr
      (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) e.
Proof.
  induction e; intros; simpl; try reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - destruct (Nat.ltb n (length pre)) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. rewrite nth_insert_before; auto.
    + destruct (Nat.eqb n (length pre)) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst. rewrite nth_insert_middle. reflexivity.
      * apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
        rewrite nth_insert_after; [reflexivity|lia].
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma subst_expr_list_at_correct :
  forall pre suf rep es,
    map (BaseLoop.eval_expr (pre ++ suf))
      (map (subst_expr_at (length pre) rep) es) =
    map
      (BaseLoop.eval_expr
        (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf)) es.
Proof.
  intros. rewrite map_map. apply map_ext. intro e.
  apply subst_expr_at_correct.
Qed.

Lemma subst_test_at_correct :
  forall pre suf rep tst,
    BaseLoop.eval_test (pre ++ suf)
      (subst_test_at (length pre) rep tst) =
    BaseLoop.eval_test
      (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tst.
Proof.
  induction tst; intros; simpl; try reflexivity.
  - rewrite !subst_expr_at_correct. reflexivity.
  - rewrite !subst_expr_at_correct. reflexivity.
  - rewrite IHtst1, IHtst2. reflexivity.
  - rewrite IHtst1, IHtst2. reflexivity.
  - rewrite IHtst. reflexivity.
Qed.

Definition point_sema_equiv
    (p1 p2 : InstrPoint) : Prop :=
  forall st1 st2,
    ILSema.instr_point_sema p1 st1 st2 <->
    ILSema.instr_point_sema p2 st1 st2.

Lemma point_sema_equiv_refl :
  forall p, point_sema_equiv p p.
Proof.
  intros p st1 st2. reflexivity.
Qed.

Lemma point_sema_equiv_trans :
  forall p1 p2 p3,
    point_sema_equiv p1 p2 ->
    point_sema_equiv p2 p3 ->
    point_sema_equiv p1 p3.
Proof.
  intros p1 p2 p3 H12 H23 st1 st2.
  specialize (H12 st1 st2).
  specialize (H23 st1 st2).
  tauto.
Qed.

Lemma Forall2_point_sema_equiv_trans :
  forall xs ys zs,
    Forall2 point_sema_equiv xs ys ->
    Forall2 point_sema_equiv ys zs ->
    Forall2 point_sema_equiv xs zs.
Proof.
  intros xs ys zs Hxy.
  revert zs.
  induction Hxy; intros zs Hyz; inversion Hyz; subst.
  - constructor.
  - constructor.
    + eapply point_sema_equiv_trans; eauto.
    + eapply IHHxy; eauto.
Qed.

Lemma instr_point_list_semantics_equiv :
  forall tr1 tr2 st1 st2,
    Forall2 point_sema_equiv tr1 tr2 ->
    ILSema.instr_point_list_semantics tr1 st1 st2 ->
    ILSema.instr_point_list_semantics tr2 st1 st2.
Proof.
  intros tr1 tr2 st1 st2 Hrel.
  revert st1 st2.
  induction Hrel; intros st1 st2 Hsem.
  - inversion Hsem; subst. constructor. assumption.
  - inversion Hsem as [|st1' stmid st2' ip il Hip Htail]; subst.
    econstructor.
    + apply (proj1 (H st1 stmid)). exact Hip.
    + eapply IHHrel. exact Htail.
Qed.

Fixpoint subst_stmt_at
    (k : nat) (rep : BaseLoop.expr) (s : stmt) : stmt :=
  match s with
  | Loop mode od lb ub body =>
      Loop mode od
        (subst_expr_at k rep lb)
        (subst_expr_at k rep ub)
        (subst_stmt_at (S k) (lift_expr rep) body)
  | Instr i es =>
      Instr i (map (subst_expr_at k rep) es)
  | Seq ss => Seq (subst_stmts_at k rep ss)
  | Guard tst body =>
      Guard
        (subst_test_at k rep tst)
        (subst_stmt_at k rep body)
  end
with subst_stmts_at
    (k : nat) (rep : BaseLoop.expr) (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' =>
      SCons (subst_stmt_at k rep s) (subst_stmts_at k rep ss')
  end.

Fixpoint singleton_elim_stmt (s : stmt) : stmt :=
  match s with
  | Loop mode od lb ub body =>
      let body' := singleton_elim_stmt body in
      match mode with
      | SeqMode =>
          if expr_eqb
               ub (BaseLoop.make_sum lb (BaseLoop.Constant 1))
          then subst_stmt_at 0 lb body'
          else Loop SeqMode od lb ub body'
      | ParMode => Loop ParMode od lb ub body'
      | VecMode => Loop VecMode od lb ub body'
      end
  | Instr i es => Instr i es
  | Seq ss => Seq (singleton_elim_stmts ss)
  | Guard tst body => Guard tst (singleton_elim_stmt body)
  end
with singleton_elim_stmts (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' =>
      SCons (singleton_elim_stmt s) (singleton_elim_stmts ss')
  end.

Definition cleanup (p : t) : t :=
  let '((s, ctxt), vars) := p in
  ((singleton_elim_stmt s, ctxt), vars).

Lemma expr_to_aff_subst_inv :
  forall e k rep aff,
    BaseLoop.expr_to_aff (subst_expr_at k rep e) = Okk aff ->
    exists aff0, BaseLoop.expr_to_aff e = Okk aff0.
Proof.
  induction e; intros k rep aff Haff; simpl in Haff.
  - eexists. reflexivity.
  - destruct (BaseLoop.expr_to_aff (subst_expr_at k rep e1))
      as [[a1 c1]|] eqn:H1; try discriminate.
    destruct (BaseLoop.expr_to_aff (subst_expr_at k rep e2))
      as [[a2 c2]|] eqn:H2; try discriminate.
    destruct (IHe1 _ _ _ H1) as [[a1' c1'] H1'].
    destruct (IHe2 _ _ _ H2) as [[a2' c2'] H2'].
    exists (add_vector a1' a2', c1' + c2').
    simpl. now rewrite H1', H2'.
  - destruct (BaseLoop.expr_to_aff (subst_expr_at k rep e))
      as [[a c]|] eqn:He; try discriminate.
    destruct (IHe _ _ _ He) as [[a' c'] He'].
    exists (mult_vector z a', z * c').
    simpl. now rewrite He'.
  - discriminate.
  - discriminate.
  - destruct (Nat.ltb n k); [|destruct (Nat.eqb n k)];
      eexists; reflexivity.
  - discriminate.
  - discriminate.
Qed.

Lemma exprlist_to_aff_subst_inv :
  forall es k rep affs,
    BaseLoop.exprlist_to_aff (map (subst_expr_at k rep) es) =
      Okk affs ->
    exists affs0, BaseLoop.exprlist_to_aff es = Okk affs0.
Proof.
  induction es as [|e es IH]; intros k rep affs Haff; simpl in Haff.
  - eexists. reflexivity.
  - destruct (BaseLoop.expr_to_aff (subst_expr_at k rep e))
      as [aff|] eqn:He; try discriminate.
    destruct (BaseLoop.exprlist_to_aff
      (map (subst_expr_at k rep) es))
      as [rest|] eqn:Hrest; try discriminate.
    destruct (expr_to_aff_subst_inv _ _ _ _ He) as [aff0 He0].
    destruct (IH _ _ _ Hrest) as [rest0 Hrest0].
    exists (aff0 :: rest0).
    simpl. now rewrite He0, Hrest0.
Qed.

Scheme p_stmt_mutind := Induction for stmt Sort Prop
with p_stmts_mutind := Induction for stmt_list Sort Prop.
Combined Scheme p_stmt_stmts_mutind from p_stmt_mutind, p_stmts_mutind.

Definition subst_safe_inv_stmt_goal (s : stmt) : Prop :=
  forall k rep,
    trace_safe_stmt (subst_stmt_at k rep s) ->
    trace_safe_stmt s.

Definition subst_safe_inv_stmts_goal (ss : stmt_list) : Prop :=
  forall k rep,
    trace_safe_stmts (subst_stmts_at k rep ss) ->
    trace_safe_stmts ss.

Lemma subst_trace_safe_inv_mutual :
  (forall s, subst_safe_inv_stmt_goal s) /\
  (forall ss, subst_safe_inv_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold subst_safe_inv_stmt_goal, subst_safe_inv_stmts_goal.
  - intros mode od lb ub body IH k rep Hsafe.
    simpl in Hsafe |- *. eapply IH; eauto.
  - intros i es k rep Hsafe. simpl in *.
    destruct Hsafe as [affs Haff].
    destruct (exprlist_to_aff_subst_inv _ _ _ _ Haff) as [affs0 Haff0].
    exists affs0. exact Haff0.
  - intros ss IH k rep Hsafe. simpl in *. eapply IH; eauto.
  - intros tst body IH k rep Hsafe. simpl in *. eapply IH; eauto.
  - intros k rep Hsafe. exact I.
  - intros s IHs ss IHss k rep Hsafe. simpl in *.
    destruct Hsafe as [Hs Hss]. split; [eapply IHs|eapply IHss]; eauto.
Qed.

Lemma subst_trace_safe_stmt_inv :
  forall s k rep,
    trace_safe_stmt (subst_stmt_at k rep s) ->
    trace_safe_stmt s.
Proof.
  exact (proj1 subst_trace_safe_inv_mutual).
Qed.

Definition cleanup_safe_inv_stmt_goal (s : stmt) : Prop :=
  trace_safe_stmt (singleton_elim_stmt s) ->
  trace_safe_stmt s.

Definition cleanup_safe_inv_stmts_goal (ss : stmt_list) : Prop :=
  trace_safe_stmts (singleton_elim_stmts ss) ->
  trace_safe_stmts ss.

Lemma cleanup_trace_safe_inv_mutual :
  (forall s, cleanup_safe_inv_stmt_goal s) /\
  (forall ss, cleanup_safe_inv_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold cleanup_safe_inv_stmt_goal, cleanup_safe_inv_stmts_goal.
  - intros mode od lb ub body IH Hsafe.
    destruct mode; simpl in Hsafe |- *.
    + destruct (expr_eqb ub
        (BaseLoop.make_sum lb (BaseLoop.Constant 1))) eqn:Hsingle.
      * apply IH. eapply subst_trace_safe_stmt_inv. exact Hsafe.
      * apply IH. exact Hsafe.
    + apply IH. exact Hsafe.
    + apply IH. exact Hsafe.
  - intros i es Hsafe. exact Hsafe.
  - intros ss IH Hsafe. simpl in Hsafe |- *. apply IH. exact Hsafe.
  - intros tst body IH Hsafe. simpl in Hsafe |- *. apply IH. exact Hsafe.
  - intros Hsafe. exact I.
  - intros s IHs ss IHss Hsafe. simpl in Hsafe |- *.
    destruct Hsafe as [Hs Hss]. split; [apply IHs|apply IHss]; assumption.
Qed.

Lemma cleanup_trace_safe_inv :
  forall p,
    trace_safe (cleanup p) ->
    trace_safe p.
Proof.
  intros [[s ctxt] vars] Hsafe.
  exact ((proj1 cleanup_trace_safe_inv_mutual) s Hsafe).
Qed.

Lemma mk_instr_point_subst_equiv :
  forall pre suf rep i es aff_sub aff_orig,
    BaseLoop.exprlist_to_aff
      (map (subst_expr_at (length pre) rep) es) =
      Okk aff_sub ->
    BaseLoop.exprlist_to_aff es = Okk aff_orig ->
    point_sema_equiv
      (BaseLoop.mk_instr_point i
        (map (subst_expr_at (length pre) rep) es)
        (pre ++ suf))
      (BaseLoop.mk_instr_point i es
        (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf)).
Proof.
  intros pre suf rep i es aff_sub aff_orig Hsub Horig st1 st2.
  pose proof
    (BaseLoop.exprlist_to_aff_correct
       (map (subst_expr_at (length pre) rep) es)
       (pre ++ suf) aff_sub Hsub) as Hsub_eval.
  pose proof
    (BaseLoop.exprlist_to_aff_correct es
       (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf)
       aff_orig Horig) as Horig_eval.
  pose proof
    (subst_expr_list_at_correct pre suf rep es) as Heval.
  assert (Hargs :
    affine_product aff_sub (pre ++ suf) =
    affine_product aff_orig
      (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf)).
  {
    rewrite <- Hsub_eval, <- Horig_eval. exact Heval.
  }
  unfold BaseLoop.mk_instr_point.
  rewrite Hsub, Horig. simpl.
  split; intro Hsem; inversion Hsem as [wcs rcs Hstep]; subst;
    econstructor; simpl in *.
  - rewrite <- Hargs. exact Hstep.
  - rewrite Hargs. exact Hstep.
Qed.

Lemma Forall2_concat_point_sema_equiv :
  forall trs1 trs2,
    Forall2 (Forall2 point_sema_equiv) trs1 trs2 ->
    Forall2 point_sema_equiv (concat trs1) (concat trs2).
Proof.
  intros trs1 trs2 Hrel.
  induction Hrel; simpl.
  - constructor.
  - apply Forall2_app; assumption.
Qed.

Lemma Forall2_split_cons_left :
  forall A B (R : A -> B -> Prop) pre x post ys,
    Forall2 R (pre ++ x :: post) ys ->
    exists pre' y post',
      ys = pre' ++ y :: post' /\
      Forall2 R pre pre' /\
      R x y /\
      Forall2 R post post'.
Proof.
  intros A B R pre.
  induction pre as [|a pre IH]; intros x post ys Hrel.
  - simpl in Hrel.
    inversion Hrel as [|? y ? ys' Hxy Htail]; subst.
    exists (nil : list B).
    exists y.
    exists ys'.
    repeat split; auto.
  - simpl in Hrel.
    inversion Hrel as [|? y ? ys' Hay Htail]; subst.
    destruct (IH _ _ _ Htail)
      as [pre' [y' [post' [Hys [Hpre [Hxy Hpost]]]]]].
    exists (y :: pre').
    exists y'.
    exists post'.
    subst ys'. simpl. repeat split; auto.
Qed.

Lemma interleave_family_point_equiv :
  forall trs1 out1 trs2,
    interleave_family trs1 out1 ->
    Forall2 (Forall2 point_sema_equiv) trs1 trs2 ->
    exists out2,
      interleave_family trs2 out2 /\
      Forall2 point_sema_equiv out1 out2.
Proof.
  intros trs1 out1 trs2 Hinter.
  revert trs2.
  induction Hinter; intros trs2 Hfamilies.
  - inversion Hfamilies; subst.
    exists (nil : list InstrPoint). split; constructor.
  - inversion Hfamilies as [|? tr2 ? trs2' Hnil Hrest]; subst.
    inversion Hnil; subst.
    destruct (IHHinter _ Hrest) as [out2 [Hinter2 Hout]].
    exists out2. split; [constructor; exact Hinter2|exact Hout].
  - destruct
      (Forall2_split_cons_left
        _ _ (Forall2 point_sema_equiv)
        pre (x :: xs) post trs2 Hfamilies)
      as [pre' [tr' [post' [Htrs2 [Hpre [Htr Hpost]]]]]].
    inversion Htr; subst.
    assert (Hreduced :
      Forall2 (Forall2 point_sema_equiv)
        (pre ++ xs :: post) (pre' ++ l' :: post')).
    {
      apply Forall2_app; [exact Hpre|].
      constructor; assumption.
    }
    destruct (IHHinter _ Hreduced) as [out2 [Hinter2 Hout]].
    exists (y :: out2). split.
    + constructor. exact Hinter2.
    + constructor; assumption.
Qed.

Lemma Forall2_trace_refine :
  forall A B C (P : A -> B -> Prop) (Q : A -> C -> Prop)
      (R : B -> C -> Prop) xs ys,
    Forall2 P xs ys ->
    (forall x y, P x y -> exists z, Q x z /\ R y z) ->
    exists zs, Forall2 Q xs zs /\ Forall2 R ys zs.
Proof.
  intros A B C P Q R xs ys Hfor Hstep.
  induction Hfor.
  - exists (nil : list C). split; constructor.
  - destruct (Hstep _ _ H) as [z [HQ HR]].
    destruct IHHfor as [zs [HQs HRs]].
    exists (z :: zs). split; constructor; assumption.
Qed.

Definition subst_trace_stmt_goal (s : stmt) : Prop :=
  forall pre suf rep tr,
    trace_safe_stmt s ->
    trace_safe_stmt (subst_stmt_at (length pre) rep s) ->
    par_trace
      (subst_stmt_at (length pre) rep s) (pre ++ suf) tr ->
    exists tr0,
      par_trace s
        (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tr0 /\
      Forall2 point_sema_equiv tr tr0.

Definition subst_trace_stmts_goal (ss : stmt_list) : Prop :=
  forall pre suf rep tr,
    trace_safe_stmts ss ->
    trace_safe_stmts (subst_stmts_at (length pre) rep ss) ->
    par_traces
      (subst_stmts_at (length pre) rep ss) (pre ++ suf) tr ->
    exists tr0,
      par_traces ss
        (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tr0 /\
      Forall2 point_sema_equiv tr tr0.

Lemma subst_par_trace_refine_mutual :
  (forall s, subst_trace_stmt_goal s) /\
  (forall ss, subst_trace_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold subst_trace_stmt_goal, subst_trace_stmts_goal.
  - intros mode od lb ub body IH pre suf rep tr Hsafe Hsafe_sub Htrace.
    simpl in Hsafe, Hsafe_sub, Htrace.
    destruct mode.
    + inversion Htrace as
          [| | | |
           od0 lb0 ub0 body0 env0 zs trs' tr'
             Hrange Htraces Hconcat
           | |]; subst.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace
            (subst_stmt_at (S (length pre)) (lift_expr rep) body)
            (z :: pre ++ suf) tri)
          (fun z tri => par_trace body
            (z :: pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz.
        specialize (IH (z :: pre) suf (lift_expr rep) tri
          Hsafe Hsafe_sub).
        simpl in IH.
        rewrite lift_expr_correct in IH.
        apply IH. exact Hz.
      }
      exists (concat trs0). split.
      * eapply PTLoopSeq with
            (zs := Zrange
              (BaseLoop.eval_expr (pre ++ suf)
                (subst_expr_at (length pre) rep lb))
              (BaseLoop.eval_expr (pre ++ suf)
                (subst_expr_at (length pre) rep ub)))
            (trs := trs0).
        -- f_equal; apply subst_expr_at_correct.
        -- exact Htraces0.
        -- reflexivity.
      * eapply Forall2_concat_point_sema_equiv. exact Hrels.
    + inversion Htrace as
          [| | | | | |
           d0 lb0 ub0 body0 env0 zs trs' tr'
             Hrange Htraces Hinter]; subst.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace
            (subst_stmt_at (S (length pre)) (lift_expr rep) body)
            (z :: pre ++ suf) tri)
          (fun z tri => par_trace body
            (z :: pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz.
        specialize (IH (z :: pre) suf (lift_expr rep) tri
          Hsafe Hsafe_sub).
        simpl in IH.
        rewrite lift_expr_correct in IH.
        apply IH. exact Hz.
      }
      destruct (interleave_family_point_equiv _ _ _ Hinter Hrels)
        as [tr0 [Hinter0 Hrel0]].
      exists tr0. split.
      * eapply PTLoopPar with
            (zs := Zrange
              (BaseLoop.eval_expr (pre ++ suf)
                (subst_expr_at (length pre) rep lb))
              (BaseLoop.eval_expr (pre ++ suf)
                (subst_expr_at (length pre) rep ub)))
            (trs := trs0).
        -- f_equal; apply subst_expr_at_correct.
        -- exact Htraces0.
        -- exact Hinter0.
      * exact Hrel0.
    + inversion Htrace as
          [| | | | |
           od0 lb0 ub0 body0 env0 zs trs' tr'
             Hrange Htraces Hconcat
           |]; subst.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace
            (subst_stmt_at (S (length pre)) (lift_expr rep) body)
            (z :: pre ++ suf) tri)
          (fun z tri => par_trace body
            (z :: pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz.
        specialize (IH (z :: pre) suf (lift_expr rep) tri
          Hsafe Hsafe_sub).
        simpl in IH.
        rewrite lift_expr_correct in IH.
        apply IH. exact Hz.
      }
      exists (concat trs0). split.
      * eapply PTLoopVec with
            (zs := Zrange
              (BaseLoop.eval_expr (pre ++ suf)
                (subst_expr_at (length pre) rep lb))
              (BaseLoop.eval_expr (pre ++ suf)
                (subst_expr_at (length pre) rep ub)))
            (trs := trs0).
        -- f_equal; apply subst_expr_at_correct.
        -- exact Htraces0.
        -- reflexivity.
      * eapply Forall2_concat_point_sema_equiv. exact Hrels.
  - intros i es pre suf rep tr Hsafe Hsafe_sub Htrace.
    simpl in Hsafe, Hsafe_sub, Htrace.
    inversion Htrace; subst.
    destruct Hsafe as [aff_orig Horig].
    destruct Hsafe_sub as [aff_sub Hsub].
    exists [BaseLoop.mk_instr_point i es
      (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf)].
    split.
    + constructor.
    + constructor.
      * eapply mk_instr_point_subst_equiv; eauto.
      * constructor.
  - intros ss IH pre suf rep tr Hsafe Hsafe_sub Htrace.
    simpl in *.
    inversion Htrace as [|env0 sts0 tr0 Htrs| | | | |]; subst.
    destruct (IH pre suf rep tr Hsafe Hsafe_sub Htrs) as [tr0 [Ht Hr]].
    exists tr0. split; [constructor; exact Ht|exact Hr].
  - intros tst body IH pre suf rep tr Hsafe Hsafe_sub Htrace.
    simpl in Hsafe, Hsafe_sub, Htrace.
    inversion Htrace as
        [| |
         env0 tst0 body0 tr0 Htest Hbody
         | env0 tst0 body0 Htest
         | | |]; subst.
    + destruct (IH pre suf rep tr Hsafe Hsafe_sub Hbody) as [tr0 [Ht Hr]].
      exists tr0. split.
      * eapply PTGuardTrue.
        -- rewrite <- (subst_test_at_correct pre suf rep tst). exact Htest.
        -- exact Ht.
      * exact Hr.
    + exists (nil : list InstrPoint). split.
      * eapply PTGuardFalse.
        rewrite <- (subst_test_at_correct pre suf rep tst). exact Htest.
      * constructor.
  - intros pre suf rep tr Hsafe Hsafe_sub Htrace.
    inversion Htrace; subst.
    exists (nil : list InstrPoint). split; constructor.
  - intros s IHs ss IHss pre suf rep tr Hsafe Hsafe_sub Htrace.
    simpl in Hsafe, Hsafe_sub.
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    destruct Hsafe_sub as [Hsafe_sub_s Hsafe_sub_ss].
    inversion Htrace as
        [|env0 st0 sts0 tr1 tr2 Htr1 Htr2]; subst.
    destruct (IHs pre suf rep tr1 Hsafe_s Hsafe_sub_s Htr1)
      as [tr1' [Ht1 Hr1]].
    destruct (IHss pre suf rep tr2 Hsafe_ss Hsafe_sub_ss Htr2)
      as [tr2' [Ht2 Hr2]].
    exists (tr1' ++ tr2'). split.
    + econstructor; eauto.
    + apply Forall2_app; assumption.
Qed.

Lemma subst_par_trace_refine :
  forall s pre suf rep tr,
    trace_safe_stmt s ->
    trace_safe_stmt (subst_stmt_at (length pre) rep s) ->
    par_trace
      (subst_stmt_at (length pre) rep s) (pre ++ suf) tr ->
    exists tr0,
      par_trace s
        (pre ++ BaseLoop.eval_expr (pre ++ suf) rep :: suf) tr0 /\
      Forall2 point_sema_equiv tr tr0.
Proof.
  exact (proj1 subst_par_trace_refine_mutual).
Qed.

Definition cleanup_trace_stmt_goal (s : stmt) : Prop :=
  forall env tr,
    trace_safe_stmt s ->
    trace_safe_stmt (singleton_elim_stmt s) ->
    par_trace (singleton_elim_stmt s) env tr ->
    exists tr0,
      par_trace s env tr0 /\
      Forall2 point_sema_equiv tr tr0.

Definition cleanup_trace_stmts_goal (ss : stmt_list) : Prop :=
  forall env tr,
    trace_safe_stmts ss ->
    trace_safe_stmts (singleton_elim_stmts ss) ->
    par_traces (singleton_elim_stmts ss) env tr ->
    exists tr0,
      par_traces ss env tr0 /\
      Forall2 point_sema_equiv tr tr0.

Lemma cleanup_par_trace_refine_mutual :
  (forall s, cleanup_trace_stmt_goal s) /\
  (forall ss, cleanup_trace_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold cleanup_trace_stmt_goal, cleanup_trace_stmts_goal.
  - intros mode od lb ub body IH env tr Hsafe Hsafe_clean Htrace.
    simpl in Hsafe.
    destruct mode.
    + simpl in Hsafe_clean, Htrace.
      destruct (expr_eqb ub
        (BaseLoop.make_sum lb (BaseLoop.Constant 1))) eqn:Hsingle.
      * pose proof
          (subst_trace_safe_stmt_inv
            (singleton_elim_stmt body) 0 lb Hsafe_clean)
          as Hsafe_body_clean.
        destruct
          (subst_par_trace_refine
            (singleton_elim_stmt body) [] env lb tr
            Hsafe_body_clean Hsafe_clean Htrace)
          as [tr_clean [Htrace_clean Hrel_clean]].
        simpl in Htrace_clean.
        destruct
          (IH (BaseLoop.eval_expr env lb :: env) tr_clean
            Hsafe Hsafe_body_clean Htrace_clean)
          as [tr_body [Htrace_body Hrel_body]].
        exists tr_body. split.
        -- eapply PTLoopSeq with
              (zs := [BaseLoop.eval_expr env lb])
              (trs := [tr_body]).
           ++ rewrite
                (expr_eqb_correct ub
                  (BaseLoop.make_sum lb (BaseLoop.Constant 1))
                  Hsingle env).
              rewrite BaseLoop.make_sum_correct. simpl.
              rewrite Zrange_single. reflexivity.
           ++ constructor; [exact Htrace_body|constructor].
           ++ simpl. rewrite app_nil_r. reflexivity.
        -- eapply Forall2_point_sema_equiv_trans; eauto.
      * inversion Htrace as
            [| | | |
             od0 lb0 ub0 body0 env0 zs trs' tr'
               Hrange Htraces Hconcat
             | |]; subst.
        destruct
          (Forall2_trace_refine
            _ _ _
            (fun z tri => par_trace
              (singleton_elim_stmt body) (z :: env) tri)
            (fun z tri => par_trace body (z :: env) tri)
            (Forall2 point_sema_equiv) _ _ Htraces)
          as [trs0 [Htraces0 Hrels]].
        {
          intros z tri Hz.
          eapply IH; eauto.
        }
        exists (concat trs0). split.
        -- eapply PTLoopSeq with
              (zs := Zrange
                (BaseLoop.eval_expr env lb)
                (BaseLoop.eval_expr env ub))
              (trs := trs0); eauto.
        -- eapply Forall2_concat_point_sema_equiv. exact Hrels.
    + simpl in Hsafe_clean, Htrace.
      inversion Htrace as
          [| | | | | |
           d0 lb0 ub0 body0 env0 zs trs' tr'
             Hrange Htraces Hinter]; subst.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace
            (singleton_elim_stmt body) (z :: env) tri)
          (fun z tri => par_trace body (z :: env) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz.
        eapply IH; eauto.
      }
      destruct (interleave_family_point_equiv _ _ _ Hinter Hrels)
        as [tr0 [Hinter0 Hrel0]].
      exists tr0. split.
      * eapply PTLoopPar with
            (zs := Zrange
              (BaseLoop.eval_expr env lb)
              (BaseLoop.eval_expr env ub))
            (trs := trs0); eauto.
      * exact Hrel0.
    + simpl in Hsafe_clean, Htrace.
      inversion Htrace as
          [| | | | |
           od0 lb0 ub0 body0 env0 zs trs' tr'
             Hrange Htraces Hconcat
           |]; subst.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace
            (singleton_elim_stmt body) (z :: env) tri)
          (fun z tri => par_trace body (z :: env) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz.
        eapply IH; eauto.
      }
      exists (concat trs0). split.
      * eapply PTLoopVec with
            (zs := Zrange
              (BaseLoop.eval_expr env lb)
              (BaseLoop.eval_expr env ub))
            (trs := trs0); eauto.
      * eapply Forall2_concat_point_sema_equiv. exact Hrels.
  - intros i es env tr Hsafe Hsafe_clean Htrace.
    simpl in Htrace. exists tr. split; [exact Htrace|].
    clear Htrace Hsafe Hsafe_clean.
    induction tr as [|ip tr IHtr].
    + constructor.
    + constructor; [apply point_sema_equiv_refl|exact IHtr].
  - intros ss IH env tr Hsafe Hsafe_clean Htrace.
    simpl in Hsafe, Hsafe_clean, Htrace.
    inversion Htrace as [|env0 sts0 tr0 Htrs| | | | |]; subst.
    destruct (IH env tr Hsafe Hsafe_clean Htrs) as [tr0 [Ht Hr]].
    exists tr0. split; [constructor; exact Ht|exact Hr].
  - intros tst body IH env tr Hsafe Hsafe_clean Htrace.
    simpl in Hsafe, Hsafe_clean, Htrace.
    inversion Htrace as
        [| |
         env0 tst0 body0 tr0 Htest Hbody
         | env0 tst0 body0 Htest
         | | |]; subst.
    + destruct (IH env tr Hsafe Hsafe_clean Hbody) as [tr0 [Ht Hr]].
      exists tr0. split.
      * eapply PTGuardTrue; [exact Htest|exact Ht].
      * exact Hr.
    + exists (nil : list InstrPoint). split.
      * eapply PTGuardFalse. exact Htest.
      * constructor.
  - intros env tr Hsafe Hsafe_clean Htrace.
    inversion Htrace; subst.
    exists (nil : list InstrPoint). split; constructor.
  - intros s IHs ss IHss env tr Hsafe Hsafe_clean Htrace.
    simpl in Hsafe, Hsafe_clean.
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    destruct Hsafe_clean as [Hsafe_clean_s Hsafe_clean_ss].
    inversion Htrace as
        [|env0 st0 sts0 tr1 tr2 Htr1 Htr2]; subst.
    destruct (IHs env tr1 Hsafe_s Hsafe_clean_s Htr1)
      as [tr1' [Ht1 Hr1]].
    destruct (IHss env tr2 Hsafe_ss Hsafe_clean_ss Htr2)
      as [tr2' [Ht2 Hr2]].
    exists (tr1' ++ tr2'). split.
    + econstructor; eauto.
    + apply Forall2_app; assumption.
Qed.

Lemma cleanup_par_trace_refine :
  forall s env tr,
    trace_safe_stmt s ->
    trace_safe_stmt (singleton_elim_stmt s) ->
    par_trace (singleton_elim_stmt s) env tr ->
    exists tr0,
      par_trace s env tr0 /\
      Forall2 point_sema_equiv tr tr0.
Proof.
  exact (proj1 cleanup_par_trace_refine_mutual).
Qed.

Lemma cleanup_loop_semantics_refine :
  forall s env mem1 mem2,
    trace_safe_stmt s ->
    trace_safe_stmt (singleton_elim_stmt s) ->
    loop_semantics (singleton_elim_stmt s) env mem1 mem2 ->
    loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2 Hsafe Hsafe_clean [tr [Htrace Hsem]].
  destruct
    (cleanup_par_trace_refine s env tr Hsafe Hsafe_clean Htrace)
    as [tr0 [Htrace0 Hrel]].
  exists tr0. split; [exact Htrace0|].
  eapply instr_point_list_semantics_equiv; eauto.
Qed.

Theorem cleanup_semantics_refine :
  forall p mem1 mem2,
    trace_safe p ->
    trace_safe (cleanup p) ->
    semantics (cleanup p) mem1 mem2 ->
    semantics p mem1 mem2.
Proof.
  intros [[s ctxt] vars] mem1 mem2 Hsafe Hsafe_clean Hsem.
  inversion Hsem as
      [loop_ext loop ctxt' vars' env mem1' mem2'
       Heq Hcompat Hna Hinit Hloop]; subst.
  inversion Heq; subst.
  econstructor.
  - reflexivity.
  - exact Hcompat.
  - exact Hna.
  - exact Hinit.
  - eapply cleanup_loop_semantics_refine; eauto.
Qed.

(** This is the bridge needed by the checked pipeline: once the pre-clean
    annotated execution has its certificate-derived ordered proof, the cleaned
    execution inherits the existing erased-program refinement theorem. *)
Theorem cleanup_certified_refines_erased :
  forall p mem1 mem2,
    trace_safe p ->
    trace_safe (cleanup p) ->
    (semantics p mem1 mem2 ->
      ordered_semantics p mem1 mem2) ->
    semantics (cleanup p) mem1 mem2 ->
    exists mem2',
      BaseLoop.semantics (erase_parallel p) mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros p mem1 mem2 Hsafe Hsafe_clean Hcert Hclean.
  apply semantics_refines_erased; [exact Hsafe|].
  apply Hcert.
  eapply cleanup_semantics_refine; eauto.
Qed.

(** Full metadata-preserving cleanup.  This mirrors the ordinary loop cleanup
    pipeline while retaining the execution mode and origin of every surviving
    loop.  Only sequential singleton loops are eliminated. *)
Fixpoint collect_sum_norm (e : BaseLoop.expr) : list BaseLoop.expr * Z :=
  match e with
  | BaseLoop.Constant c => ([], c)
  | BaseLoop.Sum e1 e2 =>
      let '(ts1, c1) := collect_sum_norm e1 in
      let '(ts2, c2) := collect_sum_norm e2 in
      (ts1 ++ ts2, c1 + c2)
  | _ => ([e], 0)
  end.

Definition build_sum (terms : list BaseLoop.expr) (c : Z) : BaseLoop.expr :=
  fold_right BaseLoop.make_sum (BaseLoop.Constant c) terms.

Definition normalize_le (e1 e2 : BaseLoop.expr) : BaseLoop.test :=
  match e1, e2 with
  | BaseLoop.Mult k e, BaseLoop.Constant c =>
      if Z.eqb k (-1)
      then BaseLoop.make_le (BaseLoop.Constant (- c)) e
      else BaseLoop.make_le e1 e2
  | BaseLoop.Constant c, BaseLoop.Mult k e =>
      if Z.eqb k (-1)
      then BaseLoop.make_le e (BaseLoop.Constant (- c))
      else BaseLoop.make_le e1 e2
  | _, _ => BaseLoop.make_le e1 e2
  end.

Fixpoint simpl_expr (e : BaseLoop.expr) : BaseLoop.expr :=
  match e with
  | BaseLoop.Constant c => BaseLoop.Constant c
  | BaseLoop.Sum e1 e2 =>
      let e1' := simpl_expr e1 in
      let e2' := simpl_expr e2 in
      let '(terms, c) := collect_sum_norm (BaseLoop.Sum e1' e2') in
      build_sum terms c
  | BaseLoop.Mult k e1 => BaseLoop.make_mult k (simpl_expr e1)
  | BaseLoop.Div e1 k => BaseLoop.make_div (simpl_expr e1) k
  | BaseLoop.Mod e1 k => BaseLoop.make_mod (simpl_expr e1) k
  | BaseLoop.Var n => BaseLoop.Var n
  | BaseLoop.Max e1 e2 => BaseLoop.make_max (simpl_expr e1) (simpl_expr e2)
  | BaseLoop.Min e1 e2 => BaseLoop.make_min (simpl_expr e1) (simpl_expr e2)
  end.

Fixpoint simpl_test (t : BaseLoop.test) : BaseLoop.test :=
  match t with
  | BaseLoop.LE e1 e2 => normalize_le (simpl_expr e1) (simpl_expr e2)
  | BaseLoop.EQ e1 e2 => BaseLoop.make_eq (simpl_expr e1) (simpl_expr e2)
  | BaseLoop.And t1 t2 => BaseLoop.make_and (simpl_test t1) (simpl_test t2)
  | BaseLoop.Or t1 t2 => BaseLoop.make_or (simpl_test t1) (simpl_test t2)
  | BaseLoop.Not t1 => BaseLoop.make_not (simpl_test t1)
  | BaseLoop.TConstantTest b => BaseLoop.TConstantTest b
  end.

Fixpoint zsum (zs : list Z) : Z :=
  match zs with
  | [] => 0
  | z :: zs' => z + zsum zs'
  end.

Local Lemma build_sum_correct :
  forall env terms c,
    BaseLoop.eval_expr env (build_sum terms c) =
    zsum (map (BaseLoop.eval_expr env) terms) + c.
Proof.
  intros env terms c.
  induction terms as [|t ts IH]; simpl.
  - reflexivity.
  - rewrite BaseLoop.make_sum_correct, IH. lia.
Qed.

Local Lemma zsum_app :
  forall zs1 zs2,
    zsum (zs1 ++ zs2) = zsum zs1 + zsum zs2.
Proof.
  induction zs1; intros; simpl; [lia|]. rewrite IHzs1. lia.
Qed.

Local Lemma collect_sum_norm_correct :
  forall env e terms c,
    collect_sum_norm e = (terms, c) ->
    zsum (map (BaseLoop.eval_expr env) terms) + c =
    BaseLoop.eval_expr env e.
Proof.
  induction e; intros terms c Hcol; simpl in Hcol.
  - inversion Hcol; subst. reflexivity.
  - destruct (collect_sum_norm e1) as [ts1 c1] eqn:H1.
    destruct (collect_sum_norm e2) as [ts2 c2] eqn:H2.
    inversion Hcol; subst; clear Hcol.
    rewrite map_app, zsum_app.
    specialize (IHe1 ts1 c1 eq_refl).
    specialize (IHe2 ts2 c2 eq_refl).
    replace (zsum (map (BaseLoop.eval_expr env) ts1) +
             (zsum (map (BaseLoop.eval_expr env) ts2) + (c1 + c2)))
      with ((zsum (map (BaseLoop.eval_expr env) ts1) + c1) +
            (zsum (map (BaseLoop.eval_expr env) ts2) + c2)) by lia.
    assert (Hz1 :
      zsum (map (BaseLoop.eval_expr env) ts1) =
      BaseLoop.eval_expr env e1 - c1) by lia.
    assert (Hz2 :
      zsum (map (BaseLoop.eval_expr env) ts2) =
      BaseLoop.eval_expr env e2 - c2) by lia.
    rewrite Hz1, Hz2. simpl. lia.
  - inversion Hcol; subst; simpl; lia.
  - inversion Hcol; subst; simpl; lia.
  - inversion Hcol; subst; simpl; lia.
  - inversion Hcol; subst; simpl; lia.
  - inversion Hcol; subst; simpl; lia.
  - inversion Hcol; subst; simpl; lia.
Qed.

Local Lemma opp_leb_mult_m1 :
  forall x c, (- c <=? x) = (((-1) * x) <=? c).
Proof.
  intros x c.
  destruct (Z.leb_spec0 (-c) x);
    destruct (Z.leb_spec0 ((-1) * x) c); simpl; lia.
Qed.

Local Lemma leb_neg_rhs_mult_m1 :
  forall x c, (x <=? - c) = (c <=? ((-1) * x)).
Proof.
  intros x c.
  destruct (Z.leb_spec0 x (-c));
    destruct (Z.leb_spec0 c ((-1) * x)); simpl; lia.
Qed.

Local Lemma normalize_le_correct :
  forall env e1 e2,
    BaseLoop.eval_test env (normalize_le e1 e2) =
    BaseLoop.eval_test env (BaseLoop.LE e1 e2).
Proof.
  intros env e1 e2.
  unfold normalize_le.
  destruct e1 as
    [c1|a1 b1|kleft eleft|dleft kdleft|mleft kmleft|n1|
     max1l max1r|min1l min1r].
  - destruct e2 as
      [c2|a2 b2|kright eright|dright kdright|mright kmright|n2|
       max2l max2r|min2l min2r]; simpl; try reflexivity.
    destruct (Z.eqb kright (-1)) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct eright; simpl; rewrite leb_neg_rhs_mult_m1; reflexivity.
    + unfold BaseLoop.make_le. simpl. reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2 as
      [c2|a2 b2|kright eright|dright kdright|mright kmright|n2|
       max2l max2r|min2l min2r]; simpl; try reflexivity.
    destruct (Z.eqb kleft (-1)) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst.
      destruct eleft; simpl; rewrite opp_leb_mult_m1; reflexivity.
    + unfold BaseLoop.make_le. simpl. reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
  - destruct e2; simpl; reflexivity.
Qed.

Local Lemma simpl_expr_correct :
  forall env e,
    BaseLoop.eval_expr env (simpl_expr e) = BaseLoop.eval_expr env e.
Proof.
  induction e; simpl; intros; try reflexivity.
  - destruct (collect_sum_norm (BaseLoop.Sum (simpl_expr e1) (simpl_expr e2)))
      as [terms c] eqn:Hsc.
    change
      (BaseLoop.eval_expr env
        (let '(terms0, c0) :=
          collect_sum_norm (BaseLoop.Sum (simpl_expr e1) (simpl_expr e2))
         in build_sum terms0 c0) =
       BaseLoop.eval_expr env (BaseLoop.Sum e1 e2)).
    rewrite Hsc. simpl.
    pose proof
      (collect_sum_norm_correct env
        (BaseLoop.Sum (simpl_expr e1) (simpl_expr e2)) terms c Hsc)
      as Hnorm.
    simpl in Hnorm. rewrite IHe1, IHe2 in Hnorm.
    etransitivity; [apply build_sum_correct|exact Hnorm].
  - rewrite BaseLoop.make_mult_correct, IHe. reflexivity.
  - rewrite BaseLoop.make_div_correct, IHe. reflexivity.
  - rewrite BaseLoop.make_mod_correct, IHe. reflexivity.
  - rewrite BaseLoop.make_max_correct, IHe1, IHe2. reflexivity.
  - rewrite BaseLoop.make_min_correct, IHe1, IHe2. reflexivity.
Qed.

Local Lemma simpl_expr_list_correct :
  forall env es,
    map (BaseLoop.eval_expr env) (map simpl_expr es) =
    map (BaseLoop.eval_expr env) es.
Proof.
  intros env es. rewrite map_map. apply map_ext. apply simpl_expr_correct.
Qed.

Local Lemma simpl_test_correct :
  forall env t,
    BaseLoop.eval_test env (simpl_test t) = BaseLoop.eval_test env t.
Proof.
  intros env tst. unfold test in tst.
  induction tst; simpl; try reflexivity.
  - rewrite normalize_le_correct. simpl. rewrite !simpl_expr_correct. reflexivity.
  - rewrite BaseLoop.make_eq_correct. simpl. rewrite !simpl_expr_correct. reflexivity.
  - rewrite BaseLoop.make_and_correct, IHtst1, IHtst2. reflexivity.
  - rewrite BaseLoop.make_or_correct, IHtst1, IHtst2. reflexivity.
  - rewrite BaseLoop.make_not_correct, IHtst. reflexivity.
Qed.

Definition make_stmt_from_list (ss : stmt_list) : stmt :=
  match ss with
  | SNil => Seq SNil
  | SCons s SNil => s
  | _ => Seq ss
  end.

Fixpoint simplify_stmt (s : stmt) : stmt :=
  match s with
  | Loop mode od lb ub body =>
      Loop mode od
        (simpl_expr lb)
        (simpl_expr ub)
        (simplify_stmt body)
  | Instr i es =>
      Instr i (map simpl_expr es)
  | Seq ss => Seq (simplify_stmts ss)
  | Guard tst body =>
      Guard (simpl_test tst) (simplify_stmt body)
  end
with simplify_stmts (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' =>
      SCons (simplify_stmt s) (simplify_stmts ss')
  end.

Definition make_guard (tst : BaseLoop.test) (body : stmt) : stmt :=
  match tst with
  | BaseLoop.TConstantTest true => body
  | BaseLoop.TConstantTest false => Seq SNil
  | _ => Guard tst body
  end.

Fixpoint cleanup_stmt (s : stmt) : stmt :=
  match s with
  | Loop mode od lb ub body =>
      Loop mode od lb ub (cleanup_stmt body)
  | Instr i es => Instr i es
  | Seq ss => make_stmt_from_list (cleanup_stmts ss)
  | Guard tst body => make_guard tst (cleanup_stmt body)
  end
with cleanup_stmts (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' =>
      match cleanup_stmt s with
      | Seq SNil => cleanup_stmts ss'
      | s' => SCons s' (cleanup_stmts ss')
      end
  end.

Definition cleanup_stmt_pass (s : stmt) : stmt :=
  cleanup_stmt
    (simplify_stmt
      (singleton_elim_stmt
        (cleanup_stmt (simplify_stmt s)))).

Definition full_cleanup (p : t) : t :=
  let '((s, ctxt), vars) := p in
  ((cleanup_stmt_pass s, ctxt), vars).

Local Lemma Forall2_impl_same :
  forall A B (P Q : A -> B -> Prop) xs ys,
    (forall x y, P x y -> Q x y) ->
    Forall2 P xs ys ->
    Forall2 Q xs ys.
Proof.
  intros A B P Q xs ys Himpl Hfor.
  induction Hfor; constructor; auto.
Qed.

Local Lemma make_stmt_from_list_par_trace_reflect :
  forall ss env tr,
    par_trace (make_stmt_from_list ss) env tr ->
    par_trace (Seq ss) env tr.
Proof.
  intros ss env tr Htrace.
  destruct ss as [|s ss']; simpl in Htrace |- *.
  - exact Htrace.
  - destruct ss' as [|s' ss'']; simpl in Htrace |- *.
    + apply PTSeqStmt.
      replace tr with (tr ++ []) by apply app_nil_r.
      constructor; [exact Htrace|constructor].
    + exact Htrace.
Qed.

Local Lemma make_guard_par_trace_reflect :
  forall tst body env tr,
    par_trace (make_guard tst body) env tr ->
    par_trace (Guard tst body) env tr.
Proof.
  intros tst body env tr Htrace.
  destruct tst; simpl in Htrace |- *; try exact Htrace.
  destruct b.
  - eapply PTGuardTrue; [reflexivity|exact Htrace].
  - inversion Htrace as [|env0 ss tr0 Hnil| | | | |]; subst.
    inversion Hnil; subst.
    eapply PTGuardFalse. reflexivity.
Qed.

Local Definition structural_trace_stmt_goal (s : stmt) : Prop :=
  forall env tr,
    par_trace (cleanup_stmt s) env tr ->
    par_trace s env tr.

Local Definition structural_trace_stmts_goal (ss : stmt_list) : Prop :=
  forall env tr,
    par_traces (cleanup_stmts ss) env tr ->
    par_traces ss env tr.

Local Lemma cleanup_structural_par_trace_reflect_mutual :
  (forall s, structural_trace_stmt_goal s) /\
  (forall ss, structural_trace_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold structural_trace_stmt_goal, structural_trace_stmts_goal.
  - intros mode od lb ub body IH env tr Htrace.
    simpl in Htrace.
    destruct mode.
    + inversion Htrace as
          [| | | |
           od0 lb0 ub0 body0 env0 zs trs tr0 Hrange Htraces Hconcat
           | |]; subst.
      eapply PTLoopSeq with
        (zs := Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub))
        (trs := trs); [reflexivity| |reflexivity].
      eapply Forall2_impl_same; [|exact Htraces].
      intros z tri Htri. eapply IH. exact Htri.
    + inversion Htrace as
          [| | | | | |
           d0 lb0 ub0 body0 env0 zs trs tr0 Hrange Htraces Hinter]; subst.
      eapply PTLoopPar with
        (zs := Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub))
        (trs := trs); [reflexivity| |exact Hinter].
      eapply Forall2_impl_same; [|exact Htraces].
      intros z tri Htri. eapply IH. exact Htri.
    + inversion Htrace as
          [| | | | |
           od0 lb0 ub0 body0 env0 zs trs tr0 Hrange Htraces Hconcat
           |]; subst.
      eapply PTLoopVec with
        (zs := Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub))
        (trs := trs); [reflexivity| |reflexivity].
      eapply Forall2_impl_same; [|exact Htraces].
      intros z tri Htri. eapply IH. exact Htri.
  - intros i es env tr Htrace. exact Htrace.
  - intros ss IH env tr Htrace. simpl in Htrace.
    pose proof (make_stmt_from_list_par_trace_reflect _ _ _ Htrace)
      as Hseq.
    inversion Hseq as [|env0 ss0 tr0 Htraces| | | | |]; subst.
    constructor. eapply IH. exact Htraces.
  - intros tst body IH env tr Htrace. simpl in Htrace.
    pose proof (make_guard_par_trace_reflect _ _ _ _ Htrace) as Hguard.
    inversion Hguard as
        [| |
         env0 tst0 body0 tr0 Htest Hbody
         | env0 tst0 body0 Htest
         | | |]; subst.
    + eapply PTGuardTrue; [exact Htest|]. eapply IH. exact Hbody.
    + eapply PTGuardFalse. exact Htest.
  - intros env tr Htrace. exact Htrace.
  - intros s IHs ss IHss env tr Htrace. simpl in Htrace.
    destruct (cleanup_stmt s) as
      [mode od lb ub body|i es|clean_ss|tst body] eqn:Hclean.
    + inversion Htrace as
          [|env0 clean_s clean_tail tr1 tr2 Hhead Htail]; subst.
      econstructor.
      * eapply IHs. exact Hhead.
      * eapply IHss. exact Htail.
    + inversion Htrace as
          [|env0 clean_s clean_tail tr1 tr2 Hhead Htail]; subst.
      econstructor.
      * eapply IHs. exact Hhead.
      * eapply IHss. exact Htail.
    + destruct clean_ss as [|clean_s clean_tail].
      * assert (Hskip :
          par_trace (cleanup_stmt s) env []).
        {
          rewrite Hclean. constructor. constructor.
        }
        rewrite Hclean in Hskip.
        eapply PTTracesCons with (tr1 := []) (tr2 := tr).
        -- eapply IHs. exact Hskip.
        -- eapply IHss. exact Htrace.
      * inversion Htrace as
            [|env0 clean_s0 clean_tail0 tr1 tr2 Hhead Htail]; subst.
        econstructor.
        -- eapply IHs. exact Hhead.
        -- eapply IHss. exact Htail.
    + inversion Htrace as
          [|env0 clean_s clean_tail tr1 tr2 Hhead Htail]; subst.
      econstructor.
      * eapply IHs. exact Hhead.
      * eapply IHss. exact Htail.
Qed.

Local Lemma cleanup_structural_par_trace_reflect :
  forall s env tr,
    par_trace (cleanup_stmt s) env tr ->
    par_trace s env tr.
Proof.
  exact (proj1 cleanup_structural_par_trace_reflect_mutual).
Qed.

Local Lemma mk_instr_point_eval_equiv :
  forall i es1 es2 env aff1 aff2,
    BaseLoop.exprlist_to_aff es1 = Okk aff1 ->
    BaseLoop.exprlist_to_aff es2 = Okk aff2 ->
    map (BaseLoop.eval_expr env) es1 =
    map (BaseLoop.eval_expr env) es2 ->
    point_sema_equiv
      (BaseLoop.mk_instr_point i es1 env)
      (BaseLoop.mk_instr_point i es2 env).
Proof.
  intros i es1 es2 env aff1 aff2 Haff1 Haff2 Heval st1 st2.
  pose proof
    (BaseLoop.exprlist_to_aff_correct es1 env aff1 Haff1) as Hargs1.
  pose proof
    (BaseLoop.exprlist_to_aff_correct es2 env aff2 Haff2) as Hargs2.
  assert (Hargs : affine_product aff1 env = affine_product aff2 env).
  {
    rewrite <- Hargs1, <- Hargs2. exact Heval.
  }
  unfold BaseLoop.mk_instr_point.
  rewrite Haff1, Haff2. simpl.
  split; intro Hsem; inversion Hsem as [wcs rcs Hstep]; subst;
    econstructor; simpl in *.
  - rewrite <- Hargs. exact Hstep.
  - rewrite Hargs. exact Hstep.
Qed.

Local Definition simplify_trace_stmt_goal (s : stmt) : Prop :=
  forall env tr,
    trace_safe_stmt s ->
    trace_safe_stmt (simplify_stmt s) ->
    par_trace (simplify_stmt s) env tr ->
    exists tr0,
      par_trace s env tr0 /\
      Forall2 point_sema_equiv tr tr0.

Local Definition simplify_trace_stmts_goal (ss : stmt_list) : Prop :=
  forall env tr,
    trace_safe_stmts ss ->
    trace_safe_stmts (simplify_stmts ss) ->
    par_traces (simplify_stmts ss) env tr ->
    exists tr0,
      par_traces ss env tr0 /\
      Forall2 point_sema_equiv tr tr0.

Local Lemma simplify_par_trace_reflect_mutual :
  (forall s, simplify_trace_stmt_goal s) /\
  (forall ss, simplify_trace_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold simplify_trace_stmt_goal, simplify_trace_stmts_goal.
  - intros mode od lb ub body IH env tr Hsafe Hsafe_simpl Htrace.
    simpl in Hsafe, Hsafe_simpl, Htrace.
    destruct mode.
    + inversion Htrace as
          [| | | |
           od0 lb0 ub0 body0 env0 zs trs tr0 Hrange Htraces Hconcat
           | |]; subst.
      rewrite !simpl_expr_correct in Htraces.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace (simplify_stmt body) (z :: env) tri)
          (fun z tri => par_trace body (z :: env) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz. eapply IH; eauto.
      }
      exists (concat trs0). split.
      * eapply PTLoopSeq with
          (zs := Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub))
          (trs := trs0); eauto.
      * eapply Forall2_concat_point_sema_equiv. exact Hrels.
    + inversion Htrace as
          [| | | | | |
           d0 lb0 ub0 body0 env0 zs trs tr0 Hrange Htraces Hinter]; subst.
      rewrite !simpl_expr_correct in Htraces.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace (simplify_stmt body) (z :: env) tri)
          (fun z tri => par_trace body (z :: env) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz. eapply IH; eauto.
      }
      destruct (interleave_family_point_equiv _ _ _ Hinter Hrels)
        as [tr0 [Hinter0 Hrel0]].
      exists tr0. split.
      * eapply PTLoopPar with
          (zs := Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub))
          (trs := trs0); eauto.
      * exact Hrel0.
    + inversion Htrace as
          [| | | | |
           od0 lb0 ub0 body0 env0 zs trs tr0 Hrange Htraces Hconcat
           |]; subst.
      rewrite !simpl_expr_correct in Htraces.
      destruct
        (Forall2_trace_refine
          _ _ _
          (fun z tri => par_trace (simplify_stmt body) (z :: env) tri)
          (fun z tri => par_trace body (z :: env) tri)
          (Forall2 point_sema_equiv) _ _ Htraces)
        as [trs0 [Htraces0 Hrels]].
      {
        intros z tri Hz. eapply IH; eauto.
      }
      exists (concat trs0). split.
      * eapply PTLoopVec with
          (zs := Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub))
          (trs := trs0); eauto.
      * eapply Forall2_concat_point_sema_equiv. exact Hrels.
  - intros i es env tr Hsafe Hsafe_simpl Htrace.
    simpl in Hsafe, Hsafe_simpl, Htrace.
    inversion Htrace; subst.
    destruct Hsafe as [aff0 Haff0].
    destruct Hsafe_simpl as [aff1 Haff1].
    exists [BaseLoop.mk_instr_point i es env]. split.
    + constructor.
    + constructor; [|constructor].
      eapply mk_instr_point_eval_equiv; eauto.
      apply simpl_expr_list_correct.
  - intros ss IH env tr Hsafe Hsafe_simpl Htrace.
    simpl in Hsafe, Hsafe_simpl, Htrace.
    inversion Htrace as [|env0 ss0 tr0 Htraces| | | | |]; subst.
    destruct (IH env tr Hsafe Hsafe_simpl Htraces) as [tr0 [Ht Hr]].
    exists tr0. split; [constructor; exact Ht|exact Hr].
  - intros tst body IH env tr Hsafe Hsafe_simpl Htrace.
    simpl in Hsafe, Hsafe_simpl, Htrace.
    inversion Htrace as
        [| |
         env0 tst0 body0 tr0 Htest Hbody
         | env0 tst0 body0 Htest
         | | |]; subst.
    + rewrite simpl_test_correct in Htest.
      destruct (IH env tr Hsafe Hsafe_simpl Hbody) as [tr0 [Ht Hr]].
      exists tr0. split.
      * eapply PTGuardTrue; eauto.
      * exact Hr.
    + rewrite simpl_test_correct in Htest.
      exists (nil : list InstrPoint). split.
      * eapply PTGuardFalse. exact Htest.
      * constructor.
  - intros env tr Hsafe Hsafe_simpl Htrace.
    inversion Htrace; subst.
    exists (nil : list InstrPoint); split; constructor.
  - intros s IHs ss IHss env tr Hsafe Hsafe_simpl Htrace.
    simpl in Hsafe, Hsafe_simpl.
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    destruct Hsafe_simpl as [Hsafe_simpl_s Hsafe_simpl_ss].
    inversion Htrace as
        [|env0 s0 ss0 tr1 tr2 Hhead Htail]; subst.
    destruct (IHs env tr1 Hsafe_s Hsafe_simpl_s Hhead)
      as [tr1' [Ht1 Hr1]].
    destruct (IHss env tr2 Hsafe_ss Hsafe_simpl_ss Htail)
      as [tr2' [Ht2 Hr2]].
    exists (tr1' ++ tr2'). split.
    + econstructor; eauto.
    + apply Forall2_app; assumption.
Qed.

Local Lemma simplify_par_trace_reflect :
  forall s env tr,
    trace_safe_stmt s ->
    trace_safe_stmt (simplify_stmt s) ->
    par_trace (simplify_stmt s) env tr ->
    exists tr0,
      par_trace s env tr0 /\
      Forall2 point_sema_equiv tr tr0.
Proof.
  exact (proj1 simplify_par_trace_reflect_mutual).
Qed.

Local Lemma cleanup_structural_loop_semantics_reflect :
  forall s env mem1 mem2,
    loop_semantics (cleanup_stmt s) env mem1 mem2 ->
    loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2 [tr [Htrace Hsem]].
  exists tr. split; [|exact Hsem].
  eapply cleanup_structural_par_trace_reflect. exact Htrace.
Qed.

Local Lemma simplify_loop_semantics_reflect :
  forall s env mem1 mem2,
    trace_safe_stmt s ->
    trace_safe_stmt (simplify_stmt s) ->
    loop_semantics (simplify_stmt s) env mem1 mem2 ->
    loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2 Hsafe Hsafe_simpl [tr [Htrace Hsem]].
  destruct (simplify_par_trace_reflect s env tr Hsafe Hsafe_simpl Htrace)
    as [tr0 [Htrace0 Hrel]].
  exists tr0. split; [exact Htrace0|].
  eapply instr_point_list_semantics_equiv; eauto.
Qed.

Local Theorem cleanup_stmt_pass_loop_semantics_reflect :
  forall s env mem1 mem2,
    trace_safe_stmt s ->
    trace_safe_stmt (simplify_stmt s) ->
    trace_safe_stmt (cleanup_stmt (simplify_stmt s)) ->
    trace_safe_stmt
      (singleton_elim_stmt (cleanup_stmt (simplify_stmt s))) ->
    trace_safe_stmt
      (simplify_stmt
        (singleton_elim_stmt (cleanup_stmt (simplify_stmt s)))) ->
    loop_semantics (cleanup_stmt_pass s) env mem1 mem2 ->
    loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2 Hsafe0 Hsafe1 Hsafe2 Hsafe3 Hsafe4 Hsem.
  unfold cleanup_stmt_pass in Hsem.
  apply cleanup_structural_loop_semantics_reflect in Hsem.
  eapply simplify_loop_semantics_reflect in Hsem; [|exact Hsafe3|exact Hsafe4].
  eapply cleanup_loop_semantics_refine in Hsem; [|exact Hsafe2|exact Hsafe3].
  apply cleanup_structural_loop_semantics_reflect in Hsem.
  eapply simplify_loop_semantics_reflect in Hsem; eauto.
Qed.

Theorem full_cleanup_semantics_reflect :
  forall s ctxt vars mem1 mem2,
    trace_safe_stmt s ->
    trace_safe_stmt (simplify_stmt s) ->
    trace_safe_stmt (cleanup_stmt (simplify_stmt s)) ->
    trace_safe_stmt
      (singleton_elim_stmt (cleanup_stmt (simplify_stmt s))) ->
    trace_safe_stmt
      (simplify_stmt
        (singleton_elim_stmt (cleanup_stmt (simplify_stmt s)))) ->
    semantics (full_cleanup ((s, ctxt), vars)) mem1 mem2 ->
    semantics ((s, ctxt), vars) mem1 mem2.
Proof.
  intros s ctxt vars mem1 mem2 Hsafe0 Hsafe1 Hsafe2 Hsafe3 Hsafe4 Hsem.
  inversion Hsem as
      [loop_ext loop ctxt' vars' env mem1' mem2'
       Heq Hcompat Hna Hinit Hloop]; subst.
  inversion Heq; subst.
  econstructor.
  - reflexivity.
  - exact Hcompat.
  - exact Hna.
  - exact Hinit.
  - eapply cleanup_stmt_pass_loop_semantics_reflect; eauto.
Qed.

End ParallelLoop.
