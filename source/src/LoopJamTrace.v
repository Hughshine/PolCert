Require Import List.
Import ListNotations.

Require Import PolIRs.
Require Import ParallelLoop.
Require Import ParallelCodegen.

Module LoopJamTrace (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module PC := ParallelCodegen PolIRs.
Module PL := PC.ParallelLoop.
Module ILSema := PL.ILSema.
Module State := Instr.State.

Definition InstrPoint := PL.InstrPoint.
Definition trace := list InstrPoint.

Definition traces_permutable (left right : trace) : Prop :=
  forall ip_left ip_right,
    In ip_left left ->
    In ip_right right ->
    ILSema.Permutable ip_left ip_right.

Fixpoint jam_cross_permutable
    (outer_traces inner_traces : list trace) : Prop :=
  match outer_traces, inner_traces with
  | _ :: outer_tail, inner_head :: inner_tail =>
      traces_permutable (concat outer_tail) inner_head /\
      jam_cross_permutable outer_tail inner_tail
  | _, _ => True
  end.

Fixpoint jam_zip (outer_traces inner_traces : list trace) : trace :=
  match outer_traces, inner_traces with
  | outer_head :: outer_tail, inner_head :: inner_tail =>
      outer_head ++ inner_head ++ jam_zip outer_tail inner_tail
  | _, _ => concat outer_traces ++ concat inner_traces
  end.

Inductive jam_interleave_safe : list trace -> trace -> Prop :=
| JIS_nil :
    jam_interleave_safe [] []
| JIS_skip_nil : forall pre post out,
    jam_interleave_safe (pre ++ post) out ->
    jam_interleave_safe (pre ++ [] :: post) out
| JIS_take : forall pre x xs post out,
    (forall y, In y (concat pre) -> ILSema.Permutable y x) ->
    jam_interleave_safe (pre ++ xs :: post) out ->
    jam_interleave_safe (pre ++ (x :: xs) :: post) (x :: out).

Lemma concat_insert_nil :
  forall (pre post : list trace),
    concat (pre ++ [] :: post) = concat (pre ++ post).
Proof.
  intros pre post.
  rewrite !concat_app.
  reflexivity.
Qed.

Lemma jam_interleave_safe_refines_concat :
  forall traces out st1 st2,
    Instr.NonAlias st1 ->
    jam_interleave_safe traces out ->
    ILSema.instr_point_list_semantics out st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (concat traces) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros traces out st1 st2 Hna Hsafe.
  revert st1 st2 Hna.
  induction Hsafe; intros st1 st2 Hna Hsem.
  - simpl in Hsem.
    exists st1.
    split.
    + constructor. apply State.eq_refl.
    + eapply State.eq_sym.
      eapply PL.instr_point_list_semantics_nil_inv; eauto.
  - destruct (IHHsafe st1 st2 Hna Hsem)
      as [st2' [Hconcat Heq]].
    exists st2'.
    split.
    + rewrite concat_insert_nil.
      exact Hconcat.
    + exact Heq.
  - destruct (PL.instr_point_list_semantics_cons_inv _ _ _ _ Hsem)
      as [stmid [Hx Htail]].
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply PL.instr_point_sema_preserve_nonalias; eauto.
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
      (PL.move_back_permutable
         x (concat pre) (concat (xs :: post)) st1 st2'
         Hna H Hcons)
      as [st2'' [Hconcat_full Heq_move]].
    exists st2''.
    split.
    + rewrite concat_app.
      simpl.
      exact Hconcat_full.
    + eapply State.eq_trans.
      * exact Heq_tail.
      * exact Heq_move.
Qed.

Lemma jam_interleave_safe_take_head_trace :
  forall tr traces out,
    jam_interleave_safe traces out ->
    jam_interleave_safe (tr :: traces) (tr ++ out).
Proof.
  induction tr as [|ip tr IH]; intros traces out Hsafe; simpl.
  - apply (JIS_skip_nil [] traces out).
    exact Hsafe.
  - eapply (JIS_take [] ip tr traces (tr ++ out)).
    + intros y Hin.
      inversion Hin.
    + apply IH.
      exact Hsafe.
Qed.

Lemma jam_interleave_safe_take_trace_after_pre :
  forall tr pre post out,
    traces_permutable (concat pre) tr ->
    jam_interleave_safe (pre ++ post) out ->
    jam_interleave_safe (pre ++ tr :: post) (tr ++ out).
Proof.
  induction tr as [|ip tr IH]; intros pre post out Hperm Hsafe; simpl.
  - apply JIS_skip_nil.
    exact Hsafe.
  - eapply JIS_take.
    + intros y Hin.
      eapply Hperm.
      * exact Hin.
      * left; reflexivity.
    + apply IH.
      * intros y z Hy Hz.
        eapply Hperm.
        -- exact Hy.
        -- right; exact Hz.
      * exact Hsafe.
Qed.

Lemma jam_interleave_safe_concat :
  forall traces,
    jam_interleave_safe traces (concat traces).
Proof.
  induction traces as [|tr traces IH]; simpl.
  - constructor.
  - apply jam_interleave_safe_take_head_trace.
    exact IH.
Qed.

Theorem jam_zip_interleave_safe :
  forall outer_traces inner_traces,
    jam_cross_permutable outer_traces inner_traces ->
    jam_interleave_safe
      (outer_traces ++ inner_traces)
      (jam_zip outer_traces inner_traces).
Proof.
  induction outer_traces as [|outer_head outer_tail IH];
    intros inner_traces Hcross.
  - simpl.
    apply jam_interleave_safe_concat.
  - destruct inner_traces as [|inner_head inner_tail].
    + simpl.
      repeat rewrite app_nil_r.
      apply jam_interleave_safe_concat.
    + simpl in Hcross.
      destruct Hcross as [Hperm Hcross].
      simpl.
      apply jam_interleave_safe_take_head_trace.
      eapply jam_interleave_safe_take_trace_after_pre.
      * exact Hperm.
      * apply IH.
        exact Hcross.
Qed.

Theorem jam_zip_refines_concat :
  forall outer_traces inner_traces st1 st2,
    Instr.NonAlias st1 ->
    jam_cross_permutable outer_traces inner_traces ->
    ILSema.instr_point_list_semantics
      (jam_zip outer_traces inner_traces) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics
        (concat (outer_traces ++ inner_traces)) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros outer_traces inner_traces st1 st2 Hna Hcross Hsem.
  eapply jam_interleave_safe_refines_concat; eauto.
  apply jam_zip_interleave_safe.
  exact Hcross.
Qed.

Corollary jam_zip_refines_unjammed :
  forall outer_traces inner_traces st1 st2,
    Instr.NonAlias st1 ->
    jam_cross_permutable outer_traces inner_traces ->
    ILSema.instr_point_list_semantics
      (jam_zip outer_traces inner_traces) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics
        (concat outer_traces ++ concat inner_traces) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros outer_traces inner_traces st1 st2 Hna Hcross Hsem.
  destruct
    (jam_zip_refines_concat
       outer_traces inner_traces st1 st2 Hna Hcross Hsem)
    as [st2' [Hconcat Heq]].
  exists st2'.
  split.
  - rewrite concat_app in Hconcat.
    exact Hconcat.
  - exact Heq.
Qed.

End LoopJamTrace.
