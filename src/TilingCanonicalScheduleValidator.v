Require Import Bool.
Require Import List.
Require Import ZArith.
Import ListNotations.

Require Import PolyBase.
Require Import PolyLang.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import TilingWitness.
Require Import PointWitness.
Require Import TilingValidator.
Require Import PolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingCanonicalScheduleValidator (PolIRs: POLIRS).

Module Base := TilingValidator PolIRs.
Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module TilingCheck := Base.TilingCheck.
Module Tiling := Base.Tiling.
Module TilingPolIRs := Base.TilingPolIRs.

Definition check_pinstr_tiling_schedule_canonicalb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  listzzs_strict_eqb
    (Tiling.PL.pi_schedule after)
    (Tiling.lift_schedule_after_env
       (List.length (stw_links w)) env_size
       (Tiling.PL.pi_schedule before)).

Fixpoint check_pinstr_list_tiling_schedule_canonicalb
    (env_size: nat)
    (before after: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before, after, ws with
  | [], [], [] => true
  | before_pi :: before', after_pi :: after', w :: ws' =>
      check_pinstr_tiling_schedule_canonicalb env_size before_pi after_pi w &&
      check_pinstr_list_tiling_schedule_canonicalb env_size before' after' ws'
  | _, _, _ => false
  end.

Definition check_pprog_tiling_schedule_canonicalb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
  TilingCheck.ctxt_ty_eqb before_vars after_vars &&
  check_pinstr_list_tiling_schedule_canonicalb
    (List.length before_ctxt) before_pis after_pis ws.

Lemma check_pinstr_tiling_schedule_canonicalb_sound :
  forall env_size before after w,
    check_pinstr_tiling_schedule_canonicalb env_size before after w = true ->
    Tiling.PL.pi_schedule after =
    Tiling.lift_schedule_after_env
      (List.length (stw_links w)) env_size
      (Tiling.PL.pi_schedule before).
Proof.
  intros env_size before after w Hcheck.
  unfold check_pinstr_tiling_schedule_canonicalb in Hcheck.
  apply listzzs_strict_eqb_eq in Hcheck.
  exact Hcheck.
Qed.

Lemma retiled_old_pinstr_eq_of_structure_and_schedule :
  forall env_size before after cw w,
    Tiling.tiling_rel_pinstr_structure_source env_size before after cw ->
    Tiling.ptw_statement_witness cw = w ->
    check_pinstr_tiling_schedule_canonicalb env_size before after w = true ->
    Tiling.retiled_old_pinstr env_size before after w = after.
Proof.
  intros env_size before after cw w Hstruct Hcw Hcheck.
  destruct before as
      [before_depth before_instr before_poly before_sched before_pw
       before_tf before_atf before_wacc before_racc].
  destruct after as
      [after_depth after_instr after_poly after_sched after_pw
       after_tf after_atf after_wacc after_racc].
  unfold Tiling.tiling_rel_pinstr_structure_source in Hstruct.
  simpl in Hstruct.
  destruct Hstruct as
      [Hinstr [Hdepth [Hpw [Htf [Hacc_tf [Hdom [Hwacc Hracc]]]]]]].
  subst.
  apply check_pinstr_tiling_schedule_canonicalb_sound in Hcheck.
  unfold Tiling.retiled_old_pinstr.
  simpl in *.
  subst after_sched.
  reflexivity.
Qed.

Lemma retiled_old_pinstr_list_eq_of_structure_and_schedule :
  forall env_size before_pis after_pis cws ws,
    Tiling.tiling_rel_pinstr_list_source env_size before_pis after_pis cws ->
    Forall2
      (fun cw w => Tiling.ptw_statement_witness cw = w)
      cws ws ->
    check_pinstr_list_tiling_schedule_canonicalb
      env_size before_pis after_pis ws = true ->
    Tiling.retiled_old_pinstrs env_size before_pis after_pis ws = after_pis.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis cws ws Hstruct Hcws Hcheck;
    destruct after_pis as [|after_pi after_pis'];
    destruct cws as [|cw cws'];
    destruct ws as [|w ws'];
    simpl in *; try contradiction; try discriminate; auto.
  destruct Hstruct as [Hhd_struct Htl_struct].
  inversion Hcws as [|cw' w' cws'' ws'' Hcw Htl_cws]; subst.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hhd_check Htl_check].
  simpl.
  rewrite (retiled_old_pinstr_eq_of_structure_and_schedule
             env_size before_pi after_pi cw (Tiling.ptw_statement_witness cw)
             Hhd_struct eq_refl Hhd_check).
  f_equal.
  eapply IH; eauto.
Qed.

Lemma compiled_pinstr_tiling_witness_Forall2 :
  forall ws,
    Forall2
      (fun cw w => Tiling.ptw_statement_witness cw = w)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)
      ws.
Proof.
  induction ws as [|w ws IH]; constructor; simpl; auto.
Qed.

Lemma check_pprog_tiling_schedule_canonicalb_sound :
  forall before after ws,
    TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
    check_pprog_tiling_schedule_canonicalb before after ws = true ->
    (let '(before_pis, before_ctxt, before_vars) := before in
     let '(after_pis, _, _) := after in
     (Tiling.retiled_old_pinstrs (List.length before_ctxt) before_pis after_pis ws,
      before_ctxt,
      before_vars)) = after.
Proof.
  intros before after ws Hstruct Hcheck.
  destruct before as ((before_pis, before_ctxt), before_vars).
  destruct after as ((after_pis, after_ctxt), after_vars).
  unfold check_pprog_tiling_schedule_canonicalb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hctxt Hvars] Hsched].
  apply TilingCheck.ctxt_eqb_eq in Hctxt.
  apply TilingCheck.ctxt_ty_eqb_eq in Hvars.
  subst after_ctxt after_vars.
  simpl.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws Hstruct)
    as [Hrel [_ [_ [_ _]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ Hrel]].
  rewrite (retiled_old_pinstr_list_eq_of_structure_and_schedule
             (List.length before_ctxt)
             before_pis after_pis
             (List.map Tiling.compiled_pinstr_tiling_witness ws)
             ws
             Hrel
             (compiled_pinstr_tiling_witness_Forall2 ws)
             Hsched).
  reflexivity.
Qed.

Definition checked_tiling_schedule_canonical_validate
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  pure
    (TilingCheck.check_pprog_tiling_sourceb before after ws &&
     check_pprog_tiling_schedule_canonicalb before after ws).

Definition checked_tiling_schedule_canonical_validate_outer
    (before after: PolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp bool :=
  checked_tiling_schedule_canonical_validate
    (Base.outer_to_tiling_pprog before)
    (Base.outer_to_tiling_pprog after)
    ws.

Definition checked_tiling_schedule_canonical_validate_poly :=
  checked_tiling_schedule_canonical_validate_outer.

Lemma checked_tiling_schedule_canonical_validate_correct :
  forall before after ws st1 st2,
    mayReturn
      (checked_tiling_schedule_canonical_validate before after ws)
      true ->
    Tiling.PL.instance_list_semantics after st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hcheck Hsem_after.
  destruct before as [[before_pis varctxt] vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl in *.
  unfold checked_tiling_schedule_canonical_validate in Hcheck.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hstruct Hsched].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, varctxt, vars)
       (after_pis, after_ctxt, after_vars)
       ws Hstruct)
    as [Htiling [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Htiling.
  simpl in Htiling.
  destruct Htiling as [Hctxt [Hvars Htiling]].
  subst after_ctxt after_vars.
  assert (Htiling_pprog :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, varctxt, vars)
      (after_pis, varctxt, vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    repeat split; auto.
  }
  pose proof
    (check_pprog_tiling_schedule_canonicalb_sound
       (before_pis, varctxt, vars)
       (after_pis, varctxt, vars)
       ws Hstruct Hsched)
    as Hafter_eq.
  rewrite <- Hafter_eq in Hsem_after.
  eapply Tiling.tiling_retiled_old_to_before_instance_correct_source; eauto.
Qed.

Lemma checked_tiling_schedule_canonical_validate_outer_correct :
  forall before after ws st1 st2,
    mayReturn
      (checked_tiling_schedule_canonical_validate_outer before after ws)
      true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hcheck Hsem_after.
  pose proof
    ((proj2 (Base.outer_to_tiling_instance_list_semantics_iff after st1 st2))
       Hsem_after)
    as Hsem_after_tiling.
  pose proof
    (checked_tiling_schedule_canonical_validate_correct
       (Base.outer_to_tiling_pprog before)
       (Base.outer_to_tiling_pprog after)
       ws st1 st2 Hcheck Hsem_after_tiling)
    as [st2' [Hbefore_tiling Heq]].
  exists st2'.
  split.
  - apply (proj1 (Base.outer_to_tiling_instance_list_semantics_iff before st1 st2')).
    exact Hbefore_tiling.
  - exact Heq.
Qed.

Lemma checked_tiling_schedule_canonical_validate_poly_correct :
  forall before after ws st1 st2,
    mayReturn
      (checked_tiling_schedule_canonical_validate_poly before after ws)
      true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  exact checked_tiling_schedule_canonical_validate_outer_correct.
Qed.

End TilingCanonicalScheduleValidator.
