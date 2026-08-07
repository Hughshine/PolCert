Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import Linalg.
Require Import Misc.
Require Import PolyBase.
Require Import PolIRs.
Require Import TilingWitness.
Require Import TilingBandScheduleValidator.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingBandMixedSecondValidator (PolIRs: POLIRS).

Module Core := TilingBandScheduleValidator PolIRs.
Module State := PolIRs.State.
Import Core.

Open Scope impure_scope.

(** * Proof map

    This file handles layouts in which a constant scalar phase identifies a
    statement class and each class has its own ordinary or second-level band.
    Unique phase constants reduce a cross-program reversal to one class; the
    class-local band checker and reversal bridge then establish permutability. *)

Definition schedule_head_constant
    (sched: Schedule) : option Z :=
  match sched with
  | [] => None
  | (coeffs, c) :: _ =>
      if forallb (fun x => Z.eqb x 0%Z) coeffs then Some c else None
  end.

Definition pinstr_head_constant
    (pi: Core.Tiling.PL.PolyInstr) : option Z :=
  schedule_head_constant (Core.Tiling.PL.pi_schedule pi).

Fixpoint infer_unique_phase_constants
    (before_pis: list Core.Tiling.PL.PolyInstr)
    (bands: list Core.pinstr_tiling_band) : option (list Z) :=
  match before_pis, bands with
  | [], [] => Some []
  | pi :: before_pis', band :: bands' =>
      if Nat.eqb (Core.ptb_start band) 1%nat then
        match pinstr_head_constant pi,
              infer_unique_phase_constants before_pis' bands'
        with
        | Some phase, Some phases => Some (phase :: phases)
        | _, _ => None
        end
      else None
  | _, _ => None
  end.

Fixpoint z_not_inb (z: Z) (zs: list Z) : bool :=
  match zs with
  | [] => true
  | z' :: zs' => negb (Z.eqb z z') && z_not_inb z zs'
  end.

Fixpoint z_nodupb (zs: list Z) : bool :=
  match zs with
  | [] => true
  | z :: zs' => z_not_inb z zs' && z_nodupb zs'
  end.

Definition check_unique_phase_constantsb
    (before_pis: list Core.Tiling.PL.PolyInstr)
    (bands: list Core.pinstr_tiling_band) : bool :=
  match infer_unique_phase_constants before_pis bands with
  | Some phases => z_nodupb phases
  | None => false
  end.

Record phase_class_entry := {
  pce_phase : Z;
  pce_band : Core.pinstr_tiling_band;
  pce_sizes : list Z
}.

Definition phase_class_entry_compatibleb
    (entry1 entry2: phase_class_entry) : bool :=
  if Z.eqb (pce_phase entry1) (pce_phase entry2) then
    Core.pinstr_tiling_band_eqb
      (pce_band entry1) (pce_band entry2) &&
    Core.listz_strict_eqb (pce_sizes entry1) (pce_sizes entry2)
  else true.

Fixpoint check_phase_class_entry_againstb
    (entry: phase_class_entry)
    (entries: list phase_class_entry) : bool :=
  match entries with
  | [] => true
  | entry' :: entries' =>
      phase_class_entry_compatibleb entry entry' &&
      check_phase_class_entry_againstb entry entries'
  end.

Fixpoint check_phase_class_entries_consistentb
    (entries: list phase_class_entry) : bool :=
  match entries with
  | [] => true
  | entry :: entries' =>
      check_phase_class_entry_againstb entry entries' &&
      check_phase_class_entries_consistentb entries'
  end.

Fixpoint infer_phase_class_entries
    (before_pis: list Core.Tiling.PL.PolyInstr)
    (bands: list Core.pinstr_tiling_band)
    (ws: list statement_tiling_witness)
    : option (list phase_class_entry) :=
  match before_pis, bands, ws with
  | [], [], [] => Some []
  | before_pi :: before_pis', band :: bands', w :: ws' =>
      if Nat.eqb (Core.ptb_start band) 1%nat then
        match pinstr_head_constant before_pi,
              infer_phase_class_entries before_pis' bands' ws'
        with
        | Some phase, Some entries =>
            Some
              ({| pce_phase := phase;
                  pce_band := band;
                  pce_sizes := List.map tl_tile_size (stw_links w) |}
               :: entries)
        | _, _ => None
        end
      else None
  | _, _, _ => None
  end.

Definition check_phase_class_consistencyb
    (before_pis: list Core.Tiling.PL.PolyInstr)
    (bands: list Core.pinstr_tiling_band)
    (ws: list statement_tiling_witness) : bool :=
  match infer_phase_class_entries before_pis bands ws with
  | Some entries => check_phase_class_entries_consistentb entries
  | None => false
  end.

Definition phase_class_entries_consistent
    (entries: list phase_class_entry) : Prop :=
  forall entry1 entry2,
    In entry1 entries ->
    In entry2 entries ->
    pce_phase entry1 = pce_phase entry2 ->
    pce_band entry1 = pce_band entry2 /\
    pce_sizes entry1 = pce_sizes entry2.

Definition constant_schedule_head_value
    (pi: Core.Tiling.PL.PolyInstr) (phase: Z) : Prop :=
  pinstr_head_constant pi = Some phase.

Definition unique_phase_schedules
    (before_pis: list Core.Tiling.PL.PolyInstr)
    (bands: list Core.pinstr_tiling_band) : Prop :=
  exists phases,
    Forall2 constant_schedule_head_value before_pis phases /\
    Forall2
      (fun band _ => Core.ptb_start band = 1%nat)
      bands phases /\
    NoDup phases.

Lemma forallb_zeqb_zero_dot_product :
  forall coeffs point,
    forallb (fun x => Z.eqb x 0%Z) coeffs = true ->
    Linalg.dot_product coeffs point = 0%Z.
Proof.
  induction coeffs as [|coeff coeffs IH];
    intros point Hzero; destruct point as [|value point]; simpl; auto.
  apply andb_true_iff in Hzero.
  destruct Hzero as [Hcoeff Hcoeffs].
  apply Z.eqb_eq in Hcoeff.
  subst coeff.
  rewrite IH by exact Hcoeffs.
  lia.
Qed.

Lemma schedule_head_constant_sound :
  forall sched phase,
    schedule_head_constant sched = Some phase ->
    forall point,
      firstn 1 (affine_product sched point) = [phase].
Proof.
  intros sched phase Hhead point.
  destruct sched as [|[coeffs c] sched]; simpl in Hhead; try discriminate.
  destruct (forallb (fun x => Z.eqb x 0%Z) coeffs) eqn:Hzero;
    try discriminate.
  inversion Hhead; subst c; clear Hhead.
  simpl.
  rewrite (forallb_zeqb_zero_dot_product coeffs point Hzero).
  f_equal.
Qed.

Lemma forallb_skipn_true :
  forall (A: Type) (f: A -> bool) n xs,
    forallb f xs = true ->
    forallb f (skipn n xs) = true.
Proof.
  intros A f n.
  induction n as [|n IH]; intros xs Hforall; simpl; auto.
  destruct xs as [|x xs]; simpl in *; auto.
  apply andb_true_iff in Hforall.
  eapply IH.
  exact (proj2 Hforall).
Qed.

Lemma schedule_head_constant_lift :
  forall sched phase added_dims env_size,
    schedule_head_constant sched = Some phase ->
    schedule_head_constant
      (Core.Tiling.lift_schedule_after_env
         added_dims env_size sched) = Some phase.
Proof.
  intros sched phase added_dims env_size Hhead.
  destruct sched as [|[coeffs c] sched]; simpl in Hhead; try discriminate.
  destruct (forallb (fun x => Z.eqb x 0%Z) coeffs) eqn:Hzero;
    try discriminate.
  inversion Hhead; subst c; clear Hhead.
  unfold Core.Tiling.lift_schedule_after_env,
         Core.Tiling.lift_affine_function_after_env.
  simpl.
  unfold Core.Tiling.lift_constraint_after_env,
         Core.Tiling.PL.insert_zeros_constraint,
         Core.Tiling.PL.insert_zeros.
  simpl.
  rewrite forallb_app.
  rewrite (resize_null_repeat env_size coeffs Hzero).
  rewrite repeat_zero_is_null.
  simpl.
  rewrite forallb_app, repeat_zero_is_null.
  simpl.
  rewrite (forallb_skipn_true _ _ _ _ Hzero).
  reflexivity.
Qed.

Lemma schedule_head_constant_lift_sound :
  forall sched phase added_dims env_size point,
    schedule_head_constant sched = Some phase ->
    firstn 1
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            added_dims env_size sched)
         point) = [phase].
Proof.
  intros sched phase added_dims env_size point Hhead.
  eapply schedule_head_constant_sound.
  eapply schedule_head_constant_lift.
  exact Hhead.
Qed.

Lemma infer_unique_phase_constants_sound :
  forall before_pis bands phases,
    infer_unique_phase_constants before_pis bands = Some phases ->
    Forall2 constant_schedule_head_value before_pis phases /\
    Forall2
      (fun band _ => Core.ptb_start band = 1%nat)
      bands phases.
Proof.
  induction before_pis as [|pi before_pis IH];
    intros bands phases Hinfer.
  - destruct bands; simpl in Hinfer; try discriminate.
    inversion Hinfer; subst phases.
    split; constructor.
  - destruct bands as [|band bands]; simpl in Hinfer; try discriminate.
    destruct (Nat.eqb (Core.ptb_start band) 1) eqn:Hstart;
      try discriminate.
    destruct (pinstr_head_constant pi) as [phase|] eqn:Hphase;
      try discriminate.
    destruct (infer_unique_phase_constants before_pis bands)
      as [phases'|] eqn:Hrest; try discriminate.
    inversion Hinfer; subst phases; clear Hinfer.
    destruct (IH bands phases' Hrest) as [Hheads Hstarts].
    split; constructor.
    + exact Hphase.
    + exact Hheads.
    + apply Nat.eqb_eq. exact Hstart.
    + exact Hstarts.
Qed.

Lemma z_not_inb_sound :
  forall z zs,
    z_not_inb z zs = true ->
    ~ In z zs.
Proof.
  intros z zs.
  induction zs as [|z' zs IH]; intros Hcheck Hin; simpl in *.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    apply negb_true_iff in Hhead.
    destruct Hin as [Heq | Hin].
    + subst z'. rewrite Z.eqb_refl in Hhead. discriminate.
    + eapply IH; eauto.
Qed.

Lemma z_nodupb_sound :
  forall zs,
    z_nodupb zs = true ->
    NoDup zs.
Proof.
  induction zs as [|z zs IH]; intros Hcheck; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply z_not_inb_sound; exact Hhead.
    + eapply IH; exact Htail.
Qed.

Lemma check_unique_phase_constantsb_sound :
  forall before_pis bands,
    check_unique_phase_constantsb before_pis bands = true ->
    unique_phase_schedules before_pis bands.
Proof.
  intros before_pis bands Hcheck.
  unfold check_unique_phase_constantsb in Hcheck.
  destruct (infer_unique_phase_constants before_pis bands)
    as [phases|] eqn:Hinfer; try discriminate.
  exists phases.
  destruct (infer_unique_phase_constants_sound _ _ _ Hinfer)
    as [Hheads Hstarts].
  repeat split; auto.
  eapply z_nodupb_sound; exact Hcheck.
Qed.

Lemma phase_class_entry_compatibleb_sound :
  forall entry1 entry2,
    phase_class_entry_compatibleb entry1 entry2 = true ->
    pce_phase entry1 = pce_phase entry2 ->
    pce_band entry1 = pce_band entry2 /\
    pce_sizes entry1 = pce_sizes entry2.
Proof.
  intros entry1 entry2 Hcheck Hphase.
  unfold phase_class_entry_compatibleb in Hcheck.
  rewrite Hphase, Z.eqb_refl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hband Hsizes].
  split.
  - eapply Core.pinstr_tiling_band_eqb_eq; exact Hband.
  - eapply Core.listz_strict_eqb_eq; exact Hsizes.
Qed.

Lemma check_phase_class_entry_againstb_sound :
  forall entry entries,
    check_phase_class_entry_againstb entry entries = true ->
    forall entry',
      In entry' entries ->
      pce_phase entry = pce_phase entry' ->
      pce_band entry = pce_band entry' /\
      pce_sizes entry = pce_sizes entry'.
Proof.
  intros entry entries.
  induction entries as [|entry0 entries IH];
    intros Hcheck entry' Hin Hphase.
  - inversion Hin.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin].
    + subst entry'.
      eapply phase_class_entry_compatibleb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma check_phase_class_entries_consistentb_sound :
  forall entries,
    check_phase_class_entries_consistentb entries = true ->
    phase_class_entries_consistent entries.
Proof.
  intros entries.
  induction entries as [|entry entries IH]; intros Hcheck.
  - unfold phase_class_entries_consistent.
    intros entry1 entry2 Hin1.
    inversion Hin1.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hagainst Htail].
    unfold phase_class_entries_consistent in *.
    intros entry1 entry2 Hin1 Hin2 Hphase.
    destruct Hin1 as [Heq1 | Hin1];
      destruct Hin2 as [Heq2 | Hin2].
    + subst entry1 entry2. split; reflexivity.
    + subst entry1.
      eapply check_phase_class_entry_againstb_sound; eauto.
    + subst entry2.
      destruct
        (check_phase_class_entry_againstb_sound
           entry entries Hagainst entry1 Hin1 (eq_sym Hphase))
        as [Hband Hsizes].
      split; symmetry; assumption.
    + eapply IH; eauto.
Qed.

Lemma infer_phase_class_entries_nth_error :
  forall before_pis bands ws entries n before_pi band w entry,
    infer_phase_class_entries before_pis bands ws = Some entries ->
    nth_error before_pis n = Some before_pi ->
    nth_error bands n = Some band ->
    nth_error ws n = Some w ->
    nth_error entries n = Some entry ->
    pinstr_head_constant before_pi = Some (pce_phase entry) /\
    Core.ptb_start band = 1%nat /\
    pce_band entry = band /\
    pce_sizes entry = Core.tile_sizes_of_witness w.
Proof.
  induction before_pis as [|before_pi0 before_pis IH];
    intros bands ws entries n before_pi band w entry
           Hinfer Hbefore Hband Hw Hentry.
  - destruct n; discriminate.
  - destruct bands as [|band0 bands]; simpl in Hinfer; try discriminate.
    destruct ws as [|w0 ws]; simpl in Hinfer; try discriminate.
    destruct (Nat.eqb (Core.ptb_start band0) 1%nat) eqn:Hstart;
      try discriminate.
    destruct (pinstr_head_constant before_pi0) as [phase0|] eqn:Hphase;
      try discriminate.
    destruct (infer_phase_class_entries before_pis bands ws)
      as [entries0|] eqn:Htail; try discriminate.
    inversion Hinfer; subst entries; clear Hinfer.
    destruct n as [|n].
    + simpl in Hbefore, Hband, Hw, Hentry.
      inversion Hbefore; inversion Hband; inversion Hw; inversion Hentry;
        subst; clear Hbefore Hband Hw Hentry.
      simpl.
      repeat split; auto.
      apply Nat.eqb_eq. exact Hstart.
    + simpl in Hbefore, Hband, Hw, Hentry.
      eapply IH; eauto.
Qed.

Lemma infer_phase_class_entries_lengths :
  forall before_pis bands ws entries,
    infer_phase_class_entries before_pis bands ws = Some entries ->
    List.length before_pis = List.length bands /\
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length entries.
Proof.
  induction before_pis as [|before_pi before_pis IH];
    intros bands ws entries Hinfer.
  - destruct bands, ws, entries; simpl in Hinfer;
      inversion Hinfer; subst; auto.
  - destruct bands as [|band bands]; simpl in Hinfer; try discriminate.
    destruct ws as [|w ws]; simpl in Hinfer; try discriminate.
    destruct (Nat.eqb (Core.ptb_start band) 1%nat); try discriminate.
    destruct (pinstr_head_constant before_pi); try discriminate.
    destruct (infer_phase_class_entries before_pis bands ws)
      as [entries0|] eqn:Htail; try discriminate.
    inversion Hinfer; subst entries; clear Hinfer.
    destruct (IH _ _ _ Htail) as [Hbands [Hws Hentries]].
    simpl.
    repeat split; lia.
Qed.

Lemma check_phase_class_consistencyb_sound :
  forall before_pis bands ws,
    check_phase_class_consistencyb before_pis bands ws = true ->
    exists entries,
      infer_phase_class_entries before_pis bands ws = Some entries /\
      phase_class_entries_consistent entries.
Proof.
  intros before_pis bands ws Hcheck.
  unfold check_phase_class_consistencyb in Hcheck.
  destruct (infer_phase_class_entries before_pis bands ws)
    as [entries|] eqn:Hinfer; try discriminate.
  exists entries.
  split; [reflexivity|].
  eapply check_phase_class_entries_consistentb_sound.
  exact Hcheck.
Qed.

Lemma NoDup_nth_error_injective_local :
  forall (A: Type) (xs: list A) i j x,
    NoDup xs ->
    nth_error xs i = Some x ->
    nth_error xs j = Some x ->
    i = j.
Proof.
  intros A xs i j x Hnodup Hi Hj.
  rewrite NoDup_nth_error in Hnodup.
  apply Hnodup.
  - rewrite <- nth_error_Some, Hi. discriminate.
  - rewrite Hi, Hj. reflexivity.
Qed.

Lemma unique_phase_schedules_identify_statement :
  forall before_pis phases i j pi1 pi2 point1 point2,
    Forall2 constant_schedule_head_value before_pis phases ->
    NoDup phases ->
    nth_error before_pis i = Some pi1 ->
    nth_error before_pis j = Some pi2 ->
    firstn 1
      (affine_product (Core.Tiling.PL.pi_schedule pi1) point1) =
    firstn 1
      (affine_product (Core.Tiling.PL.pi_schedule pi2) point2) ->
    i = j.
Proof.
  intros before_pis phases i j pi1 pi2 point1 point2
         Hheads Hnodup Hpi1 Hpi2 Hprefix.
  destruct
    (Forall2_nth_error
       _ _ _ i before_pis phases pi1 Hheads Hpi1)
    as [phase1 [Hphase1 Hhead1]].
  destruct
    (Forall2_nth_error
       _ _ _ j before_pis phases pi2 Hheads Hpi2)
    as [phase2 [Hphase2 Hhead2]].
  unfold constant_schedule_head_value, pinstr_head_constant in
    Hhead1, Hhead2.
  pose proof
    (schedule_head_constant_sound _ _ Hhead1 point1) as Heval1.
  pose proof
    (schedule_head_constant_sound _ _ Hhead2 point2) as Heval2.
  rewrite Heval1, Heval2 in Hprefix.
  inversion Hprefix; subst phase2.
  eapply NoDup_nth_error_injective_local; eauto.
Qed.

Lemma unique_phase_schedules_identify_statement_lifted :
  forall before_pis phases i j pi1 pi2
         added1 added2 env_size point1 point2,
    Forall2 constant_schedule_head_value before_pis phases ->
    NoDup phases ->
    nth_error before_pis i = Some pi1 ->
    nth_error before_pis j = Some pi2 ->
    firstn 1
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            added1 env_size (Core.Tiling.PL.pi_schedule pi1))
         point1) =
    firstn 1
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            added2 env_size (Core.Tiling.PL.pi_schedule pi2))
         point2) ->
    i = j.
Proof.
  intros before_pis phases i j pi1 pi2
         added1 added2 env_size point1 point2
         Hheads Hnodup Hpi1 Hpi2 Hprefix.
  destruct
    (Forall2_nth_error
       _ _ _ i before_pis phases pi1 Hheads Hpi1)
    as [phase1 [Hphase1 Hhead1]].
  destruct
    (Forall2_nth_error
       _ _ _ j before_pis phases pi2 Hheads Hpi2)
    as [phase2 [Hphase2 Hhead2]].
  unfold constant_schedule_head_value, pinstr_head_constant in
    Hhead1, Hhead2.
  pose proof
    (schedule_head_constant_lift_sound
       _ _ added1 env_size point1 Hhead1) as Heval1.
  pose proof
    (schedule_head_constant_lift_sound
       _ _ added2 env_size point2 Hhead2) as Heval2.
  rewrite Heval1, Heval2 in Hprefix.
  inversion Hprefix; subst phase2.
  eapply NoDup_nth_error_injective_local; eauto.
Qed.

Lemma unique_phase_schedules_band_start :
  forall before_pis bands n band,
    unique_phase_schedules before_pis bands ->
    nth_error bands n = Some band ->
    Core.ptb_start band = 1%nat.
Proof.
  intros before_pis bands n band
         [phases [_ [Hstarts _]]] Hband.
  destruct
    (Forall2_nth_error
       _ _ _ n bands phases band Hstarts Hband)
    as [phase [_ Hstart]].
  exact Hstart.
Qed.

Lemma grouped_second_level_expected_timestamp_prefix :
  forall env_size before_sched band point,
    Core.ptb_start band = 1%nat ->
    exists rest,
      affine_product
        (Core.stripmine_second_level_schedule_after_env
           env_size before_sched band)
        point =
      firstn 1
        (affine_product
           (Core.Tiling.lift_schedule_after_env
              (2 * Core.ptb_len band)%nat env_size before_sched)
           point) ++
      rest.
Proof.
  intros env_size before_sched band point Hstart.
  unfold Core.stripmine_second_level_schedule_after_env.
  rewrite Hstart.
  cbn beta iota zeta.
  repeat rewrite Core.affine_product_app.
  rewrite Core.affine_product_firstn.
  eexists.
  reflexivity.
Qed.

Lemma second_level_recipe_links_length :
  forall point_dim prefix_len links recipe,
    Core.second_level_band_recipe_spec
      point_dim prefix_len links recipe ->
    List.length links =
      (2 * List.length (Core.slbr_root_rows recipe))%nat.
Proof.
  intros point_dim prefix_len links recipe Hspec.
  induction Hspec; simpl; lia.
Qed.

Lemma mixed_second_level_reversal_same_statement :
  forall before_pis before_ctxt before_vars
         after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    Core.infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    Core.check_pinstr_list_second_level_schedule_symmetricb
      Core.SecondLevelGrouped
      (List.length before_ctxt) before_pis after_pis bands = true ->
    unique_phase_schedules before_pis bands ->
    Core.Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Core.Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Core.Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    forall ipl_ext tau1 tau2,
      Core.Tiling.PL.flatten_instrs_ext
        envv
        (Core.Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Core.Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Core.Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      Core.Tiling.PL.ip_nth_ext tau1 =
      Core.Tiling.PL.ip_nth_ext tau2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws bands recipes envv
         Hlen_env Hinfer Hsched Hunique
         Hprog Hwf_ws Hsizes_ws Hdepths
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  pose proof Hunique as Hunique0.
  destruct Hunique as [phases [Hheads [Hstarts Hnodup]]].
  assert (Hwf_ws_env :
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct (Core.infer_pinstr_list_second_level_bands_lengths
              _ _ _ _ Hinfer)
    as [Hlen_ws [Hlen_bands Hlen_recipes]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [_ [_ [_ [_ [Hbel1 _]]]]]]]]]]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [_ [_ [_ [_ [Hbel2 _]]]]]]]]]]].
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    apply nth_error_None in Hband1.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    apply nth_error_None in Hband2.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Core.Tiling.PL.ip_nth_ext tau1))
    as [recipe1|] eqn:Hrecipe1.
  2:{
    apply nth_error_None in Hrecipe1.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Core.Tiling.PL.ip_nth_ext tau2))
    as [recipe2|] eqn:Hrecipe2.
  2:{
    apply nth_error_None in Hrecipe2.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  pose proof
    (Core.infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band1 recipe1
       Hinfer Hbefore1 Hw1 Hband1 Hrecipe1) as Hinfer1.
  pose proof
    (Core.infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Core.Tiling.PL.ip_nth_ext tau2)
       before_pi2 w2 band2 recipe2
       Hinfer Hbefore2 Hw2 Hband2 Hrecipe2) as Hinfer2.
  destruct (Core.infer_pinstr_second_level_band_sound _ _ _ _ Hinfer1)
    as [Hspec1 [Hband_len1 _]].
  destruct (Core.infer_pinstr_second_level_band_sound _ _ _ _ Hinfer2)
    as [Hspec2 [Hband_len2 _]].
  assert (Hlinks1 :
    List.length (stw_links w1) = (2 * Core.ptb_len band1)%nat).
  {
    rewrite (second_level_recipe_links_length _ _ _ _ Hspec1).
    rewrite Hband_len1.
    reflexivity.
  }
  assert (Hlinks2 :
    List.length (stw_links w2) = (2 * Core.ptb_len band2)%nat).
  {
    rewrite (second_level_recipe_links_length _ _ _ _ Hspec2).
    rewrite Hband_len2.
    reflexivity.
  }
  pose proof
    (unique_phase_schedules_band_start
       before_pis bands (Core.Tiling.PL.ip_nth_ext tau1) band1
       Hunique0 Hband1) as Hstart1.
  pose proof
    (unique_phase_schedules_band_start
       before_pis bands (Core.Tiling.PL.ip_nth_ext tau2) band2
       Hunique0 Hband2) as Hstart2.
  pose proof
    (Core.check_pinstr_list_second_level_schedule_symmetricb_nth_error
       Core.SecondLevelGrouped (List.length before_ctxt)
       before_pis after_pis bands
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 band1
       Hsched Hbefore1 Hafter1 Hband1) as Hsched_match1.
  pose proof
    (Core.check_pinstr_list_second_level_schedule_symmetricb_nth_error
       Core.SecondLevelGrouped (List.length before_ctxt)
       before_pis after_pis bands
       (Core.Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 band2
       Hsched Hbefore2 Hafter2 Hband2) as Hsched_match2.
  unfold Core.Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [_ [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [_ [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert (Hts11_lift :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product
      (Core.Tiling.lift_schedule_after_env
         (List.length (stw_links w1)) (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts11. reflexivity. }
  assert (Hts12_lift :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product
      (Core.Tiling.lift_schedule_after_env
         (List.length (stw_links w2)) (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi2))
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts12. reflexivity. }
  assert (Hts21_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product
      (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. reflexivity. }
  assert (Hts22_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product
      (Core.Tiling.PL.pi_schedule after_pi2)
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. reflexivity. }
  destruct
    (grouped_second_level_expected_timestamp_prefix
       (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1)
       band1 (Core.Tiling.PL.ip_index_ext tau1) Hstart1)
    as [rest1 Hexpected1].
  destruct
    (grouped_second_level_expected_timestamp_prefix
       (List.length envv) (Core.Tiling.PL.pi_schedule before_pi2)
       band2 (Core.Tiling.PL.ip_index_ext tau2) Hstart2)
    as [rest2 Hexpected2].
  rewrite <- Hlinks1, <- Hts11_lift in Hexpected1.
  rewrite <- Hlinks2, <- Hts12_lift in Hexpected2.
  rewrite Hlen_env in Hsched_match1, Hsched_match2.
  cbn [Core.stripmine_second_level_schedule_after_env_by_layout] in
    Hsched_match1, Hsched_match2.
  pose proof
    (Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ (Core.Tiling.PL.ip_index_ext tau1)
       Hsched_match1) as Htime_eq1.
  pose proof
    (Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ (Core.Tiling.PL.ip_index_ext tau2)
       Hsched_match2) as Htime_eq2.
  rewrite <- Hts21_after, Hexpected1 in Htime_eq1.
  rewrite <- Hts22_after, Hexpected2 in Htime_eq2.
  assert (Hnew_not_lt :
    lex_compare
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (Core.Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Core.Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2) <> Lt).
  {
    assert (Hcompare :
      lex_compare
        (Core.Tiling.PL.ip_time_stamp2_ext tau1)
        (Core.Tiling.PL.ip_time_stamp2_ext tau2) =
      lex_compare
        (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
        (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2)).
    {
      transitivity
        (lex_compare
           (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
           (Core.Tiling.PL.ip_time_stamp2_ext tau2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Hprefix_len :
    List.length (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1)) =
    List.length (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2))).
  {
    destruct
      (Forall2_nth_error
         _ _ _ (Core.Tiling.PL.ip_nth_ext tau1)
         before_pis phases before_pi1 Hheads Hbefore1)
      as [phase1 [_ Hhead1]].
    destruct
      (Forall2_nth_error
         _ _ _ (Core.Tiling.PL.ip_nth_ext tau2)
         before_pis phases before_pi2 Hheads Hbefore2)
      as [phase2 [_ Hhead2]].
    unfold constant_schedule_head_value, pinstr_head_constant in
      Hhead1, Hhead2.
    pose proof
      (schedule_head_constant_lift_sound
         _ _ (List.length (stw_links w1)) (List.length envv)
         (Core.Tiling.PL.ip_index_ext tau1) Hhead1) as Hphase_eval1.
    pose proof
      (schedule_head_constant_lift_sound
         _ _ (List.length (stw_links w2)) (List.length envv)
         (Core.Tiling.PL.ip_index_ext tau2) Hhead2) as Hphase_eval2.
    rewrite Hts11_lift, Hts12_lift.
    rewrite Hphase_eval1, Hphase_eval2.
    reflexivity.
  }
  assert (Hprefix :
    firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) =
    firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2)).
  {
    unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1)) in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2)) in Hold.
    eapply Core.preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  rewrite Hts11_lift, Hts12_lift in Hprefix.
  eapply unique_phase_schedules_identify_statement_lifted; eauto.
Qed.

Lemma mixed_second_level_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars
         after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    Core.infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    Core.check_pinstr_list_second_level_schedule_symmetricb
      Core.SecondLevelGrouped
      (List.length before_ctxt) before_pis after_pis bands = true ->
    unique_phase_schedules before_pis bands ->
    Core.Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Core.Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Core.Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    forall ipl_ext tau1 tau2,
      Core.Tiling.PL.flatten_instrs_ext
        envv
        (Core.Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Core.Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Core.Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      exists band,
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau2) = Some band /\
        Core.instr_point_ext_same_band_slice band tau1 tau2 /\
        Core.instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws bands recipes envv
         Hlen_env Hinfer Hsched Hunique
         Hprog Hwf_ws Hsizes_ws Hdepths Hwf_before
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  assert (Hsame :
    Core.Tiling.PL.ip_nth_ext tau1 =
    Core.Tiling.PL.ip_nth_ext tau2).
  {
    eapply mixed_second_level_reversal_same_statement; eauto.
  }
  assert (Hwf_ws_env :
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct (Core.infer_pinstr_list_second_level_bands_lengths
              _ _ _ _ Hinfer)
    as [Hlen_ws [Hlen_bands Hlen_recipes]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [Hwf_stmt1 [Hsizes1 [Hpoint_depth1
         [Hpref1 [Hbel1 Hlen1]]]]]]]]]]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [Hwf_stmt2 [Hsizes2 [Hpoint_depth2
         [Hpref2 [Hbel2 Hlen2]]]]]]]]]]].
  rewrite <- Hsame in Hbefore2, Hafter2, Hw2.
  rewrite Hbefore1 in Hbefore2.
  inversion Hbefore2; subst before_pi2; clear Hbefore2.
  rewrite Hafter1 in Hafter2.
  inversion Hafter2; subst after_pi2; clear Hafter2.
  rewrite Hw1 in Hw2.
  inversion Hw2; subst w2; clear Hw2.
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau1))
    as [band|] eqn:Hband.
  2:{
    apply nth_error_None in Hband.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Core.Tiling.PL.ip_nth_ext tau1))
    as [recipe|] eqn:Hrecipe.
  2:{
    apply nth_error_None in Hrecipe.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  pose proof
    (Core.infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band recipe
       Hinfer Hbefore1 Hw1 Hband Hrecipe) as Hinfer1.
  destruct (Core.infer_pinstr_second_level_band_sound _ _ _ _ Hinfer1)
    as [Hspec [Hband_len Hrows_match]].
  destruct (Core.second_level_band_recipe_spec_lengths _ _ _ _ Hspec)
    as [Hroot_size_len Hchild_size_len].
  pose proof
    (Core.Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Core.Tiling.compiled_pinstr_tiling_witness ws)
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1
       (Core.Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Core.Tiling.nth_error_map_some
          _ _ Core.Tiling.compiled_pinstr_tiling_witness
          ws (Core.Tiling.PL.ip_nth_ext tau1) w1 Hw1)) as Hstmt.
  pose proof
    (Core.tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt Hpoint_depth1) as Hafter_wit.
  pose proof
    (Core.Tiling.Forall_nth_error
       _ _ before_pis (Core.Tiling.PL.ip_nth_ext tau1) before_pi1
       Hwf_before Hbefore1) as Hwf_before1.
  pose proof
    (Core.check_pinstr_list_second_level_schedule_symmetricb_nth_error
       Core.SecondLevelGrouped (List.length before_ctxt)
       before_pis after_pis bands
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 band
       Hsched Hbefore1 Hafter1 Hband) as Hsched_match.
  assert (Hstmt_env :
    Core.Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi1 after_pi1
      (Core.Tiling.compiled_pinstr_tiling_witness w1)).
  { rewrite <- Hlen_env. exact Hstmt. }
  unfold Core.Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  destruct Hafter_wit as [Hafter_pw Hafter_depth].
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  destruct Hwf_before1 as [Hwf_before1_core _].
  destruct Hwf_before1_core as
      [_ [Hcols_before [_ [_ [_ [_ [_ [Hsched_before _]]]]]]]].
  set (added1 :=
    Core.Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  set (point1 :=
    Core.Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  set (added2 :=
    Core.Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau2)).
  set (point2 :=
    Core.Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau2)).
  assert (Hadded_len1 :
    List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Core.Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite <- Hafter_depth in Hlen1.
    rewrite Hafter_pw in Hlen1.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hadded_len2 :
    List.length added2 = List.length (stw_links w1)).
  {
    subst added2.
    eapply Core.Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite <- Hafter_depth in Hlen2.
    rewrite Hafter_pw in Hlen2.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Core.Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite <- Hafter_depth in Hlen1.
    rewrite Hafter_pw in Hlen1.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w1).
  {
    subst point2.
    eapply Core.Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite <- Hafter_depth in Hlen2.
    rewrite Hafter_pw in Hlen2.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hidx_split1 :
    Core.Tiling.PL.ip_index_ext tau1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Core.Tiling.PL.ip_index_ext tau1) ++
       Core.Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau1) ++
       Core.Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau1)).
    - apply Core.Tiling.tiled_index_split.
    - rewrite Hpref1. reflexivity.
  }
  assert (Hidx_split2 :
    Core.Tiling.PL.ip_index_ext tau2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Core.Tiling.PL.ip_index_ext tau2) ++
       Core.Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau2) ++
       Core.Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau2)).
    - apply Core.Tiling.tiled_index_split.
    - rewrite Hpref2. reflexivity.
  }
  assert (Hts11_old :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product (Core.Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    rewrite Hts11. cbn [Core.Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Core.Tiling.lift_schedule_after_env.
    eapply Core.Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts12_old :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product (Core.Tiling.PL.pi_schedule before_pi1) (envv ++ point2)).
  {
    rewrite Hts12. cbn [Core.Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Core.Tiling.lift_schedule_after_env.
    eapply Core.Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts21_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. cbn [Core.Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hts22_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. cbn [Core.Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Core.Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Core.Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt_env
         (Core.Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Core.Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete1.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete1 Hafter_dom1). tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 envv (stw_links w1)).
  {
    pose proof
      (Core.Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Core.Tiling.compiled_pinstr_tiling_witness w1)
         added2 point2 Hstmt_env
         (Core.Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Core.Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len2 Hpoint_len2 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete2.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete2 Hafter_dom2). tauto.
  }
  set (roots1 := Core.second_level_root_tiles recipe envv point1).
  set (children1 := Core.second_level_child_tiles recipe envv point1).
  set (roots2 := Core.second_level_root_tiles recipe envv point2).
  set (children2 := Core.second_level_child_tiles recipe envv point2).
  assert (Hadded_tiles1 :
    added1 = Core.interleave_root_child_tiles roots1 children1).
  {
    rewrite Hadded_eq1.
    subst roots1 children1.
    change
      (eval_tile_links [] point1 envv (stw_links w1) =
       [] ++
       Core.interleave_root_child_tiles
         (Core.second_level_root_tiles recipe envv point1)
         (Core.second_level_child_tiles recipe envv point1)).
    exact
      (Core.eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec [] point1 envv eq_refl Hpoint_len1
         Hwf_stmt1 Hparams1).
  }
  assert (Hadded_tiles2 :
    added2 = Core.interleave_root_child_tiles roots2 children2).
  {
    rewrite Hadded_eq2.
    subst roots2 children2.
    change
      (eval_tile_links [] point2 envv (stw_links w1) =
       [] ++
       Core.interleave_root_child_tiles
         (Core.second_level_root_tiles recipe envv point2)
         (Core.second_level_child_tiles recipe envv point2)).
    exact
      (Core.eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec [] point2 envv eq_refl Hpoint_len2
         Hwf_stmt1 Hparams1).
  }
  assert (Hroots_len1 : List.length roots1 = Core.ptb_len band).
  {
    subst roots1.
    rewrite Core.second_level_root_tiles_length by exact Hroot_size_len.
    lia.
  }
  assert (Hroots_len2 : List.length roots2 = Core.ptb_len band).
  {
    subst roots2.
    rewrite Core.second_level_root_tiles_length by exact Hroot_size_len.
    lia.
  }
  assert (Hroots_children1 :
    List.length roots1 = List.length children1).
  {
    subst roots1 children1.
    unfold Core.second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite Core.second_level_root_tiles_length by exact Hroot_size_len.
    lia.
  }
  assert (Hroots_children2 :
    List.length roots2 = List.length children2).
  {
    subst roots2 children2.
    unfold Core.second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite Core.second_level_root_tiles_length by exact Hroot_size_len.
    lia.
  }
  assert (Hband_rows1 :
    Core.instr_point_ext_band_block_ts band tau1 =
    affine_product (Core.slbr_root_rows recipe) (envv ++ point1)).
  {
    unfold Core.instr_point_ext_band_block_ts.
    rewrite Hts11_old, <- Core.affine_product_skipn,
            <- Core.affine_product_firstn.
    rewrite Hrows_match. reflexivity.
  }
  assert (Hband_rows2 :
    Core.instr_point_ext_band_block_ts band tau2 =
    affine_product (Core.slbr_root_rows recipe) (envv ++ point2)).
  {
    unfold Core.instr_point_ext_band_block_ts.
    rewrite Hts12_old, <- Core.affine_product_skipn,
            <- Core.affine_product_firstn.
    rewrite Hrows_match. reflexivity.
  }
  set (prefix1 := Core.instr_point_ext_band_prefix_ts band tau1).
  set (prefix2 := Core.instr_point_ext_band_prefix_ts band tau2).
  set (band_ts1 := Core.instr_point_ext_band_block_ts band tau1).
  set (band_ts2 := Core.instr_point_ext_band_block_ts band tau2).
  set (tiles1 :=
    Core.second_level_schedule_tile_block_by_layout
      Core.SecondLevelGrouped recipe envv point1).
  set (tiles2 :=
    Core.second_level_schedule_tile_block_by_layout
      Core.SecondLevelGrouped recipe envv point2).
  set (suffix1 :=
    skipn (Core.ptb_start band + Core.ptb_len band)%nat
      (Core.Tiling.PL.ip_time_stamp1_ext tau1)).
  set (suffix2 :=
    skipn (Core.ptb_start band + Core.ptb_len band)%nat
      (Core.Tiling.PL.ip_time_stamp1_ext tau2)).
  assert (Hprefix_len : List.length prefix1 = List.length prefix2).
  {
    subst prefix1 prefix2.
    unfold Core.instr_point_ext_band_prefix_ts.
    rewrite !firstn_length, Hts11_old, Hts12_old.
    unfold affine_product. rewrite !map_length.
    pose proof
      (Core.infer_pinstr_second_level_band_bound _ _ _ _ Hinfer1).
    lia.
  }
  assert (Hold_split1 :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    prefix1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite <- firstn_skipn with (n := Core.ptb_start band)
      (l := Core.Tiling.PL.ip_time_stamp1_ext tau1) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := Core.ptb_len band)
      (l := skipn (Core.ptb_start band)
         (Core.Tiling.PL.ip_time_stamp1_ext tau1)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hold_split2 :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    prefix2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite <- firstn_skipn with (n := Core.ptb_start band)
      (l := Core.Tiling.PL.ip_time_stamp1_ext tau2) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := Core.ptb_len band)
      (l := skipn (Core.ptb_start band)
         (Core.Tiling.PL.ip_time_stamp1_ext tau2)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hsched_before_env :
    exact_listzzs_cols
      (List.length envv + Core.Tiling.PL.pi_depth before_pi1)
      (Core.Tiling.PL.pi_schedule before_pi1)).
  { rewrite <- Hlen_env. exact Hsched_before. }
  assert (Hexpected_ts1 :
    affine_product
      (Core.stripmine_second_level_schedule_after_env_by_layout
         Core.SecondLevelGrouped
         (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1) band)
      (Core.Tiling.PL.ip_index_ext tau1) =
    prefix1 ++ tiles1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1 tiles1.
    unfold Core.instr_point_ext_band_prefix_ts,
           Core.instr_point_ext_band_block_ts,
           Core.second_level_schedule_tile_block_by_layout.
    rewrite Hidx_split1, Hadded_tiles1.
    assert (Henv_cols :
      (List.length envv <=
       List.length envv + Core.Tiling.PL.pi_depth before_pi1)%nat) by lia.
    pose proof
      (Core.stripmine_second_level_schedule_after_env_by_layout_eval
         Core.SecondLevelGrouped
         (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1) band
         (List.length envv + Core.Tiling.PL.pi_depth before_pi1)
         envv roots1 children1 point1 Hsched_before_env Henv_cols
         eq_refl Hroots_len1 Hroots_children1) as Heval1.
    rewrite <- Hts11_old in Heval1.
    subst roots1 children1.
    unfold Core.second_level_schedule_tile_block.
    repeat rewrite app_assoc in Heval1.
    repeat rewrite app_assoc.
    exact Heval1.
  }
  assert (Hexpected_ts2 :
    affine_product
      (Core.stripmine_second_level_schedule_after_env_by_layout
         Core.SecondLevelGrouped
         (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1) band)
      (Core.Tiling.PL.ip_index_ext tau2) =
    prefix2 ++ tiles2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2 tiles2.
    unfold Core.instr_point_ext_band_prefix_ts,
           Core.instr_point_ext_band_block_ts,
           Core.second_level_schedule_tile_block_by_layout.
    rewrite Hidx_split2, Hadded_tiles2.
    assert (Henv_cols :
      (List.length envv <=
       List.length envv + Core.Tiling.PL.pi_depth before_pi1)%nat) by lia.
    pose proof
      (Core.stripmine_second_level_schedule_after_env_by_layout_eval
         Core.SecondLevelGrouped
         (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1) band
         (List.length envv + Core.Tiling.PL.pi_depth before_pi1)
         envv roots2 children2 point2 Hsched_before_env Henv_cols
         eq_refl Hroots_len2 Hroots_children2) as Heval2.
    rewrite <- Hts12_old in Heval2.
    subst roots2 children2.
    unfold Core.second_level_schedule_tile_block.
    repeat rewrite app_assoc in Heval2.
    repeat rewrite app_assoc.
    exact Heval2.
  }
  pose proof
    (Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ (Core.Tiling.PL.ip_index_ext tau1)
       Hsched_match) as Htime_eq1.
  pose proof
    (Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ (Core.Tiling.PL.ip_index_ext tau2)
       Hsched_match) as Htime_eq2.
  rewrite <- Hts21_after in Htime_eq1.
  rewrite <- Hts22_after in Htime_eq2.
  rewrite Hlen_env, Hexpected_ts1 in Htime_eq1.
  rewrite Hlen_env, Hexpected_ts2 in Htime_eq2.
  assert (Hnew_not_lt :
    lex_compare
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (Core.Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Core.Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band_ts2 ++ suffix2) <> Lt).
  {
    assert (Hcompare :
      lex_compare
        (Core.Tiling.PL.ip_time_stamp2_ext tau1)
        (Core.Tiling.PL.ip_time_stamp2_ext tau2) =
      lex_compare
        (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
        (prefix2 ++ tiles2 ++ band_ts2 ++ suffix2)).
    {
      transitivity
        (lex_compare
           (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
           (Core.Tiling.PL.ip_time_stamp2_ext tau2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Hprefix_eq : prefix1 = prefix2).
  {
    unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hold_split1, Hold_split2 in Hold.
    repeat rewrite <- app_assoc in Hnew_expected_not_lt.
    eapply Core.preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  assert (Hband_ts_len : List.length band_ts1 = List.length band_ts2).
  {
    subst band_ts1 band_ts2.
    rewrite Hband_rows1, Hband_rows2.
    unfold affine_product. rewrite !map_length.
    reflexivity.
  }
  assert (Htiles_eq : band_ts1 = band_ts2 -> tiles1 = tiles2).
  {
    intro Hband_eq_ts.
    subst tiles1 tiles2 band_ts1 band_ts2.
    eapply Core.second_level_schedule_tile_block_by_layout_eq_common_sizes;
      try reflexivity.
    rewrite <- Hband_rows1, <- Hband_rows2.
    exact Hband_eq_ts.
  }
  assert (Htiles_mono :
    listz_pointwise_le band_ts1 band_ts2 ->
    listz_pointwise_le tiles1 tiles2).
  {
    intro Hband_le.
    subst tiles1 tiles2 band_ts1 band_ts2.
    eapply
      Core.second_level_schedule_tile_block_by_layout_pointwise_le_common_sizes;
      try reflexivity; eauto.
    rewrite <- Hband_rows1, <- Hband_rows2.
    exact Hband_le.
  }
  unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (Core.stripmined_reversal_implies_decreasing_band_component
       prefix1 prefix2 tiles1 tiles2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_ts_len Htiles_eq Htiles_mono
       Hold Hnew_expected_not_lt)
    as [Hslice [dim [x [y [Hx [Hy Hgt]]]]]].
  assert (Hband_ts1_len :
    List.length band_ts1 = Core.ptb_len band).
  {
    subst band_ts1. rewrite Hband_rows1.
    unfold affine_product. rewrite List.map_length. lia.
  }
  assert (Hdim : (dim < Core.ptb_len band)%nat).
  {
    rewrite <- Hband_ts1_len.
    apply nth_error_Some. rewrite Hx. discriminate.
  }
  exists band.
  split; [reflexivity|].
  split.
  - rewrite <- Hsame. exact Hband.
  - split.
    + unfold Core.instr_point_ext_same_band_slice. exact Hslice.
    + exists dim, x, y.
      repeat split; try assumption.
      * eapply Core.nth_error_band_block_to_full; eauto.
      * eapply Core.nth_error_band_block_to_full; eauto.
Qed.

Lemma ordinary_stripmine_expected_timestamp_prefix :
  forall env_size before_sched band point,
    Core.ptb_start band = 1%nat ->
    exists rest,
      affine_product
        (Core.stripmine_schedule_after_env env_size before_sched band)
        point =
      firstn 1
        (affine_product
           (Core.Tiling.lift_schedule_after_env
              (Core.ptb_len band) env_size before_sched)
           point) ++
      rest.
Proof.
  intros env_size before_sched band point Hstart.
  unfold Core.stripmine_schedule_after_env.
  rewrite Hstart.
  cbn beta iota zeta.
  repeat rewrite Core.affine_product_app.
  rewrite Core.affine_product_firstn.
  eexists.
  reflexivity.
Qed.

Lemma phase_separated_ordinary_reversal_same_statement :
  forall before_pis before_ctxt before_vars
         after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    Core.infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    Core.pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    unique_phase_schedules before_pis bands ->
    Core.Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Core.Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Core.Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    forall ipl_ext tau1 tau2,
      Core.Tiling.PL.flatten_instrs_ext
        envv
        (Core.Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Core.Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Core.Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      Core.Tiling.PL.ip_nth_ext tau1 =
      Core.Tiling.PL.ip_nth_ext tau2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws bands envv
         Hlen_env Hinfer Hbands Hunique
         Hprog Hwf_ws Hsizes_ws Hdepths
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  pose proof Hunique as Hunique0.
  destruct Hunique as [phases [Hheads [Hstarts Hnodup]]].
  assert (Hwf_ws_env :
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct
    (Core.pprog_tiling_bands_cert_lengths
       _ _ _ _ _ Hbands)
    as [Hlen_after [Hlen_ws Hlen_bands]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [_ [_ [_ [_ [Hbel1 _]]]]]]]]]]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [_ [_ [_ [_ [Hbel2 _]]]]]]]]]]].
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    apply nth_error_None in Hband1.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    apply nth_error_None in Hband2.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  pose proof
    (Core.infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band1
       Hinfer Hbefore1 Hw1 Hband1) as Hinfer1.
  pose proof
    (Core.infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands (Core.Tiling.PL.ip_nth_ext tau2)
       before_pi2 w2 band2
       Hinfer Hbefore2 Hw2 Hband2) as Hinfer2.
  pose proof
    (Core.pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 w1 band1
       Hbands Hbefore1 Hafter1 Hw1 Hband1) as Hcert1.
  pose proof
    (Core.pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Core.Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 w2 band2
       Hbands Hbefore2 Hafter2 Hw2 Hband2) as Hcert2.
  destruct Hcert1 as [Hmatch1 Hsched1].
  destruct Hcert2 as [Hmatch2 Hsched2].
  unfold Core.pinstr_tiling_band_matches in Hmatch1, Hmatch2.
  destruct (Core.schedule_rows_of_links w1) as [rows1|] eqn:Hrows1;
    try contradiction.
  destruct (Core.schedule_rows_of_links w2) as [rows2|] eqn:Hrows2;
    try contradiction.
  destruct Hmatch1 as [Hband_len1 Hrows_match1].
  destruct Hmatch2 as [Hband_len2 Hrows_match2].
  pose proof
    (unique_phase_schedules_band_start
       before_pis bands (Core.Tiling.PL.ip_nth_ext tau1) band1
       Hunique0 Hband1) as Hstart1.
  pose proof
    (unique_phase_schedules_band_start
       before_pis bands (Core.Tiling.PL.ip_nth_ext tau2) band2
       Hunique0 Hband2) as Hstart2.
  unfold Core.Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [_ [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [_ [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert (Hts11_lift :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product
      (Core.Tiling.lift_schedule_after_env
         (List.length (stw_links w1)) (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts11. reflexivity. }
  assert (Hts12_lift :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product
      (Core.Tiling.lift_schedule_after_env
         (List.length (stw_links w2)) (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi2))
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts12. reflexivity. }
  assert (Hts21_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product
      (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. reflexivity. }
  assert (Hts22_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product
      (Core.Tiling.PL.pi_schedule after_pi2)
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. reflexivity. }
  destruct
    (ordinary_stripmine_expected_timestamp_prefix
       (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1)
       band1 (Core.Tiling.PL.ip_index_ext tau1) Hstart1)
    as [rest1 Hexpected1].
  destruct
    (ordinary_stripmine_expected_timestamp_prefix
       (List.length envv) (Core.Tiling.PL.pi_schedule before_pi2)
       band2 (Core.Tiling.PL.ip_index_ext tau2) Hstart2)
    as [rest2 Hexpected2].
  rewrite Hband_len1, <- Hts11_lift in Hexpected1.
  rewrite Hband_len2, <- Hts12_lift in Hexpected2.
  assert (Htime_eq1 :
    is_eq
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1) =
    true).
  {
    rewrite Hts21_after, <- Hexpected1.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. rewrite <- Hlen_env. exact Hsched1.
  }
  assert (Htime_eq2 :
    is_eq
      (Core.Tiling.PL.ip_time_stamp2_ext tau2)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2) =
    true).
  {
    rewrite Hts22_after, <- Hexpected2.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. rewrite <- Hlen_env. exact Hsched2.
  }
  assert (Hnew_not_lt :
    lex_compare
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (Core.Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Core.Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2) <> Lt).
  {
    assert (Hcompare :
      lex_compare
        (Core.Tiling.PL.ip_time_stamp2_ext tau1)
        (Core.Tiling.PL.ip_time_stamp2_ext tau2) =
      lex_compare
        (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
        (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2)).
    {
      transitivity
        (lex_compare
           (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
           (Core.Tiling.PL.ip_time_stamp2_ext tau2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Hprefix_len :
    List.length (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1)) =
    List.length (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2))).
  {
    destruct
      (Forall2_nth_error
         _ _ _ (Core.Tiling.PL.ip_nth_ext tau1)
         before_pis phases before_pi1 Hheads Hbefore1)
      as [phase1 [_ Hhead1]].
    destruct
      (Forall2_nth_error
         _ _ _ (Core.Tiling.PL.ip_nth_ext tau2)
         before_pis phases before_pi2 Hheads Hbefore2)
      as [phase2 [_ Hhead2]].
    unfold constant_schedule_head_value, pinstr_head_constant in
      Hhead1, Hhead2.
    pose proof
      (schedule_head_constant_lift_sound
         _ _ (List.length (stw_links w1)) (List.length envv)
         (Core.Tiling.PL.ip_index_ext tau1) Hhead1) as Hphase_eval1.
    pose proof
      (schedule_head_constant_lift_sound
         _ _ (List.length (stw_links w2)) (List.length envv)
         (Core.Tiling.PL.ip_index_ext tau2) Hhead2) as Hphase_eval2.
    rewrite Hts11_lift, Hts12_lift.
    rewrite Hphase_eval1, Hphase_eval2.
    reflexivity.
  }
  assert (Hprefix :
    firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) =
    firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2)).
  {
    unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1)) in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2)) in Hold.
    eapply Core.preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  rewrite Hts11_lift, Hts12_lift in Hprefix.
  eapply unique_phase_schedules_identify_statement_lifted; eauto.
Qed.

Lemma phase_separated_ordinary_reversal_same_class :
  forall before_pis before_ctxt before_vars
         after_pis ws bands entries envv,
    List.length before_ctxt = List.length envv ->
    Core.infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    Core.pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    infer_phase_class_entries before_pis bands ws = Some entries ->
    phase_class_entries_consistent entries ->
    Core.Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Core.Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Core.Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    forall ipl_ext tau1 tau2,
      Core.Tiling.PL.flatten_instrs_ext
        envv
        (Core.Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Core.Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Core.Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      exists band w1 w2,
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau2) = Some band /\
        nth_error ws (Core.Tiling.PL.ip_nth_ext tau1) = Some w1 /\
        nth_error ws (Core.Tiling.PL.ip_nth_ext tau2) = Some w2 /\
        Core.tile_sizes_of_witness w1 =
        Core.tile_sizes_of_witness w2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws bands entries envv
         Hlen_env Hinfer Hbands Hentries Hconsistent
         Hprog Hwf_ws Hsizes_ws Hdepths
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  assert (Hwf_ws_env :
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct
    (Core.pprog_tiling_bands_cert_lengths
       _ _ _ _ _ Hbands)
    as [Hlen_after [Hlen_ws Hlen_bands]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [_ [_ [_ [_ [Hbel1 _]]]]]]]]]]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [_ [_ [_ [_ [Hbel2 _]]]]]]]]]]].
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    apply nth_error_None in Hband1.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    apply nth_error_None in Hband2.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  destruct
    (infer_phase_class_entries_lengths
       before_pis bands ws entries Hentries)
    as [_ [_ Hentries_len]].
  destruct (nth_error entries (Core.Tiling.PL.ip_nth_ext tau1))
    as [entry1|] eqn:Hentry1.
  2:{
    apply nth_error_None in Hentry1.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error entries (Core.Tiling.PL.ip_nth_ext tau2))
    as [entry2|] eqn:Hentry2.
  2:{
    apply nth_error_None in Hentry2.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  destruct
    (infer_phase_class_entries_nth_error
       before_pis bands ws entries
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 band1 w1 entry1
       Hentries Hbefore1 Hband1 Hw1 Hentry1)
    as [Hhead1 [Hstart1 [Hentry_band1 Hentry_sizes1]]].
  destruct
    (infer_phase_class_entries_nth_error
       before_pis bands ws entries
       (Core.Tiling.PL.ip_nth_ext tau2)
       before_pi2 band2 w2 entry2
       Hentries Hbefore2 Hband2 Hw2 Hentry2)
    as [Hhead2 [Hstart2 [Hentry_band2 Hentry_sizes2]]].
  pose proof
    (Core.pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 w1 band1
       Hbands Hbefore1 Hafter1 Hw1 Hband1) as Hcert1.
  pose proof
    (Core.pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Core.Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 w2 band2
       Hbands Hbefore2 Hafter2 Hw2 Hband2) as Hcert2.
  destruct Hcert1 as [Hmatch1 Hsched1].
  destruct Hcert2 as [Hmatch2 Hsched2].
  unfold Core.pinstr_tiling_band_matches in Hmatch1, Hmatch2.
  destruct (Core.schedule_rows_of_links w1) as [rows1|] eqn:Hrows1;
    try contradiction.
  destruct (Core.schedule_rows_of_links w2) as [rows2|] eqn:Hrows2;
    try contradiction.
  destruct Hmatch1 as [Hband_len1 Hrows_match1].
  destruct Hmatch2 as [Hband_len2 Hrows_match2].
  unfold Core.Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [_ [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [_ [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert (Hts11_lift :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product
      (Core.Tiling.lift_schedule_after_env
         (List.length (stw_links w1)) (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts11. reflexivity. }
  assert (Hts12_lift :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product
      (Core.Tiling.lift_schedule_after_env
         (List.length (stw_links w2)) (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi2))
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts12. reflexivity. }
  assert (Hts21_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product
      (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. reflexivity. }
  assert (Hts22_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product
      (Core.Tiling.PL.pi_schedule after_pi2)
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. reflexivity. }
  destruct
    (ordinary_stripmine_expected_timestamp_prefix
       (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1)
       band1 (Core.Tiling.PL.ip_index_ext tau1) Hstart1)
    as [rest1 Hexpected1].
  destruct
    (ordinary_stripmine_expected_timestamp_prefix
       (List.length envv) (Core.Tiling.PL.pi_schedule before_pi2)
       band2 (Core.Tiling.PL.ip_index_ext tau2) Hstart2)
    as [rest2 Hexpected2].
  rewrite Hband_len1, <- Hts11_lift in Hexpected1.
  rewrite Hband_len2, <- Hts12_lift in Hexpected2.
  assert (Htime_eq1 :
    is_eq
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1) =
    true).
  {
    rewrite Hts21_after, <- Hexpected1.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. rewrite <- Hlen_env. exact Hsched1.
  }
  assert (Htime_eq2 :
    is_eq
      (Core.Tiling.PL.ip_time_stamp2_ext tau2)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2) =
    true).
  {
    rewrite Hts22_after, <- Hexpected2.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. rewrite <- Hlen_env. exact Hsched2.
  }
  assert (Hnew_not_lt :
    lex_compare
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (Core.Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Core.Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
      (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2) <> Lt).
  {
    assert (Hcompare :
      lex_compare
        (Core.Tiling.PL.ip_time_stamp2_ext tau1)
        (Core.Tiling.PL.ip_time_stamp2_ext tau2) =
      lex_compare
        (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
        (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2) ++ rest2)).
    {
      transitivity
        (lex_compare
           (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) ++ rest1)
           (Core.Tiling.PL.ip_time_stamp2_ext tau2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Hphase_eval1 :
    firstn 1
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            (List.length (stw_links w1)) (List.length envv)
            (Core.Tiling.PL.pi_schedule before_pi1))
         (Core.Tiling.PL.ip_index_ext tau1)) =
    [pce_phase entry1]).
  {
    eapply schedule_head_constant_lift_sound.
    exact Hhead1.
  }
  assert (Hphase_eval2 :
    firstn 1
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            (List.length (stw_links w2)) (List.length envv)
            (Core.Tiling.PL.pi_schedule before_pi2))
         (Core.Tiling.PL.ip_index_ext tau2)) =
    [pce_phase entry2]).
  {
    eapply schedule_head_constant_lift_sound.
    exact Hhead2.
  }
  assert (Hprefix_len :
    List.length (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1)) =
    List.length (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2))).
  {
    rewrite Hts11_lift, Hts12_lift, Hphase_eval1, Hphase_eval2.
    reflexivity.
  }
  assert (Hprefix :
    firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1) =
    firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2)).
  {
    unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau1)) in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext tau2)) in Hold.
    eapply Core.preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  assert (Hphase : pce_phase entry1 = pce_phase entry2).
  {
    rewrite Hts11_lift, Hts12_lift, Hphase_eval1, Hphase_eval2 in Hprefix.
    inversion Hprefix.
    reflexivity.
  }
  destruct
    (Hconsistent entry1 entry2
       (nth_error_In entries _ Hentry1)
       (nth_error_In entries _ Hentry2)
       Hphase)
    as [Hsame_band Hsame_sizes].
  rewrite Hentry_band1, Hentry_band2 in Hsame_band.
  rewrite Hentry_sizes1, Hentry_sizes2 in Hsame_sizes.
  exists band1, w1, w2.
  split; [reflexivity|].
  split.
  - rewrite Hsame_band.
    reflexivity.
  - repeat split; assumption.
Qed.

Lemma phase_class_ordinary_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars
         after_pis ws bands entries envv,
    List.length before_ctxt = List.length envv ->
    Core.infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    Core.pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    infer_phase_class_entries before_pis bands ws = Some entries ->
    phase_class_entries_consistent entries ->
    Core.Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Core.Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Core.Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Core.uniform_schedule_arity before_pis ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    forall ipl_ext tau1 tau2,
      Core.Tiling.PL.flatten_instrs_ext
        envv
        (Core.Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Core.Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Core.Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      exists band,
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau2) = Some band /\
        Core.instr_point_ext_same_band_slice band tau1 tau2 /\
        Core.instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws bands entries envv
         Hlen_env Hinfer Hbands Hentries Hconsistent
         Hprog Hwf_ws Hsizes_ws Hdepths Harity Hwf_before
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (phase_separated_ordinary_reversal_same_class
       before_pis before_ctxt before_vars
       after_pis ws bands entries envv
       Hlen_env Hinfer Hbands Hentries Hconsistent
       Hprog Hwf_ws Hsizes_ws Hdepths
       ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew)
    as [band [w1 [w2
         [Hband1 [Hband2 [Hw1 [Hw2 Hsame_sizes]]]]]]].
  eapply
    (Core.ordinary_pair_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands envv
       ipl_ext tau1 tau2); eauto.
  - intros band1 band2 Hband1' Hband2'.
    rewrite Hband1 in Hband1'.
    rewrite Hband2 in Hband2'.
    inversion Hband1'; inversion Hband2'; subst.
    reflexivity.
  - intros witness1 witness2 Hw1' Hw2'.
    rewrite Hw1 in Hw1'.
    rewrite Hw2 in Hw2'.
    inversion Hw1'; inversion Hw2'; subst.
    exact Hsame_sizes.
Qed.

Lemma phase_separated_ordinary_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars
         after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    Core.infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    Core.pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    unique_phase_schedules before_pis bands ->
    Core.Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Core.Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Core.Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    forall ipl_ext tau1 tau2,
      Core.Tiling.PL.flatten_instrs_ext
        envv
        (Core.Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Core.Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Core.Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      exists band,
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Core.Tiling.PL.ip_nth_ext tau2) = Some band /\
        Core.instr_point_ext_same_band_slice band tau1 tau2 /\
        Core.instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws bands envv
         Hlen_env Hinfer Hbands Hunique
         Hprog Hwf_ws Hsizes_ws Hdepths Hwf_before
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  assert (Hsame :
    Core.Tiling.PL.ip_nth_ext tau1 =
    Core.Tiling.PL.ip_nth_ext tau2).
  {
    eapply phase_separated_ordinary_reversal_same_statement; eauto.
  }
  assert (Hwf_ws_env :
    Forall
      (Core.Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct
    (Core.pprog_tiling_bands_cert_lengths
       _ _ _ _ _ Hbands)
    as [Hlen_after [Hlen_ws Hlen_bands]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [Hwf_stmt1 [Hsizes1 [Hpoint_depth1
         [Hpref1 [Hbel1 Hlen1]]]]]]]]]]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [Hwf_stmt2 [Hsizes2 [Hpoint_depth2
         [Hpref2 [Hbel2 Hlen2]]]]]]]]]]].
  rewrite <- Hsame in Hbefore2, Hafter2, Hw2.
  rewrite Hbefore1 in Hbefore2.
  inversion Hbefore2; subst before_pi2; clear Hbefore2.
  rewrite Hafter1 in Hafter2.
  inversion Hafter2; subst after_pi2; clear Hafter2.
  rewrite Hw1 in Hw2.
  inversion Hw2; subst w2; clear Hw2.
  destruct (nth_error bands (Core.Tiling.PL.ip_nth_ext tau1))
    as [band|] eqn:Hband.
  2:{
    apply nth_error_None in Hband.
    assert (Hlt :
      (Core.Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  pose proof
    (Core.infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band
       Hinfer Hbefore1 Hw1 Hband) as Hinfer1.
  pose proof
    (Core.pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 w1 band
       Hbands Hbefore1 Hafter1 Hw1 Hband) as Hcert1.
  pose proof
    (Core.Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Core.Tiling.compiled_pinstr_tiling_witness ws)
       (Core.Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1
       (Core.Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Core.Tiling.nth_error_map_some
          _ _ Core.Tiling.compiled_pinstr_tiling_witness
          ws (Core.Tiling.PL.ip_nth_ext tau1) w1 Hw1)) as Hstmt.
  pose proof
    (Core.tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt Hpoint_depth1) as Hafter_wit.
  pose proof
    (Core.Tiling.Forall_nth_error
       _ _ before_pis (Core.Tiling.PL.ip_nth_ext tau1) before_pi1
       Hwf_before Hbefore1) as Hwf_before1.
  assert (Hstmt_env :
    Core.Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi1 after_pi1
      (Core.Tiling.compiled_pinstr_tiling_witness w1)).
  { rewrite <- Hlen_env. exact Hstmt. }
  unfold Core.Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  destruct Hafter_wit as [Hafter_pw Hafter_depth].
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  destruct Hwf_before1 as [Hwf_before1_core _].
  destruct Hwf_before1_core as
      [_ [Hcols_before [_ [_ [_ [_ [_ [Hsched_before _]]]]]]]].
  set (added1 :=
    Core.Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  set (point1 :=
    Core.Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau1)).
  set (added2 :=
    Core.Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau2)).
  set (point2 :=
    Core.Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Core.Tiling.PL.ip_index_ext tau2)).
  assert (Hadded_len1 :
    List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Core.Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite <- Hafter_depth in Hlen1.
    rewrite Hafter_pw in Hlen1.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hadded_len2 :
    List.length added2 = List.length (stw_links w1)).
  {
    subst added2.
    eapply Core.Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite <- Hafter_depth in Hlen2.
    rewrite Hafter_pw in Hlen2.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Core.Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite <- Hafter_depth in Hlen1.
    rewrite Hafter_pw in Hlen1.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w1).
  {
    subst point2.
    eapply Core.Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite <- Hafter_depth in Hlen2.
    rewrite Hafter_pw in Hlen2.
    unfold PointWitness.witness_current_point_dim,
           PointWitness.witness_base_point_dim,
           PointWitness.witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hidx_split1 :
    Core.Tiling.PL.ip_index_ext tau1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Core.Tiling.PL.ip_index_ext tau1) ++
       Core.Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau1) ++
       Core.Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau1)).
    - apply Core.Tiling.tiled_index_split.
    - rewrite Hpref1. reflexivity.
  }
  assert (Hidx_split2 :
    Core.Tiling.PL.ip_index_ext tau2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Core.Tiling.PL.ip_index_ext tau2) ++
       Core.Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau2) ++
       Core.Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Core.Tiling.PL.ip_index_ext tau2)).
    - apply Core.Tiling.tiled_index_split.
    - rewrite Hpref2. reflexivity.
  }
  assert (Hts11_old :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product (Core.Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    rewrite Hts11. cbn [Core.Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Core.Tiling.lift_schedule_after_env.
    eapply Core.Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts12_old :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product (Core.Tiling.PL.pi_schedule before_pi1) (envv ++ point2)).
  {
    rewrite Hts12. cbn [Core.Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Core.Tiling.lift_schedule_after_env.
    eapply Core.Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts21_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. cbn [Core.Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hts22_after :
    Core.Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product (Core.Tiling.PL.pi_schedule after_pi1)
      (Core.Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. cbn [Core.Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Core.Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Core.Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt_env
         (Core.Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Core.Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete1.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete1 Hafter_dom1). tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 envv (stw_links w1)).
  {
    pose proof
      (Core.Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Core.Tiling.compiled_pinstr_tiling_witness w1)
         added2 point2 Hstmt_env
         (Core.Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Core.Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len2 Hpoint_len2 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete2.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete2 Hafter_dom2). tauto.
  }
  unfold Core.pinstr_tiling_band_cert in Hcert1.
  destruct Hcert1 as [Hmatch Hsched_match].
  unfold Core.pinstr_tiling_band_matches in Hmatch.
  destruct (Core.schedule_rows_of_links w1) as [rows|] eqn:Hrows;
    try contradiction.
  destruct Hmatch as [Hband_len Hrows_match].
  assert (Hband_rows1 :
    Core.instr_point_ext_band_block_ts band tau1 =
    affine_product rows (envv ++ point1)).
  {
    unfold Core.instr_point_ext_band_block_ts.
    rewrite Hts11_old, <- Core.affine_product_skipn,
            <- Core.affine_product_firstn.
    rewrite Hrows_match. reflexivity.
  }
  assert (Hband_rows2 :
    Core.instr_point_ext_band_block_ts band tau2 =
    affine_product rows (envv ++ point2)).
  {
    unfold Core.instr_point_ext_band_block_ts.
    rewrite Hts12_old, <- Core.affine_product_skipn,
            <- Core.affine_product_firstn.
    rewrite Hrows_match. reflexivity.
  }
  set (prefix1 := Core.instr_point_ext_band_prefix_ts band tau1).
  set (prefix2 := Core.instr_point_ext_band_prefix_ts band tau2).
  set (band_ts1 := Core.instr_point_ext_band_block_ts band tau1).
  set (band_ts2 := Core.instr_point_ext_band_block_ts band tau2).
  set (suffix1 :=
    skipn (Core.ptb_start band + Core.ptb_len band)%nat
      (Core.Tiling.PL.ip_time_stamp1_ext tau1)).
  set (suffix2 :=
    skipn (Core.ptb_start band + Core.ptb_len band)%nat
      (Core.Tiling.PL.ip_time_stamp1_ext tau2)).
  assert (Hprefix_len : List.length prefix1 = List.length prefix2).
  {
    subst prefix1 prefix2.
    unfold Core.instr_point_ext_band_prefix_ts.
    rewrite !firstn_length, Hts11_old, Hts12_old.
    unfold affine_product. rewrite !map_length. reflexivity.
  }
  assert (Hband_ts_len : List.length band_ts1 = List.length band_ts2).
  {
    subst band_ts1 band_ts2.
    unfold Core.instr_point_ext_band_block_ts.
    rewrite !firstn_length, !skipn_length, Hts11_old, Hts12_old.
    unfold affine_product. rewrite !map_length. reflexivity.
  }
  assert (Hold_split1 :
    Core.Tiling.PL.ip_time_stamp1_ext tau1 =
    prefix1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite <- firstn_skipn with (n := Core.ptb_start band)
      (l := Core.Tiling.PL.ip_time_stamp1_ext tau1) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := Core.ptb_len band)
      (l := skipn (Core.ptb_start band)
         (Core.Tiling.PL.ip_time_stamp1_ext tau1)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hold_split2 :
    Core.Tiling.PL.ip_time_stamp1_ext tau2 =
    prefix2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite <- firstn_skipn with (n := Core.ptb_start band)
      (l := Core.Tiling.PL.ip_time_stamp1_ext tau2) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := Core.ptb_len band)
      (l := skipn (Core.ptb_start band)
         (Core.Tiling.PL.ip_time_stamp1_ext tau2)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hsched_before_env :
    exact_listzzs_cols
      (List.length envv + Core.Tiling.PL.pi_depth before_pi1)
      (Core.Tiling.PL.pi_schedule before_pi1)).
  { rewrite <- Hlen_env. exact Hsched_before. }
  assert (Hexpected_ts1 :
    affine_product
      (Core.stripmine_schedule_after_env
         (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1) band)
      (Core.Tiling.PL.ip_index_ext tau1) =
    prefix1 ++ added1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite Hidx_split1.
    pose proof
      (Core.stripmine_schedule_after_env_eval
         (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1) band
         (List.length envv + Core.Tiling.PL.pi_depth before_pi1)
         envv added1 point1 Hsched_before_env
         ltac:(lia) eq_refl
         (eq_trans Hadded_len1 (eq_sym Hband_len))) as Heval1.
    rewrite <- Hts11_old in Heval1.
    exact Heval1.
  }
  assert (Hexpected_ts2 :
    affine_product
      (Core.stripmine_schedule_after_env
         (List.length envv)
         (Core.Tiling.PL.pi_schedule before_pi1) band)
      (Core.Tiling.PL.ip_index_ext tau2) =
    prefix2 ++ added2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite Hidx_split2.
    pose proof
      (Core.stripmine_schedule_after_env_eval
         (List.length envv) (Core.Tiling.PL.pi_schedule before_pi1) band
         (List.length envv + Core.Tiling.PL.pi_depth before_pi1)
         envv added2 point2 Hsched_before_env
         ltac:(lia) eq_refl
         (eq_trans Hadded_len2 (eq_sym Hband_len))) as Heval2.
    rewrite <- Hts12_old in Heval2.
    exact Heval2.
  }
  assert (Htime_eq1 :
    is_eq
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (prefix1 ++ added1 ++ band_ts1 ++ suffix1) = true).
  {
    rewrite Hts21_after, <- Hexpected_ts1.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. rewrite <- Hlen_env. exact Hsched_match.
  }
  assert (Htime_eq2 :
    is_eq
      (Core.Tiling.PL.ip_time_stamp2_ext tau2)
      (prefix2 ++ added2 ++ band_ts2 ++ suffix2) = true).
  {
    rewrite Hts22_after, <- Hexpected_ts2.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. rewrite <- Hlen_env. exact Hsched_match.
  }
  assert (Hnew_not_lt :
    lex_compare
      (Core.Tiling.PL.ip_time_stamp2_ext tau1)
      (Core.Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Core.Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
      (prefix2 ++ added2 ++ band_ts2 ++ suffix2) <> Lt).
  {
    assert (Hcompare :
      lex_compare
        (Core.Tiling.PL.ip_time_stamp2_ext tau1)
        (Core.Tiling.PL.ip_time_stamp2_ext tau2) =
      lex_compare
        (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
        (prefix2 ++ added2 ++ band_ts2 ++ suffix2)).
    {
      transitivity
        (lex_compare
           (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
           (Core.Tiling.PL.ip_time_stamp2_ext tau2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Htiles_eq : band_ts1 = band_ts2 -> added1 = added2).
  {
    intro Hband_eq_ts.
    rewrite Hadded_eq1, Hadded_eq2.
    eapply Core.eval_tile_links_from_common_recipe_affine_product_eq
      with (rows := rows)
           (sizes := List.map tl_tile_size (stw_links w1)).
    - exact Hpoint_len1.
    - exact Hpoint_len2.
    - exact Hrows.
    - reflexivity.
    - exact Hwf_stmt1.
    - exact Hparams1.
    - rewrite <- Hband_rows1, <- Hband_rows2.
      exact Hband_eq_ts.
  }
  assert (Htiles_mono :
    Core.listz_pointwise_le band_ts1 band_ts2 ->
    Core.listz_pointwise_le added1 added2).
  {
    intro Hband_le.
    rewrite Hadded_eq1, Hadded_eq2.
    eapply Core.common_recipe_band_pointwise_le_implies_tiles_pointwise_le
      with (rows1 := rows) (rows2 := rows)
           (sizes := List.map tl_tile_size (stw_links w1)).
    - exact Hpoint_len1.
    - exact Hpoint_len2.
    - exact Hrows.
    - exact Hrows.
    - reflexivity.
    - reflexivity.
    - exact Hwf_stmt1.
    - exact Hwf_stmt1.
    - exact Hparams1.
    - exact Hparams1.
    - exact Hsizes1.
    - rewrite <- Hband_rows1, <- Hband_rows2.
      exact Hband_le.
  }
  unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (Core.stripmined_reversal_implies_decreasing_band_component
       prefix1 prefix2 added1 added2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_ts_len Htiles_eq Htiles_mono
       Hold Hnew_expected_not_lt)
    as [Hslice [dim [x [y [Hx [Hy Hgt]]]]]].
  assert (Hband_ts1_len :
    List.length band_ts1 = Core.ptb_len band).
  {
    subst band_ts1. rewrite Hband_rows1.
    unfold affine_product. rewrite List.map_length.
    pose proof (Core.schedule_rows_of_links_length _ _ Hrows) as Hrows_len.
    lia.
  }
  assert (Hdim : (dim < Core.ptb_len band)%nat).
  {
    rewrite <- Hband_ts1_len.
    apply nth_error_Some. rewrite Hx. discriminate.
  }
  exists band.
  split; [reflexivity|].
  split.
  - rewrite <- Hsame. exact Hband.
  - split.
    + unfold Core.instr_point_ext_same_band_slice. exact Hslice.
    + exists dim, x, y.
      repeat split; try assumption.
      * eapply Core.nth_error_band_block_to_full; eauto.
      * eapply Core.nth_error_band_block_to_full; eauto.
Qed.

Definition check_pprog_phase_separated_ordinary_direct
    (before after: Core.Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  if Core.TilingCheck.check_pprog_tiling_sourceb before after ws then
    if Core.check_pprog_tiling_schedule_stripminedb before after ws then
      match Core.infer_pinstr_list_tiling_bands before_pis ws with
      | Some bands =>
          if Core.check_uniform_schedule_arityb before_pis then
            if check_phase_class_consistencyb before_pis bands ws then
              Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct
                (List.length before_ctxt) before_pis after_pis ws bands
            else pure false
          else pure false
      | None => pure false
      end
    else pure false
  else pure false.

Lemma check_pprog_phase_separated_ordinary_direct_true_inv :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    mayReturn
      (check_pprog_phase_separated_ordinary_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars)
         ws)
      true ->
    exists bands,
      Core.TilingCheck.check_pprog_tiling_sourceb
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars)
        ws = true /\
      Core.check_pprog_tiling_schedule_stripminedb
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars)
        ws = true /\
      Core.infer_pinstr_list_tiling_bands before_pis ws = Some bands /\
      Core.check_uniform_schedule_arityb before_pis = true /\
      check_phase_class_consistencyb before_pis bands ws = true /\
      mayReturn
        (Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct
           (List.length before_ctxt) before_pis after_pis ws bands)
        true.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hcheck.
  unfold check_pprog_phase_separated_ordinary_direct in Hcheck.
  destruct
    (Core.TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hsource.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct
    (Core.check_pprog_tiling_schedule_stripminedb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hshape.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct (Core.infer_pinstr_list_tiling_bands before_pis ws)
    as [bands|] eqn:Hinfer.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct (Core.check_uniform_schedule_arityb before_pis)
    eqn:Huniform.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct (check_phase_class_consistencyb before_pis bands ws)
    eqn:Hclasses.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  exists bands.
  repeat split; assumption.
Qed.

Lemma check_pprog_phase_separated_ordinary_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_phase_separated_ordinary_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Core.Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Core.Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  destruct
    (check_pprog_phase_separated_ordinary_direct_true_inv
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hcheck)
    as [bands
         [Hsource
          [Hshape
           [Hinfer
            [Huniform [Hclasses Hcomponent_check]]]]]].
  destruct
    (Core.check_pprog_tiling_schedule_stripminedb_sound_flat
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hshape)
    as [bands' [Hinfer' [Hbands [_ _]]]].
  rewrite Hinfer in Hinfer'.
  inversion Hinfer'; subst bands'; clear Hinfer'.
  pose proof
    (Core.check_uniform_schedule_arityb_sound
       before_pis Huniform) as Harity.
  destruct
    (check_phase_class_consistencyb_sound
       before_pis bands ws Hclasses)
    as [entries [Hentries Hconsistent]].
  pose proof
    (Core.TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
  assert (Hwits :
    Forall2 Core.Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (Core.tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  eapply
    (Core.tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws bands st1 st2); [exact Hsource| |exact Hsem].
  simpl.
  intros envv Hlen_env.
  assert (Hcomposed_wf :
    Forall
      (Core.Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
      (Core.Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply Core.compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  assert (Hcomponentwise :
    Core.pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands).
  {
    eapply
      (Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound
         before_ctxt envv before_pis after_pis ws bands); eauto.
  }
  eapply
    (Core.pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge
       envv before_pis after_pis ws bands); [exact Hcomponentwise|].
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  eapply
    (phase_class_ordinary_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars
       after_pis ws bands entries envv); eauto.
Qed.

Definition infer_pprog_mixed_second_level_shape
    (before after: Core.Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option
        (list Core.pinstr_tiling_band *
         list Core.second_level_band_recipe) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if Core.TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     Core.TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match Core.infer_pinstr_list_second_level_bands before_pis ws with
    | Some (bands, recipes) =>
        if Core.check_pinstr_list_second_level_schedule_symmetricb
             Core.SecondLevelGrouped
             (List.length before_ctxt) before_pis after_pis bands &&
           check_unique_phase_constantsb before_pis bands
        then Some (bands, recipes)
        else None
    | None => None
    end
  else None.

Definition check_pprog_mixed_second_level_direct
    (before after: Core.Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  if Core.TilingCheck.check_pprog_tiling_sourceb before after ws then
    match infer_pprog_mixed_second_level_shape before after ws with
    | Some (bands, _) =>
        Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct
          (List.length before_ctxt) before_pis after_pis ws bands
    | None => pure false
    end
  else pure false.

Lemma check_pprog_mixed_second_level_direct_true_inv :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    mayReturn
      (check_pprog_mixed_second_level_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars)
         ws)
      true ->
    exists bands recipes,
      Core.TilingCheck.check_pprog_tiling_sourceb
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars)
        ws = true /\
      infer_pprog_mixed_second_level_shape
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars)
        ws = Some (bands, recipes) /\
      mayReturn
        (Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct
           (List.length before_ctxt) before_pis after_pis ws bands)
        true.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hcheck.
  unfold check_pprog_mixed_second_level_direct in Hcheck.
  destruct
    (Core.TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hsource.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct
    (infer_pprog_mixed_second_level_shape
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars)
       ws)
    as [[bands recipes]|] eqn:Hshape.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  exists bands, recipes.
  repeat split; assumption.
Qed.

Lemma infer_pprog_mixed_second_level_shape_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes,
    infer_pprog_mixed_second_level_shape
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = Some (bands, recipes) ->
    Core.infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) /\
    Core.check_pinstr_list_second_level_schedule_symmetricb
      Core.SecondLevelGrouped
      (List.length before_ctxt) before_pis after_pis bands = true /\
    unique_phase_schedules before_pis bands.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes Hshape.
  unfold infer_pprog_mixed_second_level_shape in Hshape.
  destruct
    (Core.TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     Core.TilingCheck.ctxt_ty_eqb before_vars after_vars);
    try discriminate.
  destruct (Core.infer_pinstr_list_second_level_bands before_pis ws)
    as [[bands0 recipes0]|] eqn:Hinfer; try discriminate.
  destruct
    (Core.check_pinstr_list_second_level_schedule_symmetricb
       Core.SecondLevelGrouped (List.length before_ctxt)
       before_pis after_pis bands0) eqn:Hsched;
    try discriminate.
  destruct (check_unique_phase_constantsb before_pis bands0)
    eqn:Hphases; try discriminate.
  inversion Hshape; subst bands0 recipes0; clear Hshape.
  repeat split; auto.
  eapply check_unique_phase_constantsb_sound; exact Hphases.
Qed.

Lemma check_pprog_mixed_second_level_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_mixed_second_level_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Core.Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Core.Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  destruct
    (check_pprog_mixed_second_level_direct_true_inv
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hcheck)
    as [bands [recipes [Hsource [Hshape Hcomponent_check]]]].
  destruct
    (infer_pprog_mixed_second_level_shape_sound
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws bands recipes Hshape)
    as [Hinfer [Hsched Hunique]].
  pose proof
    (Core.TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
  assert (Hwits :
    Forall2 Core.Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (Core.tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  eapply
    (Core.tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws bands st1 st2); [exact Hsource| |exact Hsem].
  simpl.
  intros envv Hlen_env.
  assert (Hcomposed_wf :
    Forall
      (Core.Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
      (Core.Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply Core.compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  assert (Hcomponentwise :
    Core.pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands).
  {
    eapply
      (Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound
         before_ctxt envv before_pis after_pis ws bands); eauto.
  }
  eapply
    (Core.pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge
       envv before_pis after_pis ws bands); [exact Hcomponentwise|].
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  eapply
    (mixed_second_level_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars
       after_pis ws bands recipes envv); eauto.
Qed.

End TilingBandMixedSecondValidator.
