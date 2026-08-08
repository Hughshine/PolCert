Require Import ZArith.
Require Import Lia.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Base.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Require Import AffineValidator.
Require Import Linalg.
Require Import ListExt.
Require Import Misc.
Require Import PolyBase.
Require Import PointWitness.
Require Import Result.
Require Import PolIRs.

Module ParallelValidator (PolIRs : POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module ILSema := PolyLang.ILSema.
Module Instr := PolIRs.Instr.
Module AffineCore := AffineValidator PolIRs.

(** * Proof map

    A certificate for dimension [d] states that instances with the same
    environment and canonical schedule prefix, but different schedule
    coordinates at [d], commute.  All statement schedules are padded to their
    program-wide maximum width, matching the coordinates introduced before
    code generation.  The checker expresses a violation as an affine schedule
    reversal between two synthetic schedule views.  Affine-validator soundness
    yields [parallel_safe_dim_pointwise]; the historical flattened-list
    property [parallel_safe_dim] follows as a compatibility corollary. *)

Record parallel_plan := {
  target_dim : nat
}.

Record parallel_cert := {
  certified_dim : nat
}.

Definition pprog_pis (pp : PolyLang.t) : list PolyLang.PolyInstr :=
  let '(pis, _, _) := pp in pis.

Definition pprog_varctxt (pp : PolyLang.t) : list Instr.ident :=
  let '(_, varctxt, _) := pp in varctxt.

Definition current_coord_schedule_row
  (env_dim depth i : nat) : list Z * Z :=
  (resize (env_dim + depth) (V0 (env_dim + i) ++ [1%Z]), 0%Z).

Definition current_coord_old_schedule
  (env_dim depth d : nat) : list (list Z * Z) :=
  [current_coord_schedule_row env_dim depth d].

Definition current_coord_prefix_schedule
  (env_dim depth d : nat) : list (list Z * Z) :=
  map (current_coord_schedule_row env_dim depth) (seq 0 d).

Definition schedule_width_of_pis (pis : list PolyLang.PolyInstr) : nat :=
  list_max
    (List.map (fun pi => Datatypes.length pi.(PolyLang.pi_schedule)) pis).

Definition schedule_width (pp : PolyLang.t) : nat :=
  schedule_width_of_pis (pprog_pis pp).

Definition padded_pi_schedule
  (env_dim width : nat) (pi : PolyLang.PolyInstr) : list (list Z * Z) :=
  PolyLang.pad_schedule_to_len
    (env_dim + pi.(PolyLang.pi_depth)) width pi.(PolyLang.pi_schedule).

Definition schedule_coord_old_schedule
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : list (list Z * Z) :=
  [nth d (padded_pi_schedule env_dim width pi)
     (PolyLang.zero_affine_function (env_dim + pi.(PolyLang.pi_depth)))].

Definition schedule_coord_prefix_schedule
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : list (list Z * Z) :=
  firstn d (padded_pi_schedule env_dim width pi).

Definition parallel_old_pi
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      schedule_coord_old_schedule env_dim width d pi;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition parallel_new_pi
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      schedule_coord_prefix_schedule env_dim width d pi;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition parallel_old_pprog
  (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  let width := schedule_width_of_pis pis in
  ((List.map (parallel_old_pi (Datatypes.length varctxt) width d) pis,
    varctxt), vars).

Definition parallel_new_pprog
  (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  let width := schedule_width_of_pis pis in
  ((List.map (parallel_new_pi (Datatypes.length varctxt) width d) pis,
    varctxt), vars).

Local Definition parallel_point_ext
  (pp : PolyLang.t) (d : nat)
  (pi : PolyLang.PolyInstr) (tau : PolyLang.InstrPoint) :
  PolyLang.InstrPoint_ext :=
  let env_dim := Datatypes.length (pprog_varctxt pp) in
  let width := schedule_width pp in
  let old_pi := parallel_old_pi env_dim width d pi in
  {|
    PolyLang.ip_nth_ext := tau.(PolyLang.ip_nth);
    PolyLang.ip_index_ext := tau.(PolyLang.ip_index);
    PolyLang.ip_transformation_ext := tau.(PolyLang.ip_transformation);
    PolyLang.ip_access_transformation_ext :=
      PolyLang.current_access_transformation_at env_dim old_pi;
    PolyLang.ip_time_stamp1_ext :=
      [nth d (resize width tau.(PolyLang.ip_time_stamp)) 0%Z];
    PolyLang.ip_time_stamp2_ext :=
      firstn d (resize width tau.(PolyLang.ip_time_stamp));
    PolyLang.ip_instruction_ext := tau.(PolyLang.ip_instruction);
    PolyLang.ip_depth_ext := tau.(PolyLang.ip_depth)
  |}.

Local Definition parallel_pinstr_ext
    (pp : PolyLang.t) (d : nat) (pi : PolyLang.PolyInstr) :
    PolyLang.PolyInstr_ext :=
  let env_dim := Datatypes.length (pprog_varctxt pp) in
  let width := schedule_width pp in
  AffineCore.compose_pinstr_ext_at env_dim
    (parallel_old_pi env_dim width d pi)
    (parallel_new_pi env_dim width d pi).

Local Definition parallel_pinstrs_ext
    (pp : PolyLang.t) (d : nat) : list PolyLang.PolyInstr_ext :=
  let '((pis, varctxt), _) := pp in
  let env_dim := Datatypes.length varctxt in
  let width := schedule_width_of_pis pis in
  AffineCore.compose_pinstrs_ext_at env_dim
    (List.map (parallel_old_pi env_dim width d) pis)
    (List.map (parallel_new_pi env_dim width d) pis).

Definition check_current_view_pinstrb (pi : PolyLang.PolyInstr) : bool :=
  match pi.(PolyLang.pi_point_witness) with
  | PSWIdentity d' => Nat.eqb d' pi.(PolyLang.pi_depth)
  | _ => false
  end.

Definition check_current_view_pprogb (pp : PolyLang.t) : bool :=
  forallb check_current_view_pinstrb (pprog_pis pp).

Definition all_pinstrs_cover_dimb (d : nat) (pp : PolyLang.t) : bool :=
  forallb (fun pi => Nat.ltb d pi.(PolyLang.pi_depth)) (pprog_pis pp).

Definition env_dim_of (ip : PolyLang.InstrPoint) : nat :=
  Nat.sub (Datatypes.length ip.(PolyLang.ip_index)) ip.(PolyLang.ip_depth).

Definition env_prefix_of (ip : PolyLang.InstrPoint) : list Z :=
  firstn (env_dim_of ip) ip.(PolyLang.ip_index).

Definition current_coords_of (ip : PolyLang.InstrPoint) : list Z :=
  skipn (env_dim_of ip) ip.(PolyLang.ip_index).

Definition same_env_of (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  env_prefix_of ip1 = env_prefix_of ip2.

Definition padded_timestamp
  (pp : PolyLang.t) (ip : PolyLang.InstrPoint) : list Z :=
  resize (schedule_width pp) ip.(PolyLang.ip_time_stamp).

Definition same_prefix_before
  (pp : PolyLang.t) (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  firstn d (padded_timestamp pp ip1) =
  firstn d (padded_timestamp pp ip2).

Definition different_dim_at
  (pp : PolyLang.t) (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  nth_error (padded_timestamp pp ip1) d <>
  nth_error (padded_timestamp pp ip2) d.

Definition same_parallel_slice
  (pp : PolyLang.t) (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  same_env_of ip1 ip2 /\
  same_prefix_before pp d ip1 ip2 /\
  different_dim_at pp d ip1 ip2.

Lemma instr_point_sema_eq_except_sched_iff :
  forall ip1 ip2 st1 st2,
    PolyLang.eq_except_sched ip1 ip2 ->
    ILSema.instr_point_sema ip1 st1 st2 <->
    ILSema.instr_point_sema ip2 st1 st2.
Proof.
  intros ip1 ip2 st1 st2 Heq.
  unfold PolyLang.eq_except_sched in Heq.
  destruct Heq as (_ & Hidx & Htf & Hins & _).
  split; intro Hsema; inversion Hsema as [wcs rcs Hsem]; subst.
  - econstructor.
    rewrite <- Hidx, <- Htf, <- Hins.
    exact Hsem.
  - econstructor.
    rewrite Hidx, Htf, Hins.
    exact Hsem.
Qed.

Lemma eq_except_sched_symm :
  forall ip1 ip2,
    PolyLang.eq_except_sched ip1 ip2 ->
    PolyLang.eq_except_sched ip2 ip1.
Proof.
  intros ip1 ip2 Heq.
  unfold PolyLang.eq_except_sched in *.
  destruct Heq as (Hnth & Hidx & Htf & Hins & Hdepth).
  repeat split; symmetry; assumption.
Qed.

Lemma permutable_eq_except_sched :
  forall ip1 ip1' ip2 ip2',
    PolyLang.eq_except_sched ip1 ip1' ->
    PolyLang.eq_except_sched ip2 ip2' ->
    ILSema.Permutable ip1 ip2 ->
    ILSema.Permutable ip1' ip2'.
Proof.
  intros ip1 ip1' ip2 ip2' Heq1 Heq2 Hperm.
  unfold ILSema.Permutable in *.
  intros st1 Halias.
  specialize (Hperm st1 Halias).
  destruct Hperm as [Hfwd Hbwd].
  split.
  - intros st2' st3 Hs1 Hs2.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip1 ip1' st1 st2' Heq1) Hs1) as Hs1'.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip2 ip2' st2' st3 Heq2) Hs2) as Hs2'.
    destruct (Hfwd _ _ Hs1' Hs2') as (st2'' & st3' & Ht1 & Ht2 & Heq).
    exists st2'', st3'. repeat split; auto.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip2 ip2' st1 st2'' Heq2)); exact Ht1.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip1 ip1' st2'' st3' Heq1)); exact Ht2.
  - intros st2' st3 Hs1 Hs2.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip2 ip2' st1 st2' Heq2) Hs1) as Hs1'.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip1 ip1' st2' st3 Heq1) Hs2) as Hs2'.
    destruct (Hbwd _ _ Hs1' Hs2') as (st2'' & st3' & Ht1 & Ht2 & Heq).
    exists st2'', st3'. repeat split; auto.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip1 ip1' st1 st2'' Heq1)); exact Ht1.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip2 ip2' st2'' st3' Heq2)); exact Ht2.
Qed.

(** * Declarative doall property *)

Definition parallel_safe_dim (pp : PolyLang.t) (d : nat) : Prop :=
  forall envv ipl tau1 tau2,
    Datatypes.length envv = Datatypes.length (pprog_varctxt pp) ->
    PolyLang.flatten_instrs envv (pprog_pis pp) ipl ->
    In tau1 ipl ->
    In tau2 ipl ->
    same_parallel_slice pp d tau1 tau2 ->
    ILSema.Permutable tau1 tau2.

Definition parallel_safe_dim_pointwise (pp : PolyLang.t) (d : nat) : Prop :=
  forall tau1 tau2 pi1 pi2,
    nth_error (pprog_pis pp) tau1.(PolyLang.ip_nth) = Some pi1 ->
    nth_error (pprog_pis pp) tau2.(PolyLang.ip_nth) = Some pi2 ->
    PolyLang.belongs_to tau1 pi1 ->
    PolyLang.belongs_to tau2 pi2 ->
    Datatypes.length tau1.(PolyLang.ip_index) =
      (Datatypes.length (pprog_varctxt pp) + pi1.(PolyLang.pi_depth))%nat ->
    Datatypes.length tau2.(PolyLang.ip_index) =
      (Datatypes.length (pprog_varctxt pp) + pi2.(PolyLang.pi_depth))%nat ->
    same_parallel_slice pp d tau1 tau2 ->
    ILSema.Permutable tau1 tau2.

Definition parallel_cert_sound
  (pp : PolyLang.t) (cert : parallel_cert) : Prop :=
  parallel_safe_dim pp cert.(certified_dim).

Definition parallel_cert_pointwise_sound
  (pp : PolyLang.t) (cert : parallel_cert) : Prop :=
  parallel_safe_dim_pointwise pp cert.(certified_dim).

Lemma current_coord_schedule_row_cols :
  forall env_dim depth i,
    Datatypes.length (fst (current_coord_schedule_row env_dim depth i)) =
    (env_dim + depth)%nat.
Proof.
  intros env_dim depth i.
  unfold current_coord_schedule_row.
  simpl.
  rewrite resize_length.
  reflexivity.
Qed.

Lemma exact_listzzs_cols_current_coord_old_schedule :
  forall env_dim depth d,
    exact_listzzs_cols (env_dim + depth)%nat
      (current_coord_old_schedule env_dim depth d).
Proof.
  intros env_dim depth d listz z listzz Hin Heq.
  simpl in Hin.
  destruct Hin as [Hin | []].
  subst listzz.
  inversion Heq; subst.
  apply current_coord_schedule_row_cols.
Qed.

Lemma exact_listzzs_cols_current_coord_prefix_schedule :
  forall env_dim depth d,
    exact_listzzs_cols (env_dim + depth)%nat
      (current_coord_prefix_schedule env_dim depth d).
Proof.
  intros env_dim depth d listz z listzz Hin Heq.
  unfold current_coord_prefix_schedule in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hi _]].
  subst listzz.
  inversion Heq; subst.
  apply current_coord_schedule_row_cols.
Qed.

Lemma schedule_width_ge_pinstr :
  forall pis varctxt vars pi,
    In pi pis ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <=
     schedule_width ((pis, varctxt), vars))%nat.
Proof.
  intros pis varctxt vars pi Hin.
  unfold schedule_width, schedule_width_of_pis, pprog_pis.
  simpl.
  apply list_max_ge.
  rewrite in_map_iff.
  exists pi.
  split; [reflexivity | exact Hin].
Qed.

Lemma padded_pi_schedule_length :
  forall env_dim width pi,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    Datatypes.length (padded_pi_schedule env_dim width pi) = width.
Proof.
  intros env_dim width pi Hlen.
  unfold padded_pi_schedule, PolyLang.pad_schedule_to_len.
  rewrite app_length, repeat_length.
  lia.
Qed.

Lemma exact_listzzs_cols_padded_pi_schedule :
  forall env_dim width pi,
    exact_listzzs_cols
      (env_dim + pi.(PolyLang.pi_depth))%nat pi.(PolyLang.pi_schedule) ->
    exact_listzzs_cols
      (env_dim + pi.(PolyLang.pi_depth))%nat
      (padded_pi_schedule env_dim width pi).
Proof.
  intros env_dim width pi Hcols coeffs c row Hin Heq.
  unfold padded_pi_schedule, PolyLang.pad_schedule_to_len in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - eapply Hcols; eauto.
  - apply repeat_spec in Hin.
    subst row.
    inversion Heq; subst coeffs c.
    unfold PolyLang.zero_affine_function.
    simpl.
    apply repeat_length.
Qed.

Lemma in_firstn :
  forall A n (xs : list A) x,
    In x (firstn n xs) -> In x xs.
Proof.
  intros A n.
  induction n as [|n IH]; intros xs x Hin; destruct xs; simpl in *.
  - contradiction.
  - contradiction.
  - contradiction.
  - destruct Hin as [Hin | Hin]; [left; exact Hin | right; eapply IH; eauto].
Qed.

Lemma exact_listzzs_cols_schedule_coord_old_schedule :
  forall env_dim width d pi,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    (d < width)%nat ->
    exact_listzzs_cols
      (env_dim + pi.(PolyLang.pi_depth))%nat pi.(PolyLang.pi_schedule) ->
    exact_listzzs_cols
      (env_dim + pi.(PolyLang.pi_depth))%nat
      (schedule_coord_old_schedule env_dim width d pi).
Proof.
  intros env_dim width d pi Hlen Hd Hcols coeffs c row Hin Heq.
  simpl in Hin.
  destruct Hin as [Hin | []].
  subst row.
  eapply exact_listzzs_cols_padded_pi_schedule; eauto.
  - apply nth_In.
    rewrite padded_pi_schedule_length by exact Hlen.
    exact Hd.
Qed.

Lemma exact_listzzs_cols_schedule_coord_prefix_schedule :
  forall env_dim width d pi,
    exact_listzzs_cols
      (env_dim + pi.(PolyLang.pi_depth))%nat pi.(PolyLang.pi_schedule) ->
    exact_listzzs_cols
      (env_dim + pi.(PolyLang.pi_depth))%nat
      (schedule_coord_prefix_schedule env_dim width d pi).
Proof.
  intros env_dim width d pi Hcols coeffs c row Hin Heq.
  unfold schedule_coord_prefix_schedule in Hin.
  eapply exact_listzzs_cols_padded_pi_schedule; eauto.
  eapply in_firstn; eauto.
Qed.

Lemma eqdom_parallel_old_pi :
  forall env_dim width d pi,
    PolyLang.eqdom_pinstr pi (parallel_old_pi env_dim width d pi).
Proof.
  intros env_dim width d pi.
  unfold PolyLang.eqdom_pinstr, parallel_old_pi.
  repeat split; reflexivity.
Qed.

Lemma eqdom_parallel_new_pi :
  forall env_dim width d pi,
    PolyLang.eqdom_pinstr pi (parallel_new_pi env_dim width d pi).
Proof.
  intros env_dim width d pi.
  unfold PolyLang.eqdom_pinstr, parallel_new_pi.
  repeat split; reflexivity.
Qed.

Lemma eqdom_parallel_old_new_pi :
  forall env_dim width d pi,
    PolyLang.eqdom_pinstr
      (parallel_old_pi env_dim width d pi)
      (parallel_new_pi env_dim width d pi).
Proof.
  intros env_dim width d pi.
  unfold PolyLang.eqdom_pinstr, parallel_old_pi, parallel_new_pi.
  repeat split; reflexivity.
Qed.

Lemma rel_list_eqdom_parallel_old :
  forall env_dim width d pis,
    rel_list PolyLang.eqdom_pinstr pis
      (List.map (parallel_old_pi env_dim width d) pis).
Proof.
  induction pis as [|pi pis IH]; simpl.
  - constructor.
  - constructor.
    + apply eqdom_parallel_old_pi.
    + exact IH.
Qed.

Lemma rel_list_eqdom_parallel_new :
  forall env_dim width d pis,
    rel_list PolyLang.eqdom_pinstr pis
      (List.map (parallel_new_pi env_dim width d) pis).
Proof.
  induction pis as [|pi pis IH]; simpl.
  - constructor.
  - constructor.
    + apply eqdom_parallel_new_pi.
    + exact IH.
Qed.

Lemma rel_list_eqdom_parallel_old_new :
  forall env_dim width d pis,
    rel_list PolyLang.eqdom_pinstr
      (List.map (parallel_old_pi env_dim width d) pis)
      (List.map (parallel_new_pi env_dim width d) pis).
Proof.
  induction pis as [|pi pis IH]; simpl.
  - constructor.
  - constructor.
    + apply eqdom_parallel_old_new_pi.
    + exact IH.
Qed.

Lemma check_current_view_pinstrb_sound :
  forall pi,
    check_current_view_pinstrb pi = true ->
    pi.(PolyLang.pi_point_witness) = PSWIdentity pi.(PolyLang.pi_depth).
Proof.
  intros pi Hcheck.
  unfold check_current_view_pinstrb in Hcheck.
  destruct (PolyLang.pi_point_witness pi); simpl in Hcheck; try discriminate.
  apply Nat.eqb_eq in Hcheck.
  subst.
  reflexivity.
Qed.

Lemma all_pinstrs_cover_dimb_sound :
  forall pp d pi,
    all_pinstrs_cover_dimb d pp = true ->
    In pi (pprog_pis pp) ->
    (d < pi.(PolyLang.pi_depth))%nat.
Proof.
  intros pp d pi Hcheck Hin.
  unfold all_pinstrs_cover_dimb, pprog_pis in Hcheck.
  eapply forallb_forall in Hcheck; eauto.
  apply Nat.ltb_lt in Hcheck.
  exact Hcheck.
Qed.

Lemma wf_pinstr_affine_parallel_old_pi :
  forall env vars env_dim width d pi,
    PolyLang.wf_pinstr_affine env vars pi ->
    env_dim = Datatypes.length env ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    (d < width)%nat ->
    PolyLang.wf_pinstr_affine env vars (parallel_old_pi env_dim width d pi).
Proof.
  intros env vars env_dim width d pi Hwf Henvdim Hlen Hd.
  unfold PolyLang.wf_pinstr_affine in *.
  destruct Hwf as [Hwf [Hid Hacc]].
  unfold PolyLang.wf_pinstr in *.
  destruct Hwf as
    (Hcur & Hcols_le & Hpoly_nrl & Hsched_nrl &
     Hpoly & Htf & Hacc_tf & Hsched & Hw & Hr).
  subst env_dim.
  split.
  - unfold parallel_old_pi.
    simpl.
    repeat split.
    + exact Hcur.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + exact Hpoly.
    + exact Htf.
    + exact Hacc_tf.
    + eapply exact_listzzs_cols_schedule_coord_old_schedule; eauto.
    + exact Hw.
    + exact Hr.
  - split; [exact Hid | exact Hacc].
Qed.

Lemma wf_pinstr_affine_parallel_new_pi :
  forall env vars env_dim width d pi,
    PolyLang.wf_pinstr_affine env vars pi ->
    env_dim = Datatypes.length env ->
    PolyLang.wf_pinstr_affine env vars (parallel_new_pi env_dim width d pi).
Proof.
  intros env vars env_dim width d pi Hwf Henvdim.
  unfold PolyLang.wf_pinstr_affine in *.
  destruct Hwf as [Hwf [Hid Hacc]].
  unfold PolyLang.wf_pinstr in *.
  destruct Hwf as
    (Hcur & Hcols_le & Hpoly_nrl & Hsched_nrl &
     Hpoly & Htf & Hacc_tf & Hsched & Hw & Hr).
  subst env_dim.
  split.
  - unfold parallel_new_pi.
    simpl.
    repeat split.
    + exact Hcur.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + exact Hpoly.
    + exact Htf.
    + exact Hacc_tf.
    + eapply exact_listzzs_cols_schedule_coord_prefix_schedule; eauto.
    + exact Hw.
    + exact Hr.
  - split; [exact Hid | exact Hacc].
Qed.

Lemma nth_error_map_inv :
  forall A B (f : A -> B) l n y,
    nth_error (List.map f l) n = Some y ->
    exists x,
      nth_error l n = Some x /\
      f x = y.
Proof.
  intros A B f l.
  induction l as [|x l IH]; intros n y Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n as [|n']; simpl in Hnth.
    + inversion Hnth; subst. exists x. split; reflexivity.
    + eapply IH in Hnth.
      destruct Hnth as [x' [Hnth Heq]].
      exists x'. split; simpl; eauto.
Qed.

Lemma nth_error_map_fwd :
  forall A B (f : A -> B) l n x,
    nth_error l n = Some x ->
    nth_error (List.map f l) n = Some (f x).
Proof.
  intros A B f l.
  induction l as [|y l IH]; intros n x Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n as [|n']; simpl in *.
    + inversion Hnth; subst. reflexivity.
    + eapply IH. exact Hnth.
Qed.

Lemma flatten_instrs_member_inv :
  forall envv pis ipl ip,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip pi /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros envv pis ipl ip Hflat Hin.
  destruct Hflat as [_ [Hmem _]].
  specialize (Hmem ip).
  destruct ((proj1 Hmem) Hin) as [pi [Hnth [_ [Hbel Hlen]]]].
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.

Lemma dot_product_v0_app_1_nth :
  forall n xs,
    dot_product (V0 n ++ [1%Z]) xs = nth n xs 0%Z.
Proof.
  induction n as [|n IH]; intros xs.
  - destruct xs as [|x xs]; simpl; [reflexivity|].
    destruct xs; simpl; lia.
  - destruct xs as [|x xs]; simpl.
    + reflexivity.
    + apply IH.
Qed.

Lemma dot_product_select_coord :
  forall cols n xs,
    (S n <= cols)%nat ->
    dot_product (resize cols (V0 n ++ [1%Z])) xs = nth n xs 0%Z.
Proof.
  intros cols n xs Hle.
  assert (Hresize :
    resize cols (V0 n ++ [1%Z]) =
    (V0 n ++ [1%Z]) ++ repeat 0%Z (cols - S n)).
  {
    rewrite resize_app_le.
    2: {
      unfold V0.
      rewrite repeat_length.
      lia.
    }
    replace (Datatypes.length (V0 n)) with n.
    2: {
      unfold V0.
      rewrite repeat_length.
      reflexivity.
    }
    replace (cols - n)%nat with (S (cols - S n)) by lia.
    simpl.
    rewrite resize_null_repeat by reflexivity.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hresize.
  rewrite dot_product_app_left.
  rewrite dot_product_repeat_zero_left.
  replace (Datatypes.length (V0 n ++ [1%Z])) with (S n).
  2: {
    replace (Datatypes.length (V0 n ++ [1%Z]))
      with (Datatypes.length (V0 n) + Datatypes.length [1%Z])%nat.
    2: {
      rewrite app_length.
      reflexivity.
    }
    unfold V0.
    rewrite repeat_length.
    simpl.
    lia.
  }
  rewrite dot_product_v0_app_1_nth.
  rewrite nth_resize.
  assert ((n <? S n)%nat = true) as Hlt.
  { apply Nat.ltb_lt. lia. }
  rewrite Hlt.
  lia.
Qed.

Lemma affine_product_current_coord_old_schedule :
  forall env_dim depth d idx,
    (d < depth)%nat ->
    affine_product (current_coord_old_schedule env_dim depth d) idx =
    [nth (env_dim + d)%nat idx 0%Z].
Proof.
  intros env_dim depth d idx Hd.
  unfold current_coord_old_schedule, affine_product.
  simpl.
  unfold current_coord_schedule_row.
  simpl.
  rewrite Z.add_0_r.
  f_equal.
  eapply dot_product_select_coord.
  lia.
Qed.

Lemma seq_shift_succ :
  forall start len,
    seq (S start) len = List.map S (seq start len).
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma map_nth_seq_firstn :
  forall d l,
    (d <= Datatypes.length l)%nat ->
    List.map (fun i => nth i l 0%Z) (seq 0 d) = firstn d l.
Proof.
  induction d as [|d IH]; intros l Hlen.
  - reflexivity.
  - destruct l as [|x l]; [inversion Hlen|].
    simpl.
    rewrite seq_shift_succ.
    simpl.
    f_equal.
    rewrite List.map_map.
    change
      (List.map (fun i : nat => nth i l 0%Z) (seq 0 d) = firstn d l).
    apply IH.
    simpl in Hlen.
    lia.
Qed.

Lemma affine_product_current_coord_prefix_schedule :
  forall env_dim depth d idx,
    (d <= depth)%nat ->
    Datatypes.length idx = (env_dim + depth)%nat ->
    affine_product (current_coord_prefix_schedule env_dim depth d) idx =
    firstn d (skipn env_dim idx).
Proof.
  intros env_dim depth d idx Hd Hlen.
  unfold current_coord_prefix_schedule, affine_product.
  rewrite List.map_map.
  transitivity (List.map (fun i => nth (env_dim + i)%nat idx 0%Z) (seq 0 d)).
  - apply List.map_ext_in.
    intros i Hin.
    apply in_seq in Hin.
    destruct Hin as [_ Hub].
    unfold current_coord_schedule_row.
    simpl.
    rewrite Z.add_0_r.
    rewrite dot_product_select_coord by lia.
    reflexivity.
  - transitivity (List.map (fun i => nth i (skipn env_dim idx) 0%Z) (seq 0 d)).
    + apply List.map_ext_in.
      intros i Hin.
      rewrite nth_skipn.
      reflexivity.
    + apply map_nth_seq_firstn.
      rewrite skipn_length.
      lia.
Qed.

Lemma affine_product_repeat_zero_affine_function :
  forall cols n idx,
    affine_product (repeat (PolyLang.zero_affine_function cols) n) idx =
    repeat 0%Z n.
Proof.
  intros cols n idx.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - unfold PolyLang.zero_affine_function.
    simpl.
    rewrite dot_product_repeat_zero_left.
    f_equal.
    exact IH.
Qed.

Lemma affine_product_app :
  forall rows1 rows2 idx,
    affine_product (rows1 ++ rows2) idx =
    affine_product rows1 idx ++ affine_product rows2 idx.
Proof.
  intros rows1 rows2 idx.
  unfold affine_product.
  rewrite map_app.
  reflexivity.
Qed.

Lemma affine_product_padded_pi_schedule :
  forall env_dim width pi idx,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    affine_product (padded_pi_schedule env_dim width pi) idx =
    resize width (affine_product pi.(PolyLang.pi_schedule) idx).
Proof.
  intros env_dim width pi idx Hlen.
  unfold padded_pi_schedule, PolyLang.pad_schedule_to_len.
  rewrite affine_product_app.
  rewrite affine_product_repeat_zero_affine_function.
  rewrite <- (app_nil_r (affine_product pi.(PolyLang.pi_schedule) idx)) at 2.
  rewrite resize_app_le.
  - rewrite resize_null_repeat by reflexivity.
    unfold affine_product.
    rewrite map_length.
    reflexivity.
  - unfold affine_product.
    rewrite map_length.
    exact Hlen.
Qed.

Lemma affine_product_firstn :
  forall d rows idx,
    affine_product (firstn d rows) idx =
    firstn d (affine_product rows idx).
Proof.
  induction d as [|d IH]; intros rows idx; destruct rows; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma affine_product_schedule_coord_old_schedule :
  forall env_dim width d pi idx,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    (d < width)%nat ->
    affine_product (schedule_coord_old_schedule env_dim width d pi) idx =
    [nth d (resize width (affine_product pi.(PolyLang.pi_schedule) idx)) 0%Z].
Proof.
  intros env_dim width d pi idx Hlen Hd.
  unfold schedule_coord_old_schedule.
  simpl.
  rewrite <- (affine_product_padded_pi_schedule env_dim) by exact Hlen.
  unfold affine_product.
  assert
    (Hrow :
       nth_error (padded_pi_schedule env_dim width pi) d =
       Some
         (nth d (padded_pi_schedule env_dim width pi)
            (PolyLang.zero_affine_function
               (env_dim + pi.(PolyLang.pi_depth))))).
  {
    apply nth_error_nth'.
    rewrite padded_pi_schedule_length by exact Hlen.
    exact Hd.
  }
  pose proof
    (map_nth_error
       (fun t => dot_product (fst t) idx + snd t)
       d (padded_pi_schedule env_dim width pi)
       Hrow) as Hmap.
  apply nth_error_nth with (d := 0%Z) in Hmap.
  now rewrite Hmap.
Qed.

Lemma affine_product_schedule_coord_prefix_schedule :
  forall env_dim width d pi idx,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    affine_product (schedule_coord_prefix_schedule env_dim width d pi) idx =
    firstn d (resize width (affine_product pi.(PolyLang.pi_schedule) idx)).
Proof.
  intros env_dim width d pi idx Hlen.
  unfold schedule_coord_prefix_schedule.
  rewrite affine_product_firstn.
  rewrite affine_product_padded_pi_schedule by exact Hlen.
  reflexivity.
Qed.

Local Lemma parallel_point_ext_eq_except_sched :
  forall pp d pi tau,
    PolyLang.eq_except_sched
      (PolyLang.old_of_ext (parallel_point_ext pp d pi tau)) tau.
Proof.
  intros pp d pi tau.
  unfold PolyLang.eq_except_sched, PolyLang.old_of_ext, parallel_point_ext.
  simpl. repeat split; reflexivity.
Qed.

Local Lemma parallel_ext_pi_in :
  forall pis env_dim width d n pi,
    nth_error pis n = Some pi ->
    In
      (AffineCore.compose_pinstr_ext_at env_dim
        (parallel_old_pi env_dim width d pi)
        (parallel_new_pi env_dim width d pi))
      (AffineCore.compose_pinstrs_ext_at env_dim
        (List.map (parallel_old_pi env_dim width d) pis)
        (List.map (parallel_new_pi env_dim width d) pis)).
Proof.
  induction pis as [|head tail IH]; intros env_dim width d [|n] pi Hnth;
    simpl in *; try discriminate.
  - inversion Hnth; subst. left. reflexivity.
  - right. eapply IH. exact Hnth.
Qed.

Local Lemma parallel_point_ext_belongs :
  forall pis varctxt vars d tau pi,
    nth_error pis tau.(PolyLang.ip_nth) = Some pi ->
    PolyLang.belongs_to tau pi ->
    check_current_view_pinstrb pi = true ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <= schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    PolyLang.belongs_to_ext
      (parallel_point_ext ((pis, varctxt), vars) d pi tau)
      (AffineCore.compose_pinstr_ext_at (Datatypes.length varctxt)
        (parallel_old_pi
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)
        (parallel_new_pi
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)).
Proof.
  intros pis varctxt vars d tau pi Hnth Hbel Hcurrent Hwidth Hd.
  pose proof (check_current_view_pinstrb_sound pi Hcurrent) as Hwitness.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as (Hdom & Htf & Hts & Hinstr & Hdepth).
  unfold PolyLang.belongs_to_ext, parallel_point_ext,
    AffineCore.compose_pinstr_ext_at.
  simpl.
  repeat split.
  - exact Hdom.
  - rewrite Htf.
    unfold PolyLang.current_transformation_of,
      PolyLang.current_transformation_at, parallel_old_pi.
    simpl. rewrite Hwitness. reflexivity.
  - change (
      [nth d (resize (schedule_width_of_pis pis)
        tau.(PolyLang.ip_time_stamp)) 0%Z] =
      affine_product
        (schedule_coord_old_schedule
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)
        tau.(PolyLang.ip_index)).
    rewrite affine_product_schedule_coord_old_schedule by assumption.
    now rewrite Hts.
  - change (
      firstn d (resize (schedule_width_of_pis pis)
        tau.(PolyLang.ip_time_stamp)) =
      affine_product
        (schedule_coord_prefix_schedule
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)
        tau.(PolyLang.ip_index)).
    rewrite affine_product_schedule_coord_prefix_schedule by assumption.
    now rewrite Hts.
  - exact Hinstr.
  - exact Hdepth.
Qed.

Lemma flatten_parallel_old_member_inv :
  forall pis varctxt vars d envv ipl ip,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_old_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip
        (parallel_old_pi
           (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi) /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros pis varctxt vars d envv ipl ip Hflat Hin.
  unfold parallel_old_pprog, pprog_pis in Hflat.
  simpl in Hflat.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin)
    as [pi_old [Hnth_old [Hbel Hlen]]].
  eapply nth_error_map_inv in Hnth_old.
  destruct Hnth_old as [pi [Hnth Heq]].
  subst pi_old.
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.

Lemma flatten_parallel_new_member_inv :
  forall pis varctxt vars d envv ipl ip,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_new_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip
        (parallel_new_pi
           (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi) /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros pis varctxt vars d envv ipl ip Hflat Hin.
  unfold parallel_new_pprog, pprog_pis in Hflat.
  simpl in Hflat.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin)
    as [pi_new [Hnth_new [Hbel Hlen]]].
  eapply nth_error_map_inv in Hnth_new.
  destruct Hnth_new as [pi [Hnth Heq]].
  subst pi_new.
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.

Lemma member_parallel_old_timestamp :
  forall pis varctxt vars d envv ipl ip pi,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_old_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <=
     schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    ip.(PolyLang.ip_time_stamp) =
    [nth d
       (resize (schedule_width_of_pis pis)
          (affine_product pi.(PolyLang.pi_schedule) ip.(PolyLang.ip_index)))
       0%Z].
Proof.
  intros pis varctxt vars d envv ipl ip pi Hflat Hin Hnth Hlen Hd.
  destruct (flatten_parallel_old_member_inv _ _ _ _ _ _ _ Hflat Hin)
    as [pi' [Hnth' [Hbel _]]].
  rewrite Hnth in Hnth'. inversion Hnth'. subst pi'.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as [_ [_ [Hts _]]].
  rewrite Hts.
  eapply affine_product_schedule_coord_old_schedule; eauto.
Qed.

Lemma member_parallel_new_timestamp :
  forall pis varctxt vars d envv ipl ip pi,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_new_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <=
     schedule_width_of_pis pis)%nat ->
    ip.(PolyLang.ip_time_stamp) =
    firstn d
      (resize (schedule_width_of_pis pis)
         (affine_product pi.(PolyLang.pi_schedule) ip.(PolyLang.ip_index))).
Proof.
  intros pis varctxt vars d envv ipl ip pi Hflat Hin Hnth Hlen.
  destruct (flatten_parallel_new_member_inv _ _ _ _ _ _ _ Hflat Hin)
    as [pi' [Hnth' [Hbel _]]].
  rewrite Hnth in Hnth'. inversion Hnth'. subst pi'.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as [_ [_ [Hts _]]].
  rewrite Hts.
  eapply affine_product_schedule_coord_prefix_schedule; eauto.
Qed.

Lemma old_new_of_ext_eq_except_sched :
  forall ip_ext,
    PolyLang.eq_except_sched (PolyLang.old_of_ext ip_ext) (PolyLang.new_of_ext ip_ext).
Proof.
  intros ip_ext.
  unfold PolyLang.eq_except_sched, PolyLang.old_of_ext, PolyLang.new_of_ext.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma rel_list_eq_except_sched_member :
  forall ipl ipl' tau,
    rel_list PolyLang.eq_except_sched ipl ipl' ->
    In tau ipl ->
    exists tau',
      In tau' ipl' /\
      PolyLang.eq_except_sched tau tau'.
Proof.
  intros ipl ipl' tau Hrel Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hnth].
  pose proof
    (proj1 (rel_list_nth _ _ _ n ipl ipl' Hrel) (ex_intro _ tau Hnth))
    as [tau' Hnth'].
  exists tau'. split.
  - eapply nth_error_In. exact Hnth'.
  - eapply rel_list_implies_rel_nth; eauto.
Qed.

Lemma in_old_of_ext_list_inv :
  forall ipl_ext tau,
    In tau (PolyLang.old_of_ext_list ipl_ext) ->
    exists ip_ext,
      In ip_ext ipl_ext /\
      PolyLang.old_of_ext ip_ext = tau.
Proof.
  intros ipl_ext tau Hin.
  unfold PolyLang.old_of_ext_list in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [ip_ext [Heq Hin_ext]].
  exists ip_ext. split; auto.
Qed.

Lemma in_new_of_ext_list_inv :
  forall ipl_ext tau,
    In tau (PolyLang.new_of_ext_list ipl_ext) ->
    exists ip_ext,
      In ip_ext ipl_ext /\
      PolyLang.new_of_ext ip_ext = tau.
Proof.
  intros ipl_ext tau Hin.
  unfold PolyLang.new_of_ext_list in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [ip_ext [Heq Hin_ext]].
  exists ip_ext. split; auto.
Qed.

Lemma env_dim_of_flat_member :
  forall envv pis ipl ip pi,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    env_dim_of ip = Datatypes.length envv.
Proof.
  intros envv pis ipl ip pi Hflat Hin Hnth.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin)
    as [pi' [Hnth' [Hbel Hlen]]].
  rewrite Hnth in Hnth'. inversion Hnth'. subst pi'.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as [_ [_ [_ [_ Hdepth]]]].
  unfold env_dim_of.
  rewrite Hlen, Hdepth.
  lia.
Qed.

Lemma current_coords_of_flat_member :
  forall envv pis ipl ip pi,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    current_coords_of ip = skipn (Datatypes.length envv) ip.(PolyLang.ip_index).
Proof.
  intros envv pis ipl ip pi Hflat Hin Hnth.
  unfold current_coords_of.
  rewrite (env_dim_of_flat_member _ _ _ _ _ Hflat Hin Hnth).
  reflexivity.
Qed.

Lemma lex_compare_singleton_lt :
  forall z1 z2,
    (z1 < z2)%Z ->
    lex_compare [z1] [z2] = Lt.
Proof.
  intros z1 z2 Hlt.
  simpl.
  destruct (z1 ?= z2) eqn:Hcmp; simpl.
  - apply Z.compare_eq_iff in Hcmp. lia.
  - reflexivity.
  - apply Z.compare_gt_iff in Hcmp. lia.
Qed.

(** * Executable certificate and soundness *)

(** The public [*_current*] names below are retained for compatibility.
    Their dimensions now denote canonical schedule coordinates, rather than
    coordinates in the current iteration point. *)

Definition check_pprog_parallel_currentb
  (pp : PolyLang.t) (plan : parallel_plan) : imp bool :=
  let d := plan.(target_dim) in
  if Nat.ltb d (schedule_width pp)
     && check_current_view_pprogb pp
  then AffineCore.validate (parallel_old_pprog pp d) (parallel_new_pprog pp d)
  else pure false.

Definition checked_parallelize_current
  (pp : PolyLang.t) (plan : parallel_plan) : imp (result parallel_cert) :=
  BIND ok <- check_pprog_parallel_currentb pp plan -;
  if ok
  then pure (Okk {| certified_dim := plan.(target_dim) |})
  else pure (Err "Parallel validation failed").

Lemma check_pprog_parallel_currentb_true_inv :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    (target_dim plan < schedule_width pp)%nat /\
    check_current_view_pprogb pp = true /\
    mayReturn
      (AffineCore.validate
         (parallel_old_pprog pp plan.(target_dim))
         (parallel_new_pprog pp plan.(target_dim)))
      true.
Proof.
  intros pp plan Hret.
  unfold check_pprog_parallel_currentb in Hret.
  destruct
    ((Nat.ltb (target_dim plan) (schedule_width pp)
        && check_current_view_pprogb pp)%bool) eqn:Hguard.
  - apply andb_true_iff in Hguard.
    destruct Hguard as [Hlt Hcur].
    split.
    + apply Nat.ltb_lt. exact Hlt.
    + split; [exact Hcur | exact Hret].
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

Local Lemma env_dim_of_pointwise :
  forall (varctxt : list Instr.ident)
         (tau : PolyLang.InstrPoint) (pi : PolyLang.PolyInstr),
    PolyLang.belongs_to tau pi ->
    Datatypes.length tau.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth))%nat ->
    env_dim_of tau = Datatypes.length varctxt.
Proof.
  intros varctxt tau pi Hbel Hlen.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as (_ & _ & _ & _ & Hdepth).
  unfold env_dim_of. rewrite Hlen, Hdepth. lia.
Qed.

Local Lemma parallel_single_point_view :
  forall pis varctxt vars d tau pi,
    nth_error pis tau.(PolyLang.ip_nth) = Some pi ->
    PolyLang.belongs_to tau pi ->
    Datatypes.length tau.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth))%nat ->
    check_current_view_pinstrb pi = true ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <=
      schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    In
      (parallel_pinstr_ext ((pis, varctxt), vars) d pi)
      (parallel_pinstrs_ext ((pis, varctxt), vars) d) /\
    PolyLang.belongs_to_ext
      (parallel_point_ext ((pis, varctxt), vars) d pi tau)
      (parallel_pinstr_ext ((pis, varctxt), vars) d pi) /\
    Datatypes.length
      (parallel_point_ext ((pis, varctxt), vars) d pi tau).(PolyLang.ip_index_ext) =
      (Datatypes.length varctxt +
       (parallel_pinstr_ext
          ((pis, varctxt), vars) d pi).(PolyLang.pi_depth_ext))%nat /\
    PolyLang.eq_except_sched
      (PolyLang.old_of_ext
        (parallel_point_ext ((pis, varctxt), vars) d pi tau))
      tau.
Proof.
  intros pis varctxt vars d tau pi Hnth Hbel Hlen Hcurrent Hwidth Hd.
  split.
  - unfold parallel_pinstr_ext, parallel_pinstrs_ext.
    simpl. eapply parallel_ext_pi_in. exact Hnth.
  - split.
    + unfold parallel_pinstr_ext. simpl.
      eapply parallel_point_ext_belongs; eauto.
    + split.
      * unfold parallel_point_ext, parallel_pinstr_ext. simpl.
        exact Hlen.
      * eapply parallel_point_ext_eq_except_sched.
Qed.

Local Lemma parallel_direction_pointwise_permutable :
  forall pis varctxt vars d tau1 tau2 pi1 pi2,
    mayReturn
      (AffineCore.validate
        (parallel_old_pprog ((pis, varctxt), vars) d)
        (parallel_new_pprog ((pis, varctxt), vars) d))
      true ->
    nth_error pis tau1.(PolyLang.ip_nth) = Some pi1 ->
    nth_error pis tau2.(PolyLang.ip_nth) = Some pi2 ->
    PolyLang.belongs_to tau1 pi1 ->
    PolyLang.belongs_to tau2 pi2 ->
    Datatypes.length tau1.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi1.(PolyLang.pi_depth))%nat ->
    Datatypes.length tau2.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi2.(PolyLang.pi_depth))%nat ->
    check_current_view_pinstrb pi1 = true ->
    check_current_view_pinstrb pi2 = true ->
    (Datatypes.length pi1.(PolyLang.pi_schedule) <=
      schedule_width_of_pis pis)%nat ->
    (Datatypes.length pi2.(PolyLang.pi_schedule) <=
      schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    same_env_of tau1 tau2 ->
    same_prefix_before ((pis, varctxt), vars) d tau1 tau2 ->
    (nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z <
     nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z)%Z ->
    ILSema.Permutable tau1 tau2.
Proof.
  intros pis varctxt vars d tau1 tau2 pi1 pi2 Hval Hnth1 Hnth2
    Hbel1 Hbel2 Hlen1 Hlen2 Hcurrent1 Hcurrent2 Hwidth1 Hwidth2 Hd
    Hsame_env Hprefix Hlt.
  destruct
    (parallel_single_point_view
      pis varctxt vars d tau1 pi1
      Hnth1 Hbel1 Hlen1 Hcurrent1 Hwidth1 Hd)
    as (Hinext1 & Hbelext1 & Hidxext1 & Heq1).
  destruct
    (parallel_single_point_view
      pis varctxt vars d tau2 pi2
      Hnth2 Hbel2 Hlen2 Hcurrent2 Hwidth2 Hd)
    as (Hinext2 & Hbelext2 & Hidxext2 & Heq2).
  set (pi1_ext := parallel_pinstr_ext ((pis, varctxt), vars) d pi1) in *.
  set (pi2_ext := parallel_pinstr_ext ((pis, varctxt), vars) d pi2) in *.
  set (tau1_ext := parallel_point_ext ((pis, varctxt), vars) d pi1 tau1) in *.
  set (tau2_ext := parallel_point_ext ((pis, varctxt), vars) d pi2 tau2) in *.
  assert (Hsameidx :
    firstn (Datatypes.length varctxt) tau1_ext.(PolyLang.ip_index_ext) =
    firstn (Datatypes.length varctxt) tau2_ext.(PolyLang.ip_index_ext)).
  {
    subst tau1_ext tau2_ext. simpl.
    unfold same_env_of, env_prefix_of in Hsame_env.
    rewrite
      (env_dim_of_pointwise varctxt tau1 pi1 Hbel1 Hlen1),
      (env_dim_of_pointwise varctxt tau2 pi2 Hbel2 Hlen2)
      in Hsame_env.
    exact Hsame_env.
  }
  assert (Hnew_eq :
    PolyLang.ip_time_stamp2_ext tau1_ext =
    PolyLang.ip_time_stamp2_ext tau2_ext).
  {
    subst tau1_ext tau2_ext. simpl. exact Hprefix.
  }
  assert (Hold : PolyLang.instr_point_ext_old_sched_lt tau1_ext tau2_ext).
  {
    unfold PolyLang.instr_point_ext_old_sched_lt.
    subst tau1_ext tau2_ext. simpl.
    apply lex_compare_singleton_lt. exact Hlt.
  }
  assert (Hnew : PolyLang.instr_point_ext_new_sched_ge tau1_ext tau2_ext).
  {
    unfold PolyLang.instr_point_ext_new_sched_ge. left.
    rewrite Hnew_eq. apply lex_compare_reflexive.
  }
  assert (Hperm : PolyLang.Permutable_ext tau1_ext tau2_ext).
  {
    eapply AffineCore.validate_pointwise_implies_permutability
      with
        (pp1 := parallel_old_pprog ((pis, varctxt), vars) d)
        (pp2 := parallel_new_pprog ((pis, varctxt), vars) d)
        (env1 := varctxt) (env2 := varctxt)
        (vars1 := vars) (vars2 := vars)
        (pil1 := List.map
          (parallel_old_pi
            (Datatypes.length varctxt) (schedule_width_of_pis pis) d) pis)
        (pil2 := List.map
          (parallel_new_pi
            (Datatypes.length varctxt) (schedule_width_of_pis pis) d) pis)
        (pi1_ext := pi1_ext) (pi2_ext := pi2_ext); eauto.
  }
  eapply (permutable_eq_except_sched
    (PolyLang.old_of_ext tau1_ext) tau1
    (PolyLang.old_of_ext tau2_ext) tau2); eauto.
Qed.

Lemma check_pprog_parallel_currentb_pointwise_sound :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    parallel_safe_dim_pointwise pp plan.(target_dim).
Proof.
  intros [[pis varctxt] vars] [d] Hcheck.
  simpl in *.
  pose proof
    (check_pprog_parallel_currentb_true_inv
       ((pis, varctxt), vars) {| target_dim := d |} Hcheck)
    as (Hd & Hcurrent & Hval).
  unfold parallel_safe_dim_pointwise.
  intros tau1 tau2 pi1 pi2 Hnth1 Hnth2 Hbel1 Hbel2 Hlen1 Hlen2 Hslice.
  simpl in *.
  set (width := schedule_width_of_pis pis) in *.
  assert (Hinpi1 : In pi1 pis) by (eapply nth_error_In; eauto).
  assert (Hinpi2 : In pi2 pis) by (eapply nth_error_In; eauto).
  assert (Hwidth1 : (Datatypes.length pi1.(PolyLang.pi_schedule) <= width)%nat).
  { subst width. exact (schedule_width_ge_pinstr pis varctxt vars pi1 Hinpi1). }
  assert (Hwidth2 : (Datatypes.length pi2.(PolyLang.pi_schedule) <= width)%nat).
  { subst width. exact (schedule_width_ge_pinstr pis varctxt vars pi2 Hinpi2). }
  assert (Hcurrent1 : check_current_view_pinstrb pi1 = true).
  {
    unfold check_current_view_pprogb in Hcurrent.
    eapply forallb_forall in Hcurrent; eauto.
  }
  assert (Hcurrent2 : check_current_view_pinstrb pi2 = true).
  {
    unfold check_current_view_pprogb in Hcurrent.
    eapply forallb_forall in Hcurrent; eauto.
  }
  destruct Hslice as (Hsame_env & Hprefix & Hdiff).
  assert (Hneq_coord :
    nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z <>
    nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z).
  {
    intro Heq. apply Hdiff.
    rewrite nth_error_nth' with
      (d := 0%Z) (n := d)
      (l := padded_timestamp ((pis, varctxt), vars) tau1).
    2: { unfold padded_timestamp. rewrite resize_length. exact Hd. }
    rewrite nth_error_nth' with
      (d := 0%Z) (n := d)
      (l := padded_timestamp ((pis, varctxt), vars) tau2).
    2: { unfold padded_timestamp. rewrite resize_length. exact Hd. }
    now rewrite Heq.
  }
  destruct
    (Z_lt_ge_dec
      (nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z)
      (nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z))
    as [Hlt12 | Hge12].
  - subst width.
    eapply
      (parallel_direction_pointwise_permutable
        pis varctxt vars d tau1 tau2 pi1 pi2); eassumption.
  - assert (Hlt21 :
      (nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z <
       nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z)%Z) by lia.
    assert (Hsame_env_rev : same_env_of tau2 tau1).
    { unfold same_env_of in *. symmetry. exact Hsame_env. }
    assert (Hprefix_rev :
      same_prefix_before ((pis, varctxt), vars) d tau2 tau1).
    { unfold same_prefix_before in *. symmetry. exact Hprefix. }
    apply ILSema.Permutable_symm.
    subst width.
    eapply
      (parallel_direction_pointwise_permutable
        pis varctxt vars d tau2 tau1 pi2 pi1); eassumption.
Qed.

Lemma parallel_safe_dim_pointwise_implies_safe_dim :
  forall pp d,
    parallel_safe_dim_pointwise pp d ->
    parallel_safe_dim pp d.
Proof.
  intros pp d Hpointwise envv ipl tau1 tau2 Henvlen Hflat Hin1 Hin2 Hslice.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin1)
    as [pi1 [Hnth1 [Hbel1 Hlen1]]].
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin2)
    as [pi2 [Hnth2 [Hbel2 Hlen2]]].
  eapply Hpointwise with (pi1 := pi1) (pi2 := pi2); eauto.
  - now rewrite <- Henvlen.
  - now rewrite <- Henvlen.
Qed.

Lemma parallel_cert_pointwise_sound_implies_sound :
  forall pp cert,
    parallel_cert_pointwise_sound pp cert ->
    parallel_cert_sound pp cert.
Proof.
  intros pp cert Hpointwise.
  eapply parallel_safe_dim_pointwise_implies_safe_dim.
  exact Hpointwise.
Qed.

Lemma check_pprog_parallel_currentb_sound :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    parallel_safe_dim pp plan.(target_dim).
Proof.
  intros pp plan Hcheck.
  eapply parallel_safe_dim_pointwise_implies_safe_dim.
  eapply check_pprog_parallel_currentb_pointwise_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_sound :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    parallel_cert_sound pp cert.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  unfold parallel_cert_sound.
  simpl.
  eapply check_pprog_parallel_currentb_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_pointwise_sound :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    parallel_cert_pointwise_sound pp cert.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  unfold parallel_cert_pointwise_sound.
  simpl.
  eapply check_pprog_parallel_currentb_pointwise_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_implies_dim_in_range :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    (certified_dim cert < schedule_width pp)%nat.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  simpl.
  destruct (check_pprog_parallel_currentb_true_inv pp plan Hcheck)
    as (Hlt & _).
  exact Hlt.
Qed.

End ParallelValidator.
