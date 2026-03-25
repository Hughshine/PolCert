Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Sorting.Sorted.
Import ListNotations.

Require Import Linalg.
Require Import Misc.
Require Import PolyBase.
Require Import PolyLang.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import TilingWitness.
Require Import PointWitness.
Require Import ParallelValidator.
Require Import TilingValidator.
Require Import PolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingBandScheduleValidator (PolIRs: POLIRS).

Module Base := TilingValidator PolIRs.
Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module TilingCheck := Base.TilingCheck.
Module Tiling := Base.Tiling.
Module TilingPolIRs := Base.TilingPolIRs.
Module ParallelCore := ParallelValidator PolIRs.
Module BandAffine := Base.TilingVal.

Definition tiling_to_band_pinstr
    (pi: Tiling.PL.PolyInstr) : BandAffine.PolyLang.PolyInstr := pi.

Definition tiling_to_band_var
    (v: Tiling.PL.ident * Tiling.PL.Ty.t)
    : BandAffine.PolyLang.ident * BandAffine.PolyLang.Ty.t :=
  (fst v, BandAffine.Ty.dummy).

Definition tiling_to_band_pprog
    (pp: Tiling.PL.t) : BandAffine.PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  (pis, varctxt, List.map tiling_to_band_var vars).

Record pinstr_tiling_band := {
  ptb_start : nat;
  ptb_len : nat;
}.

Definition pinstr_tiling_band_eqb
    (b1 b2: pinstr_tiling_band) : bool :=
  Nat.eqb (ptb_start b1) (ptb_start b2) &&
  Nat.eqb (ptb_len b1) (ptb_len b2).

Lemma pinstr_tiling_band_eqb_eq :
  forall b1 b2,
    pinstr_tiling_band_eqb b1 b2 = true ->
    b1 = b2.
Proof.
  intros [s1 l1] [s2 l2] Heq.
  unfold pinstr_tiling_band_eqb in Heq.
  apply andb_true_iff in Heq.
  destruct Heq as [Hs Hl].
  apply Nat.eqb_eq in Hs.
  apply Nat.eqb_eq in Hl.
  simpl in *.
  subst s2 l2.
  reflexivity.
Qed.

Definition common_tiling_band
    (bands: list pinstr_tiling_band)
    (band: pinstr_tiling_band) : Prop :=
  Forall (fun b => b = band) bands.

Definition infer_common_tiling_band
    (bands: list pinstr_tiling_band) : option pinstr_tiling_band :=
  match bands with
  | [] => None
  | band :: bands' =>
      if forallb (pinstr_tiling_band_eqb band) bands'
      then Some band
      else None
  end.

Lemma infer_common_tiling_band_sound :
  forall bands band,
    infer_common_tiling_band bands = Some band ->
    common_tiling_band bands band.
Proof.
  intros bands band Hinfer.
  unfold infer_common_tiling_band in Hinfer.
  destruct bands as [|band0 bands']; try discriminate.
  destruct (forallb (pinstr_tiling_band_eqb band0) bands') eqn:Hforall;
    inversion Hinfer; subst; clear Hinfer.
  constructor; [reflexivity|].
  eapply Forall_forall.
  intros b Hb.
  eapply forallb_forall with (x := b) in Hforall; eauto.
  symmetry.
  eapply pinstr_tiling_band_eqb_eq; exact Hforall.
Qed.

Lemma common_tiling_band_nth_error :
  forall bands band n b,
    common_tiling_band bands band ->
    nth_error bands n = Some b ->
    b = band.
Proof.
  intros bands band n.
  revert bands band.
  induction n as [|n IH]; intros bands band b Hcommon Hnth.
  - destruct bands as [|b0 bands']; simpl in Hnth; try discriminate.
    inversion Hcommon; subst.
    inversion Hnth; subst.
    reflexivity.
  - destruct bands as [|b0 bands']; simpl in Hnth; try discriminate.
    inversion Hcommon; subst.
    eapply IH; eauto.
Qed.

Fixpoint listz_strict_eqb (xs ys: list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Z.eqb x y && listz_strict_eqb xs' ys'
  | _, _ => false
  end.

Lemma listz_strict_eqb_eq :
  forall xs ys,
    listz_strict_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Heq.
  - destruct ys; simpl in Heq; try discriminate; reflexivity.
  - destruct ys as [|y ys]; simpl in Heq; try discriminate.
    apply andb_true_iff in Heq.
    destruct Heq as [Hxy Hrest].
    apply Z.eqb_eq in Hxy.
    f_equal.
    + exact Hxy.
    + eapply IH; eauto.
Qed.

Definition schedule_row_of_affine_expr
    (expr: affine_expr) : list Z * Z :=
  (ae_param_coeffs expr ++ ae_var_coeffs expr, ae_const expr).

Definition tile_link_has_zero_prefix
    (prefix_len: nat) (link: tile_link) : Prop :=
  firstn prefix_len (ae_var_coeffs (tl_expr link)) = repeat 0%Z prefix_len.

Definition schedule_row_of_tile_link_base
    (prefix_len: nat) (link: tile_link) : list Z * Z :=
  let expr := tl_expr link in
  (ae_param_coeffs expr ++ skipn prefix_len (ae_var_coeffs expr), ae_const expr).

Fixpoint schedule_rows_of_links_aux
    (prefix_len: nat)
    (links: list tile_link) : option Schedule :=
  match links with
  | [] => Some []
  | link :: links' =>
      if listz_strict_eqb
           (firstn prefix_len (ae_var_coeffs (tl_expr link)))
           (repeat 0%Z prefix_len)
      then
        match schedule_rows_of_links_aux (S prefix_len) links' with
        | Some rows =>
            Some (schedule_row_of_tile_link_base prefix_len link :: rows)
        | None => None
        end
      else None
  end.

Definition schedule_rows_of_links
    (w: statement_tiling_witness) : option Schedule :=
  schedule_rows_of_links_aux 0 (stw_links w).

Definition pinstr_tiling_band_matches
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  match schedule_rows_of_links w with
  | Some rows =>
      ptb_len band = List.length (stw_links w) /\
      firstn (ptb_len band)
        (skipn (ptb_start band) (Tiling.PL.pi_schedule before)) =
      rows
  | None => False
  end.

Definition stripmine_schedule_after_env
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  let added_dims := ptb_len band in
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let prefix := firstn (ptb_start band) lifted in
  let lifted_band := firstn added_dims (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + added_dims)%nat lifted in
  prefix ++
  Tiling.identity_affine_rows_from total_cols env_size added_dims ++
  lifted_band ++
  suffix.

Definition zero_schedule_row (cols: nat) : (list Z * Z) :=
  (repeat 0%Z cols, 0%Z).

Definition pad_schedule_with_zero_rows
    (sched: Schedule) (cols extra_rows: nat) : Schedule :=
  sched ++ repeat (zero_schedule_row cols) extra_rows.

Definition check_schedule_with_trailing_zero_paddingb
    (expected actual: Schedule) : bool :=
  if Nat.leb (List.length expected) (List.length actual) then
    let cols :=
      match actual with
      | [] => 0%nat
      | (coeffs, _) :: _ => List.length coeffs
      end in
    listzzs_strict_eqb
      actual
      (pad_schedule_with_zero_rows
         expected cols (List.length actual - List.length expected))
  else false.

Definition schedule_matches_with_trailing_zero_padding
    (expected actual: Schedule) : Prop :=
  exists cols extra_rows,
    actual = pad_schedule_with_zero_rows expected cols extra_rows.

Definition schedule_take_prefix_band
    (band: pinstr_tiling_band) (sched: Schedule) : Schedule :=
  firstn (ptb_start band + ptb_len band)%nat sched.

Definition schedule_take_prefix_only
    (band: pinstr_tiling_band) (sched: Schedule) : Schedule :=
  firstn (ptb_start band) sched.

Definition retiled_old_band_old_pi
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (band: pinstr_tiling_band) : Tiling.PL.PolyInstr :=
  let pi := Tiling.retiled_old_pinstr env_size before after w in
  {|
    Tiling.PL.pi_depth := Tiling.PL.pi_depth pi;
    Tiling.PL.pi_instr := Tiling.PL.pi_instr pi;
    Tiling.PL.pi_poly := Tiling.PL.pi_poly pi;
    Tiling.PL.pi_schedule := Tiling.PL.pi_schedule pi;
    Tiling.PL.pi_point_witness := Tiling.PL.pi_point_witness pi;
    Tiling.PL.pi_transformation := Tiling.PL.pi_transformation pi;
    Tiling.PL.pi_access_transformation :=
      Tiling.PL.pi_access_transformation pi;
    Tiling.PL.pi_waccess := Tiling.PL.pi_waccess pi;
    Tiling.PL.pi_raccess := Tiling.PL.pi_raccess pi;
  |}.

Definition retiled_old_band_new_pi
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (band: pinstr_tiling_band) : Tiling.PL.PolyInstr :=
  let pi := Tiling.retiled_old_pinstr env_size before after w in
  {|
    Tiling.PL.pi_depth := Tiling.PL.pi_depth pi;
    Tiling.PL.pi_instr := Tiling.PL.pi_instr pi;
    Tiling.PL.pi_poly := Tiling.PL.pi_poly pi;
    Tiling.PL.pi_schedule :=
      schedule_take_prefix_only band (Tiling.PL.pi_schedule pi);
    Tiling.PL.pi_point_witness := Tiling.PL.pi_point_witness pi;
    Tiling.PL.pi_transformation := Tiling.PL.pi_transformation pi;
    Tiling.PL.pi_access_transformation :=
      Tiling.PL.pi_access_transformation pi;
    Tiling.PL.pi_waccess := Tiling.PL.pi_waccess pi;
    Tiling.PL.pi_raccess := Tiling.PL.pi_raccess pi;
  |}.

Definition after_stripmined_band_new_pi
    (after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : Tiling.PL.PolyInstr :=
  {|
    Tiling.PL.pi_depth := Tiling.PL.pi_depth after;
    Tiling.PL.pi_instr := Tiling.PL.pi_instr after;
    Tiling.PL.pi_poly := Tiling.PL.pi_poly after;
    Tiling.PL.pi_schedule :=
      firstn (ptb_start band + (2 * ptb_len band))%nat
        (Tiling.PL.pi_schedule after);
    Tiling.PL.pi_point_witness := Tiling.PL.pi_point_witness after;
    Tiling.PL.pi_transformation := Tiling.PL.pi_transformation after;
    Tiling.PL.pi_access_transformation :=
      Tiling.PL.pi_access_transformation after;
    Tiling.PL.pi_waccess := Tiling.PL.pi_waccess after;
    Tiling.PL.pi_raccess := Tiling.PL.pi_raccess after;
  |}.

Fixpoint retiled_old_band_old_pinstrs
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : list Tiling.PL.PolyInstr :=
  match before_pis, after_pis, ws, bands with
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', band :: bands' =>
      retiled_old_band_old_pi env_size before_pi after_pi w band ::
      retiled_old_band_old_pinstrs env_size before_pis' after_pis' ws' bands'
  | _, _, _, _ => []
  end.

Fixpoint retiled_old_band_new_pinstrs
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : list Tiling.PL.PolyInstr :=
  match before_pis, after_pis, ws, bands with
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', band :: bands' =>
      retiled_old_band_new_pi env_size before_pi after_pi w band ::
      retiled_old_band_new_pinstrs env_size before_pis' after_pis' ws' bands'
  | _, _, _, _ => []
  end.

Fixpoint after_stripmined_band_new_pinstrs
    (after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : list Tiling.PL.PolyInstr :=
  match after_pis, bands with
  | after_pi :: after_pis', band :: bands' =>
      after_stripmined_band_new_pi after_pi band ::
      after_stripmined_band_new_pinstrs after_pis' bands'
  | _, _ => []
  end.

Definition retiled_old_band_old_pprog
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Tiling.PL.t :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, _, _) := after in
  (retiled_old_band_old_pinstrs
     (List.length before_ctxt) before_pis after_pis ws bands,
   before_ctxt,
   before_vars).

Definition retiled_old_band_new_pprog
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Tiling.PL.t :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, _, _) := after in
  (retiled_old_band_new_pinstrs
     (List.length before_ctxt) before_pis after_pis ws bands,
   before_ctxt,
   before_vars).

Definition after_stripmined_band_new_pprog
    (before after: Tiling.PL.t)
    (bands: list pinstr_tiling_band) : Tiling.PL.t :=
  let '(_, before_ctxt, before_vars) := before in
  let '(after_pis, _, _) := after in
  (after_stripmined_band_new_pinstrs after_pis bands,
   before_ctxt,
   before_vars).

Definition project_band_pi_ext
    (band: pinstr_tiling_band)
    (pi_ext: Tiling.PL.PolyInstr_ext) : Tiling.PL.PolyInstr_ext :=
  {|
    Tiling.PL.pi_depth_ext := Tiling.PL.pi_depth_ext pi_ext;
    Tiling.PL.pi_instr_ext := Tiling.PL.pi_instr_ext pi_ext;
    Tiling.PL.pi_poly_ext := Tiling.PL.pi_poly_ext pi_ext;
    Tiling.PL.pi_point_witness_ext := Tiling.PL.pi_point_witness_ext pi_ext;
    Tiling.PL.pi_transformation_ext := Tiling.PL.pi_transformation_ext pi_ext;
    Tiling.PL.pi_access_transformation_ext :=
      Tiling.PL.pi_access_transformation_ext pi_ext;
    Tiling.PL.pi_schedule1_ext := Tiling.PL.pi_schedule1_ext pi_ext;
    Tiling.PL.pi_schedule2_ext :=
      firstn (ptb_start band + 2 * ptb_len band)%nat
        (Tiling.PL.pi_schedule2_ext pi_ext);
    Tiling.PL.pi_waccess_ext := Tiling.PL.pi_waccess_ext pi_ext;
    Tiling.PL.pi_raccess_ext := Tiling.PL.pi_raccess_ext pi_ext;
  |}.

Fixpoint project_pinstrs_ext_with_bands
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (bands: list pinstr_tiling_band)
    : list Tiling.PL.PolyInstr_ext :=
  match pil_ext, bands with
  | pi_ext :: pil_ext', band :: bands' =>
      project_band_pi_ext band pi_ext ::
      project_pinstrs_ext_with_bands pil_ext' bands'
  | _, _ => []
  end.

Definition project_pinstrs_ext_with_band
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    : list Tiling.PL.PolyInstr_ext :=
  List.map (project_band_pi_ext band) pil_ext.

Definition band_new_cutoff
    (band: pinstr_tiling_band) : nat :=
  (ptb_start band + 2 * ptb_len band)%nat.

Fixpoint max_band_new_cutoff
    (bands: list pinstr_tiling_band) : nat :=
  match bands with
  | [] => 0%nat
  | band :: bands' => Nat.max (band_new_cutoff band) (max_band_new_cutoff bands')
  end.

Fixpoint max_pinstr_schedule_len
    (pis: list Tiling.PL.PolyInstr) : nat :=
  match pis with
  | [] => 0%nat
  | pi :: pis' =>
      Nat.max (List.length (Tiling.PL.pi_schedule pi))
              (max_pinstr_schedule_len pis')
  end.

Definition project_cutoff_pi_ext
    (cutoff: nat)
    (pi_ext: Tiling.PL.PolyInstr_ext) : Tiling.PL.PolyInstr_ext :=
  {|
    Tiling.PL.pi_depth_ext := Tiling.PL.pi_depth_ext pi_ext;
    Tiling.PL.pi_instr_ext := Tiling.PL.pi_instr_ext pi_ext;
    Tiling.PL.pi_poly_ext := Tiling.PL.pi_poly_ext pi_ext;
    Tiling.PL.pi_point_witness_ext := Tiling.PL.pi_point_witness_ext pi_ext;
    Tiling.PL.pi_transformation_ext := Tiling.PL.pi_transformation_ext pi_ext;
    Tiling.PL.pi_access_transformation_ext :=
      Tiling.PL.pi_access_transformation_ext pi_ext;
    Tiling.PL.pi_schedule1_ext := Tiling.PL.pi_schedule1_ext pi_ext;
    Tiling.PL.pi_schedule2_ext :=
      firstn cutoff (Tiling.PL.pi_schedule2_ext pi_ext);
    Tiling.PL.pi_waccess_ext := Tiling.PL.pi_waccess_ext pi_ext;
    Tiling.PL.pi_raccess_ext := Tiling.PL.pi_raccess_ext pi_ext;
  |}.

Definition project_cutoff_ip_ext
    (cutoff: nat)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  {|
    Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
    Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
    Tiling.PL.ip_transformation_ext := Tiling.PL.ip_transformation_ext ip_ext;
    Tiling.PL.ip_access_transformation_ext :=
      Tiling.PL.ip_access_transformation_ext ip_ext;
    Tiling.PL.ip_time_stamp1_ext := Tiling.PL.ip_time_stamp1_ext ip_ext;
    Tiling.PL.ip_time_stamp2_ext :=
      firstn cutoff (Tiling.PL.ip_time_stamp2_ext ip_ext);
    Tiling.PL.ip_instruction_ext := Tiling.PL.ip_instruction_ext ip_ext;
    Tiling.PL.ip_depth_ext := Tiling.PL.ip_depth_ext ip_ext;
  |}.

Definition project_pinstrs_ext_with_cutoff
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (cutoff: nat) : list Tiling.PL.PolyInstr_ext :=
  List.map (project_cutoff_pi_ext cutoff) pil_ext.

Definition project_band_ip_ext
    (band: pinstr_tiling_band)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  {|
    Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
    Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
    Tiling.PL.ip_transformation_ext := Tiling.PL.ip_transformation_ext ip_ext;
    Tiling.PL.ip_access_transformation_ext :=
      Tiling.PL.ip_access_transformation_ext ip_ext;
    Tiling.PL.ip_time_stamp1_ext := Tiling.PL.ip_time_stamp1_ext ip_ext;
    Tiling.PL.ip_time_stamp2_ext :=
      firstn (ptb_start band + 2 * ptb_len band)%nat
        (Tiling.PL.ip_time_stamp2_ext ip_ext);
    Tiling.PL.ip_instruction_ext := Tiling.PL.ip_instruction_ext ip_ext;
    Tiling.PL.ip_depth_ext := Tiling.PL.ip_depth_ext ip_ext;
  |}.

Definition restore_projected_band_ip_ext
    (pi_ext: Tiling.PL.PolyInstr_ext)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  {|
    Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
    Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
    Tiling.PL.ip_transformation_ext := Tiling.PL.pi_transformation_ext pi_ext;
    Tiling.PL.ip_access_transformation_ext :=
      Tiling.PL.pi_access_transformation_ext pi_ext;
    Tiling.PL.ip_time_stamp1_ext :=
      affine_product
        (Tiling.PL.pi_schedule1_ext pi_ext)
        (Tiling.PL.ip_index_ext ip_ext);
    Tiling.PL.ip_time_stamp2_ext :=
      affine_product
        (Tiling.PL.pi_schedule2_ext pi_ext)
        (Tiling.PL.ip_index_ext ip_ext);
    Tiling.PL.ip_instruction_ext := Tiling.PL.pi_instr_ext pi_ext;
    Tiling.PL.ip_depth_ext := Tiling.PL.pi_depth_ext pi_ext;
  |}.

Definition restore_projected_cutoff_ip_ext
    (pi_ext: Tiling.PL.PolyInstr_ext)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  {|
    Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
    Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
    Tiling.PL.ip_transformation_ext := Tiling.PL.pi_transformation_ext pi_ext;
    Tiling.PL.ip_access_transformation_ext :=
      Tiling.PL.pi_access_transformation_ext pi_ext;
    Tiling.PL.ip_time_stamp1_ext :=
      affine_product
        (Tiling.PL.pi_schedule1_ext pi_ext)
        (Tiling.PL.ip_index_ext ip_ext);
    Tiling.PL.ip_time_stamp2_ext :=
      affine_product
        (Tiling.PL.pi_schedule2_ext pi_ext)
        (Tiling.PL.ip_index_ext ip_ext);
    Tiling.PL.ip_instruction_ext := Tiling.PL.pi_instr_ext pi_ext;
    Tiling.PL.ip_depth_ext := Tiling.PL.pi_depth_ext pi_ext;
  |}.

Lemma project_band_ip_ext_old_eq_except_sched :
  forall band ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.old_of_ext ip_ext)
      (Tiling.PL.old_of_ext (project_band_ip_ext band ip_ext)).
Proof.
  intros band ip_ext.
  unfold Tiling.PL.eq_except_sched,
         Tiling.PL.old_of_ext,
         project_band_ip_ext.
  destruct ip_ext.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma project_band_ip_ext_new_eq_except_sched :
  forall band ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.new_of_ext ip_ext)
      (Tiling.PL.new_of_ext (project_band_ip_ext band ip_ext)).
Proof.
  intros band ip_ext.
  unfold Tiling.PL.eq_except_sched,
         Tiling.PL.new_of_ext,
         project_band_ip_ext.
  destruct ip_ext.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma project_cutoff_ip_ext_old_eq_except_sched :
  forall cutoff ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.old_of_ext ip_ext)
      (Tiling.PL.old_of_ext (project_cutoff_ip_ext cutoff ip_ext)).
Proof.
  intros cutoff ip_ext.
  unfold Tiling.PL.eq_except_sched,
         Tiling.PL.old_of_ext,
         project_cutoff_ip_ext.
  destruct ip_ext.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma project_cutoff_ip_ext_new_eq_except_sched :
  forall cutoff ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.new_of_ext ip_ext)
      (Tiling.PL.new_of_ext (project_cutoff_ip_ext cutoff ip_ext)).
Proof.
  intros cutoff ip_ext.
  unfold Tiling.PL.eq_except_sched,
         Tiling.PL.new_of_ext,
         project_cutoff_ip_ext.
  destruct ip_ext.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma eq_except_sched_symm_local :
  forall ip1 ip2,
    Tiling.PL.eq_except_sched ip1 ip2 ->
    Tiling.PL.eq_except_sched ip2 ip1.
Proof.
  intros ip1 ip2 Heq.
  unfold Tiling.PL.eq_except_sched in *.
  destruct Heq as (Hnth & Hidx & Htf & Hins & Hdepth).
  repeat split; symmetry; assumption.
Qed.

Lemma instr_point_sema_eq_except_sched_iff_local :
  forall ip1 ip2 st1 st2,
    Tiling.PL.eq_except_sched ip1 ip2 ->
    Tiling.PL.ILSema.instr_point_sema ip1 st1 st2 <->
    Tiling.PL.ILSema.instr_point_sema ip2 st1 st2.
Proof.
  intros ip1 ip2 st1 st2 Heq.
  unfold Tiling.PL.eq_except_sched in Heq.
  destruct Heq as (_ & Hidx & Htf & Hins & _).
  split; intro Hsema; inversion Hsema as [wcs rcs Hsem]; subst.
  - econstructor.
    rewrite <- Hidx, <- Htf, <- Hins.
    exact Hsem.
  - econstructor.
    rewrite Hidx, Htf, Hins.
    exact Hsem.
Qed.

Lemma permutable_eq_except_sched_local :
  forall ip1 ip1' ip2 ip2',
    Tiling.PL.eq_except_sched ip1 ip1' ->
    Tiling.PL.eq_except_sched ip2 ip2' ->
    Tiling.PL.ILSema.Permutable ip1 ip2 ->
    Tiling.PL.ILSema.Permutable ip1' ip2'.
Proof.
  intros ip1 ip1' ip2 ip2' Heq1 Heq2 Hperm.
  unfold Tiling.PL.ILSema.Permutable in *.
  intros st1 Halias.
  specialize (Hperm st1 Halias).
  destruct Hperm as [Hfwd Hbwd].
  split.
  - intros st2' st3 Hs1 Hs2.
    pose proof
      (proj2
         (instr_point_sema_eq_except_sched_iff_local ip1 ip1' st1 st2' Heq1)
         Hs1) as Hs1'.
    pose proof
      (proj2
         (instr_point_sema_eq_except_sched_iff_local ip2 ip2' st2' st3 Heq2)
         Hs2) as Hs2'.
    destruct (Hfwd _ _ Hs1' Hs2') as (st2'' & st3' & Ht1 & Ht2 & Heq).
    exists st2'', st3'. repeat split; auto.
    + apply
        (proj1
           (instr_point_sema_eq_except_sched_iff_local ip2 ip2' st1 st2'' Heq2)).
      exact Ht1.
    + apply
        (proj1
           (instr_point_sema_eq_except_sched_iff_local ip1 ip1' st2'' st3' Heq1)).
      exact Ht2.
  - intros st2' st3 Hs1 Hs2.
    pose proof
      (proj2
         (instr_point_sema_eq_except_sched_iff_local ip2 ip2' st1 st2' Heq2)
         Hs1) as Hs1'.
    pose proof
      (proj2
         (instr_point_sema_eq_except_sched_iff_local ip1 ip1' st2' st3 Heq1)
         Hs2) as Hs2'.
    destruct (Hbwd _ _ Hs1' Hs2') as (st2'' & st3' & Ht1 & Ht2 & Heq).
    exists st2'', st3'. repeat split; auto.
    + apply
        (proj1
           (instr_point_sema_eq_except_sched_iff_local ip1 ip1' st1 st2'' Heq1)).
      exact Ht1.
    + apply
        (proj1
           (instr_point_sema_eq_except_sched_iff_local ip2 ip2' st2'' st3' Heq2)).
      exact Ht2.
Qed.

Lemma project_band_ip_ext_preserves_np_eq :
  forall band ip_ext,
    Tiling.PL.np_eq_ext ip_ext (project_band_ip_ext band ip_ext).
Proof.
  intros band ip_ext.
  unfold Tiling.PL.np_eq_ext, project_band_ip_ext.
  destruct ip_ext.
  simpl.
  split.
  - reflexivity.
  - apply lex_compare_reflexive.
Qed.

Lemma project_band_ip_ext_permutable_back :
  forall band ip1_ext ip2_ext,
    Tiling.PL.Permutable_ext
      (project_band_ip_ext band ip1_ext)
      (project_band_ip_ext band ip2_ext) ->
    Tiling.PL.Permutable_ext ip1_ext ip2_ext.
Proof.
  intros band ip1_ext ip2_ext Hperm_proj.
  unfold Tiling.PL.Permutable_ext in Hperm_proj |- *.
  eapply permutable_eq_except_sched_local.
  - apply eq_except_sched_symm_local.
    apply project_band_ip_ext_old_eq_except_sched.
  - apply eq_except_sched_symm_local.
    apply project_band_ip_ext_old_eq_except_sched.
  - exact Hperm_proj.
Qed.

Lemma project_cutoff_ip_ext_preserves_np_eq :
  forall cutoff ip_ext,
    Tiling.PL.np_eq_ext ip_ext (project_cutoff_ip_ext cutoff ip_ext).
Proof.
  intros cutoff ip_ext.
  unfold Tiling.PL.np_eq_ext, project_cutoff_ip_ext.
  destruct ip_ext.
  simpl.
  split.
  - reflexivity.
  - apply lex_compare_reflexive.
Qed.

Lemma project_cutoff_ip_ext_permutable_back :
  forall cutoff ip1_ext ip2_ext,
    Tiling.PL.Permutable_ext
      (project_cutoff_ip_ext cutoff ip1_ext)
      (project_cutoff_ip_ext cutoff ip2_ext) ->
    Tiling.PL.Permutable_ext ip1_ext ip2_ext.
Proof.
  intros cutoff ip1_ext ip2_ext Hperm_proj.
  unfold Tiling.PL.Permutable_ext in Hperm_proj |- *.
  eapply permutable_eq_except_sched_local.
  - apply eq_except_sched_symm_local.
    apply project_cutoff_ip_ext_old_eq_except_sched.
  - apply eq_except_sched_symm_local.
    apply project_cutoff_ip_ext_old_eq_except_sched.
  - exact Hperm_proj.
Qed.

Definition project_pprog_band_ip_ext
    (bands: list pinstr_tiling_band)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  match List.nth_error bands (Tiling.PL.ip_nth_ext ip_ext) with
  | Some band => project_band_ip_ext band ip_ext
  | None => ip_ext
  end.

Definition project_ip_ext_with_band
    (band: pinstr_tiling_band)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  project_band_ip_ext band ip_ext.

Lemma project_band_ip_ext_preserves_np_lt :
  forall band ip1 ip2,
    Tiling.PL.np_lt_ext ip1 ip2 ->
    Tiling.PL.np_lt_ext
      (project_band_ip_ext band ip1)
      (project_band_ip_ext band ip2).
Proof.
  intros band ip1 ip2 Hlt.
  unfold Tiling.PL.np_lt_ext, project_band_ip_ext in *.
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma HdRel_map_project_band_ip_ext :
  forall band ip xs,
    HdRel Tiling.PL.np_lt_ext ip xs ->
    HdRel Tiling.PL.np_lt_ext
      (project_band_ip_ext band ip)
      (List.map (project_band_ip_ext band) xs).
Proof.
  intros band ip xs Hrel.
  induction Hrel as [|y ys Hxy].
  - constructor.
  - simpl.
    constructor.
    + eapply project_band_ip_ext_preserves_np_lt.
      exact Hxy.
Qed.

Lemma HdRel_map_project_pprog_band_ip_ext :
  forall bands ip xs,
    HdRel Tiling.PL.np_lt_ext ip xs ->
    HdRel Tiling.PL.np_lt_ext
      (project_pprog_band_ip_ext bands ip)
      (List.map (project_pprog_band_ip_ext bands) xs).
Proof.
  intros bands ip xs Hrel.
  induction Hrel as [|y ys Hxy].
  - constructor.
  - simpl.
    constructor.
    + unfold Tiling.PL.np_lt_ext in *.
      unfold project_pprog_band_ip_ext in *.
      destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip)) as [band|] eqn:Hband;
      destruct (List.nth_error bands (Tiling.PL.ip_nth_ext y)) as [band'|] eqn:Hband';
      destruct ip, y; simpl in *; exact Hxy.
Qed.

Lemma Sorted_map_project_band_ip_ext :
  forall band ipl,
    Sorted Tiling.PL.np_lt_ext ipl ->
    Sorted Tiling.PL.np_lt_ext (List.map (project_band_ip_ext band) ipl).
Proof.
  intros band ipl Hsorted.
  induction Hsorted as [|x xs Hsorted_xs IH Hrel].
  - constructor.
  - simpl.
    constructor.
    + exact IH.
    + eapply HdRel_map_project_band_ip_ext.
      exact Hrel.
Qed.

Lemma project_cutoff_ip_ext_preserves_np_lt :
  forall cutoff ip1 ip2,
    Tiling.PL.np_lt_ext ip1 ip2 ->
    Tiling.PL.np_lt_ext
      (project_cutoff_ip_ext cutoff ip1)
      (project_cutoff_ip_ext cutoff ip2).
Proof.
  intros cutoff ip1 ip2 Hlt.
  unfold Tiling.PL.np_lt_ext, project_cutoff_ip_ext in *.
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma HdRel_map_project_cutoff_ip_ext :
  forall cutoff ip xs,
    HdRel Tiling.PL.np_lt_ext ip xs ->
    HdRel Tiling.PL.np_lt_ext
      (project_cutoff_ip_ext cutoff ip)
      (List.map (project_cutoff_ip_ext cutoff) xs).
Proof.
  intros cutoff ip xs Hrel.
  induction Hrel as [|y ys Hxy].
  - constructor.
  - simpl.
    constructor.
    + eapply project_cutoff_ip_ext_preserves_np_lt.
      exact Hxy.
Qed.

Lemma Sorted_map_project_cutoff_ip_ext :
  forall cutoff ipl,
    Sorted Tiling.PL.np_lt_ext ipl ->
    Sorted Tiling.PL.np_lt_ext (List.map (project_cutoff_ip_ext cutoff) ipl).
Proof.
  intros cutoff ipl Hsorted.
  induction Hsorted as [|x xs Hsorted_xs IH Hrel].
  - constructor.
  - simpl.
    constructor.
    + exact IH.
    + eapply HdRel_map_project_cutoff_ip_ext.
      exact Hrel.
Qed.

Lemma project_cutoff_ip_ext_eq_iff :
  forall cutoff ip1 ip2,
    project_cutoff_ip_ext cutoff ip1 = project_cutoff_ip_ext cutoff ip2 ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 /\
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2.
Proof.
  intros cutoff ip1 ip2 Heq.
  unfold project_cutoff_ip_ext in Heq.
  destruct ip1, ip2; simpl in *.
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma project_pprog_band_ip_ext_preserves_np_lt :
  forall bands ip1 ip2,
    Tiling.PL.np_lt_ext ip1 ip2 ->
    Tiling.PL.np_lt_ext
      (project_pprog_band_ip_ext bands ip1)
      (project_pprog_band_ip_ext bands ip2).
Proof.
  intros bands ip1 ip2 Hlt.
  unfold project_pprog_band_ip_ext.
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip1)) as [band1|] eqn:Hb1;
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip2)) as [band2|] eqn:Hb2;
  unfold Tiling.PL.np_lt_ext in Hlt |- *;
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma project_pprog_band_ip_ext_preserves_np_eq :
  forall bands ip_ext,
    Tiling.PL.np_eq_ext ip_ext (project_pprog_band_ip_ext bands ip_ext).
Proof.
  intros bands ip_ext.
  unfold project_pprog_band_ip_ext.
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip_ext)) as [band|] eqn:Hband.
  - apply project_band_ip_ext_preserves_np_eq.
  - unfold Tiling.PL.np_eq_ext.
    split.
    + reflexivity.
    + apply lex_compare_reflexive.
Qed.

Lemma project_pprog_band_ip_ext_old_eq_except_sched :
  forall bands ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.old_of_ext ip_ext)
      (Tiling.PL.old_of_ext (project_pprog_band_ip_ext bands ip_ext)).
Proof.
  intros bands ip_ext.
  unfold project_pprog_band_ip_ext.
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip_ext)) as [band|] eqn:Hband.
  - apply project_band_ip_ext_old_eq_except_sched.
  - unfold Tiling.PL.eq_except_sched, Tiling.PL.old_of_ext.
    destruct ip_ext; simpl.
    repeat split; reflexivity.
Qed.

Lemma project_pprog_band_ip_ext_permutable_back :
  forall bands ip1 ip2,
    Tiling.PL.Permutable_ext
      (project_pprog_band_ip_ext bands ip1)
      (project_pprog_band_ip_ext bands ip2) ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros bands ip1 ip2 Hperm.
  unfold Tiling.PL.Permutable_ext in *.
  assert (Hold1 :
    Tiling.PL.old_of_ext (project_pprog_band_ip_ext bands ip1) =
    Tiling.PL.old_of_ext ip1).
  {
    unfold project_pprog_band_ip_ext.
    destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip1)) as [band|] eqn:Hband;
    destruct ip1; simpl; reflexivity.
  }
  assert (Hold2 :
    Tiling.PL.old_of_ext (project_pprog_band_ip_ext bands ip2) =
    Tiling.PL.old_of_ext ip2).
  {
    unfold project_pprog_band_ip_ext.
    destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip2)) as [band|] eqn:Hband;
    destruct ip2; simpl; reflexivity.
  }
  rewrite Hold1 in Hperm.
  rewrite Hold2 in Hperm.
  exact Hperm.
Qed.

Lemma project_pprog_band_ip_ext_eq_iff :
  forall bands ip1 ip2,
    project_pprog_band_ip_ext bands ip1 = project_pprog_band_ip_ext bands ip2 ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 /\
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2.
Proof.
  intros bands ip1 ip2 Heq.
  unfold project_pprog_band_ip_ext in Heq.
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip1)) as [band1|] eqn:Hband1;
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip2)) as [band2|] eqn:Hband2;
  destruct ip1, ip2; simpl in *; inversion Heq; subst; auto.
Qed.

Lemma project_band_ip_ext_eq_iff :
  forall band ip1 ip2,
    project_band_ip_ext band ip1 = project_band_ip_ext band ip2 ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 /\
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2.
Proof.
  intros band ip1 ip2 Heq.
  unfold project_band_ip_ext in Heq.
  destruct ip1, ip2; simpl in *.
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma affine_product_firstn_local :
  forall n m p,
    affine_product (firstn n m) p = firstn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - destruct m; reflexivity.
  - destruct m as [|x m]; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Lemma restore_projected_band_ip_ext_belongs_to_ext :
  forall pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (restore_projected_band_ip_ext pi_ext ip_ext)
      pi_ext.
Proof.
  intros pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [_ [_ [Hins Hdepth]]]]]].
  unfold restore_projected_band_ip_ext.
  simpl.
  repeat split; auto.
Qed.

Lemma restore_projected_band_ip_ext_from_project_belongs_to_ext :
  forall band pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext (project_band_pi_ext band pi_ext) ->
    Tiling.PL.belongs_to_ext
      (restore_projected_band_ip_ext pi_ext ip_ext)
      pi_ext.
Proof.
  intros band pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [_ [_ [Hins Hdepth]]]]]].
  unfold restore_projected_band_ip_ext.
  simpl.
  repeat split; auto.
Qed.

Lemma project_restore_projected_band_ip_ext :
  forall band pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext (project_band_pi_ext band pi_ext) ->
    project_band_ip_ext band (restore_projected_band_ip_ext pi_ext ip_ext) = ip_ext.
Proof.
  intros band pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in Hbel.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  destruct ip_ext.
  unfold project_band_ip_ext, restore_projected_band_ip_ext in *.
  simpl in *.
  subst.
  f_equal; try reflexivity.
  rewrite <- affine_product_firstn_local.
  reflexivity.
Qed.

Lemma restore_projected_cutoff_ip_ext_belongs_to_ext :
  forall pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (restore_projected_cutoff_ip_ext pi_ext ip_ext)
      pi_ext.
Proof.
  intros pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [_ [_ [Hins Hdepth]]]]]].
  unfold restore_projected_cutoff_ip_ext.
  simpl.
  repeat split; auto.
Qed.

Lemma restore_projected_cutoff_ip_ext_from_project_belongs_to_ext :
  forall cutoff pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext (project_cutoff_pi_ext cutoff pi_ext) ->
    Tiling.PL.belongs_to_ext
      (restore_projected_cutoff_ip_ext pi_ext ip_ext)
      pi_ext.
Proof.
  intros cutoff pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [_ [_ [Hins Hdepth]]]]]].
  unfold restore_projected_cutoff_ip_ext.
  simpl.
  repeat split; auto.
Qed.

Lemma project_restore_projected_cutoff_ip_ext :
  forall cutoff pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext (project_cutoff_pi_ext cutoff pi_ext) ->
    project_cutoff_ip_ext cutoff
      (restore_projected_cutoff_ip_ext pi_ext ip_ext) = ip_ext.
Proof.
  intros cutoff pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in Hbel.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  destruct ip_ext.
  unfold project_cutoff_ip_ext, restore_projected_cutoff_ip_ext in *.
  simpl in *.
  subst.
  f_equal; try reflexivity.
  rewrite <- affine_product_firstn_local.
  reflexivity.
Qed.

Lemma flatten_instr_nth_ext_index_injective_local :
  forall envv nth pi_ext ipl ip1 ip2,
    Tiling.PL.flatten_instr_nth_ext envv nth pi_ext ipl ->
    In ip1 ipl ->
    In ip2 ipl ->
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2 ->
    ip1 = ip2.
Proof.
  intros envv nth pi_ext ipl ip1 ip2 Hflat Hin1 Hin2 Hidx.
  destruct Hflat as [_ [Hmem _]].
  pose proof (Hmem ip1) as Hmem1.
  pose proof (Hmem ip2) as Hmem2.
  destruct Hmem1 as [Hfwd1 _].
  destruct Hmem2 as [Hfwd2 _].
  specialize (Hfwd1 Hin1).
  specialize (Hfwd2 Hin2).
  destruct Hfwd1 as [_ [Hbel1 [Hnth1 _]]].
  destruct Hfwd2 as [_ [Hbel2 [Hnth2 _]]].
  assert (Hnth_eq : Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2).
  {
    rewrite Hnth1, Hnth2.
    reflexivity.
  }
  unfold Tiling.PL.belongs_to_ext in Hbel1, Hbel2.
  destruct Hbel1 as
      [Hdom1 [Htf1 [Hacc1 [Hts11 [Hts12 [Hins1 Hdepth1]]]]]].
  destruct Hbel2 as
      [Hdom2 [Htf2 [Hacc2 [Hts21 [Hts22 [Hins2 Hdepth2]]]]]].
  destruct ip1, ip2.
  simpl in *.
  subst.
  repeat match goal with
         | H : _ = _ |- _ => rewrite H
         end.
  reflexivity.
Qed.

Lemma project_band_ip_ext_belongs_to_ext_local :
  forall band ip_ext pi_ext,
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (project_band_ip_ext band ip_ext)
      (project_band_pi_ext band pi_ext).
Proof.
  intros band ip_ext pi_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  unfold project_band_ip_ext, project_band_pi_ext.
  simpl.
  repeat split.
  - exact Hdom.
  - exact Htf.
  - exact Hacc_tf.
  - exact Hts1.
  - rewrite affine_product_firstn_local.
    rewrite Hts2.
    reflexivity.
  - exact Hins.
  - exact Hdepth.
Qed.

Lemma flatten_instr_nth_ext_project_band :
  forall envv nth pi_ext ipl band,
    Tiling.PL.flatten_instr_nth_ext envv nth pi_ext ipl ->
    Tiling.PL.flatten_instr_nth_ext
      envv nth
      (project_band_pi_ext band pi_ext)
      (List.map (project_band_ip_ext band) ipl).
Proof.
  intros envv nth pi_ext ipl band Hflat.
  pose proof Hflat as Hflat0.
  destruct Hflat as [Hpref [Hmem [Hnodup Hsorted]]].
  split.
  - intros ip_ext Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip0 [Hip Hin0]].
    subst.
    exact (Hpref _ Hin0).
  - split.
    + intros ip_ext.
      split; intro Hin.
      * apply in_map_iff in Hin.
        destruct Hin as [ip0 [Hip Hin0]].
        subst.
        destruct (Hmem ip0) as [Hfwd _].
        specialize (Hfwd Hin0).
        destruct Hfwd as [Hpref0 [Hbel0 [Hnth0 Hlen0]]].
        split; [exact Hpref0|].
        split.
        -- eapply project_band_ip_ext_belongs_to_ext_local; exact Hbel0.
        -- split; [exact Hnth0| exact Hlen0].
      * destruct Hin as [Hpref0 [Hbel0 [Hnth0 Hlen0]]].
        pose (ip_full := restore_projected_band_ip_ext pi_ext ip_ext).
        assert (Hin_full : In ip_full ipl).
        {
          destruct (Hmem ip_full) as [_ Hbwd].
          apply Hbwd.
          split; [exact Hpref0|].
          split.
          -- unfold ip_full.
             eapply restore_projected_band_ip_ext_from_project_belongs_to_ext.
             exact Hbel0.
          -- split; [exact Hnth0| exact Hlen0].
        }
        apply in_map_iff.
        exists ip_full.
        split.
        -- unfold ip_full.
           eapply project_restore_projected_band_ip_ext; exact Hbel0.
        -- exact Hin_full.
    + assert (Hnodup_proj :
          NoDup (List.map (project_band_ip_ext band) ipl)).
      {
        eapply Tiling.NoDup_map_on; [exact Hnodup|].
        intros ip1 ip2 Hin1 Hin2 Heq.
        apply project_band_ip_ext_eq_iff in Heq.
        destruct Heq as [_ Hidx].
        exact
          (flatten_instr_nth_ext_index_injective_local
             envv nth pi_ext ipl ip1 ip2 Hflat0 Hin1 Hin2 Hidx).
      }
      assert (Hsorted_proj :
          Sorted Tiling.PL.np_lt_ext
            (List.map (project_band_ip_ext band) ipl)).
      {
        eapply Sorted_map_project_band_ip_ext.
        exact Hsorted.
      }
      split; assumption.
Qed.

Lemma flatten_instrs_ext_index_injective_local :
  forall envv pil_ext ipl_ext ip1 ip2,
    Tiling.PL.flatten_instrs_ext envv pil_ext ipl_ext ->
    In ip1 ipl_ext ->
    In ip2 ipl_ext ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 ->
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2 ->
    ip1 = ip2.
Proof.
  intros envv pil_ext ipl_ext ip1 ip2 Hflat Hin1 Hin2 Hnth Hidx.
  destruct Hflat as [_ [Hmem _]].
  destruct (Hmem ip1) as [Hmem1 _].
  destruct (Hmem ip2) as [Hmem2 _].
  specialize (Hmem1 Hin1).
  specialize (Hmem2 Hin2).
  destruct Hmem1 as (pi1 & Hnth1 & Hpref1 & Hbel1 & Hlen1).
  destruct Hmem2 as (pi2 & Hnth2 & Hpref2 & Hbel2 & Hlen2).
  rewrite Hnth in Hnth1.
  rewrite Hidx in *.
  assert (Hpi : pi1 = pi2).
  {
    rewrite Hnth1 in Hnth2.
    inversion Hnth2.
    reflexivity.
  }
  subst pi2.
  unfold Tiling.PL.belongs_to_ext in Hbel1, Hbel2.
  destruct Hbel1 as
      [Hdom1 [Htf1 [Hacc1 [Hts11 [Hts12 [Hins1 Hdepth1]]]]]].
  destruct Hbel2 as
      [Hdom2 [Htf2 [Hacc2 [Hts21 [Hts22 [Hins2 Hdepth2]]]]]].
  destruct ip1, ip2; simpl in *; subst; reflexivity.
Qed.

Lemma flatten_instrs_ext_project_band :
  forall envv pil_ext ipl_ext band,
    Tiling.PL.flatten_instrs_ext envv pil_ext ipl_ext ->
    Tiling.PL.flatten_instrs_ext
      envv
      (project_pinstrs_ext_with_band pil_ext band)
      (List.map (project_ip_ext_with_band band) ipl_ext).
Proof.
  intros envv pil_ext ipl_ext band Hflat.
  unfold project_pinstrs_ext_with_band, project_ip_ext_with_band.
  destruct Hflat as [Hprefix [Hmem [Hnodup Hsorted]]].
  split.
  - intros ip_ext Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip0 [Hip Hin0]].
    subst.
    unfold project_ip_ext_with_band, project_band_ip_ext.
    simpl.
    exact (Hprefix _ Hin0).
  - split.
    + intros ip_ext.
      split; intro Hin.
      * apply in_map_iff in Hin.
        destruct Hin as [ip0 [Hip Hin0]].
        subst.
        destruct (Hmem ip0) as [Hfwd _].
        specialize (Hfwd Hin0).
        destruct Hfwd as (pi0 & Hnth0 & Hpref0 & Hbel0 & Hlen0).
        exists (project_band_pi_ext band pi0).
        split.
        -- erewrite map_nth_error; eauto.
        -- split.
           ++ exact Hpref0.
           ++ split.
              ** eapply project_band_ip_ext_belongs_to_ext_local; eauto.
              ** exact Hlen0.
      * destruct Hin as (pi_proj & Hnth_proj & Hpref_proj & Hbel_proj & Hlen_proj).
        destruct (nth_error pil_ext (Tiling.PL.ip_nth_ext ip_ext)) as [pi0|] eqn:Hnth0.
        -- assert (Hpi_proj : pi_proj = project_band_pi_ext band pi0).
           {
             erewrite map_nth_error in Hnth_proj; eauto.
             inversion Hnth_proj; reflexivity.
           }
           subst pi_proj.
           pose (ip_full := restore_projected_band_ip_ext pi0 ip_ext).
           assert (Hin_full : In ip_full ipl_ext).
           {
             destruct (Hmem ip_full) as [_ Hbwd].
             apply Hbwd.
             exists pi0.
             split; [exact Hnth0|].
             split.
             ++ exact Hpref_proj.
             ++ split.
                ** unfold ip_full.
                   eapply restore_projected_band_ip_ext_from_project_belongs_to_ext.
                   exact Hbel_proj.
                ** exact Hlen_proj.
           }
           apply in_map_iff.
           exists ip_full.
           split.
           ++ unfold ip_full.
              eapply project_restore_projected_band_ip_ext.
              exact Hbel_proj.
           ++ exact Hin_full.
        -- rewrite map_nth_error_none in Hnth_proj; congruence.
    + split.
      * apply Tiling.NoDup_map_on.
        -- exact Hnodup.
        -- intros ip1 ip2 Hin1 Hin2 Heq.
           apply project_band_ip_ext_eq_iff in Heq.
           destruct Heq as [Hnth Hidx].
           eapply flatten_instrs_ext_index_injective_local.
           ++ split; [exact Hprefix|].
              split; [exact Hmem|].
              split; [exact Hnodup| exact Hsorted].
           ++ exact Hin1.
           ++ exact Hin2.
           ++ exact Hnth.
           ++ exact Hidx.
      * apply Sorted_map_project_band_ip_ext.
        exact Hsorted.
Qed.

Lemma flatten_instrs_ext_project_cutoff :
  forall envv pil_ext ipl_ext cutoff,
    Tiling.PL.flatten_instrs_ext envv pil_ext ipl_ext ->
    Tiling.PL.flatten_instrs_ext
      envv
      (project_pinstrs_ext_with_cutoff pil_ext cutoff)
      (List.map (project_cutoff_ip_ext cutoff) ipl_ext).
Proof.
  intros envv pil_ext ipl_ext cutoff Hflat.
  unfold project_pinstrs_ext_with_cutoff.
  destruct Hflat as [Hprefix [Hmem [Hnodup Hsorted]]].
  split.
  - intros ip_ext Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip0 [Hip Hin0]].
    subst.
    unfold project_cutoff_ip_ext.
    simpl.
    exact (Hprefix _ Hin0).
  - split.
    + intros ip_ext.
      split; intro Hin.
      * apply in_map_iff in Hin.
        destruct Hin as [ip0 [Hip Hin0]].
        subst.
        destruct (Hmem ip0) as [Hfwd _].
        specialize (Hfwd Hin0).
        destruct Hfwd as (pi0 & Hnth0 & Hpref0 & Hbel0 & Hlen0).
        exists (project_cutoff_pi_ext cutoff pi0).
        split.
        -- erewrite map_nth_error; eauto.
        -- split.
           ++ exact Hpref0.
           ++ split.
              ** unfold Tiling.PL.belongs_to_ext in *.
                 destruct Hbel0 as
                     [Hdom [Htf [Hacc [Hts1 [Hts2 [Hins Hdepth]]]]]].
                 repeat split; try assumption.
                 simpl.
                 rewrite Hts2.
                 rewrite affine_product_firstn_local.
                 reflexivity.
              ** exact Hlen0.
      * destruct Hin as (pi_proj & Hnth_proj & Hpref_proj & Hbel_proj & Hlen_proj).
        destruct (nth_error pil_ext (Tiling.PL.ip_nth_ext ip_ext)) as [pi0|] eqn:Hnth0.
        -- assert (Hpi_proj : pi_proj = project_cutoff_pi_ext cutoff pi0).
           {
             erewrite map_nth_error in Hnth_proj; eauto.
             inversion Hnth_proj; reflexivity.
           }
           subst pi_proj.
           pose (ip_full := restore_projected_cutoff_ip_ext pi0 ip_ext).
           assert (Hin_full : In ip_full ipl_ext).
           {
             destruct (Hmem ip_full) as [_ Hbwd].
             apply Hbwd.
             exists pi0.
             split; [exact Hnth0|].
             split.
             ++ exact Hpref_proj.
             ++ split.
                ** unfold ip_full.
                   eapply restore_projected_cutoff_ip_ext_from_project_belongs_to_ext.
                   exact Hbel_proj.
                ** exact Hlen_proj.
           }
           apply in_map_iff.
           exists ip_full.
           split.
           ++ unfold ip_full.
              eapply project_restore_projected_cutoff_ip_ext.
              exact Hbel_proj.
           ++ exact Hin_full.
        -- rewrite map_nth_error_none in Hnth_proj; congruence.
    + split.
      * apply Tiling.NoDup_map_on.
        -- exact Hnodup.
        -- intros ip1 ip2 Hin1 Hin2 Heq.
           apply project_cutoff_ip_ext_eq_iff in Heq.
           destruct Heq as [Hnth Hidx].
           eapply flatten_instrs_ext_index_injective_local.
           ++ split; [exact Hprefix|].
              split; [exact Hmem|].
              split; [exact Hnodup| exact Hsorted].
           ++ exact Hin1.
           ++ exact Hin2.
           ++ exact Hnth.
           ++ exact Hidx.
      * apply Sorted_map_project_cutoff_ip_ext.
        exact Hsorted.
Qed.

Lemma project_pprog_band_ip_ext_preserves_old_sched_lt :
  forall bands ip1 ip2,
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_pprog_band_ip_ext bands ip1)
      (project_pprog_band_ip_ext bands ip2).
Proof.
  intros bands ip1 ip2 Hlt.
  unfold Tiling.PL.instr_point_ext_old_sched_lt in *.
  unfold project_pprog_band_ip_ext in *.
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip1)) as [band1|] eqn:Hband1;
  destruct (List.nth_error bands (Tiling.PL.ip_nth_ext ip2)) as [band2|] eqn:Hband2;
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma project_pprog_band_ip_ext_belongs_to_ext_local :
  forall bands ip_ext pi_ext band,
    List.nth_error bands (Tiling.PL.ip_nth_ext ip_ext) = Some band ->
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (project_pprog_band_ip_ext bands ip_ext)
      (project_band_pi_ext band pi_ext).
Proof.
  intros bands ip_ext pi_ext band Hband Hbel.
  unfold project_pprog_band_ip_ext.
  rewrite Hband.
  eapply project_band_ip_ext_belongs_to_ext_local; eauto.
Qed.

Lemma Sorted_map_project_pprog_band_ip_ext :
  forall bands ipl,
    Sorted Tiling.PL.np_lt_ext ipl ->
    Sorted Tiling.PL.np_lt_ext (List.map (project_pprog_band_ip_ext bands) ipl).
Proof.
  intros bands ipl Hsorted.
  induction Hsorted.
  - constructor.
  - simpl.
    constructor.
    + exact IHHsorted.
    + eapply HdRel_map_project_pprog_band_ip_ext.
      exact H.
Qed.

Lemma nth_error_project_pinstrs_ext_with_bands :
  forall pil_ext bands n pi_ext band,
    List.nth_error pil_ext n = Some pi_ext ->
    List.nth_error bands n = Some band ->
    List.nth_error (project_pinstrs_ext_with_bands pil_ext bands) n =
    Some (project_band_pi_ext band pi_ext).
Proof.
  induction pil_ext as [|pi_ext0 pil_ext' IH];
    intros bands n pi_ext band Hpi Hband.
  - destruct n; simpl in Hpi; discriminate.
  - destruct bands as [|band0 bands']; simpl in *.
    + destruct n; simpl in Hband; discriminate.
    + destruct n as [|n'].
      * now inversion Hpi; inversion Hband; subst.
      * eapply IH; eauto.
Qed.

Fixpoint find_schedule_block_start_aux
    (fuel start: nat)
    (sched block: Schedule) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      if listzzs_strict_eqb block (firstn (List.length block) (skipn start sched))
      then Some start
      else find_schedule_block_start_aux fuel' (S start) sched block
  end.

Definition find_schedule_block_start
    (sched block: Schedule) : option nat :=
  find_schedule_block_start_aux (S (List.length sched)) O sched block.

Lemma affine_product_app :
  forall m1 m2 p,
    affine_product (m1 ++ m2) p = affine_product m1 p ++ affine_product m2 p.
Proof.
  intros m1 m2 p.
  unfold affine_product.
  rewrite List.map_app.
  reflexivity.
Qed.

Lemma schedule_rows_of_links_aux_length :
  forall prefix links rows,
    schedule_rows_of_links_aux prefix links = Some rows ->
    List.length rows = List.length links.
Proof.
  intros prefix links.
  revert prefix.
  induction links as [|link links IH]; intros prefix rows Hrows.
  - simpl in Hrows. inversion Hrows. reflexivity.
  - simpl in Hrows.
    destruct (listz_strict_eqb
                (firstn prefix (ae_var_coeffs (tl_expr link)))
                (repeat 0%Z prefix)) eqn:Hprefix.
    + destruct (schedule_rows_of_links_aux (S prefix) links) as [rows'|] eqn:Hrest.
      * inversion Hrows; subst; clear Hrows.
        simpl.
        f_equal.
        apply (IH (S prefix) rows').
        exact Hrest.
      * discriminate.
    + discriminate.
Qed.

Lemma schedule_rows_of_links_length :
  forall w rows,
    schedule_rows_of_links w = Some rows ->
    List.length rows = List.length (stw_links w).
Proof.
  intros w rows Hrows.
  unfold schedule_rows_of_links in Hrows.
  eapply schedule_rows_of_links_aux_length; eauto.
Qed.

Lemma affine_product_schedule_row_of_tile_link_base :
  forall prefix_len prefix point params link,
    List.length prefix = prefix_len ->
    List.length (ae_var_coeffs (tl_expr link)) = (prefix_len + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length params ->
    firstn prefix_len (ae_var_coeffs (tl_expr link)) = repeat 0%Z prefix_len ->
    affine_product [schedule_row_of_tile_link_base prefix_len link] (params ++ point) =
    [eval_affine (tl_expr link) (prefix ++ point) params].
Proof.
  intros prefix_len prefix point params link Hprefix Hvars Hparams Hzero.
  unfold affine_product, schedule_row_of_tile_link_base, eval_affine.
  simpl.
  rewrite <-
    (Tiling.tiling_dot_product_eq_linalg_dot_product
       (ae_param_coeffs (tl_expr link) ++
        skipn prefix_len (ae_var_coeffs (tl_expr link)))
       (params ++ point)).
  rewrite TilingWitness.dot_product_app_exact by exact Hparams.
  rewrite (TilingWitness.dot_product_split_firstn_skipn
             (ae_var_coeffs (tl_expr link)) prefix point).
  2:{ rewrite Hprefix. exact Hvars. }
  rewrite Hprefix.
  rewrite Hzero.
  rewrite TilingWitness.dot_product_repeat_zero_exact by exact Hprefix.
  simpl.
  f_equal.
  lia.
Qed.

Lemma eval_tile_links_from_schedule_rows_aux :
  forall prefix prefix_len point params links rows sizes,
    List.length prefix = prefix_len ->
    schedule_rows_of_links_aux prefix_len links = Some rows ->
    List.map tl_tile_size links = sizes ->
    well_formed_tile_links prefix_len (List.length point) links ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      links ->
    eval_tile_links prefix point params links =
    prefix ++
    List.map
      (fun '(v, sz) => Z.div v sz)
      (List.combine (affine_product rows (params ++ point)) sizes).
Proof.
  intros prefix prefix_len point params links.
  revert prefix prefix_len.
  induction links as [|link links IH]; intros prefix prefix_len rows sizes
         Hprefix Hrows Hsizes Hwf Hparams.
  - simpl in Hrows. inversion Hrows; subst rows.
    simpl in Hsizes. inversion Hsizes; subst sizes.
    simpl. now rewrite app_nil_r.
  - simpl in Hrows.
    destruct (listz_strict_eqb
                (firstn prefix_len (ae_var_coeffs (tl_expr link)))
                (repeat 0%Z prefix_len)) eqn:Hzero_b; try discriminate.
    destruct (schedule_rows_of_links_aux (S prefix_len) links) as [rows'|] eqn:Hrows';
      try discriminate.
    inversion Hrows; subst rows; clear Hrows.
    simpl in Hsizes.
    destruct sizes as [|size sizes']; try discriminate.
    inversion Hsizes; subst size sizes'; clear Hsizes.
    destruct Hwf as [Hvars Hwf].
    inversion Hparams as [|link0 links0 Hparam Hparams']; subst link0 links0.
    apply listz_strict_eqb_eq in Hzero_b.
    simpl.
    specialize
      (IH (prefix ++ [eval_tile_parent link (prefix ++ point) params])
          (S prefix_len) rows' (List.map tl_tile_size links))
      as IH'.
    assert
      (Hprefix' :
         List.length (prefix ++ [eval_tile_parent link (prefix ++ point) params]) =
         S prefix_len).
    { rewrite app_length; simpl. lia. }
    specialize (IH' Hprefix' Hrows' eq_refl Hwf Hparams').
    rewrite IH'.
    rewrite <- app_assoc.
    simpl.
    f_equal.
    assert
      (Hrow :
         Linalg.dot_product
           (ae_param_coeffs (tl_expr link) ++
            skipn prefix_len (ae_var_coeffs (tl_expr link)))
           (params ++ point) + ae_const (tl_expr link) =
         eval_affine (tl_expr link) (prefix ++ point) params).
    {
      pose proof
        (affine_product_schedule_row_of_tile_link_base
           prefix_len prefix point params link Hprefix Hvars Hparam Hzero_b)
        as Htmp.
      simpl in Htmp.
      injection Htmp as Htmp'.
      exact Htmp'.
    }
    unfold eval_tile_parent.
    rewrite <- Hrow.
    reflexivity.
Qed.

Lemma eval_tile_links_from_schedule_rows :
  forall w point params rows sizes,
    List.length point = stw_point_dim w ->
    schedule_rows_of_links w = Some rows ->
    List.map tl_tile_size (stw_links w) = sizes ->
    well_formed_statement_tiling_witness w ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w) ->
    eval_tile_links [] point params (stw_links w) =
    List.map
      (fun '(v, sz) => Z.div v sz)
      (List.combine (affine_product rows (params ++ point)) sizes).
Proof.
  intros w point params rows sizes Hpoint_dim Hrows Hsizes Hwf Hparams.
  unfold well_formed_statement_tiling_witness in Hwf.
  assert (Hwf' : well_formed_tile_links 0 (List.length point) (stw_links w)).
  { rewrite Hpoint_dim. exact Hwf. }
  specialize
    (eval_tile_links_from_schedule_rows_aux
       [] 0 point params (stw_links w) rows sizes eq_refl Hrows Hsizes Hwf' Hparams)
    as Haux.
  simpl in Haux.
  exact Haux.
Qed.

Lemma insert_zeros_length_exact_local :
  forall d i l,
    (i <= length l)%nat ->
    length (Tiling.PL.insert_zeros d i l) = (d + length l)%nat.
Proof.
  intros d i l Hle.
  unfold Tiling.PL.insert_zeros.
  rewrite app_length, app_length.
  rewrite repeat_length.
  rewrite resize_length.
  rewrite skipn_length.
  lia.
Qed.

Lemma lift_schedule_after_env_exact_cols :
  forall cols added env_size sched,
    exact_listzzs_cols cols sched ->
    (env_size <= cols)%nat ->
    exact_listzzs_cols (added + cols)%nat
      (Tiling.lift_schedule_after_env added env_size sched).
Proof.
  intros cols added env_size sched Hcols Henv listz z listzz Hin Heq.
  unfold Tiling.lift_schedule_after_env, Tiling.lift_affine_function_after_env in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [[coeffs rhs] [Hmap Hin0]].
  rewrite Heq in Hmap.
  unfold Tiling.lift_constraint_after_env in Hmap.
  simpl in Hmap.
  inversion Hmap; subst listz z.
  specialize (Hcols coeffs rhs (coeffs, rhs) Hin0 eq_refl).
  unfold Tiling.lift_constraint_after_env.
  simpl.
  rewrite insert_zeros_length_exact_local by lia.
  rewrite Hcols.
  reflexivity.
Qed.

Lemma affine_product_firstn :
  forall n m p,
    affine_product (firstn n m) p = firstn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - destruct m; reflexivity.
  - destruct m as [|x m]; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Lemma in_firstn_local :
  forall {A} n (xs: list A) x,
    In x (firstn n xs) ->
    In x xs.
Proof.
  induction n as [|n IH]; intros xs x Hin.
  - destruct xs; simpl in Hin; contradiction.
  - destruct xs as [|y ys]; simpl in Hin.
    + contradiction.
    + destruct Hin as [Hin | Hin].
      * subst. left. reflexivity.
      * right. eapply IH. exact Hin.
Qed.

Lemma exact_listzzs_cols_firstn_local :
  forall cols n rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols (firstn n rows).
Proof.
  intros cols n rows Hcols listz z listzz Hin Heq.
  eapply Hcols; eauto.
  eapply in_firstn_local; eauto.
Qed.

Lemma exact_listzzs_cols_lift_schedule_after_env_local :
  forall cols added env_size sched,
    exact_listzzs_cols cols sched ->
    (env_size <= cols)%nat ->
    exact_listzzs_cols (cols + added)%nat
      (Tiling.lift_schedule_after_env added env_size sched).
Proof.
  intros cols added env_size sched Hcols Henv.
  unfold Tiling.lift_schedule_after_env, Tiling.lift_affine_function_after_env.
  eapply Tiling.PL.exact_listzzs_cols_current_insert_zeros_constraint; eauto.
Qed.

Lemma compose_tiling_pinstr_ext_wf_tiling_local :
  forall env vars before after w,
    Tiling.PL.wf_pinstr_tiling env vars before ->
    Tiling.PL.wf_pinstr_tiling env vars after ->
    stw_point_dim w = Tiling.PL.pi_depth before ->
    Tiling.after_matches_tiling_witness after w ->
    Tiling.PL.wf_pinstr_ext_tiling env
      (Tiling.compose_tiling_pinstr_ext (List.length env) before after w).
Proof.
  intros env vars before after w Hwf_before Hwf_after Hpoint_dim Hafter_wit.
  destruct Hafter_wit as [Hwitness_after Hwitdim_after].
  unfold Tiling.PL.wf_pinstr_ext_tiling, Tiling.PL.wf_pinstr_ext.
  unfold Tiling.compose_tiling_pinstr_ext, Tiling.current_src_transformation_of_pinstr.
  simpl.
  destruct Hwf_before as [Hwf_before_core _].
  destruct Hwf_after as [Hwf_after_core Htf_eq_after].
  destruct Hwf_before_core as
      [Hwit_before [Hcols_before [Hpoly_nrl_before [Hsched_nrl_before
       [Hpoly_before [Htf_before [Hacc_before [Hsched_before
       [Hw_before Hr_before]]]]]]]]].
  destruct Hwf_after_core as
      [Hwit_after [Hcols_after [Hpoly_nrl_after [Hsched_nrl_after
       [Hpoly_after [Htf_after [Hacc_after [Hsched_after
       [Hw_after Hr_after]]]]]]]]].
  split.
  - repeat split.
    + exact Hwitdim_after.
    + exact Hpoly_after.
    + rewrite <- Hwit_after.
      eapply Tiling.PL.exact_listzzs_cols_current_transformation_at.
      exact Htf_after.
    + rewrite <- Hwit_after.
      eapply Tiling.PL.exact_listzzs_cols_current_transformation_at.
      exact Htf_after.
    + replace
        (length env + Tiling.PL.pi_depth after)%nat
        with
          (length env + Tiling.PL.pi_depth before + List.length (stw_links w))%nat.
      * eapply exact_listzzs_cols_lift_schedule_after_env_local.
        -- exact Hsched_before.
        -- lia.
      * rewrite <- Hpoint_dim.
        rewrite <- Hwitdim_after.
        rewrite Hwitness_after.
        unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
        simpl.
        lia.
    + exact Hsched_after.
    + rewrite Tiling.PL.current_transformation_at_preserve_length.
      exact Hw_after.
    + rewrite Tiling.PL.current_transformation_at_preserve_length.
      exact Hr_after.
  - reflexivity.
Qed.

Lemma project_band_pi_ext_wf_tiling :
  forall env band pi_ext,
    Tiling.PL.wf_pinstr_ext_tiling env pi_ext ->
    Tiling.PL.wf_pinstr_ext_tiling env (project_band_pi_ext band pi_ext).
Proof.
  intros env band pi_ext Hwf.
  unfold Tiling.PL.wf_pinstr_ext_tiling in *.
  destruct Hwf as [Hwf Htf].
  unfold Tiling.PL.wf_pinstr_ext in *.
  simpl in *.
  destruct Hwf as
      (Hwit & Hpoly & Htf_cols & Hacc_tf_cols &
       Hsched1 & Hsched2 & Hw & Hr).
  split.
  - repeat split.
    + exact Hwit.
    + exact Hpoly.
    + exact Htf_cols.
    + exact Hacc_tf_cols.
    + exact Hsched1.
    + eapply exact_listzzs_cols_firstn_local. exact Hsched2.
    + exact Hw.
    + exact Hr.
  - exact Htf.
Qed.

Lemma project_cutoff_pi_ext_wf_tiling :
  forall env cutoff pi_ext,
    Tiling.PL.wf_pinstr_ext_tiling env pi_ext ->
    Tiling.PL.wf_pinstr_ext_tiling env (project_cutoff_pi_ext cutoff pi_ext).
Proof.
  intros env cutoff pi_ext Hwf.
  unfold Tiling.PL.wf_pinstr_ext_tiling in *.
  destruct Hwf as [Hwf Htf].
  unfold Tiling.PL.wf_pinstr_ext in *.
  simpl in *.
  destruct Hwf as
      (Hwit & Hpoly & Htf_cols & Hacc_tf_cols &
       Hsched1 & Hsched2 & Hw & Hr).
  split.
  - repeat split.
    + exact Hwit.
    + exact Hpoly.
    + exact Htf_cols.
    + exact Hacc_tf_cols.
    + exact Hsched1.
    + eapply exact_listzzs_cols_firstn_local. exact Hsched2.
    + exact Hw.
    + exact Hr.
  - exact Htf.
Qed.

Lemma project_pinstrs_ext_with_bands_preserve_length :
  forall pil_ext bands,
    List.length pil_ext = List.length bands ->
    List.length (project_pinstrs_ext_with_bands pil_ext bands) =
    List.length pil_ext.
Proof.
  induction pil_ext as [|pi_ext pil_ext' IH]; intros bands Hlen.
  - destruct bands; simpl in *; try discriminate; reflexivity.
  - destruct bands as [|band bands']; simpl in *; try discriminate.
    simpl.
    f_equal.
    eapply IH; lia.
Qed.

Lemma identity_affine_rows_from_length :
  forall total_cols pos count,
    List.length (Tiling.identity_affine_rows_from total_cols pos count) = count.
Proof.
  intros total_cols pos count.
  revert total_cols pos.
  induction count as [|count IH]; intros total_cols pos; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma stripmine_schedule_after_env_length :
  forall env_size before_sched band,
    List.length (stripmine_schedule_after_env env_size before_sched band) =
    (List.length before_sched + ptb_len band)%nat.
Proof.
  intros env_size before_sched band.
  unfold stripmine_schedule_after_env.
  set (added_dims := ptb_len band).
  set (lifted := Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (prefix := firstn (ptb_start band) lifted).
  set (lifted_band := firstn added_dims (skipn (ptb_start band) lifted)).
  set (suffix := skipn (ptb_start band + added_dims)%nat lifted).
  assert (Hlifted_len : List.length lifted = List.length before_sched).
  {
    subst lifted.
    unfold Tiling.lift_schedule_after_env, Tiling.lift_affine_function_after_env.
    rewrite List.map_length.
    reflexivity.
  }
  assert (Hsplit :
    (List.length prefix + List.length lifted_band + List.length suffix)%nat =
    List.length lifted).
  {
    subst prefix lifted_band suffix.
    rewrite !firstn_length.
    rewrite !skipn_length.
    lia.
  }
  rewrite !app_length.
  rewrite identity_affine_rows_from_length.
  lia.
Qed.

Lemma schedule_matches_with_trailing_zero_padding_length_ge :
  forall expected actual,
    schedule_matches_with_trailing_zero_padding expected actual ->
    (List.length expected <= List.length actual)%nat.
Proof.
  intros expected actual [cols [extra_rows Hactual]].
  subst actual.
  unfold pad_schedule_with_zero_rows.
  rewrite app_length, repeat_length.
  lia.
Qed.

Lemma schedule_matches_with_trailing_zero_padding_affine_product_firstn :
  forall expected actual idx n,
    schedule_matches_with_trailing_zero_padding expected actual ->
    (n <= List.length expected)%nat ->
    firstn n (affine_product actual idx) =
    firstn n (affine_product expected idx).
Proof.
  intros expected actual idx n [cols [extra_rows Hactual]] Hn.
  subst actual.
  unfold pad_schedule_with_zero_rows.
  rewrite <- affine_product_firstn.
  rewrite <- affine_product_firstn.
  rewrite firstn_app.
  assert
    (Hdrop :
       firstn (n - List.length expected)%nat
         (repeat (zero_schedule_row cols) extra_rows) = []).
  {
    replace (n - List.length expected)%nat with 0%nat by lia.
    reflexivity.
  }
  rewrite Hdrop.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma affine_product_zero_schedule_rows :
  forall cols extra_rows idx,
    affine_product (repeat (zero_schedule_row cols) extra_rows) idx =
    repeat 0%Z extra_rows.
Proof.
  intros cols extra_rows idx.
  unfold affine_product.
  induction extra_rows as [|extra_rows IH]; simpl.
  - reflexivity.
  - unfold zero_schedule_row.
    simpl.
    rewrite dot_product_repeat_zero_left.
    f_equal.
    exact IH.
Qed.

Lemma affine_product_pad_schedule_with_zero_rows :
  forall sched cols extra_rows idx,
    affine_product
      (pad_schedule_with_zero_rows sched cols extra_rows)
      idx =
    affine_product sched idx ++ repeat 0%Z extra_rows.
Proof.
  intros sched cols extra_rows idx.
  unfold pad_schedule_with_zero_rows.
  rewrite affine_product_app.
  rewrite affine_product_zero_schedule_rows.
  reflexivity.
Qed.

Lemma belongs_to_ext_ts2_length :
  forall ip pi,
    Tiling.PL.belongs_to_ext ip pi ->
    List.length (Tiling.PL.ip_time_stamp2_ext ip) =
    List.length (Tiling.PL.pi_schedule2_ext pi).
Proof.
  intros ip pi Hbel.
  unfold Tiling.PL.belongs_to_ext in Hbel.
  destruct Hbel as [_ [_ [_ [_ [Hts2 [_ _]]]]]].
  rewrite Hts2.
  unfold affine_product.
  rewrite List.map_length.
  reflexivity.
Qed.

Lemma compose_tiling_pinstrs_ext_from_after_wf_tiling :
  forall env vars before_pis after_pis ws,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws).
Proof.
  intros env vars before_pis.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hwf_before Hwf_after Hdepths Hwits.
  - destruct after_pis as [|after_pi after_pis'];
      destruct ws as [|w ws']; inversion Hwf_before; inversion Hwf_after;
      inversion Hdepths; inversion Hwits; subst; constructor.
  - destruct after_pis as [|after_pi after_pis'];
      destruct ws as [|w ws']; inversion Hwf_before; inversion Hwf_after;
      inversion Hdepths; inversion Hwits; subst; simpl.
    all: try solve [inversion Hdepths | inversion Hwits].
    constructor.
    + eapply compose_tiling_pinstr_ext_wf_tiling_local; eauto.
    + eapply IH; eauto.
Qed.

Lemma project_pinstrs_ext_with_band_wf_tiling :
  forall env vars before_pis after_pis ws band,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (project_pinstrs_ext_with_band
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length env) before_pis after_pis ws)
         band).
Proof.
  intros env vars before_pis after_pis ws band
         Hwf_before Hwf_after Hdepths Hwits.
  unfold project_pinstrs_ext_with_band.
  assert (Hwf_full :
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  eapply Forall_forall.
  intros pi_ext HIn.
  apply in_map_iff in HIn.
  destruct HIn as [pi_ext0 [Hpi_ext HIn0]].
  subst pi_ext.
  eapply project_band_pi_ext_wf_tiling.
  eapply Forall_forall; eauto.
Qed.

Lemma project_pinstrs_ext_with_bands_wf_tiling :
  forall env vars before_pis after_pis ws bands,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (project_pinstrs_ext_with_bands
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length env) before_pis after_pis ws)
         bands).
Proof.
  intros env vars before_pis.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws bands Hwf_before Hwf_after Hdepths Hwits.
  - destruct after_pis as [|after_pi after_pis']; destruct ws as [|w ws'];
      destruct bands as [|band bands']; simpl in *; constructor.
  - destruct after_pis as [|after_pi after_pis']; destruct ws as [|w ws'];
      destruct bands as [|band bands']; inversion Hwf_before;
      inversion Hwf_after; inversion Hdepths; inversion Hwits; subst; simpl in *;
      try solve [constructor].
    constructor.
    + eapply project_band_pi_ext_wf_tiling.
      eapply compose_tiling_pinstr_ext_wf_tiling_local; eauto.
    + eapply IH; eauto.
Qed.

Lemma project_pinstrs_ext_with_cutoff_wf_tiling :
  forall env vars before_pis after_pis ws cutoff,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (project_pinstrs_ext_with_cutoff
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length env) before_pis after_pis ws)
         cutoff).
Proof.
  intros env vars before_pis after_pis ws cutoff
         Hwf_before Hwf_after Hdepths Hwits.
  unfold project_pinstrs_ext_with_cutoff.
  assert (Hwf_full :
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  eapply Forall_forall.
  intros pi_ext HIn.
  apply in_map_iff in HIn.
  destruct HIn as [pi_ext0 [Hpi_ext HIn0]].
  subst pi_ext.
  eapply project_cutoff_pi_ext_wf_tiling.
  eapply Forall_forall; eauto.
Qed.

Lemma project_band_ip_ext_belongs_to_ext :
  forall band ip_ext pi_ext,
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (project_band_ip_ext band ip_ext)
      (project_band_pi_ext band pi_ext).
Proof.
  intros band ip_ext pi_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  unfold project_band_ip_ext, project_band_pi_ext.
  simpl.
  repeat split.
  - exact Hdom.
  - exact Htf.
  - exact Hacc_tf.
  - exact Hts1.
  - rewrite affine_product_firstn.
    rewrite Hts2.
    reflexivity.
  - exact Hins.
  - exact Hdepth.
Qed.

Lemma affine_product_skipn :
  forall n m p,
    affine_product (skipn n m) p = skipn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - reflexivity.
  - destruct m as [|x m]; simpl; auto.
Qed.

Lemma affine_product_identity_affine_row :
  forall total_cols pos idx,
    (S pos <= total_cols)%nat ->
    affine_product [Tiling.identity_affine_row total_cols pos] idx =
    [nth pos idx 0%Z].
Proof.
  intros total_cols pos idx Hle.
  unfold Tiling.identity_affine_row.
  simpl.
  assert (Hrow :
    repeat 0%Z pos ++ 1%Z :: repeat 0%Z (total_cols - pos - 1) =
    resize total_cols (V0 pos ++ [1%Z])).
  {
    rewrite resize_app_le.
    2: {
      unfold V0.
      rewrite repeat_length.
      lia.
    }
    replace (Datatypes.length (V0 pos)) with pos.
    2: {
      unfold V0.
      rewrite repeat_length.
      reflexivity.
    }
    replace (total_cols - pos)%nat with (S (total_cols - pos - 1)) by lia.
    simpl.
    rewrite resize_null_repeat by reflexivity.
    unfold V0.
    replace (total_cols - pos - 1 - 0)%nat with (total_cols - pos - 1)%nat by lia.
    reflexivity.
  }
  rewrite Hrow.
  rewrite ParallelCore.dot_product_select_coord by exact Hle.
  f_equal.
  lia.
Qed.

Lemma affine_product_identity_affine_rows_from :
  forall total_cols pos count idx,
    (pos + count <= total_cols)%nat ->
    (pos + count <= List.length idx)%nat ->
    affine_product (Tiling.identity_affine_rows_from total_cols pos count) idx =
    firstn count (skipn pos idx).
Proof.
  intros total_cols pos count.
  revert pos.
  induction count as [|count IH]; intros pos idx Hle Hlen.
  - simpl. reflexivity.
  - simpl Tiling.identity_affine_rows_from.
    replace
      (Tiling.identity_affine_row total_cols pos ::
       Tiling.identity_affine_rows_from total_cols (S pos) count)
      with
      ([Tiling.identity_affine_row total_cols pos] ++
       Tiling.identity_affine_rows_from total_cols (S pos) count)
      by reflexivity.
    rewrite affine_product_app.
    rewrite affine_product_identity_affine_row by lia.
    rewrite IH by lia.
    destruct (skipn pos idx) as [|x xs] eqn:Hskip.
    + assert (Hskip_len : List.length (skipn pos idx) = 0%nat).
      { rewrite Hskip. reflexivity. }
      rewrite skipn_length in Hskip_len.
      lia.
    + assert (Hnth : nth pos idx 0%Z = x).
      {
        assert (Hplus : (pos + 0)%nat = pos) by lia.
        rewrite <- Hplus.
        rewrite <- Misc.nth_skipn with (m := pos) (n := 0%nat) (d := 0%Z).
        rewrite Hskip.
        reflexivity.
      }
      assert (Htail : skipn (S pos) idx = xs).
      {
        replace (S pos) with (1 + pos)%nat by lia.
        rewrite <- skipn_skipn with (n := 1%nat) (m := pos) (l := idx).
        rewrite Hskip.
        simpl.
        reflexivity.
      }
      simpl.
      rewrite Hnth.
      replace match idx with
              | [] => []
              | _ :: l => skipn pos l
              end
        with (skipn (S pos) idx).
      2:{
        destruct idx as [|y ys]; reflexivity.
      }
      rewrite Htail.
      reflexivity.
Qed.

Lemma stripmine_schedule_after_env_eval :
  forall env_size before_sched band cols env tiles iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    length env = env_size ->
    length tiles = ptb_len band ->
    affine_product
      (stripmine_schedule_after_env env_size before_sched band)
      (env ++ tiles ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    tiles ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros env_size before_sched band cols env tiles iters Hsched_cols Henv_cols Henv Htiles.
  unfold stripmine_schedule_after_env.
  set (added_dims := ptb_len band).
  set (lifted := Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end).
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted (env ++ tiles ++ iters) = old_ts).
  {
    subst lifted old_ts added_dims.
    apply Tiling.lift_affine_function_after_env_eval; assumption.
  }
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_firstn.
  rewrite affine_product_firstn.
  rewrite !affine_product_skipn.
  rewrite (affine_product_identity_affine_rows_from total_cols env_size added_dims
            (env ++ tiles ++ iters)).
  2:{
    subst total_cols.
    pose proof (lift_schedule_after_env_exact_cols cols added_dims env_size before_sched
                 Hsched_cols Henv_cols) as Hlift_cols.
    subst lifted.
    destruct (Tiling.lift_schedule_after_env added_dims env_size before_sched) as [|[coeffs rhs] rows].
    - lia.
    - assert (length coeffs = (added_dims + cols)%nat).
      {
        eapply Hlift_cols.
        - left. reflexivity.
        - reflexivity.
      }
      lia.
  }
  2:{
    subst added_dims.
    repeat rewrite app_length.
    lia.
  }
  rewrite Hlift.
  rewrite <- Henv.
  assert (Hskip_mid :
    skipn (length env) (env ++ tiles ++ iters) = tiles ++ iters).
  {
    replace (env ++ tiles ++ iters) with (env ++ (tiles ++ iters)) by reflexivity.
    rewrite skipn_app_le by lia.
    replace (length env - length env)%nat with 0%nat by lia.
    simpl.
    reflexivity.
  }
  rewrite Hskip_mid.
  rewrite firstn_app.
  replace (firstn added_dims tiles) with tiles.
  2:{
    subst added_dims.
    symmetry.
    rewrite <- Htiles.
    apply firstn_all.
  }
  subst added_dims.
  rewrite Htiles.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma find_schedule_block_start_aux_sound :
  forall fuel start sched block found,
    find_schedule_block_start_aux fuel start sched block = Some found ->
    firstn (List.length block) (skipn found sched) = block.
Proof.
  induction fuel as [|fuel IH]; intros start sched block found Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (listzzs_strict_eqb block (firstn (List.length block) (skipn start sched)))
      eqn:Hhere.
    + inversion Hfind; subst.
      apply listzzs_strict_eqb_eq in Hhere.
      symmetry. exact Hhere.
    + eapply IH; eauto.
Qed.

Lemma find_schedule_block_start_aux_bound :
  forall fuel start sched block found,
    find_schedule_block_start_aux fuel start sched block = Some found ->
    (found < start + fuel)%nat.
Proof.
  induction fuel as [|fuel IH]; intros start sched block found Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (listzzs_strict_eqb block (firstn (List.length block) (skipn start sched)))
      eqn:Hhere.
    + inversion Hfind; subst. lia.
    + specialize (IH (S start) sched block found Hfind).
      lia.
Qed.

Lemma find_schedule_block_start_sound :
  forall sched block found,
    find_schedule_block_start sched block = Some found ->
    firstn (List.length block) (skipn found sched) = block.
Proof.
  intros sched block found Hfind.
  unfold find_schedule_block_start in Hfind.
  eapply find_schedule_block_start_aux_sound; eauto.
Qed.

Lemma find_schedule_block_start_bound :
  forall sched block found,
    find_schedule_block_start sched block = Some found ->
    (found <= List.length sched)%nat.
Proof.
  intros sched block found Hfind.
  unfold find_schedule_block_start in Hfind.
  pose proof (find_schedule_block_start_aux_bound _ _ _ _ _ Hfind) as Hbound.
  lia.
Qed.

Definition check_pinstr_tiling_bandb
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  match schedule_rows_of_links w with
  | Some rows =>
      match find_schedule_block_start
              (Tiling.PL.pi_schedule before)
              rows with
      | Some _ => true
      | None => false
      end
  | None => false
  end.

Definition infer_pinstr_tiling_band
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : option pinstr_tiling_band :=
  match schedule_rows_of_links w with
  | Some rows =>
      match find_schedule_block_start
              (Tiling.PL.pi_schedule before)
              rows with
      | Some start =>
          Some {| ptb_start := start; ptb_len := List.length (stw_links w) |}
      | None => None
      end
  | None => None
  end.

Lemma check_pinstr_tiling_bandb_sound :
  forall before w,
    check_pinstr_tiling_bandb before w = true ->
    exists band,
      infer_pinstr_tiling_band before w = Some band /\
      pinstr_tiling_band_matches before w band.
Proof.
  intros before w Hcheck.
  unfold check_pinstr_tiling_bandb, infer_pinstr_tiling_band in *.
  destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows; try discriminate.
  destruct (find_schedule_block_start
              (Tiling.PL.pi_schedule before)
              rows) as [start|] eqn:Hstart;
    try discriminate.
  exists {| ptb_start := start; ptb_len := List.length (stw_links w) |}.
  split; [reflexivity|].
  unfold pinstr_tiling_band_matches.
  rewrite Hrows.
  split.
  - reflexivity.
  - replace (List.length (stw_links w)) with (List.length rows).
    2:{ eapply schedule_rows_of_links_length; eauto. }
    eapply find_schedule_block_start_sound; eauto.
Qed.

Lemma infer_pinstr_tiling_band_bound :
  forall before w band,
    infer_pinstr_tiling_band before w = Some band ->
    (ptb_start band + ptb_len band <= List.length (Tiling.PL.pi_schedule before))%nat.
Proof.
  intros before w band Hinfer.
  unfold infer_pinstr_tiling_band in Hinfer.
  destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows; try discriminate.
  destruct (find_schedule_block_start (Tiling.PL.pi_schedule before) rows)
    as [start|] eqn:Hstart; try discriminate.
  inversion Hinfer; subst; clear Hinfer.
  pose proof (find_schedule_block_start_bound _ _ _ Hstart) as Hstart_bound.
  pose proof (find_schedule_block_start_sound _ _ _ Hstart) as Hblock.
  pose proof (schedule_rows_of_links_length _ _ Hrows) as Hrows_len.
  assert (Hrows_fit :
    (List.length rows <=
     List.length (Tiling.PL.pi_schedule before) - start)%nat).
  {
    assert (Hlen_block :
      List.length
        (firstn (List.length rows)
           (skipn start (Tiling.PL.pi_schedule before))) =
      List.length rows).
    {
      rewrite Hblock.
      reflexivity.
    }
    rewrite firstn_length, skipn_length in Hlen_block.
    destruct
      (le_gt_dec (List.length rows)
         (List.length (Tiling.PL.pi_schedule before) - start)%nat); auto.
    rewrite Nat.min_r in Hlen_block by lia.
    lia.
  }
  assert (Hle_skip :
    (List.length (stw_links w) <=
     List.length (Tiling.PL.pi_schedule before) - start)%nat).
  {
    rewrite <- Hrows_len.
    exact Hrows_fit.
  }
  eapply Nat.le_trans.
  - apply (proj1 (Nat.add_le_mono_l
                    (List.length (stw_links w))
                    (List.length (Tiling.PL.pi_schedule before) - start)
                    start)).
    exact Hle_skip.
  - replace
      (start + (List.length (Tiling.PL.pi_schedule before) - start))%nat
      with (List.length (Tiling.PL.pi_schedule before)) by lia.
    apply Nat.le_refl.
Qed.

Definition check_pinstr_tiling_schedule_stripminedb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  match infer_pinstr_tiling_band before w with
  | Some band =>
      check_schedule_with_trailing_zero_paddingb
        (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
        (Tiling.PL.pi_schedule after)
  | None => false
  end.

Lemma check_schedule_with_trailing_zero_paddingb_sound :
  forall expected actual,
    check_schedule_with_trailing_zero_paddingb expected actual = true ->
    schedule_matches_with_trailing_zero_padding expected actual.
Proof.
  intros expected actual Hcheck.
  unfold check_schedule_with_trailing_zero_paddingb in Hcheck.
  destruct (Nat.leb (List.length expected) (List.length actual)) eqn:Hlen;
    try discriminate.
  exists
    (match actual with
     | [] => 0%nat
     | (coeffs, _) :: _ => List.length coeffs
     end).
  exists (List.length actual - List.length expected)%nat.
  apply listzzs_strict_eqb_eq in Hcheck.
  exact Hcheck.
Qed.

Lemma check_pinstr_tiling_schedule_stripminedb_sound :
  forall env_size before after w,
    check_pinstr_tiling_schedule_stripminedb env_size before after w = true ->
    exists band,
      infer_pinstr_tiling_band before w = Some band /\
      pinstr_tiling_band_matches before w band /\
      schedule_matches_with_trailing_zero_padding
        (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
        (Tiling.PL.pi_schedule after).
Proof.
  intros env_size before after w Hcheck.
  unfold check_pinstr_tiling_schedule_stripminedb in Hcheck.
  destruct (infer_pinstr_tiling_band before w) as [band|] eqn:Hband;
    try discriminate.
  exists band.
  split.
  - reflexivity.
  - split.
    + unfold infer_pinstr_tiling_band in Hband.
      destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows;
        try discriminate.
      destruct (find_schedule_block_start
                  (Tiling.PL.pi_schedule before)
                  rows) as [start|] eqn:Hstart;
        inversion Hband; subst; clear Hband.
      unfold pinstr_tiling_band_matches.
      rewrite Hrows.
      split.
      * reflexivity.
      * replace (List.length (stw_links w)) with (List.length rows).
        2:{ eapply schedule_rows_of_links_length; eauto. }
        eapply find_schedule_block_start_sound; eauto.
    + eapply check_schedule_with_trailing_zero_paddingb_sound.
      exact Hcheck.
Qed.

Fixpoint check_pinstr_list_tiling_bandb
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before_pis, ws with
  | [], [] => true
  | before_pi :: before_pis', w :: ws' =>
      check_pinstr_tiling_bandb before_pi w &&
      check_pinstr_list_tiling_bandb before_pis' ws'
  | _, _ => false
  end.

Fixpoint check_pinstr_list_tiling_schedule_stripminedb
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before_pis, after_pis, ws with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', w :: ws' =>
      check_pinstr_tiling_schedule_stripminedb env_size before_pi after_pi w &&
      check_pinstr_list_tiling_schedule_stripminedb
        env_size before_pis' after_pis' ws'
  | _, _, _ => false
  end.

Fixpoint infer_pinstr_list_tiling_bands
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band) :=
  match before_pis, ws with
  | [], [] => Some []
  | before_pi :: before_pis', w :: ws' =>
      match infer_pinstr_tiling_band before_pi w,
            infer_pinstr_list_tiling_bands before_pis' ws' with
      | Some band, Some bands' => Some (band :: bands')
      | _, _ => None
      end
  | _, _ => None
  end.

Definition check_pprog_tiling_bandb
    (before: Tiling.PL.t)
    (ws: list statement_tiling_witness) : bool :=
  let '(before_pis, _, _) := before in
  check_pinstr_list_tiling_bandb before_pis ws.

Definition check_pprog_tiling_schedule_stripminedb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
  TilingCheck.ctxt_ty_eqb before_vars after_vars &&
  check_pinstr_list_tiling_schedule_stripminedb
    (List.length before_ctxt) before_pis after_pis ws.

Definition infer_pprog_tiling_bands
    (before: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band) :=
  let '(before_pis, _, _) := before in
  infer_pinstr_list_tiling_bands before_pis ws.

Lemma infer_pinstr_list_tiling_bands_lengths :
  forall before_pis ws bands,
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros ws bands Hinfer.
  - destruct ws, bands; simpl in Hinfer; inversion Hinfer; subst; auto.
  - destruct ws as [|w ws']; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_tiling_band before_pi w) as [band|] eqn:Hband;
      try discriminate.
    destruct (infer_pinstr_list_tiling_bands before_pis' ws') as [bands'|] eqn:Hbands;
      try discriminate.
    inversion Hinfer; subst; clear Hinfer.
    destruct (IH _ _ Hbands) as [Hlen_ws Hlen_bands].
    split; simpl; lia.
Qed.

Lemma infer_pinstr_list_tiling_bands_nth_error :
  forall before_pis ws bands n before_pi w band,
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error bands n = Some band ->
    infer_pinstr_tiling_band before_pi w = Some band.
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros ws bands n before_pi w band Hinfer Hbefore Hw Hband.
  - destruct n; simpl in Hbefore; discriminate.
  - destruct ws as [|w0 ws']; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_tiling_band before_pi0 w0) as [band0|] eqn:Hhd; try discriminate.
    destruct (infer_pinstr_list_tiling_bands before_pis' ws') as [bands'|] eqn:Htl;
      try discriminate.
    inversion Hinfer; subst; clear Hinfer.
    destruct n as [|n']; simpl in *.
    + now inversion Hbefore; inversion Hw; inversion Hband; subst.
    + eapply IH; eauto.
Qed.

Fixpoint rel_list4
    {A B C D: Type}
    (R: A -> B -> C -> D -> Prop)
    (la: list A) (lb: list B) (lc: list C) (ld: list D) : Prop :=
  match la, lb, lc, ld with
  | [], [], [], [] => True
  | a :: la', b :: lb', c :: lc', d :: ld' =>
      R a b c d /\ rel_list4 R la' lb' lc' ld'
  | _, _, _, _ => False
  end.

Definition pinstr_tiling_band_cert
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  pinstr_tiling_band_matches before w band /\
  schedule_matches_with_trailing_zero_padding
    (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Definition pprog_tiling_bands_cert
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  rel_list4
    (pinstr_tiling_band_cert env_size)
    before_pis after_pis ws bands.

Lemma pinstr_tiling_band_cert_after_schedule_length_ge :
  forall env_size before after w band,
    infer_pinstr_tiling_band before w = Some band ->
    pinstr_tiling_band_cert env_size before after w band ->
    (ptb_start band + 2 * ptb_len band <= List.length (Tiling.PL.pi_schedule after))%nat.
Proof.
  intros env_size before after w band Hinfer Hcert.
  destruct Hcert as [Hmatch Hsched].
  pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer) as Hbound.
  pose proof
    (schedule_matches_with_trailing_zero_padding_length_ge
       (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
       (Tiling.PL.pi_schedule after)
       Hsched) as Hlen.
  rewrite stripmine_schedule_after_env_length in Hlen.
  lia.
Qed.

Lemma pprog_tiling_bands_cert_lengths :
  forall env_size before_pis after_pis ws bands,
    pprog_tiling_bands_cert env_size before_pis after_pis ws bands ->
    List.length before_pis = List.length after_pis /\
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws bands Hcert.
  - destruct after_pis, ws, bands; simpl in *; try contradiction; repeat split; reflexivity.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try contradiction.
    destruct ws as [|w ws']; simpl in *; try contradiction.
    destruct bands as [|band bands']; simpl in *; try contradiction.
    destruct Hcert as [_ Hcert'].
    destruct (IH _ _ _ Hcert') as [Hlen_after [Hlen_ws Hlen_bands]].
    repeat split; simpl; lia.
Qed.

Lemma pprog_tiling_bands_cert_nth_error :
  forall env_size before_pis after_pis ws bands
         n before_pi after_pi w band,
    pprog_tiling_bands_cert env_size before_pis after_pis ws bands ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error bands n = Some band ->
    pinstr_tiling_band_cert env_size before_pi after_pi w band.
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros after_pis ws bands n before_pi after_pi w band
           Hcert Hbefore Hafter Hw Hband.
  - destruct n; simpl in Hbefore; discriminate.
  - destruct after_pis as [|after_pi0 after_pis']; [destruct n; simpl in Hafter; discriminate|].
    destruct ws as [|w0 ws']; [destruct n; simpl in Hw; discriminate|].
    destruct bands as [|band0 bands']; [destruct n; simpl in Hband; discriminate|].
    simpl in *.
    destruct n as [|n']; simpl in *.
    + unfold pprog_tiling_bands_cert in Hcert.
      simpl in Hcert.
      inversion Hbefore; inversion Hafter; inversion Hw; inversion Hband; subst.
      exact (proj1 Hcert).
    + destruct Hcert as [_ Hcert'].
      eapply IH; eauto.
Qed.

Lemma inferred_tiling_band_schedule_length_lower :
  forall env_size before after w band,
    infer_pinstr_tiling_band before w = Some band ->
    schedule_matches_with_trailing_zero_padding
      (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
      (Tiling.PL.pi_schedule after) ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma project_band_ip_ext_preserves_old_sched_lt :
  forall band ip1 ip2,
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_band_ip_ext band ip1)
      (project_band_ip_ext band ip2).
Proof.
  intros band ip1 ip2 Hlt.
  unfold Tiling.PL.instr_point_ext_old_sched_lt in *.
  unfold project_band_ip_ext in *.
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma project_cutoff_ip_ext_preserves_old_sched_lt :
  forall cutoff ip1 ip2,
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_cutoff_ip_ext cutoff ip1)
      (project_cutoff_ip_ext cutoff ip2).
Proof.
  intros cutoff ip1 ip2 Hlt.
  unfold Tiling.PL.instr_point_ext_old_sched_lt in *.
  unfold project_cutoff_ip_ext in *.
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma project_band_ip_ext_preserves_new_sched_ge_if_long :
  forall band ip1 ip2,
    (ptb_start band + 2 * ptb_len band <= List.length (Tiling.PL.ip_time_stamp2_ext ip1))%nat ->
    (ptb_start band + 2 * ptb_len band <= List.length (Tiling.PL.ip_time_stamp2_ext ip2))%nat ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_band_ip_ext band ip1)
      (project_band_ip_ext band ip2).
Proof.
  intros band ip1 ip2 Hlen1 Hlen2 Hge.
  unfold Tiling.PL.instr_point_ext_new_sched_ge in *.
  unfold project_band_ip_ext in *.
  destruct ip1 as [nth1 idx1 tf1 acc1 ts11 ts12 ins1 depth1].
  destruct ip2 as [nth2 idx2 tf2 acc2 ts21 ts22 ins2 depth2].
  simpl in *.
  remember (ptb_start band + 2 * ptb_len band)%nat as n eqn:Heqn.
  destruct (lex_compare (firstn n ts12) (firstn n ts22)) eqn:Hcmp.
  - rewrite Heqn in Hcmp. left. exact Hcmp.
  - exfalso.
    assert (Hfull_lt : lex_compare ts12 ts22 = Lt).
    {
      rewrite <- (firstn_skipn n ts12).
      rewrite <- (firstn_skipn n ts22).
      rewrite lex_compare_app by (rewrite !firstn_length; lia).
      rewrite Hcmp.
      reflexivity.
    }
    destruct Hge as [Heq_full | Hgt_full]; congruence.
  - rewrite Heqn in Hcmp. right. exact Hcmp.
Qed.

Lemma project_cutoff_ip_ext_preserves_new_sched_ge_if_long :
  forall cutoff ip1 ip2,
    (cutoff <= List.length (Tiling.PL.ip_time_stamp2_ext ip1))%nat ->
    (cutoff <= List.length (Tiling.PL.ip_time_stamp2_ext ip2))%nat ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_cutoff_ip_ext cutoff ip1)
      (project_cutoff_ip_ext cutoff ip2).
Proof.
  intros cutoff ip1 ip2 Hlen1 Hlen2 Hge.
  unfold Tiling.PL.instr_point_ext_new_sched_ge in *.
  unfold project_cutoff_ip_ext in *.
  destruct ip1 as [nth1 idx1 tf1 acc1 ts11 ts12 ins1 depth1].
  destruct ip2 as [nth2 idx2 tf2 acc2 ts21 ts22 ins2 depth2].
  simpl in *.
  destruct (lex_compare (firstn cutoff ts12) (firstn cutoff ts22)) eqn:Hcmp.
  - left. reflexivity.
  - exfalso.
    assert (Hfull_lt : lex_compare ts12 ts22 = Lt).
    {
      rewrite <- (firstn_skipn cutoff ts12).
      rewrite <- (firstn_skipn cutoff ts22).
      rewrite lex_compare_app by (rewrite !firstn_length; lia).
      rewrite Hcmp.
      reflexivity.
    }
    destruct Hge as [Heq_full | Hgt_full]; congruence.
  - right. reflexivity.
Qed.

Definition pprog_permutable_tiling_bands
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (_bands: list pinstr_tiling_band) : Prop :=
  forall ipl_ext tau1 tau2,
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
      In tau2 ipl_ext ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Definition pprog_tiling_reordering_safe :=
  pprog_permutable_tiling_bands.

Definition uniform_schedule_arity
    (pis: list Tiling.PL.PolyInstr) : Prop :=
  exists len,
    Forall (fun pi => List.length (Tiling.PL.pi_schedule pi) = len) pis.

Lemma uniform_schedule_arity_nth_error :
  forall pis len n pi,
    Forall (fun pi0 => List.length (Tiling.PL.pi_schedule pi0) = len) pis ->
    nth_error pis n = Some pi ->
    List.length (Tiling.PL.pi_schedule pi) = len.
Proof.
  intros pis len n pi Hlen Hnth.
  eapply Forall_forall in Hlen.
  - exact Hlen.
  - eapply nth_error_In; eauto.
Qed.

Definition instr_point_ext_band_prefix_ts
    (band: pinstr_tiling_band)
    (tau: Tiling.PL.InstrPoint_ext) : list Z :=
  firstn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau).

Definition instr_point_ext_band_block_ts
    (band: pinstr_tiling_band)
    (tau: Tiling.PL.InstrPoint_ext) : list Z :=
  firstn (ptb_len band)
    (skipn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau)).

Definition instr_point_ext_same_band_slice
    (band: pinstr_tiling_band)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  instr_point_ext_band_prefix_ts band tau1 =
  instr_point_ext_band_prefix_ts band tau2.

Definition instr_point_ext_band_order_lt
    (band: pinstr_tiling_band)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  lex_compare
    (instr_point_ext_band_block_ts band tau1)
    (instr_point_ext_band_block_ts band tau2) = Lt.

Definition instr_point_ext_tile_block_ts
    (band: pinstr_tiling_band)
    (tau: Tiling.PL.InstrPoint_ext) : list Z :=
  firstn (ptb_len band)
    (skipn (ptb_start band) (Tiling.PL.ip_time_stamp2_ext tau)).

Definition pprog_pluto_permutable_band
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  forall ipl_ext tau1 tau2,
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_order_lt band tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Definition pprog_pluto_permutable_tiling_bands
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  exists band,
    common_tiling_band bands band /\
    pprog_pluto_permutable_band envv before_pis after_pis ws band.

Definition common_tiling_band_recipe_with
    (sizes: list Z)
    (ws: list statement_tiling_witness) : Prop :=
  Forall (fun w => List.map tl_tile_size (stw_links w) = sizes) ws.

Definition common_tiling_band_recipe
    (ws: list statement_tiling_witness) : Prop :=
  exists sizes, common_tiling_band_recipe_with sizes ws.

Definition pprog_pluto_permutable_tiling_bands_strong
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  exists band sizes,
    common_tiling_band bands band /\
    common_tiling_band_recipe_with sizes ws /\
    pprog_pluto_permutable_band envv before_pis after_pis ws band.

Lemma lex_compare_eq_same_length_implies_eq_local_band :
  forall t1 t2,
    lex_compare t1 t2 = Eq ->
    List.length t1 = List.length t2 ->
    t1 = t2.
Proof.
  induction t1 as [|x t1 IH]; intros t2 Hcmp Hlen.
  - destruct t2 as [|y t2].
    + reflexivity.
    + simpl in Hlen. discriminate.
  - destruct t2 as [|y t2].
    + simpl in Hlen. discriminate.
    + simpl in Hcmp.
      destruct (Z.compare x y) eqn:Hxy; try discriminate.
      apply Z.compare_eq_iff in Hxy.
      subst y.
      f_equal.
      eapply IH.
      * exact Hcmp.
      * simpl in Hlen. lia.
Qed.

Lemma stripmined_reversal_implies_prefix_eq_and_band_lt :
  forall prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2,
    List.length prefix1 = List.length prefix2 ->
    List.length band1 = List.length band2 ->
    (band1 = band2 -> tiles1 = tiles2) ->
    lex_compare
      (prefix1 ++ band1 ++ suffix1)
      (prefix2 ++ band2 ++ suffix2) = Lt ->
    lex_compare
      (prefix1 ++ tiles1 ++ band1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band2 ++ suffix2) <> Lt ->
    prefix1 = prefix2 /\ lex_compare band1 band2 = Lt.
Proof.
  intros prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2
         Hprefix_len Hband_len Htiles_eq Hold Hnew.
  destruct (lex_compare prefix1 prefix2) eqn:Hprefix_cmp.
  - assert (prefix1 = prefix2).
    {
      eapply lex_compare_eq_same_length_implies_eq_local_band; eauto.
    }
    subst prefix2.
    destruct (lex_compare band1 band2) eqn:Hband_cmp.
    + assert (band1 = band2).
      {
        eapply lex_compare_eq_same_length_implies_eq_local_band; eauto.
      }
      subst band2.
      assert (tiles1 = tiles2) by auto.
      subst tiles2.
      assert (Hsuffix_lt : lex_compare suffix1 suffix2 = Lt).
      {
        rewrite lex_compare_app in Hold by exact Hprefix_len.
        rewrite lex_compare_reflexive in Hold.
        rewrite lex_compare_app in Hold by exact Hband_len.
        rewrite lex_compare_reflexive in Hold.
        exact Hold.
      }
      rewrite lex_compare_app in Hnew by exact Hprefix_len.
      rewrite lex_compare_reflexive in Hnew.
      rewrite lex_compare_app in Hnew.
      2:{ reflexivity. }
      rewrite lex_compare_reflexive in Hnew.
      rewrite lex_compare_app in Hnew by exact Hband_len.
      rewrite lex_compare_reflexive in Hnew.
      exfalso.
      apply Hnew.
      exact Hsuffix_lt.
    + split; auto.
    + exfalso.
      rewrite lex_compare_app in Hold by exact Hprefix_len.
      rewrite lex_compare_reflexive in Hold.
      rewrite lex_compare_app in Hold by exact Hband_len.
      rewrite Hband_cmp in Hold.
      discriminate.
  - exfalso.
    rewrite lex_compare_app in Hnew by exact Hprefix_len.
    rewrite Hprefix_cmp in Hnew.
    exact (Hnew eq_refl).
  - rewrite lex_compare_app in Hold by exact Hprefix_len.
    rewrite Hprefix_cmp in Hold.
    discriminate.
Qed.

Lemma eval_tile_links_from_common_recipe_affine_product_eq :
  forall w point1 point2 params rows sizes,
    List.length point1 = stw_point_dim w ->
    List.length point2 = stw_point_dim w ->
    schedule_rows_of_links w = Some rows ->
    List.map tl_tile_size (stw_links w) = sizes ->
    well_formed_statement_tiling_witness w ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w) ->
    affine_product rows (params ++ point1) =
    affine_product rows (params ++ point2) ->
    eval_tile_links [] point1 params (stw_links w) =
    eval_tile_links [] point2 params (stw_links w).
Proof.
  intros w point1 point2 params rows sizes
         Hpoint1 Hpoint2 Hrows Hsizes Hwf Hparams Heq_aff.
  rewrite (eval_tile_links_from_schedule_rows
             w point1 params rows sizes
             Hpoint1 Hrows Hsizes Hwf Hparams).
  rewrite (eval_tile_links_from_schedule_rows
             w point2 params rows sizes
             Hpoint2 Hrows Hsizes Hwf Hparams).
  now rewrite Heq_aff.
Qed.

Lemma common_recipe_equal_band_block_implies_equal_tiles :
  forall w1 w2 point1 point2 params rows1 rows2 sizes,
    List.length point1 = stw_point_dim w1 ->
    List.length point2 = stw_point_dim w2 ->
    schedule_rows_of_links w1 = Some rows1 ->
    schedule_rows_of_links w2 = Some rows2 ->
    List.map tl_tile_size (stw_links w1) = sizes ->
    List.map tl_tile_size (stw_links w2) = sizes ->
    well_formed_statement_tiling_witness w1 ->
    well_formed_statement_tiling_witness w2 ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w1) ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w2) ->
    affine_product rows1 (params ++ point1) =
    affine_product rows2 (params ++ point2) ->
    eval_tile_links [] point1 params (stw_links w1) =
    eval_tile_links [] point2 params (stw_links w2).
Proof.
  intros w1 w2 point1 point2 params rows1 rows2 sizes
         Hpoint1 Hpoint2 Hrows1 Hrows2 Hsizes1 Hsizes2
         Hwf1 Hwf2 Hparams1 Hparams2 Heq_aff.
  rewrite (eval_tile_links_from_schedule_rows
             w1 point1 params rows1 sizes
             Hpoint1 Hrows1 Hsizes1 Hwf1 Hparams1).
  rewrite (eval_tile_links_from_schedule_rows
             w2 point2 params rows2 sizes
             Hpoint2 Hrows2 Hsizes2 Hwf2 Hparams2).
  now rewrite Heq_aff.
Qed.

Lemma lex_compare_app_preserves_lt_local :
  forall (xs ys zs1 zs2: list Z),
    List.length xs = List.length ys ->
    lex_compare xs ys = Lt ->
    lex_compare (xs ++ zs1) (ys ++ zs2) = Lt.
Proof.
  intros xs ys zs1 zs2 Hlen Hlt.
  rewrite lex_compare_app by exact Hlen.
  now rewrite Hlt.
Qed.

Lemma lex_compare_app_preserves_not_lt_backward_local :
  forall (xs ys zs1 zs2: list Z),
    List.length xs = List.length ys ->
    lex_compare (xs ++ zs1) (ys ++ zs2) <> Lt ->
    lex_compare xs ys <> Lt.
Proof.
  intros xs ys zs1 zs2 Hlen Hnot Hlt.
  apply Hnot.
  eapply lex_compare_app_preserves_lt_local; eauto.
Qed.

Lemma pprog_pluto_permutable_tiling_bands_common :
  forall envv before_pis after_pis ws bands band,
    pprog_pluto_permutable_tiling_bands envv before_pis after_pis ws bands ->
    infer_common_tiling_band bands = Some band ->
    pprog_pluto_permutable_band envv before_pis after_pis ws band.
Proof.
  intros envv before_pis after_pis ws bands band [band' [Hcommon' Hperm]] Hinfer.
  pose proof (infer_common_tiling_band_sound _ _ Hinfer) as Hcommon.
  assert (band = band').
  {
    destruct bands as [|b0 bands'].
    - unfold infer_common_tiling_band in Hinfer. discriminate.
    - pose proof (common_tiling_band_nth_error _ _ 0 b0 Hcommon eq_refl) as Hb.
      pose proof (common_tiling_band_nth_error _ _ 0 b0 Hcommon' eq_refl) as Hb'.
      congruence.
  }
  subst band'.
  exact Hperm.
Qed.

Lemma pprog_pluto_permutable_tiling_bands_intro :
  forall envv before_pis after_pis ws bands band,
    common_tiling_band bands band ->
    pprog_pluto_permutable_band envv before_pis after_pis ws band ->
    pprog_pluto_permutable_tiling_bands envv before_pis after_pis ws bands.
Proof.
  intros envv before_pis after_pis ws bands band Hcommon Hperm.
  exists band.
  split; assumption.
Qed.

Lemma common_tiling_band_recipe_nth_error :
  forall ws sizes n w,
    common_tiling_band_recipe_with sizes ws ->
    nth_error ws n = Some w ->
    List.map tl_tile_size (stw_links w) = sizes.
Proof.
  intros ws sizes n.
  revert ws.
  induction n as [|n IH]; intros ws w Hforall Hnth.
  - destruct ws as [|w0 ws']; simpl in Hnth; [discriminate|].
    inversion Hforall; subst.
    inversion Hnth; subst.
    reflexivity.
  - destruct ws as [|w0 ws']; simpl in Hnth; [discriminate|].
    inversion Hforall; subst.
    eapply IH; eauto.
Qed.

Lemma pprog_pluto_permutable_tiling_bands_strong_common :
  forall envv before_pis after_pis ws bands band sizes,
    pprog_pluto_permutable_tiling_bands_strong envv before_pis after_pis ws bands ->
    infer_common_tiling_band bands = Some band ->
    common_tiling_band_recipe_with sizes ws ->
    pprog_pluto_permutable_band envv before_pis after_pis ws band.
Proof.
  intros envv before_pis after_pis ws bands band sizes
         [band' [sizes' [Hcommon' [_ Hperm]]]] Hinfer _.
  pose proof (infer_common_tiling_band_sound _ _ Hinfer) as Hcommon.
  assert (band = band').
  {
    destruct bands as [|b0 bands'].
    - unfold infer_common_tiling_band in Hinfer. discriminate.
    - pose proof (common_tiling_band_nth_error _ _ 0 b0 Hcommon eq_refl) as Hb.
      pose proof (common_tiling_band_nth_error _ _ 0 b0 Hcommon' eq_refl) as Hb'.
      congruence.
  }
  subst band'.
  exact Hperm.
Qed.

Lemma retiled_old_band_old_pi_eqdom_retiled_old :
  forall env_size before after w band,
    Tiling.PL.eqdom_pinstr
      (retiled_old_band_old_pi env_size before after w band)
      (Tiling.retiled_old_pinstr env_size before after w).
Proof.
  intros env_size before after w band.
  unfold Tiling.PL.eqdom_pinstr,
         retiled_old_band_old_pi,
         Tiling.retiled_old_pinstr.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma after_stripmined_band_new_pi_eqdom_after :
  forall after band,
    Tiling.PL.eqdom_pinstr
      (after_stripmined_band_new_pi after band)
      after.
Proof.
  intros after band.
  unfold Tiling.PL.eqdom_pinstr, after_stripmined_band_new_pi.
  simpl.
  repeat split; reflexivity.
Qed.

Fixpoint rel_list_eqdom_retiled_old_band_old
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  match before_pis, after_pis, ws, bands with
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', band :: bands' =>
      Tiling.PL.eqdom_pinstr
        (retiled_old_band_old_pi env_size before_pi after_pi w band)
        (Tiling.retiled_old_pinstr env_size before_pi after_pi w) /\
      rel_list_eqdom_retiled_old_band_old env_size before_pis' after_pis' ws' bands'
  | [], [], [], [] => True
  | _, _, _, _ => False
  end.

Fixpoint rel_list_eqdom_after_stripmined_band_new
    (after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : Prop :=
  match after_pis, bands with
  | after_pi :: after_pis', band :: bands' =>
      Tiling.PL.eqdom_pinstr
        (after_stripmined_band_new_pi after_pi band)
        after_pi /\
      rel_list_eqdom_after_stripmined_band_new after_pis' bands'
  | [], [] => True
  | _, _ => False
  end.

Lemma rel_list_eqdom_retiled_old_band_old_sound :
  forall env_size before_pis after_pis ws bands,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    List.length before_pis = List.length bands ->
    rel_list_eqdom_retiled_old_band_old env_size before_pis after_pis ws bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws bands Hlen_after Hlen_ws Hlen_bands.
  - destruct after_pis, ws, bands; simpl in *; try discriminate; exact I.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try discriminate.
    destruct ws as [|w ws']; simpl in *; try discriminate.
    destruct bands as [|band bands']; simpl in *; try discriminate.
    split.
    + apply retiled_old_band_old_pi_eqdom_retiled_old.
    + eapply IH; lia.
Qed.

Lemma rel_list_eqdom_after_stripmined_band_new_sound :
  forall after_pis bands,
    List.length after_pis = List.length bands ->
    rel_list_eqdom_after_stripmined_band_new after_pis bands.
Proof.
  induction after_pis as [|after_pi after_pis' IH];
    intros bands Hlen.
  - destruct bands; simpl in *; try discriminate; exact I.
  - destruct bands as [|band bands']; simpl in *; try discriminate.
    split.
    + apply after_stripmined_band_new_pi_eqdom_after.
    + eapply IH; lia.
Qed.

Lemma retiled_old_band_old_pinstrs_preserve_length :
  forall env_size before_pis after_pis ws bands,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    List.length before_pis = List.length bands ->
    List.length
      (retiled_old_band_old_pinstrs env_size before_pis after_pis ws bands) =
    List.length before_pis.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws bands Hlen_after Hlen_ws Hlen_bands.
  - destruct after_pis, ws, bands; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try discriminate.
    destruct ws as [|w ws']; simpl in *; try discriminate.
    destruct bands as [|band bands']; simpl in *; try discriminate.
    simpl.
    f_equal.
    eapply IH; lia.
Qed.

Lemma after_stripmined_band_new_pinstrs_preserve_length :
  forall after_pis bands,
    List.length after_pis = List.length bands ->
    List.length (after_stripmined_band_new_pinstrs after_pis bands) =
    List.length after_pis.
Proof.
  induction after_pis as [|after_pi after_pis' IH]; intros bands Hlen.
  - destruct bands; simpl in *; try discriminate; reflexivity.
  - destruct bands as [|band bands']; simpl in *; try discriminate.
    simpl.
    f_equal.
    eapply IH; lia.
Qed.

Lemma retiled_old_band_old_pprog_eqdom_retiled_old_pprog :
  forall before after ws bands,
    let '(before_pis, _, _) := before in
    let '(after_pis, _, _) := after in
    List.length before_pis = List.length after_pis ->
    infer_pprog_tiling_bands before ws = Some bands ->
    Tiling.PL.eqdom_pprog
      (retiled_old_band_old_pprog before after ws bands)
      (let '(before_pis, before_ctxt, before_vars) := before in
       let '(after_pis, _, _) := after in
       (Tiling.retiled_old_pinstrs
          (List.length before_ctxt) before_pis after_pis ws,
        before_ctxt,
        before_vars)).
Proof.
  intros before after ws bands.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl.
  intros Hlen_before_after Hinfer.
  unfold infer_pprog_tiling_bands in Hinfer.
  simpl in *.
  pose proof
    (infer_pinstr_list_tiling_bands_lengths
       before_pis ws bands Hinfer)
    as [Hlen_ws Hlen_bands].
  unfold Tiling.PL.eqdom_pprog.
  intros pil1 pil2 varctxt1 varctxt2 vars1 vars2 Hpp1 Hpp2.
  inversion Hpp1; inversion Hpp2; subst.
  repeat match goal with |- _ /\ _ => split end.
  - reflexivity.
  - reflexivity.
  - rewrite retiled_old_band_old_pinstrs_preserve_length
      with (after_pis := after_pis) (ws := ws) (bands := bands); eauto.
    rewrite Tiling.retiled_old_pinstrs_preserve_length
      with (after_pis := after_pis) (ws := ws); eauto.
  - clear Hpp1 Hpp2.
    induction before_pis as [|before_pi before_pis' IH]
      in after_pis, ws, bands, Hlen_before_after, Hlen_ws, Hlen_bands |- *.
    + destruct after_pis, ws, bands; simpl in *; try discriminate; exact I.
    + destruct after_pis as [|after_pi after_pis']; simpl in *; try discriminate.
      destruct ws as [|w ws']; simpl in *; try discriminate.
      destruct bands as [|band bands']; simpl in *; try discriminate.
      split.
      * apply retiled_old_band_old_pi_eqdom_retiled_old.
      * eapply IH; lia.
Qed.

Lemma after_stripmined_band_new_pprog_eqdom_after :
  forall before after bands,
    let '(after_pis, _, _) := after in
    List.length after_pis = List.length bands ->
    Tiling.PL.eqdom_pprog
      (after_stripmined_band_new_pprog before after bands)
      (let '(after_pis, _, _) := after in
       let '(_, before_ctxt, before_vars) := before in
       (after_pis, before_ctxt, before_vars)).
Proof.
  intros before after bands.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl.
  intros Hlen_bands.
  unfold Tiling.PL.eqdom_pprog.
  intros pil1 pil2 varctxt1 varctxt2 vars1 vars2 Hpp1 Hpp2.
  inversion Hpp1; inversion Hpp2; subst.
  repeat match goal with |- _ /\ _ => split end.
  - reflexivity.
  - reflexivity.
  - eapply after_stripmined_band_new_pinstrs_preserve_length; eauto.
  - clear Hpp1 Hpp2.
    induction pil2 as [|after_pi after_pis' IH] in bands, Hlen_bands |- *.
    + destruct bands; simpl in *; try discriminate; exact I.
    + destruct bands as [|band bands']; simpl in *; try discriminate.
      split.
      * apply after_stripmined_band_new_pi_eqdom_after.
      * eapply IH; lia.
Qed.

Lemma check_pinstr_list_tiling_schedule_stripminedb_sound :
  forall env_size before_pis after_pis ws,
    check_pinstr_list_tiling_schedule_stripminedb
      env_size before_pis after_pis ws = true ->
    exists bands,
      pprog_tiling_bands_cert env_size before_pis after_pis ws bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hcheck;
    destruct after_pis as [|after_pi after_pis'];
    destruct ws as [|w ws'];
    simpl in *; try discriminate.
  - exists [].
    reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    destruct (check_pinstr_tiling_schedule_stripminedb_sound
                env_size before_pi after_pi w Hhd)
      as [band [Hinfer_hd [Hband_match Hband_sched]]].
    destruct (IH _ _ Htl) as [bands' Hcert_tl].
    exists (band :: bands').
    simpl.
    split.
    + exact (conj Hband_match Hband_sched).
    + exact Hcert_tl.
Qed.

Lemma check_pinstr_list_tiling_schedule_stripminedb_sound_infer :
  forall env_size before_pis after_pis ws,
    check_pinstr_list_tiling_schedule_stripminedb
      env_size before_pis after_pis ws = true ->
    exists bands,
      infer_pinstr_list_tiling_bands before_pis ws = Some bands /\
      pprog_tiling_bands_cert env_size before_pis after_pis ws bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hcheck;
    destruct after_pis as [|after_pi after_pis'];
    destruct ws as [|w ws'];
    simpl in *; try discriminate.
  - exists [].
    split; reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    destruct (check_pinstr_tiling_schedule_stripminedb_sound
                env_size before_pi after_pi w Hhd)
      as [band [Hinfer_hd [Hband_match Hband_sched]]].
    destruct (IH _ _ Htl) as [bands' [Hinfer_tl Hcert_tl]].
    exists (band :: bands').
    split.
    + simpl. rewrite Hinfer_hd, Hinfer_tl. reflexivity.
    + simpl. split.
      * exact (conj Hband_match Hband_sched).
      * exact Hcert_tl.
Qed.

Lemma check_pprog_tiling_schedule_stripminedb_ctxt_sound :
  forall before after ws,
    check_pprog_tiling_schedule_stripminedb before after ws = true ->
    let '(_, before_ctxt, before_vars) := before in
    let '(_, after_ctxt, after_vars) := after in
    before_ctxt = after_ctxt /\ before_vars = after_vars.
Proof.
  intros before after ws Hcheck.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  unfold check_pprog_tiling_schedule_stripminedb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hctxt Hvars] _].
  split.
  - apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
Qed.

Lemma check_pprog_tiling_schedule_stripminedb_sound_flat :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    check_pprog_tiling_schedule_stripminedb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = true ->
    exists bands,
      infer_pinstr_list_tiling_bands before_pis ws = Some bands /\
      pprog_tiling_bands_cert
        (List.length before_ctxt) before_pis after_pis ws bands /\
      before_ctxt = after_ctxt /\ before_vars = after_vars.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hcheck.
  simpl in *.
  pose proof
    (check_pprog_tiling_schedule_stripminedb_ctxt_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hcheck)
    as [Hctxt Hvars].
  unfold check_pprog_tiling_schedule_stripminedb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[_ _] Hsched].
  destruct
    (check_pinstr_list_tiling_schedule_stripminedb_sound_infer
       (List.length before_ctxt) before_pis after_pis ws Hsched)
    as [bands [Hinfer Hcert]].
  exists bands.
  repeat split; auto.
Qed.

Lemma tiling_rel_pinstr_structure_source_after_matches :
  forall env_size before after w,
    Tiling.tiling_rel_pinstr_structure_source
      env_size before after (Tiling.compiled_pinstr_tiling_witness w) ->
    stw_point_dim w = Tiling.PL.pi_depth before ->
    Tiling.after_matches_tiling_witness after w.
Proof.
  intros env_size before after w Hrel Hpoint_dim.
  unfold Tiling.after_matches_tiling_witness.
  unfold Tiling.tiling_rel_pinstr_structure_source in Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [Hdepth [Hpw _]]].
  assert (Hsum :
    (List.length (stw_links w) + stw_point_dim w = Tiling.PL.pi_depth after)%nat).
  {
    cbn [Tiling.compiled_pinstr_tiling_witness Tiling.ptw_added_dims Tiling.ptw_statement_witness] in Hdepth.
    rewrite <- Hpoint_dim in Hdepth.
    lia.
  }
  split.
  - exact Hpw.
  - rewrite Hpw.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
    simpl.
    rewrite Nat.add_comm.
    exact Hsum.
Qed.

Lemma tiling_rel_pinstr_list_source_after_matches :
  forall env_size before_pis after_pis ws,
    Tiling.tiling_rel_pinstr_list_source
      env_size before_pis after_pis (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall2 (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hrel Hdepths;
    destruct after_pis as [|after_pi after_pis'];
    destruct ws as [|w ws'];
    simpl in *; try contradiction; constructor.
  - destruct Hrel as [Hhd _].
    inversion Hdepths; subst.
    eapply tiling_rel_pinstr_structure_source_after_matches; eauto.
  - destruct Hrel as [_ Htl].
    inversion Hdepths; subst.
    eapply IH; eauto.
Qed.

Lemma tiling_rel_pprog_structure_source_after_matches :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall2 (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hprog Hdepths.
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [_ [_ Hrel]].
  eapply tiling_rel_pinstr_list_source_after_matches; eauto.
Qed.

Lemma flatten_instrs_ext_from_after_member_nth_data_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_ext tau,
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau ipl_ext ->
    exists before_pi after_pi w,
      List.nth_error before_pis (Tiling.PL.ip_nth_ext tau) = Some before_pi /\
      List.nth_error after_pis (Tiling.PL.ip_nth_ext tau) = Some after_pi /\
      List.nth_error ws (Tiling.PL.ip_nth_ext tau) = Some w /\
      Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv) w /\
      Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
      stw_point_dim w = Tiling.PL.pi_depth before_pi /\
      firstn (List.length envv) (Tiling.PL.ip_index_ext tau) = envv /\
      Tiling.PL.belongs_to_ext
        tau
        (Tiling.compose_tiling_pinstr_ext
           (List.length envv) before_pi after_pi w) /\
      List.length (Tiling.PL.ip_index_ext tau) =
        (List.length envv + Tiling.PL.pi_depth after_pi)%nat.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_ext tau
         Hprog Hwf_ws Hsizes_ws Hdepths
         Hflat Hin_tau.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_lengths
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hprog)
    as [Hlen_after Hlen_ws_map].
  rewrite List.map_length in Hlen_ws_map.
  assert (Hcomp_len :
    List.length
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws) =
    List.length before_pis).
  {
    eapply Tiling.compose_tiling_pinstrs_ext_from_after_preserve_length.
    - exact Hlen_after.
    - rewrite Hlen_after.
      exact Hlen_ws_map.
  }
  destruct Hflat as [_ [Hmem _]].
  destruct (proj1 (Hmem tau) Hin_tau)
    as [pi_ext [Hnth_ext [Hpref_tau [Hbel_tau Hlen_tau]]]].
  assert (Hn_lt_comp :
    (Tiling.PL.ip_nth_ext tau <
     List.length
       (Tiling.compose_tiling_pinstrs_ext_from_after
          (List.length envv) before_pis after_pis ws))%nat).
  {
    eapply Tiling.PL.nth_error_Some'.
    exact Hnth_ext.
  }
  assert (Hn_lt_before :
    (Tiling.PL.ip_nth_ext tau < List.length before_pis)%nat).
  {
    rewrite <- Hcomp_len.
    exact Hn_lt_comp.
  }
  destruct (List.nth_error before_pis (Tiling.PL.ip_nth_ext tau)) eqn:Hbefore_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hbefore_nth.
    lia.
  }
  destruct (List.nth_error after_pis (Tiling.PL.ip_nth_ext tau)) eqn:Hafter_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hafter_nth.
    rewrite <- Hlen_after in Hafter_nth.
    lia.
  }
  destruct (List.nth_error ws (Tiling.PL.ip_nth_ext tau)) eqn:Hw_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hw_nth.
    rewrite <- Hlen_ws_map in Hw_nth.
    rewrite <- Hlen_after in Hw_nth.
    lia.
  }
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws (Tiling.PL.ip_nth_ext tau)
       p p0 s Hbefore_nth Hafter_nth Hw_nth)
    as Hnth_expected.
  rewrite Hnth_ext in Hnth_expected.
  inversion Hnth_expected; subst pi_ext.
  pose proof
    (Tiling.Forall_nth_error _ _ _ _ _ Hwf_ws Hw_nth)
    as Hwf_w.
  pose proof
    (Tiling.Forall_nth_error _ _ _ _ _ Hsizes_ws Hw_nth)
    as Hsizes_w.
  pose proof
    (Tiling.Forall2_nth_error
       _ _ _
       before_pis ws (Tiling.PL.ip_nth_ext tau) p s
       Hdepths Hbefore_nth Hw_nth)
    as Hpoint_depth.
  exists p, p0, s.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  destruct Hwf_w as [Hwf_core Hparams_w].
  split.
  - split; [exact Hwf_core|exact Hparams_w].
  - split; [exact Hsizes_w|].
  split; [exact Hpoint_depth|].
  split; [exact Hpref_tau|].
  split; [exact Hbel_tau|].
  cbn [Tiling.compose_tiling_pinstr_ext] in Hlen_tau.
  exact Hlen_tau.
Qed.

Lemma tiling_schedule_stripmined_validate_correct_with_bands :
  forall before after ws bands st1 st2,
    TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
    pprog_tiling_bands_cert
      (let '(_, before_ctxt, _) := before in List.length before_ctxt)
      (let '(before_pis, _, _) := before in before_pis)
      (let '(after_pis, _, _) := after in after_pis)
      ws bands ->
    (let '(before_pis, _, _) := before in
     let '(after_pis, _, _) := after in
     forall envv,
       pprog_permutable_tiling_bands envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics after st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws bands st1 st2 Hstruct Hbands Hperm Hsem_after.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl in *.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hstruct)
    as [Hprog [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  subst after_ctxt after_vars.
  assert (Hprog_full :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    repeat split; auto.
  }
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length before_ctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  {
    rewrite List.map_length in Hlen_ws_map.
    exact Hlen_ws_map.
  }
  inversion Hsem_after as
    [pprog pis varctxt vars envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  pose proof Hpprog as Hpprog_eq.
  inversion Hpprog_eq; subst pis varctxt vars; clear Hpprog_eq Hpprog.
  pose proof (Instr.init_env_samelen before_ctxt envv st1 Hinit) as Hlen_env.
  assert (Hwf_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf.
  }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws).
    - exact Hprog_full.
    - exact Hdepths.
  }
  assert (Hlayer :
    Tiling.tiling_retiled_old_to_before_poly_layer
      envv before_pis after_pis ws before_ctxt before_vars).
  {
    intros stx stmid Hretiled.
    eapply Tiling.tiling_retiled_old_to_before_poly_correct_with_env_len_source.
    - exact Hprog_full.
    - symmetry. exact Hlen_env.
    - exact Hbefore_ids.
    - exact Hwf_env.
    - exact Hsizes.
    - exact Hdepths.
    - exact Hretiled.
  }
  destruct
    (Tiling.tiling_after_to_before_poly_correct_via_retiled_old
       envv before_pis after_pis ws before_ctxt before_vars st1 st2
       Hlen_after Hlen_ws Hwits
       (Hperm envv) Hlayer Halias Hpoly)
    as [st2' [Hpoly_before Heq]].
  exists st2'.
  split.
  - refine
      (Tiling.PL.PIPSemaIntro
         (before_pis, before_ctxt, before_vars)
         before_pis before_ctxt before_vars envv st1 st2'
         _ _ _ _ _).
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hpoly_before.
  - exact Heq.
Qed.

Definition checked_tiling_schedule_stripmined_validate
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  pure
    (TilingCheck.check_pprog_tiling_sourceb before after ws &&
     check_pprog_tiling_schedule_stripminedb before after ws).

Definition checked_tiling_schedule_stripmined_validate_outer
    (before after: PolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp bool :=
  checked_tiling_schedule_stripmined_validate
    (Base.outer_to_tiling_pprog before)
    (Base.outer_to_tiling_pprog after)
    ws.

Definition checked_tiling_schedule_stripmined_validate_poly :=
  checked_tiling_schedule_stripmined_validate_outer.

Fixpoint check_pinstr_list_schedule_len_ge
    (pis: list Tiling.PL.PolyInstr)
    (cutoff: nat) : bool :=
  match pis with
  | [] => true
  | pi :: pis' =>
      Nat.leb cutoff (List.length (Tiling.PL.pi_schedule pi)) &&
      check_pinstr_list_schedule_len_ge pis' cutoff
  end.

Lemma check_pinstr_list_schedule_len_ge_sound :
  forall pis cutoff,
    check_pinstr_list_schedule_len_ge pis cutoff = true ->
    Forall (fun pi => (cutoff <= List.length (Tiling.PL.pi_schedule pi))%nat) pis.
Proof.
  induction pis as [|pi pis' IH]; intros cutoff Hcheck; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    constructor.
    + apply Nat.leb_le. exact Hhd.
    + eapply IH. exact Htl.
Qed.

Definition check_pinstr_list_permutable_tiling_band_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (cutoff: nat) : imp bool :=
  let pil_ext :=
    project_pinstrs_ext_with_cutoff
      (Tiling.compose_tiling_pinstrs_ext_from_after
         env_size before_pis after_pis ws)
      cutoff in
  let valid_access := BandAffine.check_valid_access pil_ext in
  BIND res <- BandAffine.validate_instr_list (rev pil_ext) env_size -;
  pure (res && valid_access).

Definition check_pprog_permutable_tiling_bands_via_validate_tiling
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars then
    if Nat.eqb (List.length bands) (List.length before_pis) then
      let cutoff := max_pinstr_schedule_len after_pis in
      if check_pinstr_list_schedule_len_ge after_pis cutoff then
        check_pinstr_list_permutable_tiling_band_via_validate_tiling
          (List.length before_ctxt) before_pis after_pis ws cutoff
      else pure false
    else pure false
  else pure false.

Lemma check_pprog_permutable_tiling_bands_via_validate_tiling_true_inv :
  forall before after ws bands,
    mayReturn
      (check_pprog_permutable_tiling_bands_via_validate_tiling
         before after ws bands)
      true ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma ctxt_ty_eqb_refl_local :
  forall before_vars,
    TilingCheck.ctxt_ty_eqb before_vars before_vars = true.
Proof.
  induction before_vars as [|(v, ty) before_vars IH]; simpl.
  - reflexivity.
  - repeat rewrite andb_true_iff.
    split.
    + split.
      * apply Instr.ident_eqb_eq. reflexivity.
      * apply Tiling.PL.Ty.eqb_eq. reflexivity.
    + exact IH.
Qed.

Lemma check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    mayReturn
      (check_pprog_permutable_tiling_bands_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands)
      true ->
    pprog_permutable_tiling_bands envv before_pis after_pis ws bands.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer_bands Hbands
         Hwf_before Hwf_after Hdepths Hwits Hcheck.
  unfold check_pprog_permutable_tiling_bands_via_validate_tiling in Hcheck.
  assert (Hctxt_refl : TilingCheck.ctxt_eqb before_ctxt before_ctxt = true).
  {
    apply (proj2 (TilingCheck.ctxt_eqb_eq before_ctxt before_ctxt)).
    reflexivity.
  }
  assert (Hvars_refl :
    TilingCheck.ctxt_ty_eqb before_vars before_vars = true).
  {
    apply ctxt_ty_eqb_refl_local.
  }
  rewrite Hctxt_refl in Hcheck.
  rewrite Hvars_refl in Hcheck.
  destruct (infer_pinstr_list_tiling_bands_lengths _ _ _ Hinfer_bands)
    as [_ Hlen_bands].
  rewrite Hlen_bands in Hcheck.
  rewrite Nat.eqb_refl in Hcheck.
  set (cutoff := max_pinstr_schedule_len after_pis) in *.
  destruct (check_pinstr_list_schedule_len_ge after_pis cutoff) eqn:Hlen_check.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  pose proof (check_pinstr_list_schedule_len_ge_sound _ _ Hlen_check)
    as Hafter_long.
  simpl in Hcheck.
  unfold check_pinstr_list_permutable_tiling_band_via_validate_tiling in Hcheck.
  bind_imp_destruct Hcheck res Hres.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hres_true Hvalid_true].
  unfold pprog_permutable_tiling_bands.
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  assert (Hflat_ctxt :
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)
      ipl_ext).
  {
    rewrite Hlen_env.
    exact Hflat.
  }
  set (pil_ext :=
         Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length before_ctxt) before_pis after_pis ws).
  set (pil_proj := project_pinstrs_ext_with_cutoff pil_ext cutoff).
  assert (Hflat_proj :
    Tiling.PL.flatten_instrs_ext
      envv pil_proj
      (List.map (project_cutoff_ip_ext cutoff) ipl_ext)).
  {
    subst pil_proj pil_ext.
    eapply flatten_instrs_ext_project_cutoff.
    exact Hflat_ctxt.
  }
  assert (Hwf_proj :
    Forall (Tiling.PL.wf_pinstr_ext_tiling before_ctxt) pil_proj).
  {
    subst pil_proj pil_ext.
    eapply project_pinstrs_ext_with_cutoff_wf_tiling.
    - exact Hwf_before.
    - exact Hwf_after.
    - exact Hdepths.
    - exact Hwits.
  }
  assert (Hvalid_proj :
    Forall
      (fun pi_ext =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi_ext)
           (Tiling.PL.pi_raccess_ext pi_ext)
           (Tiling.PL.pi_instr_ext pi_ext))
      pil_proj).
  {
    subst pil_proj pil_ext.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  assert (Hin1_proj :
    In (project_cutoff_ip_ext cutoff tau1)
       (List.map (project_cutoff_ip_ext cutoff) ipl_ext)).
  {
    apply in_map.
    exact Hin1.
  }
  assert (Hin2_proj :
    In (project_cutoff_ip_ext cutoff tau2)
       (List.map (project_cutoff_ip_ext cutoff) ipl_ext)).
  {
    apply in_map.
    exact Hin2.
  }
  assert (Hold_proj :
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_cutoff_ip_ext cutoff tau1)
      (project_cutoff_ip_ext cutoff tau2)).
  {
    eapply project_cutoff_ip_ext_preserves_old_sched_lt.
    exact Hold.
  }
  assert (Hlen_after :
    List.length before_pis = List.length after_pis).
  {
    destruct (pprog_tiling_bands_cert_lengths _ _ _ _ _ Hbands)
      as [Hlen_after' _].
    exact Hlen_after'.
  }
  assert (Hlen_ws :
    List.length before_pis = List.length ws).
  {
    destruct (pprog_tiling_bands_cert_lengths _ _ _ _ _ Hbands)
      as [_ [Hlen_ws' _]].
    exact Hlen_ws'.
  }
  assert (Hlen_comp :
    List.length pil_ext = List.length before_pis).
  {
    subst pil_ext.
    eapply Tiling.compose_tiling_pinstrs_ext_from_after_preserve_length.
    - exact Hlen_after.
    - exact Hlen_ws.
  }
  destruct Hflat_ctxt as [_ [Hmem _]].
  destruct (proj1 (Hmem tau1) Hin1)
    as [pi_ext1 [Hnth_ext1 [_ [Hbel1 _]]]].
  destruct (proj1 (Hmem tau2) Hin2)
    as [pi_ext2 [Hnth_ext2 [_ [Hbel2 _]]]].
  assert (Hnth1_lt : (Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
  {
    rewrite <- Hlen_comp.
    eapply Tiling.PL.nth_error_Some'.
    exact Hnth_ext1.
  }
  assert (Hnth2_lt : (Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
  {
    rewrite <- Hlen_comp.
    eapply Tiling.PL.nth_error_Some'.
    exact Hnth_ext2.
  }
  destruct (List.nth_error before_pis (Tiling.PL.ip_nth_ext tau1))
    as [before_pi1|] eqn:Hbefore1.
  2:{ exfalso. apply List.nth_error_None in Hbefore1. lia. }
  destruct (List.nth_error after_pis (Tiling.PL.ip_nth_ext tau1))
    as [after_pi1|] eqn:Hafter1.
  2:{ exfalso. apply List.nth_error_None in Hafter1. rewrite <- Hlen_after in Hafter1. lia. }
  destruct (List.nth_error ws (Tiling.PL.ip_nth_ext tau1))
    as [w1|] eqn:Hw1.
  2:{ exfalso. apply List.nth_error_None in Hw1. rewrite <- Hlen_ws in Hw1. lia. }
  destruct (List.nth_error before_pis (Tiling.PL.ip_nth_ext tau2))
    as [before_pi2|] eqn:Hbefore2.
  2:{ exfalso. apply List.nth_error_None in Hbefore2. lia. }
  destruct (List.nth_error after_pis (Tiling.PL.ip_nth_ext tau2))
    as [after_pi2|] eqn:Hafter2.
  2:{ exfalso. apply List.nth_error_None in Hafter2. rewrite <- Hlen_after in Hafter2. lia. }
  destruct (List.nth_error ws (Tiling.PL.ip_nth_ext tau2))
    as [w2|] eqn:Hw2.
  2:{ exfalso. apply List.nth_error_None in Hw2. rewrite <- Hlen_ws in Hw2. lia. }
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length before_ctxt) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 w1
       Hbefore1 Hafter1 Hw1) as Hnth_expected1.
  rewrite Hnth_ext1 in Hnth_expected1.
  inversion Hnth_expected1; subst pi_ext1; clear Hnth_expected1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length before_ctxt) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 w2
       Hbefore2 Hafter2 Hw2) as Hnth_expected2.
  rewrite Hnth_ext2 in Hnth_expected2.
  inversion Hnth_expected2; subst pi_ext2; clear Hnth_expected2.
  assert (Htau1_ts2_len :
    List.length (Tiling.PL.ip_time_stamp2_ext tau1) =
    List.length (Tiling.PL.pi_schedule after_pi1)).
  {
    pose proof (belongs_to_ext_ts2_length _ _ Hbel1) as Hlen_ts2.
    simpl in Hlen_ts2.
    exact Hlen_ts2.
  }
  assert (Htau2_ts2_len :
    List.length (Tiling.PL.ip_time_stamp2_ext tau2) =
    List.length (Tiling.PL.pi_schedule after_pi2)).
  {
    pose proof (belongs_to_ext_ts2_length _ _ Hbel2) as Hlen_ts2.
    simpl in Hlen_ts2.
    exact Hlen_ts2.
  }
  assert (Hlen_new1 :
    (cutoff <= List.length (Tiling.PL.ip_time_stamp2_ext tau1))%nat).
  {
    rewrite Htau1_ts2_len.
    pose proof
      (Tiling.Forall_nth_error
         _
         (fun pi => (cutoff <= List.length (Tiling.PL.pi_schedule pi))%nat)
         after_pis
         (Tiling.PL.ip_nth_ext tau1)
         after_pi1
         Hafter_long Hafter1) as Hafter1_long.
    exact Hafter1_long.
  }
  assert (Hlen_new2 :
    (cutoff <= List.length (Tiling.PL.ip_time_stamp2_ext tau2))%nat).
  {
    rewrite Htau2_ts2_len.
    pose proof
      (Tiling.Forall_nth_error
         _
         (fun pi => (cutoff <= List.length (Tiling.PL.pi_schedule pi))%nat)
         after_pis
         (Tiling.PL.ip_nth_ext tau2)
         after_pi2
         Hafter_long Hafter2) as Hafter2_long.
    exact Hafter2_long.
  }
  assert (Hnew_proj :
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_cutoff_ip_ext cutoff tau1)
      (project_cutoff_ip_ext cutoff tau2)).
  {
    eapply project_cutoff_ip_ext_preserves_new_sched_ge_if_long.
    - exact Hlen_new1.
    - exact Hlen_new2.
    - exact Hnew.
  }
  assert (Hperm_proj :
    Tiling.PL.Permutable_ext
      (project_cutoff_ip_ext cutoff tau1)
      (project_cutoff_ip_ext cutoff tau2)).
  {
    eapply
      (BandAffine.validate_pinstrs_ext_implies_permutability
         pil_proj before_ctxt envv
         (List.map (project_cutoff_ip_ext cutoff) ipl_ext)
         res Hres).
    - exact Hres_true.
    - exact Hwf_proj.
    - exact Hlen_env.
    - exact Hflat_proj.
    - exact Hvalid_proj.
    - exact Hin1_proj.
    - exact Hin2_proj.
    - exact Hold_proj.
    - exact Hnew_proj.
  }
  eapply project_cutoff_ip_ext_permutable_back.
  exact Hperm_proj.
Qed.

Lemma checked_tiling_schedule_stripmined_and_band_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws bands st1 st2,
    mayReturn
      (checked_tiling_schedule_stripmined_validate
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_permutable_tiling_bands_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands st1 st2
         Hcheck_shape Hinfer_bands Hwfbefore_pis Hwfafter_pis
         Hcheck_perm Hsem_after.
  unfold checked_tiling_schedule_stripmined_validate in Hcheck_shape.
  apply mayReturn_pure in Hcheck_shape.
  apply andb_true_iff in Hcheck_shape.
  destruct Hcheck_shape as [Hstruct Hsched].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hstruct)
    as [Hprog [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  assert (Hprog_full :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    repeat split; auto.
  }
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length before_ctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  {
    rewrite List.map_length in Hlen_ws_map.
    exact Hlen_ws_map.
  }
  destruct
    (check_pprog_tiling_schedule_stripminedb_sound_flat
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hsched)
    as [bands' [Hinfer' [Hbands [_ _]]]].
  rewrite Hinfer_bands in Hinfer'.
  inversion Hinfer'; subst bands'; clear Hinfer'.
  inversion Hsem_after as
    [pprog pis varctxt vars envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  pose proof Hpprog as Hpprog_eq.
  inversion Hpprog_eq; subst pis varctxt vars; clear Hpprog_eq Hpprog.
  pose proof (Instr.init_env_samelen before_ctxt envv st1 Hinit) as Hlen_env.
  assert (Hwf_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf.
  }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws).
    - exact Hprog_full.
    - exact Hdepths.
  }
  assert (Hlayer :
    Tiling.tiling_retiled_old_to_before_poly_layer
      envv before_pis after_pis ws before_ctxt before_vars).
  {
    intros stx stmid Hretiled.
    eapply Tiling.tiling_retiled_old_to_before_poly_correct_with_env_len_source.
    - exact Hprog_full.
    - symmetry. exact Hlen_env.
    - exact Hbefore_ids.
    - exact Hwf_env.
    - exact Hsizes.
    - exact Hdepths.
    - exact Hretiled.
  }
  assert (Hperm_envv :
    pprog_permutable_tiling_bands envv before_pis after_pis ws bands).
  {
    eapply
      (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv).
    - exact Hlen_env.
    - exact Hinfer_bands.
    - exact Hbands.
    - exact Hwfbefore_pis.
    - exact Hwfafter_pis.
    - exact Hdepths.
    - exact Hwits.
    - exact Hcheck_perm.
  }
  destruct
    (Tiling.tiling_after_to_before_poly_correct_via_retiled_old
       envv before_pis after_pis ws before_ctxt before_vars st1 st2
       Hlen_after Hlen_ws Hwits Hperm_envv Hlayer Halias Hpoly)
    as [st2' [Hbefore Heq_before]].
  exists st2'.
  split.
  - refine
      (Tiling.PL.PIPSemaIntro
         (before_pis, before_ctxt, before_vars)
         before_pis before_ctxt before_vars envv st1 st2'
         _ _ _ _ _).
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hbefore.
  - exact Heq_before.
Qed.

Lemma checked_tiling_schedule_stripmined_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    mayReturn
      (checked_tiling_schedule_stripmined_validate
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    (forall bands envv,
       infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
       pprog_tiling_bands_cert
         (List.length before_ctxt) before_pis after_pis ws bands ->
       pprog_permutable_tiling_bands envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hcheck Hperm Hsem_after.
  unfold checked_tiling_schedule_stripmined_validate in Hcheck.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hstruct Hsched].
  destruct
    (check_pprog_tiling_schedule_stripminedb_sound_flat
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hsched)
    as [bands [Hinfer [Hbands [_ _]]]].
  eapply
    (tiling_schedule_stripmined_validate_correct_with_bands
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws bands st1 st2).
  - exact Hstruct.
  - exact Hbands.
  - intros envv. eapply Hperm; eauto.
  - exact Hsem_after.
Qed.

Lemma pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_if_local_bridge :
  forall envv before_pis after_pis ws bands,
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands ->
    (forall ipl_ext tau1 tau2 band sizes,
       common_tiling_band bands band ->
       common_tiling_band_recipe_with sizes ws ->
       Tiling.PL.flatten_instrs_ext
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length envv) before_pis after_pis ws)
         ipl_ext ->
       In tau1 ipl_ext ->
       In tau2 ipl_ext ->
       Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
       Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
       instr_point_ext_same_band_slice band tau1 tau2 /\
       instr_point_ext_band_order_lt band tau1 tau2) ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros envv before_pis after_pis ws bands
         Hpluto Hlocal.
  destruct Hpluto as [band [sizes [Hcommon [Hrecipe Hperm]]]].
  unfold pprog_tiling_reordering_safe, pprog_permutable_tiling_bands.
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (Hlocal ipl_ext tau1 tau2 band sizes
              Hcommon Hrecipe Hflat Hin1 Hin2 Hold Hnew)
    as [Hslice Hbandlt].
  eapply Hperm; eauto.
Qed.

Lemma checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    mayReturn
      (checked_tiling_schedule_stripmined_validate
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    (forall bands envv,
       infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
       pprog_tiling_bands_cert
         (List.length before_ctxt) before_pis after_pis ws bands ->
       pprog_pluto_permutable_tiling_bands_strong
         envv before_pis after_pis ws bands) ->
    (forall bands envv,
       infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
       pprog_tiling_bands_cert
         (List.length before_ctxt) before_pis after_pis ws bands ->
       pprog_pluto_permutable_tiling_bands_strong
         envv before_pis after_pis ws bands ->
       mayReturn
         (check_pprog_permutable_tiling_bands_via_validate_tiling
            (before_pis, before_ctxt, before_vars)
            (after_pis, before_ctxt, before_vars)
            ws bands)
         true) ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hcheck Hwfbefore_pis Hwfafter_pis
         Hpluto Hcheck_perm Hsem_after.
  unfold checked_tiling_schedule_stripmined_validate in Hcheck.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hstruct Hsched].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hstruct)
    as [Hprog [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  assert (Hprog_full :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    repeat split; auto.
  }
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length before_ctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  {
    rewrite List.map_length in Hlen_ws_map.
    exact Hlen_ws_map.
  }
  destruct
    (check_pprog_tiling_schedule_stripminedb_sound_flat
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hsched)
    as [bands' [Hinfer' [Hbands' [_ _]]]].
  pose proof Hinfer' as Hinfer_bands.
  inversion Hsem_after as
    [pprog pis varctxt vars envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  pose proof Hpprog as Hpprog_eq.
  inversion Hpprog_eq; subst pis varctxt vars; clear Hpprog_eq Hpprog.
  pose proof (Instr.init_env_samelen before_ctxt envv st1 Hinit) as Hlen_env.
  assert (Hwf_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf.
  }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws).
    - exact Hprog_full.
    - exact Hdepths.
  }
  assert (Hlayer :
    Tiling.tiling_retiled_old_to_before_poly_layer
      envv before_pis after_pis ws before_ctxt before_vars).
  {
    intros stx stmid Hretiled.
    eapply Tiling.tiling_retiled_old_to_before_poly_correct_with_env_len_source.
    - exact Hprog_full.
    - symmetry. exact Hlen_env.
    - exact Hbefore_ids.
    - exact Hwf_env.
    - exact Hsizes.
    - exact Hdepths.
    - exact Hretiled.
  }
  pose proof
    (Hcheck_perm bands' envv Hinfer_bands Hbands'
       (Hpluto bands' envv Hinfer_bands Hbands'))
    as Hcheck_perm_true.
  pose proof
    (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands' envv
       Hlen_env Hinfer_bands Hbands'
       Hwfbefore_pis Hwfafter_pis Hdepths Hwits Hcheck_perm_true)
    as Hperm_envv.
  destruct
    (Tiling.tiling_after_to_before_poly_correct_via_retiled_old
       envv before_pis after_pis ws before_ctxt before_vars st1 st2
       Hlen_after Hlen_ws Hwits Hperm_envv Hlayer Halias Hpoly)
    as [st2' [Hbefore Heq_before]].
  exists st2'.
  split.
  - refine
      (Tiling.PL.PIPSemaIntro
         (before_pis, before_ctxt, before_vars)
         before_pis before_ctxt before_vars envv st1 st2'
         _ _ _ _ _).
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hbefore.
  - exact Heq_before.
Qed.

Lemma pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    uniform_schedule_arity before_pis ->
    BandAffine.PolyLang.wf_pprog_tiling
      (tiling_to_band_pprog (before_pis, before_ctxt, before_vars)) ->
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer_bands Hbands Hprog_full Hwf_ws Hsizes_ws Hdepths
         Harity_before Hwf_before_pp Hpluto.
  assert (Hwf_ws_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  assert (Hwf_before_pis :
    Forall
      (Tiling.PL.wf_pinstr_tiling
         before_ctxt (List.map tiling_to_band_var before_vars))
      before_pis).
  {
    unfold BandAffine.PolyLang.wf_pprog_tiling in Hwf_before_pp.
    destruct Hwf_before_pp as [_ Hwf_before_pp].
    eapply Forall_forall.
    intros pi Hin.
    eapply Hwf_before_pp; eauto.
  }
  eapply
    (pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_if_local_bridge
       envv before_pis after_pis ws bands); eauto.
  intros ipl_ext tau1 tau2 band sizes
         Hcommon Hrecipe Hflat Hin1 Hin2 Hold Hnew.
  destruct (pprog_tiling_bands_cert_lengths _ _ _ _ _ Hbands)
    as [Hlen_after [Hlen_ws Hlen_bands]].
  destruct Harity_before as [before_sched_len Hbefore_sched_len].
  destruct
    (flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog_full Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [Hwf_stmt1 [Hsizes1 [Hpoint_depth1 [Hpref1 [Hbel1 Hlen1]]]]]]]]]]].
  assert (Hbefore1_some :
    nth_error before_pis (Tiling.PL.ip_nth_ext tau1) <> None).
  {
    rewrite Hbefore1.
    discriminate.
  }
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    exfalso.
    apply nth_error_None in Hband1.
    apply nth_error_Some in Hbefore1_some.
    lia.
  }
  destruct
    (flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog_full Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [Hwf_stmt2 [Hsizes2 [Hpoint_depth2 [Hpref2 [Hbel2 Hlen2]]]]]]]]]]].
  assert (Hbefore2_some :
    nth_error before_pis (Tiling.PL.ip_nth_ext tau2) <> None).
  {
    rewrite Hbefore2.
    discriminate.
  }
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    exfalso.
    apply nth_error_None in Hband2.
    apply nth_error_Some in Hbefore2_some.
    lia.
  }
  assert (Hband1_eq : band1 = band).
  {
    eapply common_tiling_band_nth_error; eauto.
  }
  assert (Hband2_eq : band2 = band).
  {
    eapply common_tiling_band_nth_error; eauto.
  }
  pose proof
    (pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 w1 band1
       Hbands Hbefore1 Hafter1 Hw1 Hband1)
    as Hcert1.
  pose proof
    (pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 w2 band2
       Hbands Hbefore2 Hafter2 Hw2 Hband2)
    as Hcert2.
  pose proof
    (infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band1
       Hinfer_bands Hbefore1 Hw1 Hband1)
    as Hinfer1.
  pose proof
    (infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 w2 band2
       Hinfer_bands Hbefore2 Hw2 Hband2)
    as Hinfer2.
  rewrite Hband1_eq in Hcert1, Hinfer1.
  rewrite Hband2_eq in Hcert2, Hinfer2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog_full Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog_full Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau2) w2 Hw2))
    as Hstmt2.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       before_pis (Tiling.PL.ip_nth_ext tau1) before_pi1
       Hwf_before_pis Hbefore1)
    as Hwf_before1.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       before_pis (Tiling.PL.ip_nth_ext tau2) before_pi2
       Hwf_before_pis Hbefore2)
    as Hwf_before2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1 Hstmt1 Hpoint_depth1)
    as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2 Hstmt2 Hpoint_depth2)
    as Hafter_wit2.
  assert (Hafter_depth_eq1 :
    Tiling.PL.pi_depth after_pi1 =
    (Tiling.PL.pi_depth before_pi1 + List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth_eq1 _]].
    exact Hdepth_eq1.
  }
  assert (Hafter_depth_eq2 :
    Tiling.PL.pi_depth after_pi2 =
    (Tiling.PL.pi_depth before_pi2 + List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth_eq2 _]].
    exact Hdepth_eq2.
  }
  assert (Hstmt1_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi1 after_pi1
      (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert (Hstmt2_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi2 after_pi2
      (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ Hbel_len1]]]]]].
  destruct Hbel2 as [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ Hbel_len2]]]]]].
  destruct Hafter_wit1 as [Hafter_pw1 Hafter_depth1].
  destruct Hafter_wit2 as [Hafter_pw2 Hafter_depth2].
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  destruct Hwf_before1 as [Hwf_before1_core _].
  destruct Hwf_before2 as [Hwf_before2_core _].
  destruct Hwf_before1_core as
      [_ [Hcols_before1 [_ [_ [_ [_ [_ [Hsched_before1 _]]]]]]]].
  destruct Hwf_before2_core as
      [_ [Hcols_before2 [_ [_ [_ [_ [_ [Hsched_before2 _]]]]]]]].
  set (added1 :=
    Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Tiling.PL.ip_index_ext tau1)).
  set (point1 :=
    Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Tiling.PL.ip_index_ext tau1)).
  set (added2 :=
    Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w2))
      (Tiling.PL.ip_index_ext tau2)).
  set (point2 :=
    Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w2))
      (Tiling.PL.ip_index_ext tau2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    assert (Hlen1_split :
      List.length (Tiling.PL.ip_index_ext tau1) =
      (List.length envv + List.length (stw_links w1) + stw_point_dim w1)%nat).
    {
      rewrite <- Hafter_depth1 in Hlen1.
      rewrite Hafter_pw1 in Hlen1.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
      simpl in Hlen1.
      lia.
    }
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w1).
    exact Hlen1_split.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    assert (Hlen2_split :
      List.length (Tiling.PL.ip_index_ext tau2) =
      (List.length envv + List.length (stw_links w2) + stw_point_dim w2)%nat).
    {
      rewrite <- Hafter_depth2 in Hlen2.
      rewrite Hafter_pw2 in Hlen2.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
      simpl in Hlen2.
      lia.
    }
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w2).
    exact Hlen2_split.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    assert (Hlen1_split :
      List.length (Tiling.PL.ip_index_ext tau1) =
      (List.length envv + List.length (stw_links w1) + stw_point_dim w1)%nat).
    {
      rewrite <- Hafter_depth1 in Hlen1.
      rewrite Hafter_pw1 in Hlen1.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
      simpl in Hlen1.
      lia.
    }
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    exact Hlen1_split.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    assert (Hlen2_split :
      List.length (Tiling.PL.ip_index_ext tau2) =
      (List.length envv + List.length (stw_links w2) + stw_point_dim w2)%nat).
    {
      rewrite <- Hafter_depth2 in Hlen2.
      rewrite Hafter_pw2 in Hlen2.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
      simpl in Hlen2.
      lia.
    }
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    exact Hlen2_split.
  }
  assert (Hidx_split1 :
    Tiling.PL.ip_index_ext tau1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext tau1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext tau1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext tau1)).
    - apply Tiling.tiled_index_split.
    - replace
        (firstn (List.length envv) (Tiling.PL.ip_index_ext tau1))
        with envv by exact Hpref1.
      reflexivity.
  }
  assert (Hidx_split2 :
    Tiling.PL.ip_index_ext tau2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext tau2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext tau2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext tau2)).
    - apply Tiling.tiled_index_split.
    - replace
        (firstn (List.length envv) (Tiling.PL.ip_index_ext tau2))
        with envv by exact Hpref2.
      reflexivity.
  }
  assert (Hts11_old :
    Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product (Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert (Hts12_old :
    Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product (Tiling.PL.pi_schedule before_pi2) (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert (Hts21_after :
    Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product (Tiling.PL.pi_schedule after_pi1) (Tiling.PL.ip_index_ext tau1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert (Hts22_after :
    Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product (Tiling.PL.pi_schedule after_pi2) (Tiling.PL.ip_index_ext tau2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1
         Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete1.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete1 Hafter_dom1).
    tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2
         Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2 (conj Hwf_stmt2 Hparams2) Hsizes2)
      as Hcomplete2.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete2 Hafter_dom2).
    tauto.
  }
  unfold pinstr_tiling_band_cert in Hcert1, Hcert2.
  destruct Hcert1 as [Hmatch1 Hsched_match1].
  destruct Hcert2 as [Hmatch2 Hsched_match2].
  unfold pinstr_tiling_band_matches in Hmatch1, Hmatch2.
  destruct (schedule_rows_of_links w1) as [rows1|] eqn:Hrows1; try contradiction.
  destruct (schedule_rows_of_links w2) as [rows2|] eqn:Hrows2; try contradiction.
  destruct Hmatch1 as [Hband_len1 Hrows_match1].
  destruct Hmatch2 as [Hband_len2 Hrows_match2].
  assert (Hadded_len1_band : List.length added1 = ptb_len band).
  {
    rewrite Hadded_len1.
    symmetry.
    exact Hband_len1.
  }
  assert (Hadded_len2_band : List.length added2 = ptb_len band).
  {
    rewrite Hadded_len2.
    symmetry.
    exact Hband_len2.
  }
  assert (Hband_rows1 :
    instr_point_ext_band_block_ts band tau1 =
    affine_product rows1 (envv ++ point1)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts11_old.
    rewrite <- affine_product_skipn.
    rewrite <- affine_product_firstn.
    rewrite Hrows_match1.
    reflexivity.
  }
  assert (Hband_rows2 :
    instr_point_ext_band_block_ts band tau2 =
    affine_product rows2 (envv ++ point2)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts12_old.
    rewrite <- affine_product_skipn.
    rewrite <- affine_product_firstn.
    rewrite Hrows_match2.
    reflexivity.
  }
  set (prefix1 := instr_point_ext_band_prefix_ts band tau1).
  set (prefix2 := instr_point_ext_band_prefix_ts band tau2).
  set (band_ts1 := instr_point_ext_band_block_ts band tau1).
  set (band_ts2 := instr_point_ext_band_block_ts band tau2).
  set (suffix1 :=
    skipn (ptb_start band + ptb_len band)%nat
      (Tiling.PL.ip_time_stamp1_ext tau1)).
  set (suffix2 :=
    skipn (ptb_start band + ptb_len band)%nat
      (Tiling.PL.ip_time_stamp1_ext tau2)).
  assert (Hprefix_len :
    List.length prefix1 = List.length prefix2).
  {
    subst prefix1 prefix2.
    unfold instr_point_ext_band_prefix_ts.
    rewrite !firstn_length.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer1) as Hbound1.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer2) as Hbound2.
    try rewrite Hts11_old.
    try rewrite Hts12_old.
    unfold affine_product.
    rewrite !map_length.
    lia.
  }
  assert (Hband_len :
    List.length band_ts1 = List.length band_ts2).
  {
    subst band_ts1 band_ts2.
    unfold instr_point_ext_band_block_ts.
    rewrite !firstn_length, !skipn_length.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer1) as Hbound1.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer2) as Hbound2.
    try rewrite Hts11_old.
    try rewrite Hts12_old.
    unfold affine_product.
    rewrite !map_length.
    lia.
  }
  assert (Hold_split1 :
    Tiling.PL.ip_time_stamp1_ext tau1 = prefix1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite <- firstn_skipn with (n := ptb_start band)
      (l := Tiling.PL.ip_time_stamp1_ext tau1) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band)
      (l := skipn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau1)) at 1.
    f_equal.
    rewrite skipn_skipn.
    rewrite Nat.add_comm.
    reflexivity.
  }
  assert (Hold_split2 :
    Tiling.PL.ip_time_stamp1_ext tau2 = prefix2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite <- firstn_skipn with (n := ptb_start band)
      (l := Tiling.PL.ip_time_stamp1_ext tau2) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band)
      (l := skipn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau2)) at 1.
    f_equal.
    rewrite skipn_skipn.
    rewrite Nat.add_comm.
    reflexivity.
  }
  assert (Hcols_before1_local :
    (List.length envv <= List.length envv + Tiling.PL.pi_depth before_pi1)%nat).
  { lia. }
  assert (Hcols_before2_local :
    (List.length envv <= List.length envv + Tiling.PL.pi_depth before_pi2)%nat).
  { lia. }
  assert (Hsched_before1_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi1)
      (Tiling.PL.pi_schedule before_pi1)).
  {
    rewrite <- Hlen_env.
    exact Hsched_before1.
  }
  assert (Hsched_before2_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi2)
      (Tiling.PL.pi_schedule before_pi2)).
  {
    rewrite <- Hlen_env.
    exact Hsched_before2.
  }
  assert (Hexpected_ts1 :
    affine_product
      (stripmine_schedule_after_env
         (List.length envv) (Tiling.PL.pi_schedule before_pi1) band)
      (Tiling.PL.ip_index_ext tau1) =
    prefix1 ++ added1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite Hidx_split1.
    pose proof
      (stripmine_schedule_after_env_eval
         (List.length envv) (Tiling.PL.pi_schedule before_pi1) band
         (List.length envv + Tiling.PL.pi_depth before_pi1)
         envv added1 point1
         Hsched_before1_env Hcols_before1_local eq_refl
         (eq_trans Hadded_len1 (eq_sym Hband_len1)))
      as Heval1.
    rewrite <- Hts11_old in Heval1.
    exact Heval1.
  }
  assert (Hexpected_ts2 :
    affine_product
      (stripmine_schedule_after_env
         (List.length envv) (Tiling.PL.pi_schedule before_pi2) band)
      (Tiling.PL.ip_index_ext tau2) =
    prefix2 ++ added2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite Hidx_split2.
    pose proof
      (stripmine_schedule_after_env_eval
         (List.length envv) (Tiling.PL.pi_schedule before_pi2) band
         (List.length envv + Tiling.PL.pi_depth before_pi2)
         envv added2 point2
         Hsched_before2_env Hcols_before2_local eq_refl
         (eq_trans Hadded_len2 (eq_sym Hband_len2)))
      as Heval2.
    rewrite <- Hts12_old in Heval2.
    exact Heval2.
  }
  destruct Hsched_match1 as [cols1 [extra1 Hafter_sched1]].
  destruct Hsched_match2 as [cols2 [extra2 Hafter_sched2]].
  assert (Hactual_ts1 :
    Tiling.PL.ip_time_stamp2_ext tau1 =
    (prefix1 ++ added1 ++ band_ts1 ++ suffix1) ++ repeat 0%Z extra1).
  {
    rewrite Hts21_after.
    rewrite Hafter_sched1.
    rewrite affine_product_pad_schedule_with_zero_rows.
    replace
      (affine_product
         (stripmine_schedule_after_env
            (List.length before_ctxt) (Tiling.PL.pi_schedule before_pi1) band)
         (Tiling.PL.ip_index_ext tau1))
      with (prefix1 ++ added1 ++ band_ts1 ++ suffix1).
    2:{
      symmetry.
      rewrite Hlen_env.
      exact Hexpected_ts1.
    }
    reflexivity.
  }
  assert (Hactual_ts2 :
    Tiling.PL.ip_time_stamp2_ext tau2 =
    (prefix2 ++ added2 ++ band_ts2 ++ suffix2) ++ repeat 0%Z extra2).
  {
    rewrite Hts22_after.
    rewrite Hafter_sched2.
    rewrite affine_product_pad_schedule_with_zero_rows.
    replace
      (affine_product
         (stripmine_schedule_after_env
            (List.length before_ctxt) (Tiling.PL.pi_schedule before_pi2) band)
         (Tiling.PL.ip_index_ext tau2))
      with (prefix2 ++ added2 ++ band_ts2 ++ suffix2).
    2:{
      symmetry.
      rewrite Hlen_env.
      exact Hexpected_ts2.
    }
    reflexivity.
  }
  assert (Hexpected_len_eq :
    List.length (prefix1 ++ added1 ++ band_ts1 ++ suffix1) =
    List.length (prefix2 ++ added2 ++ band_ts2 ++ suffix2)).
  {
    assert (Hsched_len1 :
      List.length (Tiling.PL.pi_schedule before_pi1) = before_sched_len).
    {
      eapply uniform_schedule_arity_nth_error; eauto.
    }
    assert (Hsched_len2 :
      List.length (Tiling.PL.pi_schedule before_pi2) = before_sched_len).
    {
      eapply uniform_schedule_arity_nth_error; eauto.
    }
    rewrite <- Hexpected_ts1, <- Hexpected_ts2.
    unfold affine_product.
    rewrite !map_length.
    rewrite !stripmine_schedule_after_env_length.
    rewrite Hsched_len1, Hsched_len2.
    reflexivity.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
      (prefix2 ++ added2 ++ band_ts2 ++ suffix2) <> Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    rewrite Hactual_ts1 in Hnew.
    rewrite Hactual_ts2 in Hnew.
    eapply
      (lex_compare_app_preserves_not_lt_backward_local
         (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
         (prefix2 ++ added2 ++ band_ts2 ++ suffix2)
         (repeat 0%Z extra1) (repeat 0%Z extra2)); eauto.
    intro Hlt.
    destruct Hnew as [Heq | Hgt]; congruence.
  }
  assert (Htiles_eq :
    band_ts1 = band_ts2 -> added1 = added2).
  {
    intro Hband_eq_ts.
    pose proof
      (common_tiling_band_recipe_nth_error ws sizes
         (Tiling.PL.ip_nth_ext tau1) w1 Hrecipe Hw1) as Hsizes_recipe1.
    pose proof
      (common_tiling_band_recipe_nth_error ws sizes
         (Tiling.PL.ip_nth_ext tau2) w2 Hrecipe Hw2) as Hsizes_recipe2.
    rewrite Hadded_eq1, Hadded_eq2.
    eapply common_recipe_equal_band_block_implies_equal_tiles.
    - exact Hpoint_len1.
    - exact Hpoint_len2.
    - exact Hrows1.
    - exact Hrows2.
    - exact Hsizes_recipe1.
    - exact Hsizes_recipe2.
    - exact Hwf_stmt1.
    - exact Hwf_stmt2.
    - exact Hparams1.
    - exact Hparams2.
    - rewrite <- Hband_rows1, <- Hband_rows2.
      exact Hband_eq_ts.
  }
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (stripmined_reversal_implies_prefix_eq_and_band_lt
       prefix1 prefix2 added1 added2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Hold Hnew_expected_not_lt)
    as [Hprefix_eq Hband_lt].
  split.
  - exact Hprefix_eq.
  - exact Hband_lt.
Qed.

Lemma checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto_wf :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    mayReturn
      (checked_tiling_schedule_stripmined_validate
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    uniform_schedule_arity before_pis ->
    BandAffine.PolyLang.wf_pprog_tiling
      (tiling_to_band_pprog (before_pis, before_ctxt, before_vars)) ->
    (forall bands envv,
       infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
       pprog_tiling_bands_cert
         (List.length before_ctxt) before_pis after_pis ws bands ->
       pprog_pluto_permutable_tiling_bands_strong
         envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hcheck Harity_before Hwf_before_pp Hpluto Hsem_after.
  unfold checked_tiling_schedule_stripmined_validate in Hcheck.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hstruct Hsched].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hstruct)
    as [Hprog [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  assert (Hprog_full :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    repeat split; auto.
  }
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length before_ctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  {
    rewrite List.map_length in Hlen_ws_map.
    exact Hlen_ws_map.
  }
  destruct
    (check_pprog_tiling_schedule_stripminedb_sound_flat
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hsched)
    as [bands [Hinfer [Hbands [_ _]]]].
  inversion Hsem_after as
    [pprog pis varctxt vars envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  pose proof Hpprog as Hpprog_eq.
  inversion Hpprog_eq; subst pis varctxt vars; clear Hpprog_eq Hpprog.
  pose proof (Instr.init_env_samelen before_ctxt envv st1 Hinit) as Hlen_env.
  assert (Hwf_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf.
  }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws).
    - exact Hprog_full.
    - exact Hdepths.
  }
  assert (Hlayer :
    Tiling.tiling_retiled_old_to_before_poly_layer
      envv before_pis after_pis ws before_ctxt before_vars).
  {
    intros stx stmid Hretiled.
    eapply Tiling.tiling_retiled_old_to_before_poly_correct_with_env_len_source.
    - exact Hprog_full.
    - symmetry. exact Hlen_env.
    - exact Hbefore_ids.
    - exact Hwf_env.
    - exact Hsizes.
    - exact Hdepths.
    - exact Hretiled.
  }
  assert (Hperm_envv :
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands).
  {
    eapply
      (pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv).
    - exact Hlen_env.
    - exact Hinfer.
    - exact Hbands.
    - exact Hprog_full.
    - exact Hwf.
    - exact Hsizes.
    - exact Hdepths.
    - exact Harity_before.
    - exact Hwf_before_pp.
    - eapply Hpluto; eauto.
  }
  destruct
    (Tiling.tiling_after_to_before_poly_correct_via_retiled_old
       envv before_pis after_pis ws before_ctxt before_vars st1 st2
       Hlen_after Hlen_ws Hwits Hperm_envv Hlayer Halias Hpoly)
    as [st2' [Hbefore Heq_before]].
  exists st2'.
  split.
  - refine
      (Tiling.PL.PIPSemaIntro
         (before_pis, before_ctxt, before_vars)
         before_pis before_ctxt before_vars envv st1 st2'
         _ _ _ _ _).
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hbefore.
  - exact Heq_before.
Qed.

Lemma checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto_structured :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    mayReturn
      (checked_tiling_schedule_stripmined_validate
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
      ws)
      true ->
    uniform_schedule_arity before_pis ->
    uniform_schedule_arity after_pis ->
    BandAffine.PolyLang.wf_pprog_tiling
      (tiling_to_band_pprog (before_pis, before_ctxt, before_vars)) ->
    (forall bands envv,
       infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
       pprog_tiling_bands_cert
         (List.length before_ctxt) before_pis after_pis ws bands ->
       pprog_pluto_permutable_tiling_bands_strong
         envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hcheck Harity_before _ Hwf_before_pp Hpluto Hsem_after.
  eapply checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto_wf; eauto.
Qed.

End TilingBandScheduleValidator.
