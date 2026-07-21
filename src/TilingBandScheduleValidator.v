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
Require Import PolyOperations.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import TilingWitness.
Require Import PointWitness.
Require Import ParallelValidator.
Require Import TilingValidator.
Require Import TilingCanonicalScheduleValidator.
Require Import PolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingBandScheduleValidator (PolIRs: POLIRS).

Module Base := TilingValidator PolIRs.
Module Canonical := TilingCanonicalScheduleValidator PolIRs.
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

Definition check_ordinary_tiling_witnessb
    (w: statement_tiling_witness) : bool :=
  match schedule_rows_of_links w with
  | Some _ => true
  | None => false
  end.

Definition check_ordinary_tiling_witnessesb
    (ws: list statement_tiling_witness) : bool :=
  forallb check_ordinary_tiling_witnessb ws.

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

Definition check_schedule_with_symmetric_trailing_zero_paddingb
    (expected actual: Schedule) : bool :=
  check_schedule_with_trailing_zero_paddingb expected actual ||
  check_schedule_with_trailing_zero_paddingb actual expected.

Definition schedule_matches_with_symmetric_trailing_zero_padding
    (expected actual: Schedule) : Prop :=
  schedule_matches_with_trailing_zero_padding expected actual \/
  schedule_matches_with_trailing_zero_padding actual expected.

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

Definition tile_sizes_of_witness
    (w: statement_tiling_witness) : list Z :=
  List.map tl_tile_size (stw_links w).

Fixpoint check_common_tiling_band_recipe_withb
    (sizes: list Z)
    (ws: list statement_tiling_witness) : bool :=
  match ws with
  | [] => true
  | w :: ws' =>
      listz_strict_eqb sizes (tile_sizes_of_witness w) &&
      check_common_tiling_band_recipe_withb sizes ws'
  end.

Definition check_common_tiling_band_recipeb
    (ws: list statement_tiling_witness) : bool :=
  match ws with
  | [] => true
  | w :: ws' =>
      check_common_tiling_band_recipe_withb (tile_sizes_of_witness w) ws'
  end.

Definition constant_schedule_row_like
    (sched: Schedule)
    (c: Z) : (list Z * Z) :=
  match sched with
  | [] => ([], c)
  | (coeffs, _) :: _ => (repeat 0%Z (List.length coeffs), c)
  end.

Fixpoint uniform_tile_link_const_opt
    (links: list tile_link) : option Z :=
  match links with
  | [] => Some 0%Z
  | link :: links' =>
      let c := ae_const (tl_expr link) in
      if forallb (fun link' => Z.eqb c (ae_const (tl_expr link'))) links'
      then Some c
      else None
  end.

Definition witness_phase_const_opt
    (w: statement_tiling_witness) : option Z :=
  uniform_tile_link_const_opt (stw_links w).

Definition schedule_band_rows
    (band: pinstr_tiling_band)
    (sched: Schedule) : Schedule :=
  firstn (ptb_len band) (skipn (ptb_start band) sched).

Definition project_pluto_phased_band_pi_ext
    (band: pinstr_tiling_band)
    (phase: Z)
    (pi_ext: Tiling.PL.PolyInstr_ext) : Tiling.PL.PolyInstr_ext :=
  let prefix := schedule_take_prefix_only band (Tiling.PL.pi_schedule1_ext pi_ext) in
  let phase_row := constant_schedule_row_like (Tiling.PL.pi_schedule1_ext pi_ext) phase in
  let band_rows := schedule_band_rows band (Tiling.PL.pi_schedule1_ext pi_ext) in
  {|
    Tiling.PL.pi_depth_ext := Tiling.PL.pi_depth_ext pi_ext;
    Tiling.PL.pi_instr_ext := Tiling.PL.pi_instr_ext pi_ext;
    Tiling.PL.pi_poly_ext := Tiling.PL.pi_poly_ext pi_ext;
    Tiling.PL.pi_point_witness_ext := Tiling.PL.pi_point_witness_ext pi_ext;
    Tiling.PL.pi_transformation_ext := Tiling.PL.pi_transformation_ext pi_ext;
    Tiling.PL.pi_access_transformation_ext :=
      Tiling.PL.pi_access_transformation_ext pi_ext;
    Tiling.PL.pi_schedule1_ext := prefix ++ phase_row :: band_rows;
    Tiling.PL.pi_schedule2_ext := prefix ++ [phase_row];
    Tiling.PL.pi_waccess_ext := Tiling.PL.pi_waccess_ext pi_ext;
    Tiling.PL.pi_raccess_ext := Tiling.PL.pi_raccess_ext pi_ext;
  |}.

Fixpoint project_pinstrs_ext_with_pluto_phased_band
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : option (list Tiling.PL.PolyInstr_ext) :=
  match pil_ext, ws with
  | [], [] => Some []
  | pi_ext :: pil_ext', w :: ws' =>
      match witness_phase_const_opt w,
            project_pinstrs_ext_with_pluto_phased_band pil_ext' ws' band with
      | Some phase, Some rest =>
          Some (project_pluto_phased_band_pi_ext band phase pi_ext :: rest)
      | _, _ => None
      end
  | _, _ => None
  end.

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

Definition project_pluto_band_pi_ext
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
    Tiling.PL.pi_schedule1_ext :=
      firstn (ptb_start band + ptb_len band)%nat
        (Tiling.PL.pi_schedule1_ext pi_ext);
    Tiling.PL.pi_schedule2_ext :=
      firstn (ptb_start band)%nat
        (Tiling.PL.pi_schedule1_ext pi_ext);
    Tiling.PL.pi_waccess_ext := Tiling.PL.pi_waccess_ext pi_ext;
    Tiling.PL.pi_raccess_ext := Tiling.PL.pi_raccess_ext pi_ext;
  |}.

Definition project_pluto_band_ip_ext
    (band: pinstr_tiling_band)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  {|
    Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
    Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
    Tiling.PL.ip_transformation_ext := Tiling.PL.ip_transformation_ext ip_ext;
    Tiling.PL.ip_access_transformation_ext :=
      Tiling.PL.ip_access_transformation_ext ip_ext;
    Tiling.PL.ip_time_stamp1_ext :=
      firstn (ptb_start band + ptb_len band)%nat
        (Tiling.PL.ip_time_stamp1_ext ip_ext);
    Tiling.PL.ip_time_stamp2_ext :=
      firstn (ptb_start band)
        (Tiling.PL.ip_time_stamp1_ext ip_ext);
    Tiling.PL.ip_instruction_ext := Tiling.PL.ip_instruction_ext ip_ext;
    Tiling.PL.ip_depth_ext := Tiling.PL.ip_depth_ext ip_ext;
  |}.

Definition prioritize_pluto_band_component_rows
    (band: pinstr_tiling_band)
    (dim: nat)
    (rows: list (list Z * Z)) : list (list Z * Z) :=
  firstn (ptb_start band) rows ++
  firstn 1 (skipn (ptb_start band + dim) rows) ++
  rows.

Definition prioritize_pluto_band_component_ts
    (band: pinstr_tiling_band)
    (dim: nat)
    (ts: list Z) : list Z :=
  firstn (ptb_start band) ts ++
  firstn 1 (skipn (ptb_start band + dim) ts) ++
  ts.

Definition project_pluto_band_component_pi_ext
    (band: pinstr_tiling_band)
    (dim: nat)
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
      prioritize_pluto_band_component_rows
        band dim (Tiling.PL.pi_schedule1_ext pi_ext);
    Tiling.PL.pi_waccess_ext := Tiling.PL.pi_waccess_ext pi_ext;
    Tiling.PL.pi_raccess_ext := Tiling.PL.pi_raccess_ext pi_ext;
  |}.

Definition project_pluto_band_component_ip_ext
    (band: pinstr_tiling_band)
    (dim: nat)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  {|
    Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
    Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
    Tiling.PL.ip_transformation_ext := Tiling.PL.ip_transformation_ext ip_ext;
    Tiling.PL.ip_access_transformation_ext :=
      Tiling.PL.ip_access_transformation_ext ip_ext;
    Tiling.PL.ip_time_stamp1_ext := Tiling.PL.ip_time_stamp1_ext ip_ext;
    Tiling.PL.ip_time_stamp2_ext :=
      prioritize_pluto_band_component_ts
        band dim (Tiling.PL.ip_time_stamp1_ext ip_ext);
    Tiling.PL.ip_instruction_ext := Tiling.PL.ip_instruction_ext ip_ext;
    Tiling.PL.ip_depth_ext := Tiling.PL.ip_depth_ext ip_ext;
  |}.

Definition project_pinstrs_ext_with_pluto_band_component
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim: nat) : list Tiling.PL.PolyInstr_ext :=
  List.map (project_pluto_band_component_pi_ext band dim) pil_ext.

Definition prioritize_pluto_band_component_or_zero_rows
    (band: pinstr_tiling_band)
    (dim: nat)
    (rows: Schedule) : Schedule :=
  if Nat.ltb dim (ptb_len band) then
    prioritize_pluto_band_component_rows band dim rows
  else
    firstn (ptb_start band) rows ++
    [constant_schedule_row_like rows 0%Z] ++
    rows.

Definition prioritize_pluto_band_component_or_zero_ts
    (band: pinstr_tiling_band)
    (dim: nat)
    (ts: list Z) : list Z :=
  if Nat.ltb dim (ptb_len band) then
    prioritize_pluto_band_component_ts band dim ts
  else
    firstn (ptb_start band) ts ++ [0%Z] ++ ts.

Definition project_pluto_bands_component_pi_ext
    (band: pinstr_tiling_band)
    (dim: nat)
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
      prioritize_pluto_band_component_or_zero_rows
        band dim (Tiling.PL.pi_schedule1_ext pi_ext);
    Tiling.PL.pi_waccess_ext := Tiling.PL.pi_waccess_ext pi_ext;
    Tiling.PL.pi_raccess_ext := Tiling.PL.pi_raccess_ext pi_ext;
  |}.

Definition project_pluto_bands_component_ip_ext
    (bands: list pinstr_tiling_band)
    (dim: nat)
    (ip_ext: Tiling.PL.InstrPoint_ext) : Tiling.PL.InstrPoint_ext :=
  match List.nth_error bands (Tiling.PL.ip_nth_ext ip_ext) with
  | Some band =>
      {|
        Tiling.PL.ip_nth_ext := Tiling.PL.ip_nth_ext ip_ext;
        Tiling.PL.ip_index_ext := Tiling.PL.ip_index_ext ip_ext;
        Tiling.PL.ip_transformation_ext :=
          Tiling.PL.ip_transformation_ext ip_ext;
        Tiling.PL.ip_access_transformation_ext :=
          Tiling.PL.ip_access_transformation_ext ip_ext;
        Tiling.PL.ip_time_stamp1_ext :=
          Tiling.PL.ip_time_stamp1_ext ip_ext;
        Tiling.PL.ip_time_stamp2_ext :=
          prioritize_pluto_band_component_or_zero_ts
            band dim (Tiling.PL.ip_time_stamp1_ext ip_ext);
        Tiling.PL.ip_instruction_ext := Tiling.PL.ip_instruction_ext ip_ext;
        Tiling.PL.ip_depth_ext := Tiling.PL.ip_depth_ext ip_ext;
      |}
  | None => ip_ext
  end.

Fixpoint project_pinstrs_ext_with_pluto_bands_component
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (bands: list pinstr_tiling_band)
    (dim: nat) : list Tiling.PL.PolyInstr_ext :=
  match pil_ext, bands with
  | pi_ext :: pil_ext', band :: bands' =>
      project_pluto_bands_component_pi_ext band dim pi_ext ::
      project_pinstrs_ext_with_pluto_bands_component pil_ext' bands' dim
  | _, _ => []
  end.

Fixpoint max_tiling_band_len (bands: list pinstr_tiling_band) : nat :=
  match bands with
  | [] => O
  | band :: bands' => Nat.max (ptb_len band) (max_tiling_band_len bands')
  end.

Lemma project_pinstrs_ext_with_pluto_bands_component_length :
  forall pil_ext bands dim,
    List.length pil_ext = List.length bands ->
    List.length
      (project_pinstrs_ext_with_pluto_bands_component pil_ext bands dim) =
    List.length pil_ext.
Proof.
  induction pil_ext as [|pi_ext pil_ext' IH]; intros bands dim Hlen.
  - destruct bands; simpl in *; try discriminate; reflexivity.
  - destruct bands as [|band bands']; simpl in *; try discriminate.
    f_equal.
    eapply IH.
    lia.
Qed.

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

Definition project_pinstrs_ext_with_pluto_band
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band) : list Tiling.PL.PolyInstr_ext :=
  List.map (project_pluto_band_pi_ext band) pil_ext.

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

Lemma project_pluto_band_ip_ext_old_eq_except_sched :
  forall band ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.old_of_ext ip_ext)
      (Tiling.PL.old_of_ext (project_pluto_band_ip_ext band ip_ext)).
Proof.
  intros band ip_ext.
  unfold Tiling.PL.eq_except_sched,
         Tiling.PL.old_of_ext,
         project_pluto_band_ip_ext.
  destruct ip_ext; simpl.
  repeat split; reflexivity.
Qed.

Lemma project_pluto_band_ip_ext_permutable_back :
  forall band ip1_ext ip2_ext,
    Tiling.PL.Permutable_ext
      (project_pluto_band_ip_ext band ip1_ext)
      (project_pluto_band_ip_ext band ip2_ext) ->
    Tiling.PL.Permutable_ext ip1_ext ip2_ext.
Proof.
  intros band ip1_ext ip2_ext Hperm_proj.
  unfold Tiling.PL.Permutable_ext in Hperm_proj |- *.
  eapply permutable_eq_except_sched_local.
  - apply eq_except_sched_symm_local.
    apply project_pluto_band_ip_ext_old_eq_except_sched.
  - apply eq_except_sched_symm_local.
    apply project_pluto_band_ip_ext_old_eq_except_sched.
  - exact Hperm_proj.
Qed.

Lemma project_pluto_band_ip_ext_preserves_np_lt :
  forall band ip1 ip2,
    Tiling.PL.np_lt_ext ip1 ip2 ->
    Tiling.PL.np_lt_ext
      (project_pluto_band_ip_ext band ip1)
      (project_pluto_band_ip_ext band ip2).
Proof.
  intros band ip1 ip2 Hlt.
  unfold Tiling.PL.np_lt_ext, project_pluto_band_ip_ext in *.
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma HdRel_map_project_pluto_band_ip_ext :
  forall band ip xs,
    HdRel Tiling.PL.np_lt_ext ip xs ->
    HdRel Tiling.PL.np_lt_ext
      (project_pluto_band_ip_ext band ip)
      (List.map (project_pluto_band_ip_ext band) xs).
Proof.
  intros band ip xs Hrel.
  induction Hrel as [|y ys Hxy].
  - constructor.
  - simpl. constructor.
    eapply project_pluto_band_ip_ext_preserves_np_lt; exact Hxy.
Qed.

Lemma Sorted_map_project_pluto_band_ip_ext :
  forall band ipl,
    Sorted Tiling.PL.np_lt_ext ipl ->
    Sorted Tiling.PL.np_lt_ext
      (List.map (project_pluto_band_ip_ext band) ipl).
Proof.
  intros band ipl Hsorted.
  induction Hsorted as [|x xs Hsorted_xs IH Hrel].
  - constructor.
  - simpl. constructor.
    + exact IH.
    + eapply HdRel_map_project_pluto_band_ip_ext; exact Hrel.
Qed.

Lemma project_pluto_band_ip_ext_eq_iff :
  forall band ip1 ip2,
    project_pluto_band_ip_ext band ip1 =
    project_pluto_band_ip_ext band ip2 ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 /\
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2.
Proof.
  intros band ip1 ip2 Heq.
  unfold project_pluto_band_ip_ext in Heq.
  destruct ip1, ip2; simpl in *.
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma project_pluto_band_component_ip_ext_old_eq_except_sched :
  forall band dim ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.old_of_ext ip_ext)
      (Tiling.PL.old_of_ext
         (project_pluto_band_component_ip_ext band dim ip_ext)).
Proof.
  intros band dim ip_ext.
  unfold Tiling.PL.eq_except_sched,
         Tiling.PL.old_of_ext,
         project_pluto_band_component_ip_ext.
  destruct ip_ext; simpl.
  repeat split; reflexivity.
Qed.

Lemma project_pluto_band_component_ip_ext_permutable_back :
  forall band dim ip1_ext ip2_ext,
    Tiling.PL.Permutable_ext
      (project_pluto_band_component_ip_ext band dim ip1_ext)
      (project_pluto_band_component_ip_ext band dim ip2_ext) ->
    Tiling.PL.Permutable_ext ip1_ext ip2_ext.
Proof.
  intros band dim ip1_ext ip2_ext Hperm_proj.
  unfold Tiling.PL.Permutable_ext in Hperm_proj |- *.
  eapply permutable_eq_except_sched_local.
  - apply eq_except_sched_symm_local.
    apply project_pluto_band_component_ip_ext_old_eq_except_sched.
  - apply eq_except_sched_symm_local.
    apply project_pluto_band_component_ip_ext_old_eq_except_sched.
  - exact Hperm_proj.
Qed.

Lemma project_pluto_band_component_ip_ext_preserves_np_lt :
  forall band dim ip1 ip2,
    Tiling.PL.np_lt_ext ip1 ip2 ->
    Tiling.PL.np_lt_ext
      (project_pluto_band_component_ip_ext band dim ip1)
      (project_pluto_band_component_ip_ext band dim ip2).
Proof.
  intros band dim ip1 ip2 Hlt.
  unfold Tiling.PL.np_lt_ext,
         project_pluto_band_component_ip_ext in *.
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma HdRel_map_project_pluto_band_component_ip_ext :
  forall band dim ip xs,
    HdRel Tiling.PL.np_lt_ext ip xs ->
    HdRel Tiling.PL.np_lt_ext
      (project_pluto_band_component_ip_ext band dim ip)
      (List.map
         (project_pluto_band_component_ip_ext band dim) xs).
Proof.
  intros band dim ip xs Hrel.
  induction Hrel as [|y ys Hxy].
  - constructor.
  - simpl. constructor.
    eapply project_pluto_band_component_ip_ext_preserves_np_lt.
    exact Hxy.
Qed.

Lemma Sorted_map_project_pluto_band_component_ip_ext :
  forall band dim ipl,
    Sorted Tiling.PL.np_lt_ext ipl ->
    Sorted Tiling.PL.np_lt_ext
      (List.map
         (project_pluto_band_component_ip_ext band dim) ipl).
Proof.
  intros band dim ipl Hsorted.
  induction Hsorted as [|x xs Hsorted_xs IH Hrel].
  - constructor.
  - simpl. constructor.
    + exact IH.
    + eapply HdRel_map_project_pluto_band_component_ip_ext.
      exact Hrel.
Qed.

Lemma project_pluto_band_component_ip_ext_eq_iff :
  forall band dim ip1 ip2,
    project_pluto_band_component_ip_ext band dim ip1 =
    project_pluto_band_component_ip_ext band dim ip2 ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 /\
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2.
Proof.
  intros band dim ip1 ip2 Heq.
  unfold project_pluto_band_component_ip_ext in Heq.
  destruct ip1, ip2; simpl in *.
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma project_pluto_bands_component_ip_ext_old_eq_except_sched :
  forall bands dim ip_ext,
    Tiling.PL.eq_except_sched
      (Tiling.PL.old_of_ext ip_ext)
      (Tiling.PL.old_of_ext
         (project_pluto_bands_component_ip_ext bands dim ip_ext)).
Proof.
  intros bands dim ip_ext.
  unfold project_pluto_bands_component_ip_ext.
  destruct (nth_error bands (Tiling.PL.ip_nth_ext ip_ext));
    unfold Tiling.PL.eq_except_sched, Tiling.PL.old_of_ext;
    destruct ip_ext; simpl; repeat split; reflexivity.
Qed.

Lemma project_pluto_bands_component_ip_ext_permutable_back :
  forall bands dim ip1_ext ip2_ext,
    Tiling.PL.Permutable_ext
      (project_pluto_bands_component_ip_ext bands dim ip1_ext)
      (project_pluto_bands_component_ip_ext bands dim ip2_ext) ->
    Tiling.PL.Permutable_ext ip1_ext ip2_ext.
Proof.
  intros bands dim ip1_ext ip2_ext Hperm_proj.
  unfold Tiling.PL.Permutable_ext in Hperm_proj |- *.
  eapply permutable_eq_except_sched_local.
  - apply eq_except_sched_symm_local.
    apply project_pluto_bands_component_ip_ext_old_eq_except_sched.
  - apply eq_except_sched_symm_local.
    apply project_pluto_bands_component_ip_ext_old_eq_except_sched.
  - exact Hperm_proj.
Qed.

Lemma project_pluto_bands_component_ip_ext_preserves_np_lt :
  forall bands dim ip1 ip2,
    Tiling.PL.np_lt_ext ip1 ip2 ->
    Tiling.PL.np_lt_ext
      (project_pluto_bands_component_ip_ext bands dim ip1)
      (project_pluto_bands_component_ip_ext bands dim ip2).
Proof.
  intros bands dim ip1 ip2 Hlt.
  unfold Tiling.PL.np_lt_ext,
         project_pluto_bands_component_ip_ext in *.
  destruct (nth_error bands (Tiling.PL.ip_nth_ext ip1));
  destruct (nth_error bands (Tiling.PL.ip_nth_ext ip2));
  destruct ip1, ip2; simpl in *; exact Hlt.
Qed.

Lemma Sorted_map_project_pluto_bands_component_ip_ext :
  forall bands dim ipl,
    Sorted Tiling.PL.np_lt_ext ipl ->
    Sorted Tiling.PL.np_lt_ext
      (List.map (project_pluto_bands_component_ip_ext bands dim) ipl).
Proof.
  intros bands dim ipl Hsorted.
  induction Hsorted as [|x xs Hsorted_xs IH Hrel].
  - constructor.
  - simpl. constructor.
    + exact IH.
    + induction Hrel as [|y ys Hxy].
      * constructor.
      * simpl. constructor.
        eapply project_pluto_bands_component_ip_ext_preserves_np_lt.
        exact Hxy.
Qed.

Lemma project_pluto_bands_component_ip_ext_eq_iff :
  forall bands dim ip1 ip2,
    project_pluto_bands_component_ip_ext bands dim ip1 =
    project_pluto_bands_component_ip_ext bands dim ip2 ->
    Tiling.PL.ip_nth_ext ip1 = Tiling.PL.ip_nth_ext ip2 /\
    Tiling.PL.ip_index_ext ip1 = Tiling.PL.ip_index_ext ip2.
Proof.
  intros bands dim ip1 ip2 Heq.
  unfold project_pluto_bands_component_ip_ext in Heq.
  destruct (nth_error bands (Tiling.PL.ip_nth_ext ip1));
  destruct (nth_error bands (Tiling.PL.ip_nth_ext ip2));
  destruct ip1, ip2; simpl in *; inversion Heq; subst;
    split; reflexivity.
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

Lemma affine_product_app_local_component :
  forall m1 m2 p,
    affine_product (m1 ++ m2) p =
    affine_product m1 p ++ affine_product m2 p.
Proof.
  intros m1 m2 p.
  unfold affine_product.
  rewrite List.map_app.
  reflexivity.
Qed.

Lemma affine_product_skipn_local_component :
  forall n m p,
    affine_product (skipn n m) p = skipn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - reflexivity.
  - destruct m as [|x m]; simpl; auto.
Qed.

Lemma affine_product_prioritize_pluto_band_component_rows :
  forall band dim rows p,
    affine_product
      (prioritize_pluto_band_component_rows band dim rows) p =
    prioritize_pluto_band_component_ts
      band dim (affine_product rows p).
Proof.
  intros band dim rows p.
  unfold prioritize_pluto_band_component_rows,
         prioritize_pluto_band_component_ts.
  rewrite !affine_product_app_local_component.
  rewrite !affine_product_firstn_local.
  rewrite affine_product_skipn_local_component.
  reflexivity.
Qed.

Lemma affine_product_constant_schedule_row_like_zero :
  forall rows p,
    affine_product [constant_schedule_row_like rows 0%Z] p = [0%Z].
Proof.
  intros rows p.
  destruct rows as [|[coeffs c] rows]; simpl.
  - destruct p; reflexivity.
  - rewrite dot_product_repeat_zero_left.
    reflexivity.
Qed.

Lemma affine_product_prioritize_pluto_band_component_or_zero_rows :
  forall band dim rows p,
    affine_product
      (prioritize_pluto_band_component_or_zero_rows band dim rows) p =
    prioritize_pluto_band_component_or_zero_ts
      band dim (affine_product rows p).
Proof.
  intros band dim rows p.
  unfold prioritize_pluto_band_component_or_zero_rows,
         prioritize_pluto_band_component_or_zero_ts.
  destruct (Nat.ltb dim (ptb_len band)).
  - apply affine_product_prioritize_pluto_band_component_rows.
  - rewrite !affine_product_app_local_component.
    rewrite affine_product_firstn_local.
    rewrite affine_product_constant_schedule_row_like_zero.
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

Lemma restore_projected_band_ip_ext_from_pluto_project_belongs_to_ext :
  forall band pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext (project_pluto_band_pi_ext band pi_ext) ->
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

Lemma project_restore_projected_pluto_band_ip_ext :
  forall band pi_ext ip_ext,
    Tiling.PL.belongs_to_ext ip_ext (project_pluto_band_pi_ext band pi_ext) ->
    project_pluto_band_ip_ext band
      (restore_projected_band_ip_ext pi_ext ip_ext) = ip_ext.
Proof.
  intros band pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in Hbel.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  destruct ip_ext.
  unfold project_pluto_band_ip_ext,
         project_pluto_band_pi_ext,
         restore_projected_band_ip_ext in *.
  simpl in *.
  subst.
  f_equal; try reflexivity;
    rewrite <- affine_product_firstn_local;
    reflexivity.
Qed.

Lemma restore_projected_band_ip_ext_from_pluto_component_project_belongs_to_ext :
  forall band dim pi_ext ip_ext,
    Tiling.PL.belongs_to_ext
      ip_ext (project_pluto_band_component_pi_ext band dim pi_ext) ->
    Tiling.PL.belongs_to_ext
      (restore_projected_band_ip_ext pi_ext ip_ext)
      pi_ext.
Proof.
  intros band dim pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [_ [_ [Hins Hdepth]]]]]].
  unfold restore_projected_band_ip_ext.
  simpl.
  repeat split; auto.
Qed.

Lemma project_restore_projected_pluto_band_component_ip_ext :
  forall band dim pi_ext ip_ext,
    Tiling.PL.belongs_to_ext
      ip_ext (project_pluto_band_component_pi_ext band dim pi_ext) ->
    project_pluto_band_component_ip_ext band dim
      (restore_projected_band_ip_ext pi_ext ip_ext) = ip_ext.
Proof.
  intros band dim pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in Hbel.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  destruct ip_ext.
  unfold project_pluto_band_component_ip_ext,
         project_pluto_band_component_pi_ext,
         restore_projected_band_ip_ext in *.
  simpl in *.
  subst.
  f_equal; try reflexivity.
  rewrite affine_product_prioritize_pluto_band_component_rows.
  reflexivity.
Qed.

Lemma restore_projected_band_ip_ext_from_pluto_bands_component_project_belongs_to_ext :
  forall band dim pi_ext ip_ext,
    Tiling.PL.belongs_to_ext
      ip_ext (project_pluto_bands_component_pi_ext band dim pi_ext) ->
    Tiling.PL.belongs_to_ext
      (restore_projected_band_ip_ext pi_ext ip_ext)
      pi_ext.
Proof.
  intros band dim pi_ext ip_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [_ [_ [Hins Hdepth]]]]]].
  unfold restore_projected_band_ip_ext.
  simpl.
  repeat split; auto.
Qed.

Lemma project_restore_projected_pluto_bands_component_ip_ext :
  forall bands band dim pi_ext ip_ext,
    nth_error bands (Tiling.PL.ip_nth_ext ip_ext) = Some band ->
    Tiling.PL.belongs_to_ext
      ip_ext (project_pluto_bands_component_pi_ext band dim pi_ext) ->
    project_pluto_bands_component_ip_ext bands dim
      (restore_projected_band_ip_ext pi_ext ip_ext) = ip_ext.
Proof.
  intros bands band dim pi_ext ip_ext Hband Hbel.
  unfold Tiling.PL.belongs_to_ext in Hbel.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [Hts2 [Hins Hdepth]]]]]].
  destruct ip_ext.
  simpl in Hband.
  unfold project_pluto_bands_component_ip_ext,
         project_pluto_bands_component_pi_ext,
         restore_projected_band_ip_ext in *.
  simpl in *.
  rewrite Hband.
  simpl.
  subst.
  f_equal; try reflexivity.
  rewrite affine_product_prioritize_pluto_band_component_or_zero_rows.
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

Lemma project_pluto_band_ip_ext_belongs_to_ext_local :
  forall band ip_ext pi_ext,
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (project_pluto_band_ip_ext band ip_ext)
      (project_pluto_band_pi_ext band pi_ext).
Proof.
  intros band ip_ext pi_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [_ [Hins Hdepth]]]]]].
  unfold project_pluto_band_ip_ext, project_pluto_band_pi_ext.
  simpl.
  repeat split.
  - exact Hdom.
  - exact Htf.
  - exact Hacc_tf.
  - rewrite affine_product_firstn_local, Hts1. reflexivity.
  - rewrite affine_product_firstn_local, Hts1. reflexivity.
  - exact Hins.
  - exact Hdepth.
Qed.

Lemma project_pluto_band_component_ip_ext_belongs_to_ext_local :
  forall band dim ip_ext pi_ext,
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (project_pluto_band_component_ip_ext band dim ip_ext)
      (project_pluto_band_component_pi_ext band dim pi_ext).
Proof.
  intros band dim ip_ext pi_ext Hbel.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [_ [Hins Hdepth]]]]]].
  unfold project_pluto_band_component_ip_ext,
         project_pluto_band_component_pi_ext.
  simpl.
  repeat split.
  - exact Hdom.
  - exact Htf.
  - exact Hacc_tf.
  - exact Hts1.
  - rewrite affine_product_prioritize_pluto_band_component_rows.
    rewrite Hts1.
    reflexivity.
  - exact Hins.
  - exact Hdepth.
Qed.

Lemma project_pluto_bands_component_ip_ext_belongs_to_ext_local :
  forall bands band dim ip_ext pi_ext,
    nth_error bands (Tiling.PL.ip_nth_ext ip_ext) = Some band ->
    Tiling.PL.belongs_to_ext ip_ext pi_ext ->
    Tiling.PL.belongs_to_ext
      (project_pluto_bands_component_ip_ext bands dim ip_ext)
      (project_pluto_bands_component_pi_ext band dim pi_ext).
Proof.
  intros bands band dim ip_ext pi_ext Hband Hbel.
  unfold project_pluto_bands_component_ip_ext.
  rewrite Hband.
  unfold Tiling.PL.belongs_to_ext in *.
  destruct Hbel as
      [Hdom [Htf [Hacc_tf [Hts1 [_ [Hins Hdepth]]]]]].
  unfold project_pluto_bands_component_pi_ext.
  simpl.
  repeat split.
  - exact Hdom.
  - exact Htf.
  - exact Hacc_tf.
  - exact Hts1.
  - rewrite affine_product_prioritize_pluto_band_component_or_zero_rows.
    rewrite Hts1.
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

Lemma flatten_instr_nth_ext_project_pluto_band :
  forall envv nth pi_ext ipl band,
    Tiling.PL.flatten_instr_nth_ext envv nth pi_ext ipl ->
    Tiling.PL.flatten_instr_nth_ext
      envv nth
      (project_pluto_band_pi_ext band pi_ext)
      (List.map (project_pluto_band_ip_ext band) ipl).
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
        -- eapply project_pluto_band_ip_ext_belongs_to_ext_local; exact Hbel0.
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
             eapply restore_projected_band_ip_ext_from_pluto_project_belongs_to_ext.
             exact Hbel0.
          -- split; [exact Hnth0| exact Hlen0].
        }
        apply in_map_iff.
        exists ip_full.
        split.
        -- unfold ip_full.
           eapply project_restore_projected_pluto_band_ip_ext; exact Hbel0.
        -- exact Hin_full.
    + assert (Hnodup_proj :
          NoDup (List.map (project_pluto_band_ip_ext band) ipl)).
      {
        eapply Tiling.NoDup_map_on; [exact Hnodup|].
        intros ip1 ip2 Hin1 Hin2 Heq.
        apply project_pluto_band_ip_ext_eq_iff in Heq.
        destruct Heq as [_ Hidx].
        exact
          (flatten_instr_nth_ext_index_injective_local
             envv nth pi_ext ipl ip1 ip2 Hflat0 Hin1 Hin2 Hidx).
      }
      assert (Hsorted_proj :
          Sorted Tiling.PL.np_lt_ext
            (List.map (project_pluto_band_ip_ext band) ipl)).
      {
        eapply Sorted_map_project_pluto_band_ip_ext.
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

Lemma flatten_instrs_ext_project_pluto_band :
  forall envv pil_ext ipl_ext band,
    Tiling.PL.flatten_instrs_ext envv pil_ext ipl_ext ->
    Tiling.PL.flatten_instrs_ext
      envv
      (project_pinstrs_ext_with_pluto_band pil_ext band)
      (List.map (project_pluto_band_ip_ext band) ipl_ext).
Proof.
  intros envv pil_ext ipl_ext band Hflat.
  unfold project_pinstrs_ext_with_pluto_band.
  destruct Hflat as [Hprefix [Hmem [Hnodup Hsorted]]].
  split.
  - intros ip_ext Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip0 [Hip Hin0]].
    subst.
    unfold project_pluto_band_ip_ext.
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
        exists (project_pluto_band_pi_ext band pi0).
        split.
        -- erewrite map_nth_error; eauto.
        -- split.
           ++ exact Hpref0.
           ++ split.
              ** eapply project_pluto_band_ip_ext_belongs_to_ext_local; eauto.
              ** exact Hlen0.
      * destruct Hin as (pi_proj & Hnth_proj & Hpref_proj & Hbel_proj & Hlen_proj).
        destruct (nth_error pil_ext (Tiling.PL.ip_nth_ext ip_ext)) as [pi0|]
          eqn:Hnth0.
        -- assert (Hpi_proj : pi_proj = project_pluto_band_pi_ext band pi0).
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
                   eapply restore_projected_band_ip_ext_from_pluto_project_belongs_to_ext.
                   exact Hbel_proj.
                ** exact Hlen_proj.
           }
           apply in_map_iff.
           exists ip_full.
           split.
           ++ unfold ip_full.
              eapply project_restore_projected_pluto_band_ip_ext.
              exact Hbel_proj.
           ++ exact Hin_full.
        -- rewrite map_nth_error_none in Hnth_proj; congruence.
    + split.
      * apply Tiling.NoDup_map_on.
        -- exact Hnodup.
        -- intros ip1 ip2 Hin1 Hin2 Heq.
           apply project_pluto_band_ip_ext_eq_iff in Heq.
           destruct Heq as [Hnth Hidx].
           eapply flatten_instrs_ext_index_injective_local.
           ++ split; [exact Hprefix|].
              split; [exact Hmem|].
              split; [exact Hnodup| exact Hsorted].
           ++ exact Hin1.
           ++ exact Hin2.
           ++ exact Hnth.
           ++ exact Hidx.
      * apply Sorted_map_project_pluto_band_ip_ext.
        exact Hsorted.
Qed.

Lemma flatten_instrs_ext_project_pluto_band_component :
  forall envv pil_ext ipl_ext band dim,
    Tiling.PL.flatten_instrs_ext envv pil_ext ipl_ext ->
    Tiling.PL.flatten_instrs_ext
      envv
      (project_pinstrs_ext_with_pluto_band_component pil_ext band dim)
      (List.map
         (project_pluto_band_component_ip_ext band dim) ipl_ext).
Proof.
  intros envv pil_ext ipl_ext band dim Hflat.
  unfold project_pinstrs_ext_with_pluto_band_component.
  destruct Hflat as [Hprefix [Hmem [Hnodup Hsorted]]].
  split.
  - intros ip_ext Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip0 [Hip Hin0]].
    subst.
    unfold project_pluto_band_component_ip_ext.
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
        exists (project_pluto_band_component_pi_ext band dim pi0).
        split.
        -- erewrite map_nth_error; eauto.
        -- split.
           ++ exact Hpref0.
           ++ split.
              ** eapply
                   project_pluto_band_component_ip_ext_belongs_to_ext_local;
                   eauto.
              ** exact Hlen0.
      * destruct Hin as
          (pi_proj & Hnth_proj & Hpref_proj & Hbel_proj & Hlen_proj).
        destruct (nth_error pil_ext (Tiling.PL.ip_nth_ext ip_ext)) as [pi0|]
          eqn:Hnth0.
        -- assert (Hpi_proj :
             pi_proj = project_pluto_band_component_pi_ext band dim pi0).
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
                   eapply
                     restore_projected_band_ip_ext_from_pluto_component_project_belongs_to_ext.
                   exact Hbel_proj.
                ** exact Hlen_proj.
           }
           apply in_map_iff.
           exists ip_full.
           split.
           ++ unfold ip_full.
              eapply
                project_restore_projected_pluto_band_component_ip_ext.
              exact Hbel_proj.
           ++ exact Hin_full.
        -- rewrite map_nth_error_none in Hnth_proj; congruence.
    + split.
      * apply Tiling.NoDup_map_on.
        -- exact Hnodup.
        -- intros ip1 ip2 Hin1 Hin2 Heq.
           apply project_pluto_band_component_ip_ext_eq_iff in Heq.
           destruct Heq as [Hnth Hidx].
           eapply flatten_instrs_ext_index_injective_local.
           ++ split; [exact Hprefix|].
              split; [exact Hmem|].
              split; [exact Hnodup| exact Hsorted].
           ++ exact Hin1.
           ++ exact Hin2.
           ++ exact Hnth.
           ++ exact Hidx.
      * apply Sorted_map_project_pluto_band_component_ip_ext.
        exact Hsorted.
Qed.

Lemma nth_error_project_pinstrs_ext_with_pluto_bands_component_local :
  forall pil_ext bands dim n pi_ext band,
    List.nth_error pil_ext n = Some pi_ext ->
    List.nth_error bands n = Some band ->
    List.nth_error
      (project_pinstrs_ext_with_pluto_bands_component pil_ext bands dim)
      n = Some (project_pluto_bands_component_pi_ext band dim pi_ext).
Proof.
  induction pil_ext as [|pi_ext0 pil_ext' IH];
    intros bands dim n pi_ext band Hpi Hband.
  - destruct n; simpl in Hpi; discriminate.
  - destruct bands as [|band0 bands']; simpl in *.
    + destruct n; simpl in Hband; discriminate.
    + destruct n as [|n'].
      * now inversion Hpi; inversion Hband; subst.
      * eapply IH; eauto.
Qed.

Lemma flatten_instrs_ext_project_pluto_bands_component :
  forall envv pil_ext ipl_ext bands dim,
    List.length pil_ext = List.length bands ->
    Tiling.PL.flatten_instrs_ext envv pil_ext ipl_ext ->
    Tiling.PL.flatten_instrs_ext
      envv
      (project_pinstrs_ext_with_pluto_bands_component pil_ext bands dim)
      (List.map
         (project_pluto_bands_component_ip_ext bands dim) ipl_ext).
Proof.
  intros envv pil_ext ipl_ext bands dim Hlen_bands Hflat.
  destruct Hflat as [Hprefix [Hmem [Hnodup Hsorted]]].
  split.
  - intros ip_ext Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip0 [Hip Hin0]].
    subst.
    unfold project_pluto_bands_component_ip_ext.
    destruct (nth_error bands (Tiling.PL.ip_nth_ext ip0));
      simpl; exact (Hprefix _ Hin0).
  - split.
    + intros ip_ext.
      split; intro Hin.
      * apply in_map_iff in Hin.
        destruct Hin as [ip0 [Hip Hin0]].
        subst.
        destruct (Hmem ip0) as [Hfwd _].
        specialize (Hfwd Hin0).
        destruct Hfwd as (pi0 & Hnth0 & Hpref0 & Hbel0 & Hlen0).
        assert (Hband_some :
          nth_error bands (Tiling.PL.ip_nth_ext ip0) <> None).
        {
          apply nth_error_Some.
          rewrite <- Hlen_bands.
          apply nth_error_Some.
          rewrite Hnth0.
          discriminate.
        }
        destruct (nth_error bands (Tiling.PL.ip_nth_ext ip0)) as [band|]
          eqn:Hband; [|contradiction].
        exists (project_pluto_bands_component_pi_ext band dim pi0).
        split.
        -- unfold project_pluto_bands_component_ip_ext.
           rewrite Hband.
           simpl.
           exact
             (nth_error_project_pinstrs_ext_with_pluto_bands_component_local
                pil_ext bands dim (Tiling.PL.ip_nth_ext ip0)
                pi0 band Hnth0 Hband).
        -- split.
           ++ unfold project_pluto_bands_component_ip_ext.
              rewrite Hband.
              simpl.
              exact Hpref0.
           ++ split.
              ** eapply
                   project_pluto_bands_component_ip_ext_belongs_to_ext_local;
                   eauto.
              ** unfold project_pluto_bands_component_ip_ext.
                 rewrite Hband.
                 simpl.
                 exact Hlen0.
      * destruct Hin as
          (pi_proj & Hnth_proj & Hpref_proj & Hbel_proj & Hlen_proj).
        assert (Hn_lt :
          (Tiling.PL.ip_nth_ext ip_ext < List.length pil_ext)%nat).
        {
          assert (Hproj_len :
            List.length
              (project_pinstrs_ext_with_pluto_bands_component
                 pil_ext bands dim) = List.length pil_ext).
          {
            eapply project_pinstrs_ext_with_pluto_bands_component_length.
            exact Hlen_bands.
          }
          assert (Hproj_some :
            nth_error
              (project_pinstrs_ext_with_pluto_bands_component
                 pil_ext bands dim)
              (Tiling.PL.ip_nth_ext ip_ext) <> None).
          {
            rewrite Hnth_proj.
            discriminate.
          }
          apply nth_error_Some in Hproj_some.
          rewrite Hproj_len in Hproj_some.
          exact Hproj_some.
        }
        destruct (nth_error pil_ext (Tiling.PL.ip_nth_ext ip_ext)) as [pi0|]
          eqn:Hnth0.
        2:{ apply nth_error_None in Hnth0. lia. }
        destruct (nth_error bands (Tiling.PL.ip_nth_ext ip_ext)) as [band|]
          eqn:Hband.
        2:{
          apply nth_error_None in Hband.
          rewrite <- Hlen_bands in Hband.
          lia.
        }
        assert (Hpi_proj :
          pi_proj = project_pluto_bands_component_pi_ext band dim pi0).
        {
          pose proof
            (nth_error_project_pinstrs_ext_with_pluto_bands_component_local
               pil_ext bands dim (Tiling.PL.ip_nth_ext ip_ext)
               pi0 band Hnth0 Hband) as Hnth_expected.
          rewrite Hnth_proj in Hnth_expected.
          inversion Hnth_expected.
          reflexivity.
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
          - exact Hpref_proj.
          - split.
            + unfold ip_full.
              eapply
                restore_projected_band_ip_ext_from_pluto_bands_component_project_belongs_to_ext.
              exact Hbel_proj.
            + exact Hlen_proj.
        }
        apply in_map_iff.
        exists ip_full.
        split.
        -- unfold ip_full.
           eapply project_restore_projected_pluto_bands_component_ip_ext;
             eauto.
        -- exact Hin_full.
    + split.
      * apply Tiling.NoDup_map_on.
        -- exact Hnodup.
        -- intros ip1 ip2 Hin1 Hin2 Heq.
           apply project_pluto_bands_component_ip_ext_eq_iff in Heq.
           destruct Heq as [Hnth Hidx].
           eapply flatten_instrs_ext_index_injective_local.
           ++ split; [exact Hprefix|].
              split; [exact Hmem|].
              split; [exact Hnodup| exact Hsorted].
           ++ exact Hin1.
           ++ exact Hin2.
           ++ exact Hnth.
           ++ exact Hidx.
      * apply Sorted_map_project_pluto_bands_component_ip_ext.
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

Lemma nth_error_project_pinstrs_ext_with_pluto_bands_component :
  forall pil_ext bands dim n pi_ext band,
    List.nth_error pil_ext n = Some pi_ext ->
    List.nth_error bands n = Some band ->
    List.nth_error
      (project_pinstrs_ext_with_pluto_bands_component pil_ext bands dim)
      n = Some (project_pluto_bands_component_pi_ext band dim pi_ext).
Proof.
  induction pil_ext as [|pi_ext0 pil_ext' IH];
    intros bands dim n pi_ext band Hpi Hband.
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

Record second_level_band_recipe := {
  slbr_root_rows : Schedule;
  slbr_root_sizes : list Z;
  slbr_child_sizes : list Z;
}.

Definition second_level_child_coeffs
    (prefix_len point_dim: nat) : list Z :=
  repeat 0%Z prefix_len ++ [1%Z] ++ repeat 0%Z point_dim.

Fixpoint second_level_band_recipe_of_links_aux
    (point_dim prefix_len: nat)
    (links: list tile_link) : option second_level_band_recipe :=
  match links with
  | [] =>
      Some
        {| slbr_root_rows := [];
           slbr_root_sizes := [];
           slbr_child_sizes := [] |}
  | root :: child :: links' =>
      let root_expr := tl_expr root in
      let child_expr := tl_expr child in
      if listz_strict_eqb
           (firstn prefix_len (ae_var_coeffs root_expr))
           (repeat 0%Z prefix_len) &&
         listz_strict_eqb
           (ae_var_coeffs child_expr)
           (second_level_child_coeffs prefix_len point_dim) &&
         listz_strict_eqb
           (ae_param_coeffs child_expr)
           (repeat 0%Z (List.length (ae_param_coeffs child_expr))) &&
         Z.eqb (ae_const child_expr) 0%Z
      then
        match
          second_level_band_recipe_of_links_aux
            point_dim (prefix_len + 2)%nat links'
        with
        | Some rest =>
            Some
              {| slbr_root_rows :=
                   schedule_row_of_tile_link_base prefix_len root ::
                   slbr_root_rows rest;
                 slbr_root_sizes :=
                   tl_tile_size root :: slbr_root_sizes rest;
                 slbr_child_sizes :=
                   tl_tile_size child :: slbr_child_sizes rest |}
        | None => None
        end
      else None
  | _ => None
  end.

Definition second_level_band_recipe_of_witness
    (w: statement_tiling_witness) : option second_level_band_recipe :=
  match stw_links w with
  | [] => None
  | links => second_level_band_recipe_of_links_aux (stw_point_dim w) O links
  end.

Definition second_level_recipe_has_strict_zero_rootb
    (recipe: second_level_band_recipe) : bool :=
  existsb Tiling.PL.affine_function_is_zero (slbr_root_rows recipe).

Definition check_pinstr_source_like_second_level_recipeb
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  match second_level_band_recipe_of_witness w with
  | Some recipe =>
      second_level_recipe_has_strict_zero_rootb recipe &&
      listzzs_strict_eqb
        (Tiling.PL.remove_zero_schedule_dims (slbr_root_rows recipe))
        (Tiling.PL.remove_zero_schedule_dims (Tiling.PL.pi_schedule before))
  | None => false
  end.

Fixpoint check_pprog_source_like_second_level_recipesb
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before_pis, ws with
  | [], [] => true
  | before_pi :: before_pis', w :: ws' =>
      check_pinstr_source_like_second_level_recipeb before_pi w &&
      check_pprog_source_like_second_level_recipesb before_pis' ws'
  | _, _ => false
  end.

(** Executable near-miss checks for the source-like classifier. *)
Definition source_like_guard_test_pinstr
    (sched: Schedule) : Tiling.PL.PolyInstr :=
  let pi := Tiling.PL.dummy_pi in
  {|
    Tiling.PL.pi_depth := Tiling.PL.pi_depth pi;
    Tiling.PL.pi_instr := Tiling.PL.pi_instr pi;
    Tiling.PL.pi_poly := Tiling.PL.pi_poly pi;
    Tiling.PL.pi_schedule := sched;
    Tiling.PL.pi_point_witness := Tiling.PL.pi_point_witness pi;
    Tiling.PL.pi_transformation := Tiling.PL.pi_transformation pi;
    Tiling.PL.pi_access_transformation :=
      Tiling.PL.pi_access_transformation pi;
    Tiling.PL.pi_waccess := Tiling.PL.pi_waccess pi;
    Tiling.PL.pi_raccess := Tiling.PL.pi_raccess pi;
  |}.

Definition source_like_guard_test_link
    (coeffs: list Z) (tile_size: Z) : tile_link :=
  {|
    tl_expr :=
      {| ae_var_coeffs := coeffs;
         ae_param_coeffs := [];
         ae_const := 0%Z |};
    tl_tile_size := tile_size;
  |}.

Definition source_like_guard_test_witness
    (root_coeffs: list Z) : statement_tiling_witness :=
  {|
    stw_point_dim := 1;
    stw_links :=
      [source_like_guard_test_link root_coeffs 32%Z;
       source_like_guard_test_link [1%Z; 0%Z] 8%Z];
  |}.

Example source_like_guard_rejects_normalized_schedule_mismatch :
  check_pinstr_source_like_second_level_recipeb
    (source_like_guard_test_pinstr [([1%Z], 0%Z)])
    (source_like_guard_test_witness [0%Z]) = false.
Proof. reflexivity. Qed.

Example source_like_guard_requires_strict_zero_recipe_root :
  check_pinstr_source_like_second_level_recipeb
    (source_like_guard_test_pinstr [([1%Z], 0%Z)])
    (source_like_guard_test_witness [1%Z]) = false.
Proof. reflexivity. Qed.

Inductive second_level_band_recipe_spec (point_dim: nat) :
    nat -> list tile_link -> second_level_band_recipe -> Prop :=
| second_level_band_recipe_spec_nil :
    forall prefix_len,
      second_level_band_recipe_spec point_dim prefix_len []
        {| slbr_root_rows := [];
           slbr_root_sizes := [];
           slbr_child_sizes := [] |}
| second_level_band_recipe_spec_cons :
    forall prefix_len root child links rest,
      firstn prefix_len (ae_var_coeffs (tl_expr root)) =
        repeat 0%Z prefix_len ->
      ae_var_coeffs (tl_expr child) =
        second_level_child_coeffs prefix_len point_dim ->
      ae_param_coeffs (tl_expr child) =
        repeat 0%Z (List.length (ae_param_coeffs (tl_expr child))) ->
      ae_const (tl_expr child) = 0%Z ->
      second_level_band_recipe_spec
        point_dim (prefix_len + 2)%nat links rest ->
      second_level_band_recipe_spec
        point_dim prefix_len (root :: child :: links)
        {| slbr_root_rows :=
             schedule_row_of_tile_link_base prefix_len root ::
             slbr_root_rows rest;
           slbr_root_sizes := tl_tile_size root :: slbr_root_sizes rest;
           slbr_child_sizes := tl_tile_size child :: slbr_child_sizes rest |}.

Lemma second_level_band_recipe_of_links_aux_sound :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_of_links_aux point_dim prefix_len links =
      Some recipe ->
    second_level_band_recipe_spec point_dim prefix_len links recipe.
Proof.
  fix IH 3.
  intros point_dim prefix_len links recipe Hparse.
  destruct links as [|root links].
  - simpl in Hparse.
    inversion Hparse; subst recipe.
    constructor.
  - destruct links as [|child links].
    { simpl in Hparse. discriminate. }
    simpl in Hparse.
    destruct
      (listz_strict_eqb
         (firstn prefix_len (ae_var_coeffs (tl_expr root)))
         (repeat 0%Z prefix_len)) eqn:Hroot; try discriminate.
    destruct
      (listz_strict_eqb
         (ae_var_coeffs (tl_expr child))
         (second_level_child_coeffs prefix_len point_dim)) eqn:Hchild_vars;
      try discriminate.
    destruct
      (listz_strict_eqb
         (ae_param_coeffs (tl_expr child))
         (repeat 0%Z (List.length (ae_param_coeffs (tl_expr child)))))
      eqn:Hchild_params; try discriminate.
    destruct (Z.eqb (ae_const (tl_expr child)) 0%Z) eqn:Hchild_const;
      try discriminate.
    destruct
      (second_level_band_recipe_of_links_aux
         point_dim (prefix_len + 2)%nat links) as [rest|] eqn:Hrest;
      try discriminate.
    inversion Hparse; subst recipe; clear Hparse.
    constructor.
    + eapply listz_strict_eqb_eq; exact Hroot.
    + eapply listz_strict_eqb_eq; exact Hchild_vars.
    + eapply listz_strict_eqb_eq; exact Hchild_params.
    + eapply Z.eqb_eq; exact Hchild_const.
    + eapply IH; exact Hrest.
Qed.

Lemma second_level_band_recipe_of_witness_sound :
  forall w recipe,
    second_level_band_recipe_of_witness w = Some recipe ->
    stw_links w <> [] /\
    second_level_band_recipe_spec (stw_point_dim w) O (stw_links w) recipe.
Proof.
  intros w recipe Hparse.
  unfold second_level_band_recipe_of_witness in Hparse.
  destruct (stw_links w) as [|link links] eqn:Hlinks.
  - discriminate.
  - split; [congruence|].
    eapply second_level_band_recipe_of_links_aux_sound.
    exact Hparse.
Qed.

Lemma second_level_band_recipe_of_witness_rejects_ordinary :
  forall w recipe,
    second_level_band_recipe_of_witness w = Some recipe ->
    check_ordinary_tiling_witnessb w = false.
Proof.
  intros w recipe Hparse.
  destruct (second_level_band_recipe_of_witness_sound _ _ Hparse)
    as [Hnonempty Hspec].
  inversion Hspec as
      [prefix_len
      |prefix_len root child links rest
         Hroot Hchild_vars Hchild_params Hchild_const Hrest]; subst.
  - exfalso.
    apply Hnonempty.
    symmetry.
    exact H0.
  - unfold check_ordinary_tiling_witnessb, schedule_rows_of_links.
    rewrite <- H0.
    simpl.
    rewrite Hchild_vars.
    unfold second_level_child_coeffs.
    simpl.
    reflexivity.
Qed.

Fixpoint interleave_root_child_tiles
    (roots children: list Z) : list Z :=
  match roots, children with
  | root :: roots', child :: children' =>
      root :: child :: interleave_root_child_tiles roots' children'
  | _, _ => []
  end.

Definition second_level_root_tiles
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  List.map
    (fun '(v, sz) => Z.div v sz)
    (List.combine
       (affine_product (slbr_root_rows recipe) (params ++ point))
       (slbr_root_sizes recipe)).

Definition second_level_child_tiles
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  List.map
    (fun '(v, sz) => Z.div v sz)
    (List.combine
       (second_level_root_tiles recipe params point)
       (slbr_child_sizes recipe)).

Definition second_level_schedule_tile_block
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  second_level_child_tiles recipe params point ++
  second_level_root_tiles recipe params point.

Definition second_level_schedule_interleaved_tile_block
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  interleave_root_child_tiles
    (second_level_root_tiles recipe params point)
    (second_level_child_tiles recipe params point).

Lemma affine_product_schedule_row_of_tile_link_base_second_level :
  forall prefix_len prefix point params link,
    List.length prefix = prefix_len ->
    List.length (ae_var_coeffs (tl_expr link)) =
      (prefix_len + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length params ->
    firstn prefix_len (ae_var_coeffs (tl_expr link)) =
      repeat 0%Z prefix_len ->
    affine_product [schedule_row_of_tile_link_base prefix_len link]
      (params ++ point) =
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

Lemma dot_product_second_level_child_coeffs :
  forall prefix point root_value,
    dot_product
      (second_level_child_coeffs (List.length prefix) (List.length point))
      ((prefix ++ [root_value]) ++ point) = root_value.
Proof.
  induction prefix as [|x prefix IH]; intros point root_value.
  - unfold second_level_child_coeffs.
    simpl.
    rewrite TilingWitness.dot_product_repeat_zero_exact by reflexivity.
    lia.
  - unfold second_level_child_coeffs in *.
    simpl.
    eapply IH.
Qed.

Lemma eval_affine_second_level_child :
  forall child prefix point params root_value,
    ae_var_coeffs (tl_expr child) =
      second_level_child_coeffs (List.length prefix) (List.length point) ->
    ae_param_coeffs (tl_expr child) =
      repeat 0%Z (List.length params) ->
    ae_const (tl_expr child) = 0%Z ->
    eval_affine (tl_expr child) ((prefix ++ [root_value]) ++ point) params =
      root_value.
Proof.
  intros child prefix point params root_value Hvars Hparams Hconst.
  unfold eval_affine.
  rewrite Hvars, Hparams, Hconst.
  rewrite dot_product_second_level_child_coeffs.
  rewrite TilingWitness.dot_product_repeat_zero_exact by reflexivity.
  lia.
Qed.

Lemma eval_tile_links_from_second_level_recipe_spec :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    forall prefix point params,
      List.length prefix = prefix_len ->
      List.length point = point_dim ->
      well_formed_tile_links prefix_len point_dim links ->
      Forall
        (fun link =>
           List.length (ae_param_coeffs (tl_expr link)) = List.length params)
        links ->
      eval_tile_links prefix point params links =
      prefix ++
      interleave_root_child_tiles
        (second_level_root_tiles recipe params point)
        (second_level_child_tiles recipe params point).
Proof.
  fix IH 3.
  intros point_dim prefix_len links recipe Hspec
         prefix point params Hprefix_len Hpoint_len Hwf Hparams.
  destruct links as [|root links].
  - inversion Hspec; subst recipe.
    simpl. now rewrite app_nil_r.
  - destruct links as [|child links].
    { inversion Hspec. }
    inversion Hspec as
      [|prefix_len0 root0 child0 links0 rest
         Hroot_zero Hchild_vars Hchild_params Hchild_const Hrest];
      subst root0 child0 links0 recipe.
    simpl in Hwf.
    destruct Hwf as [Hroot_vars [Hchild_vars_len Hwf_rest]].
    inversion Hparams as [|root0 links0 Hroot_params Hparams_tail]; subst.
    inversion Hparams_tail as
      [|child0 links0 Hchild_params_len Hparams_rest]; subst.
    set (root_tile := eval_tile_parent root (prefix ++ point) params).
    assert (Hroot_eval :
      affine_product
        [schedule_row_of_tile_link_base (List.length prefix) root]
        (params ++ point) =
      [eval_affine (tl_expr root) (prefix ++ point) params]).
    {
      eapply affine_product_schedule_row_of_tile_link_base_second_level.
      - reflexivity.
      - exact Hroot_vars.
      - exact Hroot_params.
      - exact Hroot_zero.
    }
    assert (Hchild_eval :
      eval_tile_parent child ((prefix ++ [root_tile]) ++ point) params =
      Z.div root_tile (tl_tile_size child)).
    {
      unfold eval_tile_parent.
      f_equal.
      eapply eval_affine_second_level_child.
      - exact Hchild_vars.
      - rewrite <- Hchild_params_len.
        exact Hchild_params.
      - exact Hchild_const.
    }
    assert (Hprefix_rest :
      List.length (prefix ++ [root_tile; Z.div root_tile (tl_tile_size child)]) =
      (List.length prefix + 2)%nat).
    {
      rewrite app_length.
      simpl. lia.
    }
    assert (Hwf_rest' :
      well_formed_tile_links
        (List.length prefix + 2)%nat (List.length point) links).
    {
      replace (List.length prefix + 2)%nat
        with (S (S (List.length prefix))) by lia.
      exact Hwf_rest.
    }
    pose proof
      (IH _ _ links rest Hrest
         (prefix ++ [root_tile; Z.div root_tile (tl_tile_size child)])
         point params Hprefix_rest eq_refl Hwf_rest' Hparams_rest)
      as IHrest.
    simpl [eval_tile_links].
    fold root_tile.
    rewrite Hchild_eval.
    replace
      ((prefix ++ [root_tile]) ++ [Z.div root_tile (tl_tile_size child)])
      with
      (prefix ++ [root_tile; Z.div root_tile (tl_tile_size child)]) by
      exact (app_assoc prefix [root_tile]
               [Z.div root_tile (tl_tile_size child)]).
    rewrite IHrest.
    unfold second_level_root_tiles,
           second_level_child_tiles in *.
    simpl.
    simpl in Hroot_eval.
    injection Hroot_eval as Hroot_eval_value.
    unfold root_tile, eval_tile_parent.
    rewrite <- Hroot_eval_value.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Definition infer_pinstr_second_level_band
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    : option (pinstr_tiling_band * second_level_band_recipe) :=
  match second_level_band_recipe_of_witness w with
  | Some recipe =>
      match
        find_schedule_block_start
          (Tiling.PL.pi_schedule before)
          (slbr_root_rows recipe)
      with
      | Some start =>
          Some
            ({| ptb_start := start;
                ptb_len := List.length (slbr_root_rows recipe) |},
             recipe)
      | None => None
      end
  | None => None
  end.

Fixpoint infer_pinstr_list_second_level_bands
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band * list second_level_band_recipe) :=
  match before_pis, ws with
  | [], [] => Some ([], [])
  | before_pi :: before_pis', w :: ws' =>
      match infer_pinstr_second_level_band before_pi w,
            infer_pinstr_list_second_level_bands before_pis' ws' with
      | Some (band, recipe), Some (bands, recipes) =>
          Some (band :: bands, recipe :: recipes)
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint check_band_starts_eqb
    (start: nat) (bands: list pinstr_tiling_band) : bool :=
  match bands with
  | [] => true
  | band :: bands' =>
      Nat.eqb (ptb_start band) start && check_band_starts_eqb start bands'
  end.

Definition check_common_band_startb
    (bands: list pinstr_tiling_band) : bool :=
  match bands with
  | [] => true
  | band :: bands' => check_band_starts_eqb (ptb_start band) bands'
  end.

Definition common_band_start (bands: list pinstr_tiling_band) : Prop :=
  exists start, Forall (fun band => ptb_start band = start) bands.

Fixpoint check_second_level_recipe_sizes_eqb
    (root_sizes child_sizes: list Z)
    (recipes: list second_level_band_recipe) : bool :=
  match recipes with
  | [] => true
  | recipe :: recipes' =>
      listz_strict_eqb (slbr_root_sizes recipe) root_sizes &&
      listz_strict_eqb (slbr_child_sizes recipe) child_sizes &&
      check_second_level_recipe_sizes_eqb root_sizes child_sizes recipes'
  end.

Definition check_common_second_level_recipe_sizesb
    (recipes: list second_level_band_recipe) : bool :=
  match recipes with
  | [] => true
  | recipe :: recipes' =>
      check_second_level_recipe_sizes_eqb
        (slbr_root_sizes recipe) (slbr_child_sizes recipe) recipes'
  end.

Definition common_second_level_recipe_sizes
    (recipes: list second_level_band_recipe) : Prop :=
  exists root_sizes child_sizes,
    Forall
      (fun recipe =>
         slbr_root_sizes recipe = root_sizes /\
         slbr_child_sizes recipe = child_sizes)
      recipes.

Lemma check_band_starts_eqb_sound :
  forall start bands,
    check_band_starts_eqb start bands = true ->
    Forall (fun band => ptb_start band = start) bands.
Proof.
  intros start bands Hcheck.
  induction bands as [|band bands IH]; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + apply Nat.eqb_eq. exact Hhead.
    + eapply IH. exact Htail.
Qed.

Lemma check_common_band_startb_sound :
  forall bands,
    check_common_band_startb bands = true ->
    common_band_start bands.
Proof.
  intros bands Hcheck.
  destruct bands as [|band bands].
  - exists O. constructor.
  - exists (ptb_start band).
    constructor; [reflexivity|].
    eapply check_band_starts_eqb_sound.
    exact Hcheck.
Qed.

Lemma check_second_level_recipe_sizes_eqb_sound :
  forall root_sizes child_sizes recipes,
    check_second_level_recipe_sizes_eqb
      root_sizes child_sizes recipes = true ->
    Forall
      (fun recipe =>
         slbr_root_sizes recipe = root_sizes /\
         slbr_child_sizes recipe = child_sizes)
      recipes.
Proof.
  intros root_sizes child_sizes recipes Hcheck.
  induction recipes as [|recipe recipes IH]; simpl in *.
  - constructor.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hroot Hchild] Htail].
    constructor.
    + split; eapply listz_strict_eqb_eq; eauto.
    + eapply IH. exact Htail.
Qed.

Lemma check_common_second_level_recipe_sizesb_sound :
  forall recipes,
    check_common_second_level_recipe_sizesb recipes = true ->
    common_second_level_recipe_sizes recipes.
Proof.
  intros recipes Hcheck.
  destruct recipes as [|recipe recipes].
  - exists [], []. constructor.
  - exists (slbr_root_sizes recipe), (slbr_child_sizes recipe).
    constructor.
    + auto.
    + eapply check_second_level_recipe_sizes_eqb_sound.
      exact Hcheck.
Qed.

Lemma common_second_level_recipe_sizes_nth_error_equal :
  forall recipes i j recipe1 recipe2,
    common_second_level_recipe_sizes recipes ->
    nth_error recipes i = Some recipe1 ->
    nth_error recipes j = Some recipe2 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 /\
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2.
Proof.
  intros recipes i j recipe1 recipe2
         [root_sizes [child_sizes Hsizes]] Hrecipe1 Hrecipe2.
  pose proof
    (Tiling.Forall_nth_error
       _ _ recipes i recipe1 Hsizes Hrecipe1) as Hsizes1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ recipes j recipe2 Hsizes Hrecipe2) as Hsizes2.
  destruct Hsizes1, Hsizes2.
  split; congruence.
Qed.

Fixpoint second_level_root_positions (count: nat) : list nat :=
  match count with
  | O => []
  | S count' =>
      O :: List.map (fun pos => S (S pos)) (second_level_root_positions count')
  end.

Definition second_level_child_positions (count: nat) : list nat :=
  List.map S (second_level_root_positions count).

Definition identity_affine_rows_at
    (total_cols env_size: nat)
    (positions: list nat) : Schedule :=
  List.map
    (fun pos => Tiling.identity_affine_row total_cols (env_size + pos)%nat)
    positions.

Definition stripmine_second_level_schedule_after_env
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  let root_count := ptb_len band in
  let added_dims := (2 * root_count)%nat in
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let prefix := firstn (ptb_start band) lifted in
  let lifted_band := firstn root_count (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + root_count)%nat lifted in
  prefix ++
  identity_affine_rows_at
    total_cols env_size (second_level_child_positions root_count) ++
  identity_affine_rows_at
    total_cols env_size (second_level_root_positions root_count) ++
  lifted_band ++ suffix.

Definition stripmine_second_level_schedule_interleaved_after_env
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  let root_count := ptb_len band in
  let added_dims := (2 * root_count)%nat in
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let prefix := firstn (ptb_start band) lifted in
  let lifted_band := firstn root_count (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + root_count)%nat lifted in
  prefix ++
  Tiling.identity_affine_rows_from total_cols env_size added_dims ++
  lifted_band ++ suffix.

Inductive second_level_schedule_layout : Type :=
| SecondLevelGrouped
| SecondLevelInterleaved.

Definition stripmine_second_level_schedule_after_env_by_layout
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  match layout with
  | SecondLevelGrouped =>
      stripmine_second_level_schedule_after_env env_size before_sched band
  | SecondLevelInterleaved =>
      stripmine_second_level_schedule_interleaved_after_env
        env_size before_sched band
  end.

Definition second_level_schedule_tile_block_by_layout
    (layout: second_level_schedule_layout)
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  match layout with
  | SecondLevelGrouped =>
      second_level_schedule_tile_block recipe params point
  | SecondLevelInterleaved =>
      second_level_schedule_interleaved_tile_block recipe params point
  end.

Definition check_pinstr_second_level_schedule_stripminedb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : bool :=
  check_schedule_with_trailing_zero_paddingb
    (stripmine_second_level_schedule_after_env
       env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Definition check_pinstr_second_level_schedule_interleavedb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : bool :=
  check_schedule_with_trailing_zero_paddingb
    (stripmine_second_level_schedule_interleaved_after_env
       env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Definition check_schedule_up_to_trailing_zero_rowsb
    (expected actual: Schedule) : bool :=
  listzzs_strict_eqb
    (Tiling.PL.drop_trailing_zero_schedule expected)
    (Tiling.PL.drop_trailing_zero_schedule actual).

Definition check_pinstr_second_level_schedule_stripmined_normalizedb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : bool :=
  check_schedule_up_to_trailing_zero_rowsb
    (stripmine_second_level_schedule_after_env
       env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Definition check_pinstr_second_level_schedule_interleaved_normalizedb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : bool :=
  check_schedule_up_to_trailing_zero_rowsb
    (stripmine_second_level_schedule_interleaved_after_env
       env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Fixpoint check_pinstr_list_second_level_schedule_stripminedb
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match before_pis, after_pis, bands with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', band :: bands' =>
      check_pinstr_second_level_schedule_stripminedb
        env_size before_pi after_pi band &&
      check_pinstr_list_second_level_schedule_stripminedb
        env_size before_pis' after_pis' bands'
  | _, _, _ => false
  end.

Fixpoint check_pinstr_list_second_level_schedule_interleavedb
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match before_pis, after_pis, bands with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', band :: bands' =>
      check_pinstr_second_level_schedule_interleavedb
        env_size before_pi after_pi band &&
      check_pinstr_list_second_level_schedule_interleavedb
        env_size before_pis' after_pis' bands'
  | _, _, _ => false
  end.

Definition check_pinstr_list_second_level_schedule_by_layoutb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match layout with
  | SecondLevelGrouped =>
      check_pinstr_list_second_level_schedule_stripminedb
        env_size before_pis after_pis bands
  | SecondLevelInterleaved =>
      check_pinstr_list_second_level_schedule_interleavedb
        env_size before_pis after_pis bands
  end.

Definition check_pinstr_second_level_schedule_symmetricb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : bool :=
  check_schedule_with_symmetric_trailing_zero_paddingb
    (stripmine_second_level_schedule_after_env_by_layout
       layout env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Fixpoint check_pinstr_list_second_level_schedule_symmetricb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match before_pis, after_pis, bands with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', band :: bands' =>
      check_pinstr_second_level_schedule_symmetricb
        layout env_size before_pi after_pi band &&
      check_pinstr_list_second_level_schedule_symmetricb
        layout env_size before_pis' after_pis' bands'
  | _, _, _ => false
  end.

Fixpoint check_pinstr_list_second_level_schedule_variantb
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match before_pis, after_pis, bands with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', band :: bands' =>
      (check_pinstr_second_level_schedule_stripmined_normalizedb
         env_size before_pi after_pi band ||
       check_pinstr_second_level_schedule_interleaved_normalizedb
         env_size before_pi after_pi band) &&
      check_pinstr_list_second_level_schedule_variantb
        env_size before_pis' after_pis' bands'
  | _, _, _ => false
  end.

Definition check_pprog_statementwise_second_level_scheduleb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band * list second_level_band_recipe) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match infer_pinstr_list_second_level_bands before_pis ws with
    | Some (bands, recipes) =>
        if check_pinstr_list_second_level_schedule_variantb
             (List.length before_ctxt) before_pis after_pis bands
        then Some (bands, recipes)
        else None
    | None => None
    end
  else None.

Definition check_pprog_second_level_schedule_stripminedb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band * list second_level_band_recipe) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match infer_pinstr_list_second_level_bands before_pis ws with
    | Some (bands, recipes) =>
        if check_pinstr_list_second_level_schedule_stripminedb
             (List.length before_ctxt) before_pis after_pis bands &&
           check_common_second_level_recipe_sizesb recipes &&
           check_common_band_startb bands
        then Some (bands, recipes)
        else None
    | None => None
    end
  else None.

Definition check_pprog_second_level_schedule_interleavedb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band * list second_level_band_recipe) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match infer_pinstr_list_second_level_bands before_pis ws with
    | Some (bands, recipes) =>
        if check_pinstr_list_second_level_schedule_interleavedb
             (List.length before_ctxt) before_pis after_pis bands &&
           check_common_second_level_recipe_sizesb recipes &&
           check_common_band_startb bands
        then Some (bands, recipes)
        else None
    | None => None
    end
  else None.

Definition check_pprog_second_level_schedule_symmetricb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option
        (list pinstr_tiling_band *
         list second_level_band_recipe *
         second_level_schedule_layout) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match infer_pinstr_list_second_level_bands before_pis ws with
    | Some (bands, recipes) =>
        if check_common_second_level_recipe_sizesb recipes &&
           check_common_band_startb bands
        then
          if check_pinstr_list_second_level_schedule_symmetricb
               SecondLevelGrouped (List.length before_ctxt)
               before_pis after_pis bands
          then Some (bands, recipes, SecondLevelGrouped)
          else if check_pinstr_list_second_level_schedule_symmetricb
                    SecondLevelInterleaved (List.length before_ctxt)
                    before_pis after_pis bands
               then Some (bands, recipes, SecondLevelInterleaved)
               else None
        else None
    | None => None
    end
  else None.

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

Lemma exact_listzzs_cols_skipn_local_component :
  forall cols n rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols (skipn n rows).
Proof.
  intros cols n rows Hcols listz z listzz Hin Heq.
  eapply Hcols; eauto.
  clear Hcols Heq.
  revert rows Hin.
  induction n as [|n IH]; intros rows Hin.
  - exact Hin.
  - destruct rows as [|row rows]; simpl in Hin.
    + contradiction.
    + right. eapply IH; exact Hin.
Qed.

Lemma exact_listzzs_cols_app_local_component :
  forall cols rows1 rows2,
    exact_listzzs_cols cols rows1 ->
    exact_listzzs_cols cols rows2 ->
    exact_listzzs_cols cols (rows1 ++ rows2).
Proof.
  intros cols rows1 rows2 Hrows1 Hrows2 listz z listzz Hin Heq.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - eapply Hrows1; eauto.
  - eapply Hrows2; eauto.
Qed.

Lemma exact_listzzs_cols_prioritize_pluto_band_component_rows :
  forall cols band dim rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols
      (prioritize_pluto_band_component_rows band dim rows).
Proof.
  intros cols band dim rows Hcols.
  unfold prioritize_pluto_band_component_rows.
  eapply exact_listzzs_cols_app_local_component.
  - eapply exact_listzzs_cols_firstn_local; exact Hcols.
  - eapply exact_listzzs_cols_app_local_component.
    + eapply exact_listzzs_cols_firstn_local.
      eapply exact_listzzs_cols_skipn_local_component.
      exact Hcols.
    + exact Hcols.
Qed.

Lemma exact_listzzs_cols_constant_schedule_row_like_zero :
  forall cols rows,
    rows <> [] ->
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols [constant_schedule_row_like rows 0%Z].
Proof.
  intros cols rows Hnonempty Hcols.
  destruct rows as [|[coeffs c] rows]; [contradiction|].
  intros listz z listzz Hin Heq.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; [|contradiction].
  subst listzz.
  simpl in Heq.
  inversion Heq; subst listz z.
  simpl.
  rewrite repeat_length.
  eapply (Hcols coeffs c (coeffs, c)).
  - left. reflexivity.
  - reflexivity.
Qed.

Lemma exact_listzzs_cols_prioritize_pluto_band_component_or_zero_rows :
  forall cols band dim rows,
    rows <> [] ->
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols
      (prioritize_pluto_band_component_or_zero_rows band dim rows).
Proof.
  intros cols band dim rows Hnonempty Hcols.
  unfold prioritize_pluto_band_component_or_zero_rows.
  destruct (Nat.ltb dim (ptb_len band)).
  - eapply exact_listzzs_cols_prioritize_pluto_band_component_rows.
    exact Hcols.
  - eapply exact_listzzs_cols_app_local_component.
    + eapply exact_listzzs_cols_firstn_local; exact Hcols.
    + eapply exact_listzzs_cols_app_local_component.
      * eapply exact_listzzs_cols_constant_schedule_row_like_zero; eauto.
      * exact Hcols.
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

Lemma project_pluto_band_pi_ext_wf_tiling :
  forall env band pi_ext,
    Tiling.PL.wf_pinstr_ext_tiling env pi_ext ->
    Tiling.PL.wf_pinstr_ext_tiling env (project_pluto_band_pi_ext band pi_ext).
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
    + eapply exact_listzzs_cols_firstn_local. exact Hsched1.
    + eapply exact_listzzs_cols_firstn_local. exact Hsched1.
    + exact Hw.
    + exact Hr.
  - exact Htf.
Qed.

Lemma project_pluto_band_component_pi_ext_wf_tiling :
  forall env band dim pi_ext,
    Tiling.PL.wf_pinstr_ext_tiling env pi_ext ->
    Tiling.PL.wf_pinstr_ext_tiling env
      (project_pluto_band_component_pi_ext band dim pi_ext).
Proof.
  intros env band dim pi_ext Hwf.
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
    + eapply exact_listzzs_cols_prioritize_pluto_band_component_rows.
      exact Hsched1.
    + exact Hw.
    + exact Hr.
  - exact Htf.
Qed.

Lemma project_pluto_bands_component_pi_ext_wf_tiling :
  forall env band dim pi_ext,
    Tiling.PL.pi_schedule1_ext pi_ext <> [] ->
    Tiling.PL.wf_pinstr_ext_tiling env pi_ext ->
    Tiling.PL.wf_pinstr_ext_tiling env
      (project_pluto_bands_component_pi_ext band dim pi_ext).
Proof.
  intros env band dim pi_ext Hnonempty Hwf.
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
    + eapply
        exact_listzzs_cols_prioritize_pluto_band_component_or_zero_rows;
        eauto.
    + exact Hw.
    + exact Hr.
  - exact Htf.
Qed.

Lemma project_pinstrs_ext_with_pluto_bands_component_wf_tiling :
  forall env pil_ext bands dim,
    Forall (Tiling.PL.wf_pinstr_ext_tiling env) pil_ext ->
    Forall2
      (fun pi_ext _ => Tiling.PL.pi_schedule1_ext pi_ext <> [])
      pil_ext bands ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (project_pinstrs_ext_with_pluto_bands_component pil_ext bands dim).
Proof.
  intros env pil_ext bands dim Hwf Hnonempty.
  revert Hwf.
  induction Hnonempty as
      [|pi_ext band pil_ext bands Hpi_nonempty Hnonempty IH];
    intros Hwf; simpl.
  - constructor.
  - inversion Hwf as [|pi0 pil0 Hwf_pi Hwf_rest]; subst.
    constructor.
    + eapply project_pluto_bands_component_pi_ext_wf_tiling; eauto.
    + eapply IH; exact Hwf_rest.
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

Lemma project_pinstrs_ext_with_pluto_band_wf_tiling :
  forall env vars before_pis after_pis ws band,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (project_pinstrs_ext_with_pluto_band
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length env) before_pis after_pis ws)
         band).
Proof.
  intros env vars before_pis after_pis ws band
         Hwf_before Hwf_after Hdepths Hwits.
  unfold project_pinstrs_ext_with_pluto_band.
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
  eapply project_pluto_band_pi_ext_wf_tiling.
  eapply Forall_forall; eauto.
Qed.

Lemma project_pinstrs_ext_with_pluto_band_component_wf_tiling :
  forall env vars before_pis after_pis ws band dim,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (project_pinstrs_ext_with_pluto_band_component
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length env) before_pis after_pis ws)
         band dim).
Proof.
  intros env vars before_pis after_pis ws band dim
         Hwf_before Hwf_after Hdepths Hwits.
  unfold project_pinstrs_ext_with_pluto_band_component.
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
  eapply project_pluto_band_component_pi_ext_wf_tiling.
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

Lemma affine_product_identity_affine_rows_at :
  forall total_cols env_size positions idx,
    Forall (fun pos => (S (env_size + pos) <= total_cols)%nat) positions ->
    affine_product (identity_affine_rows_at total_cols env_size positions) idx =
    List.map (fun pos => nth (env_size + pos)%nat idx 0%Z) positions.
Proof.
  intros total_cols env_size positions idx Hpositions.
  induction Hpositions as [|pos positions Hpos Hpositions IH].
  - reflexivity.
  - unfold identity_affine_rows_at in *.
    simpl in *.
    change
      (affine_product
         ([Tiling.identity_affine_row total_cols (env_size + pos)%nat] ++
          List.map
            (fun pos0 =>
               Tiling.identity_affine_row total_cols (env_size + pos0)%nat)
            positions) idx =
       nth (env_size + pos)%nat idx 0%Z ::
       List.map (fun pos0 => nth (env_size + pos0)%nat idx 0%Z) positions).
    rewrite affine_product_app.
    rewrite affine_product_identity_affine_row by exact Hpos.
    rewrite IH.
    reflexivity.
Qed.

Lemma second_level_root_positions_bound :
  forall count pos,
    In pos (second_level_root_positions count) ->
    (S pos < 2 * count)%nat.
Proof.
  induction count as [|count IH]; intros pos Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst pos. lia.
    + apply in_map_iff in Hin.
      destruct Hin as [pos0 [Heq Hin0]].
      subst pos.
      specialize (IH pos0 Hin0).
      lia.
Qed.

Lemma second_level_child_positions_bound :
  forall count pos,
    In pos (second_level_child_positions count) ->
    (pos < 2 * count)%nat.
Proof.
  intros count pos Hin.
  unfold second_level_child_positions in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [pos0 [Heq Hin0]].
  subst pos.
  pose proof (second_level_root_positions_bound _ _ Hin0).
  lia.
Qed.

Lemma map_nth_root_positions_interleave :
  forall roots children,
    List.length roots = List.length children ->
    List.map
      (fun pos => nth pos (interleave_root_child_tiles roots children) 0%Z)
      (second_level_root_positions (List.length roots)) = roots.
Proof.
  induction roots as [|root roots IH]; intros children Hlen.
  - destruct children; [reflexivity|discriminate].
  - destruct children as [|child children]; [discriminate|].
    simpl in Hlen.
    simpl.
    f_equal.
    rewrite List.map_map.
    change
      (List.map
         (fun pos => nth pos (interleave_root_child_tiles roots children) 0%Z)
         (second_level_root_positions (List.length roots)) = roots).
    eapply IH.
    lia.
Qed.

Lemma map_nth_child_positions_interleave :
  forall roots children,
    List.length roots = List.length children ->
    List.map
      (fun pos => nth pos (interleave_root_child_tiles roots children) 0%Z)
      (second_level_child_positions (List.length roots)) = children.
Proof.
  induction roots as [|root roots IH]; intros children Hlen.
  - destruct children; [reflexivity|discriminate].
  - destruct children as [|child children]; [discriminate|].
    simpl in Hlen.
    unfold second_level_child_positions.
    simpl.
    rewrite List.map_map.
    simpl.
    f_equal.
    rewrite List.map_map.
    assert (Hlen_tail : List.length roots = List.length children) by lia.
    pose proof (IH children Hlen_tail) as IHchildren.
    unfold second_level_child_positions in IHchildren.
    rewrite List.map_map in IHchildren.
    exact IHchildren.
Qed.

Lemma interleave_root_child_tiles_length :
  forall roots children,
    List.length roots = List.length children ->
    List.length (interleave_root_child_tiles roots children) =
      (2 * List.length roots)%nat.
Proof.
  induction roots as [|root roots IH]; intros children Hlen.
  - destruct children; simpl in *; try discriminate; lia.
  - destruct children; simpl in *; try discriminate.
    rewrite IH by lia.
    lia.
Qed.

Lemma nth_app_left_local_second_level :
  forall (A: Type) (xs ys: list A) n d,
    (n < List.length xs)%nat ->
    nth n (xs ++ ys) d = nth n xs d.
Proof.
  intros A xs.
  induction xs as [|x xs IH]; intros ys n d Hlt.
  - exfalso. simpl in Hlt. lia.
  - destruct n as [|n]; simpl; auto.
    eapply IH. simpl in Hlt. lia.
Qed.

Lemma nth_app_offset_local_second_level :
  forall (A: Type) (xs ys: list A) n d,
    nth (List.length xs + n)%nat (xs ++ ys) d = nth n ys d.
Proof.
  intros A xs.
  induction xs as [|x xs IH]; intros ys n d; simpl.
  - reflexivity.
  - exact (IH ys n d).
Qed.

Lemma nth_env_added_app :
  forall env_size env added point pos,
    List.length env = env_size ->
    (pos < List.length added)%nat ->
    nth (env_size + pos)%nat (env ++ added ++ point) 0%Z =
      nth pos added 0%Z.
Proof.
  intros env_size env added point pos Henv Hpos.
  replace (env_size + pos)%nat with (List.length env + pos)%nat by lia.
  rewrite nth_app_offset_local_second_level.
  eapply nth_app_left_local_second_level.
  exact Hpos.
Qed.

Lemma affine_product_second_level_root_rows_at :
  forall total_cols env_size env roots children point,
    List.length env = env_size ->
    List.length roots = List.length children ->
    (env_size + 2 * List.length roots <= total_cols)%nat ->
    affine_product
      (identity_affine_rows_at
         total_cols env_size
         (second_level_root_positions (List.length roots)))
      (env ++ interleave_root_child_tiles roots children ++ point) = roots.
Proof.
  intros total_cols env_size env roots children point
         Henv Hlen Hcols.
  rewrite affine_product_identity_affine_rows_at.
  2:{
    apply Forall_forall.
    intros pos Hin.
    pose proof (second_level_root_positions_bound _ _ Hin).
    lia.
  }
  erewrite List.map_ext_in.
  2:{
    intros pos Hin.
    eapply nth_env_added_app.
    - exact Henv.
    - rewrite interleave_root_child_tiles_length by exact Hlen.
      pose proof (second_level_root_positions_bound _ _ Hin).
      lia.
  }
  eapply map_nth_root_positions_interleave.
  exact Hlen.
Qed.

Lemma affine_product_second_level_child_rows_at :
  forall total_cols env_size env roots children point,
    List.length env = env_size ->
    List.length roots = List.length children ->
    (env_size + 2 * List.length roots <= total_cols)%nat ->
    affine_product
      (identity_affine_rows_at
         total_cols env_size
         (second_level_child_positions (List.length roots)))
      (env ++ interleave_root_child_tiles roots children ++ point) = children.
Proof.
  intros total_cols env_size env roots children point
         Henv Hlen Hcols.
  rewrite affine_product_identity_affine_rows_at.
  2:{
    apply Forall_forall.
    intros pos Hin.
    pose proof (second_level_child_positions_bound _ _ Hin).
    lia.
  }
  erewrite List.map_ext_in.
  2:{
    intros pos Hin.
    eapply nth_env_added_app.
    - exact Henv.
    - rewrite interleave_root_child_tiles_length by exact Hlen.
      pose proof (second_level_child_positions_bound _ _ Hin).
      lia.
  }
  eapply map_nth_child_positions_interleave.
  exact Hlen.
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

Lemma stripmine_second_level_schedule_after_env_eval :
  forall env_size before_sched band cols env roots children iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length roots = ptb_len band ->
    List.length roots = List.length children ->
    affine_product
      (stripmine_second_level_schedule_after_env env_size before_sched band)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    children ++ roots ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros env_size before_sched band cols env roots children iters
         Hsched_cols Henv_cols Henv Hroots Hlen.
  unfold stripmine_second_level_schedule_after_env.
  set (root_count := ptb_len band).
  set (added_dims := (2 * root_count)%nat).
  set (lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end).
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted
      (env ++ interleave_root_child_tiles roots children ++ iters) = old_ts).
  {
    subst lifted old_ts added_dims root_count.
    apply Tiling.lift_affine_function_after_env_eval; try assumption.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    lia.
  }
  assert (Htotal_cols : (env_size + added_dims <= total_cols)%nat).
  {
    subst total_cols.
    pose proof
      (lift_schedule_after_env_exact_cols
         cols added_dims env_size before_sched Hsched_cols Henv_cols)
      as Hlift_cols.
    subst lifted.
    destruct
      (Tiling.lift_schedule_after_env added_dims env_size before_sched)
      as [|[coeffs rhs] rows].
    - lia.
    - assert (Hcoeffs : List.length coeffs = (added_dims + cols)%nat).
      {
        eapply Hlift_cols.
        - left. reflexivity.
        - reflexivity.
      }
      lia.
  }
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_firstn.
  rewrite affine_product_firstn.
  rewrite !affine_product_skipn.
  assert (Hroot_count : root_count = List.length roots).
  { subst root_count. lia. }
  rewrite Hroot_count.
  rewrite
    (affine_product_second_level_child_rows_at
       total_cols env_size env roots children iters Henv Hlen).
  2:{ subst added_dims root_count. rewrite Hroots. exact Htotal_cols. }
  rewrite
    (affine_product_second_level_root_rows_at
       total_cols env_size env roots children iters Henv Hlen).
  2:{ subst added_dims root_count. rewrite Hroots. exact Htotal_cols. }
  rewrite Hlift.
  reflexivity.
Qed.

Lemma stripmine_second_level_schedule_interleaved_after_env_eval :
  forall env_size before_sched band cols env roots children iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length roots = ptb_len band ->
    List.length roots = List.length children ->
    affine_product
      (stripmine_second_level_schedule_interleaved_after_env
         env_size before_sched band)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    interleave_root_child_tiles roots children ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros env_size before_sched band cols env roots children iters
         Hsched_cols Henv_cols Henv Hroots Hlen.
  unfold stripmine_second_level_schedule_interleaved_after_env.
  set (root_count := ptb_len band).
  set (added_dims := (2 * root_count)%nat).
  set (lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end).
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted
      (env ++ interleave_root_child_tiles roots children ++ iters) = old_ts).
  {
    subst lifted old_ts added_dims root_count.
    apply Tiling.lift_affine_function_after_env_eval; try assumption.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    lia.
  }
  assert (Htotal_cols : (env_size + added_dims <= total_cols)%nat).
  {
    subst total_cols.
    pose proof
      (lift_schedule_after_env_exact_cols
         cols added_dims env_size before_sched Hsched_cols Henv_cols)
      as Hlift_cols.
    subst lifted.
    destruct
      (Tiling.lift_schedule_after_env added_dims env_size before_sched)
      as [|[coeffs rhs] rows].
    - lia.
    - assert (Hcoeffs : List.length coeffs = (added_dims + cols)%nat).
      {
        eapply Hlift_cols.
        - left. reflexivity.
        - reflexivity.
      }
      lia.
  }
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_firstn.
  rewrite affine_product_firstn.
  rewrite !affine_product_skipn.
  rewrite
    (affine_product_identity_affine_rows_from
       total_cols env_size added_dims
       (env ++ interleave_root_child_tiles roots children ++ iters)).
  2:{ exact Htotal_cols. }
  2:{
    subst added_dims root_count.
    repeat rewrite app_length.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    rewrite Henv, Hroots.
    lia.
  }
  rewrite Hlift.
  rewrite <- Henv.
  assert (Hskip_mid :
    skipn (List.length env)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    interleave_root_child_tiles roots children ++ iters).
  {
    replace
      (env ++ interleave_root_child_tiles roots children ++ iters)
      with
      (env ++ (interleave_root_child_tiles roots children ++ iters))
      by reflexivity.
    rewrite skipn_app_le by lia.
    replace (List.length env - List.length env)%nat with 0%nat by lia.
    simpl.
    reflexivity.
  }
  rewrite Hskip_mid.
  rewrite firstn_app.
  assert (Hadded_len :
    List.length (interleave_root_child_tiles roots children) = added_dims).
  {
    subst added_dims root_count.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    rewrite Hroots.
    reflexivity.
  }
  replace
    (firstn added_dims (interleave_root_child_tiles roots children))
    with (interleave_root_child_tiles roots children).
  2:{
    rewrite <- Hadded_len.
    symmetry.
    apply firstn_all.
  }
  rewrite Hadded_len, Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma stripmine_second_level_schedule_after_env_by_layout_eval :
  forall layout env_size before_sched band cols env roots children iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length roots = ptb_len band ->
    List.length roots = List.length children ->
    affine_product
      (stripmine_second_level_schedule_after_env_by_layout
         layout env_size before_sched band)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    match layout with
    | SecondLevelGrouped => children ++ roots
    | SecondLevelInterleaved => interleave_root_child_tiles roots children
    end ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros layout.
  destruct layout; simpl.
  - intros.
    pose proof
      (stripmine_second_level_schedule_after_env_eval
         env_size before_sched band cols env roots children iters
         H H0 H1 H2 H3) as Heval.
    repeat rewrite app_assoc in Heval.
    repeat rewrite app_assoc.
    exact Heval.
  - intros.
    pose proof
      (stripmine_second_level_schedule_interleaved_after_env_eval
         env_size before_sched band cols env roots children iters
         H H0 H1 H2 H3) as Heval.
    repeat rewrite app_assoc in Heval.
    repeat rewrite app_assoc.
    exact Heval.
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

Lemma check_schedule_with_symmetric_trailing_zero_paddingb_sound :
  forall expected actual,
    check_schedule_with_symmetric_trailing_zero_paddingb expected actual = true ->
    schedule_matches_with_symmetric_trailing_zero_padding expected actual.
Proof.
  intros expected actual Hcheck.
  unfold check_schedule_with_symmetric_trailing_zero_paddingb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hforward | Hreverse].
  - left.
    eapply check_schedule_with_trailing_zero_paddingb_sound.
    exact Hforward.
  - right.
    eapply check_schedule_with_trailing_zero_paddingb_sound.
    exact Hreverse.
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

Lemma infer_pinstr_second_level_band_sound :
  forall before w band recipe,
    infer_pinstr_second_level_band before w = Some (band, recipe) ->
    second_level_band_recipe_spec
      (stw_point_dim w) O (stw_links w) recipe /\
    ptb_len band = List.length (slbr_root_rows recipe) /\
    firstn (ptb_len band)
      (skipn (ptb_start band) (Tiling.PL.pi_schedule before)) =
      slbr_root_rows recipe.
Proof.
  intros before w band recipe Hinfer.
  unfold infer_pinstr_second_level_band in Hinfer.
  destruct (second_level_band_recipe_of_witness w)
    as [recipe0|] eqn:Hrecipe; try discriminate.
  destruct
    (find_schedule_block_start
       (Tiling.PL.pi_schedule before) (slbr_root_rows recipe0))
    as [start|] eqn:Hstart; try discriminate.
  inversion Hinfer; subst band recipe0; clear Hinfer.
  destruct (second_level_band_recipe_of_witness_sound _ _ Hrecipe)
    as [_ Hspec].
  split; [exact Hspec|].
  split; [reflexivity|].
  eapply find_schedule_block_start_sound; exact Hstart.
Qed.

Lemma infer_pinstr_second_level_band_bound :
  forall before w band recipe,
    infer_pinstr_second_level_band before w = Some (band, recipe) ->
    (ptb_start band + ptb_len band <=
     List.length (Tiling.PL.pi_schedule before))%nat.
Proof.
  intros before w band recipe Hinfer.
  unfold infer_pinstr_second_level_band in Hinfer.
  destruct (second_level_band_recipe_of_witness w)
    as [recipe0|] eqn:Hrecipe; try discriminate.
  destruct
    (find_schedule_block_start
       (Tiling.PL.pi_schedule before) (slbr_root_rows recipe0))
    as [start|] eqn:Hstart; try discriminate.
  inversion Hinfer; subst band recipe0; clear Hinfer.
  pose proof (find_schedule_block_start_bound _ _ _ Hstart) as Hstart_bound.
  pose proof (find_schedule_block_start_sound _ _ _ Hstart) as Hblock.
  assert (Hrows_fit :
    (List.length (slbr_root_rows recipe) <=
     List.length (Tiling.PL.pi_schedule before) - start)%nat).
  {
    assert (Hlen_block :
      List.length
        (firstn (List.length (slbr_root_rows recipe))
           (skipn start (Tiling.PL.pi_schedule before))) =
      List.length (slbr_root_rows recipe)).
    {
      rewrite Hblock.
      reflexivity.
    }
    rewrite firstn_length, skipn_length in Hlen_block.
    destruct
      (le_gt_dec (List.length (slbr_root_rows recipe))
         (List.length (Tiling.PL.pi_schedule before) - start)%nat); auto.
    rewrite Nat.min_r in Hlen_block by lia.
    lia.
  }
  simpl.
  lia.
Qed.

Lemma second_level_band_recipe_spec_root_rows_nonempty :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    links <> [] ->
    slbr_root_rows recipe <> [].
Proof.
  intros point_dim prefix_len links recipe Hspec Hlinks.
  destruct Hspec; simpl in *; congruence.
Qed.

Lemma infer_pinstr_second_level_band_positive_len :
  forall before w band recipe,
    infer_pinstr_second_level_band before w = Some (band, recipe) ->
    (0 < ptb_len band)%nat.
Proof.
  intros before w band recipe Hinfer.
  destruct (infer_pinstr_second_level_band_sound _ _ _ _ Hinfer)
    as [Hspec [Hlen _]].
  assert (Hlinks : stw_links w <> []).
  {
    unfold infer_pinstr_second_level_band in Hinfer.
    destruct (second_level_band_recipe_of_witness w)
      as [recipe0|] eqn:Hrecipe; try discriminate.
    destruct
      (find_schedule_block_start
         (Tiling.PL.pi_schedule before) (slbr_root_rows recipe0));
      try discriminate.
    eapply (proj1 (second_level_band_recipe_of_witness_sound _ _ Hrecipe)).
  }
  pose proof
    (second_level_band_recipe_spec_root_rows_nonempty
       _ _ _ _ Hspec Hlinks) as Hrows.
  destruct (slbr_root_rows recipe) as [|row rows].
  - exfalso. apply Hrows. reflexivity.
  - simpl in Hlen. lia.
Qed.

Lemma common_band_start_nth_error_equal :
  forall bands i j band1 band2,
    common_band_start bands ->
    nth_error bands i = Some band1 ->
    nth_error bands j = Some band2 ->
    ptb_start band1 = ptb_start band2.
Proof.
  intros bands i j band1 band2 [start Hstarts] Hband1 Hband2.
  pose proof
    (Tiling.Forall_nth_error
       _ (fun band => ptb_start band = start)
       bands i band1 Hstarts Hband1) as Hstart1.
  pose proof
    (Tiling.Forall_nth_error
       _ (fun band => ptb_start band = start)
       bands j band2 Hstarts Hband2) as Hstart2.
  congruence.
Qed.

Lemma infer_pinstr_list_second_level_bands_nth_error :
  forall before_pis ws bands recipes n before_pi w band recipe,
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error bands n = Some band ->
    nth_error recipes n = Some recipe ->
    infer_pinstr_second_level_band before_pi w = Some (band, recipe).
Proof.
  induction before_pis as [|before_pi0 before_pis IH];
    intros ws bands recipes n before_pi w band recipe
           Hinfer Hbefore Hw Hband Hrecipe.
  - destruct n; discriminate.
  - destruct ws as [|w0 ws]; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_second_level_band before_pi0 w0)
      as [[band0 recipe0]|] eqn:Hhead; try discriminate.
    destruct (infer_pinstr_list_second_level_bands before_pis ws)
      as [[bands0 recipes0]|] eqn:Htail; try discriminate.
    inversion Hinfer; subst bands recipes; clear Hinfer.
    destruct n as [|n].
    + inversion Hbefore; inversion Hw; inversion Hband; inversion Hrecipe; subst.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma infer_pinstr_list_second_level_bands_lengths :
  forall before_pis ws bands recipes,
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length bands /\
    List.length before_pis = List.length recipes.
Proof.
  induction before_pis as [|before_pi before_pis IH];
    intros ws bands recipes Hinfer.
  - destruct ws; simpl in Hinfer; try discriminate.
    inversion Hinfer; subst. auto.
  - destruct ws as [|w ws]; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_second_level_band before_pi w); try discriminate.
    destruct p as [band recipe].
    destruct (infer_pinstr_list_second_level_bands before_pis ws)
      as [[bands' recipes']|] eqn:Htail; try discriminate.
    inversion Hinfer; subst bands recipes.
    specialize (IH ws bands' recipes' Htail).
    simpl. lia.
Qed.

Lemma check_pinstr_list_second_level_schedule_stripminedb_nth_error :
  forall env_size before_pis after_pis bands n before_pi after_pi band,
    check_pinstr_list_second_level_schedule_stripminedb
      env_size before_pis after_pis bands = true ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error bands n = Some band ->
    schedule_matches_with_trailing_zero_padding
      (stripmine_second_level_schedule_after_env
         env_size (Tiling.PL.pi_schedule before_pi) band)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  induction before_pis as [|before_pi0 before_pis IH];
    intros after_pis bands n before_pi after_pi band
           Hcheck Hbefore Hafter Hband.
  - destruct n; discriminate.
  - destruct after_pis as [|after_pi0 after_pis];
      destruct bands as [|band0 bands]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct n as [|n].
    + inversion Hbefore; inversion Hafter; inversion Hband; subst.
      eapply check_schedule_with_trailing_zero_paddingb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma check_pinstr_list_second_level_schedule_interleavedb_nth_error :
  forall env_size before_pis after_pis bands n before_pi after_pi band,
    check_pinstr_list_second_level_schedule_interleavedb
      env_size before_pis after_pis bands = true ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error bands n = Some band ->
    schedule_matches_with_trailing_zero_padding
      (stripmine_second_level_schedule_interleaved_after_env
         env_size (Tiling.PL.pi_schedule before_pi) band)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  induction before_pis as [|before_pi0 before_pis IH];
    intros after_pis bands n before_pi after_pi band
           Hcheck Hbefore Hafter Hband.
  - destruct n; discriminate.
  - destruct after_pis as [|after_pi0 after_pis];
      destruct bands as [|band0 bands]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct n as [|n].
    + inversion Hbefore; inversion Hafter; inversion Hband; subst.
      eapply check_schedule_with_trailing_zero_paddingb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma check_pinstr_list_second_level_schedule_by_layoutb_nth_error :
  forall layout env_size before_pis after_pis bands n
         before_pi after_pi band,
    check_pinstr_list_second_level_schedule_by_layoutb
      layout env_size before_pis after_pis bands = true ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error bands n = Some band ->
    schedule_matches_with_trailing_zero_padding
      (stripmine_second_level_schedule_after_env_by_layout
         layout env_size (Tiling.PL.pi_schedule before_pi) band)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  intros layout.
  destruct layout; simpl.
  - intros.
    eapply check_pinstr_list_second_level_schedule_stripminedb_nth_error;
      eauto.
  - intros.
    eapply check_pinstr_list_second_level_schedule_interleavedb_nth_error;
      eauto.
Qed.

Lemma check_pinstr_list_second_level_schedule_symmetricb_nth_error :
  forall layout env_size before_pis after_pis bands n
         before_pi after_pi band,
    check_pinstr_list_second_level_schedule_symmetricb
      layout env_size before_pis after_pis bands = true ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error bands n = Some band ->
    schedule_matches_with_symmetric_trailing_zero_padding
      (stripmine_second_level_schedule_after_env_by_layout
         layout env_size (Tiling.PL.pi_schedule before_pi) band)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  intros layout env_size before_pis.
  induction before_pis as [|before_pi0 before_pis IH];
    intros after_pis bands n before_pi after_pi band
           Hcheck Hbefore Hafter Hband.
  - destruct n; discriminate.
  - destruct after_pis as [|after_pi0 after_pis];
      destruct bands as [|band0 bands]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct n as [|n].
    + inversion Hbefore; inversion Hafter; inversion Hband; subst.
      eapply check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma check_pinstr_list_second_level_schedule_by_layoutb_implies_symmetricb :
  forall layout env_size before_pis after_pis bands,
    check_pinstr_list_second_level_schedule_by_layoutb
      layout env_size before_pis after_pis bands = true ->
    check_pinstr_list_second_level_schedule_symmetricb
      layout env_size before_pis after_pis bands = true.
Proof.
  intros layout.
  destruct layout; intros env_size before_pis;
    induction before_pis as [|before_pi before_pis IH];
    intros after_pis bands Hcheck.
  - destruct after_pis, bands; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi after_pis];
      destruct bands as [|band bands]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    apply andb_true_iff; split.
    + unfold check_pinstr_second_level_schedule_symmetricb,
             check_schedule_with_symmetric_trailing_zero_paddingb.
      unfold check_pinstr_second_level_schedule_stripminedb in Hhead.
      simpl. rewrite Hhead. reflexivity.
    + eapply IH. exact Htail.
  - destruct after_pis, bands; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi after_pis];
      destruct bands as [|band bands]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    apply andb_true_iff; split.
    + unfold check_pinstr_second_level_schedule_symmetricb,
             check_schedule_with_symmetric_trailing_zero_paddingb.
      unfold check_pinstr_second_level_schedule_interleavedb in Hhead.
      simpl. rewrite Hhead. reflexivity.
    + eapply IH. exact Htail.
Qed.

Lemma check_pprog_second_level_schedule_stripminedb_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes,
    check_pprog_second_level_schedule_stripminedb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = Some (bands, recipes) ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) /\
    check_pinstr_list_second_level_schedule_stripminedb
      (List.length before_ctxt) before_pis after_pis bands = true /\
    common_second_level_recipe_sizes recipes /\
    common_band_start bands.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes Hcheck.
  unfold check_pprog_second_level_schedule_stripminedb in Hcheck.
  destruct
    (TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars) eqn:Hctxt;
    try discriminate.
  destruct (infer_pinstr_list_second_level_bands before_pis ws)
    as [[bands0 recipes0]|] eqn:Hinfer; try discriminate.
  destruct
    (check_pinstr_list_second_level_schedule_stripminedb
       (List.length before_ctxt) before_pis after_pis bands0)
    eqn:Hsched; try discriminate.
  destruct (check_common_second_level_recipe_sizesb recipes0)
    eqn:Hsizes; try discriminate.
  destruct (check_common_band_startb bands0) eqn:Hstart; try discriminate.
  inversion Hcheck; subst bands0 recipes0; clear Hcheck.
  repeat split; auto.
  - eapply check_common_second_level_recipe_sizesb_sound.
    exact Hsizes.
  - eapply check_common_band_startb_sound.
    exact Hstart.
Qed.

Lemma check_pprog_second_level_schedule_interleavedb_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes,
    check_pprog_second_level_schedule_interleavedb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = Some (bands, recipes) ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) /\
    check_pinstr_list_second_level_schedule_interleavedb
      (List.length before_ctxt) before_pis after_pis bands = true /\
    common_second_level_recipe_sizes recipes /\
    common_band_start bands.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes Hcheck.
  unfold check_pprog_second_level_schedule_interleavedb in Hcheck.
  destruct
    (TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars) eqn:Hctxt;
    try discriminate.
  destruct (infer_pinstr_list_second_level_bands before_pis ws)
    as [[bands0 recipes0]|] eqn:Hinfer; try discriminate.
  destruct
    (check_pinstr_list_second_level_schedule_interleavedb
       (List.length before_ctxt) before_pis after_pis bands0)
    eqn:Hsched; try discriminate.
  destruct (check_common_second_level_recipe_sizesb recipes0)
    eqn:Hsizes; try discriminate.
  destruct (check_common_band_startb bands0) eqn:Hstart; try discriminate.
  inversion Hcheck; subst bands0 recipes0; clear Hcheck.
  repeat split; auto.
  - eapply check_common_second_level_recipe_sizesb_sound.
    exact Hsizes.
  - eapply check_common_band_startb_sound.
    exact Hstart.
Qed.

Lemma check_pprog_second_level_schedule_symmetricb_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes layout,
    check_pprog_second_level_schedule_symmetricb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = Some (bands, recipes, layout) ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) /\
    check_pinstr_list_second_level_schedule_symmetricb
      layout (List.length before_ctxt) before_pis after_pis bands = true /\
    common_second_level_recipe_sizes recipes /\
    common_band_start bands.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes layout Hcheck.
  unfold check_pprog_second_level_schedule_symmetricb in Hcheck.
  destruct
    (TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars) eqn:Hctxt;
    try discriminate.
  destruct (infer_pinstr_list_second_level_bands before_pis ws)
    as [[bands0 recipes0]|] eqn:Hinfer; try discriminate.
  destruct (check_common_second_level_recipe_sizesb recipes0)
    eqn:Hsizes; try discriminate.
  destruct (check_common_band_startb bands0) eqn:Hstart; try discriminate.
  destruct
    (check_pinstr_list_second_level_schedule_symmetricb
       SecondLevelGrouped (List.length before_ctxt)
       before_pis after_pis bands0)
    eqn:Hgrouped.
  - inversion Hcheck; subst bands recipes layout.
    repeat split; auto.
    + eapply check_common_second_level_recipe_sizesb_sound. exact Hsizes.
    + eapply check_common_band_startb_sound. exact Hstart.
  - destruct
      (check_pinstr_list_second_level_schedule_symmetricb
         SecondLevelInterleaved (List.length before_ctxt)
         before_pis after_pis bands0)
      eqn:Hinterleaved; try discriminate.
    inversion Hcheck; subst bands recipes layout.
    repeat split; auto.
    + eapply check_common_second_level_recipe_sizesb_sound. exact Hsizes.
    + eapply check_common_band_startb_sound. exact Hstart.
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

Fixpoint check_pinstr_list_schedule_len_eq
    (pis: list Tiling.PL.PolyInstr)
    (len: nat) : bool :=
  match pis with
  | [] => true
  | pi :: pis' =>
      Nat.eqb (List.length (Tiling.PL.pi_schedule pi)) len &&
      check_pinstr_list_schedule_len_eq pis' len
  end.

Definition check_uniform_schedule_arityb
    (pis: list Tiling.PL.PolyInstr) : bool :=
  match pis with
  | [] => true
  | pi :: pis' =>
      check_pinstr_list_schedule_len_eq
        pis' (List.length (Tiling.PL.pi_schedule pi))
  end.

Lemma check_pinstr_list_schedule_len_eq_sound :
  forall pis len,
    check_pinstr_list_schedule_len_eq pis len = true ->
    Forall (fun pi => List.length (Tiling.PL.pi_schedule pi) = len) pis.
Proof.
  induction pis as [|pi pis IH]; intros len Hcheck; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + apply Nat.eqb_eq. exact Hhead.
    + eapply IH. exact Htail.
Qed.

Lemma check_uniform_schedule_arityb_sound :
  forall pis,
    check_uniform_schedule_arityb pis = true ->
    uniform_schedule_arity pis.
Proof.
  intros pis Hcheck.
  destruct pis as [|pi pis].
  - exists 0%nat. constructor.
  - exists (List.length (Tiling.PL.pi_schedule pi)).
    constructor.
    + reflexivity.
    + eapply check_pinstr_list_schedule_len_eq_sound.
      exact Hcheck.
Qed.

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

Definition instr_point_ext_band_component_decreases_at
    (band: pinstr_tiling_band)
    (dim: nat)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  exists x y,
    (dim < ptb_len band)%nat /\
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau1)
      (ptb_start band + dim)%nat = Some x /\
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau2)
      (ptb_start band + dim)%nat = Some y /\
    (x > y)%Z.

Definition instr_point_ext_band_component_decreases
    (band: pinstr_tiling_band)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  exists dim,
    instr_point_ext_band_component_decreases_at band dim tau1 tau2.

Lemma firstn_one_skipn_of_nth_error_local :
  forall (A: Type) (xs: list A) n x,
    nth_error xs n = Some x ->
    firstn 1 (skipn n xs) = [x].
Proof.
  intros A xs.
  induction xs as [|y ys IH]; intros n x Hnth.
  - destruct n; discriminate.
  - destruct n as [|n].
    + simpl in Hnth. inversion Hnth. reflexivity.
    + simpl in Hnth. simpl. eapply IH; exact Hnth.
Qed.

Lemma nth_error_firstn_local :
  forall (A: Type) limit (xs: list A) n,
    (n < limit)%nat ->
    nth_error (firstn limit xs) n = nth_error xs n.
Proof.
  intros A limit.
  induction limit as [|limit IH]; intros xs n Hlt; [lia|].
  destruct xs as [|x xs]; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|].
  simpl.
  eapply IH.
  lia.
Qed.

Lemma nth_error_skipn_local :
  forall (A: Type) start (xs: list A) n,
    nth_error (skipn start xs) n = nth_error xs (start + n)%nat.
Proof.
  intros A start.
  induction start as [|start IH]; intros xs n.
  - reflexivity.
  - destruct xs as [|x xs].
    + rewrite skipn_nil. destruct n; reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_error_band_block_to_full :
  forall band (ts: list Z) dim x,
    (dim < ptb_len band)%nat ->
    nth_error
      (firstn (ptb_len band) (skipn (ptb_start band) ts))
      dim = Some x ->
    nth_error ts (ptb_start band + dim)%nat = Some x.
Proof.
  intros band ts dim x Hdim Hnth.
  rewrite nth_error_firstn_local in Hnth by exact Hdim.
  rewrite nth_error_skipn_local in Hnth.
  exact Hnth.
Qed.

Lemma project_pluto_band_component_ip_ext_old_sched_lt :
  forall band dim tau1 tau2,
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_pluto_band_component_ip_ext band dim tau1)
      (project_pluto_band_component_ip_ext band dim tau2).
Proof.
  intros band dim tau1 tau2 Hold.
  unfold Tiling.PL.instr_point_ext_old_sched_lt,
         project_pluto_band_component_ip_ext in *.
  simpl in *.
  exact Hold.
Qed.

Lemma project_pluto_band_component_ip_ext_new_sched_ge :
  forall band dim tau1 tau2,
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_component_decreases_at band dim tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_pluto_band_component_ip_ext band dim tau1)
      (project_pluto_band_component_ip_ext band dim tau2).
Proof.
  intros band dim tau1 tau2 Hprefix
         [x [y [Hdim [Hx [Hy Hgt]]]]].
  unfold Tiling.PL.instr_point_ext_new_sched_ge,
         project_pluto_band_component_ip_ext.
  simpl.
  unfold prioritize_pluto_band_component_ts.
  assert (Hone1 :
    firstn 1
      (skipn (ptb_start band + dim)
         (Tiling.PL.ip_time_stamp1_ext tau1)) = [x]).
  {
    eapply firstn_one_skipn_of_nth_error_local; exact Hx.
  }
  assert (Hone2 :
    firstn 1
      (skipn (ptb_start band + dim)
         (Tiling.PL.ip_time_stamp1_ext tau2)) = [y]).
  {
    eapply firstn_one_skipn_of_nth_error_local; exact Hy.
  }
  rewrite Hone1, Hone2.
  unfold instr_point_ext_same_band_slice,
         instr_point_ext_band_prefix_ts in Hprefix.
  rewrite Hprefix.
  rewrite lex_compare_app by reflexivity.
  rewrite lex_compare_reflexive.
  rewrite lex_compare_app by reflexivity.
  right.
  assert (Hcmp : Z.compare x y = Gt).
  {
    apply Z.compare_gt_iff.
    lia.
  }
  simpl.
  rewrite Hcmp.
  reflexivity.
Qed.

Lemma project_pluto_bands_component_ip_ext_eq_single_if_present :
  forall bands band dim tau,
    nth_error bands (Tiling.PL.ip_nth_ext tau) = Some band ->
    (dim < ptb_len band)%nat ->
    project_pluto_bands_component_ip_ext bands dim tau =
    project_pluto_band_component_ip_ext band dim tau.
Proof.
  intros bands band dim tau Hband Hdim.
  unfold project_pluto_bands_component_ip_ext,
         project_pluto_band_component_ip_ext,
         prioritize_pluto_band_component_or_zero_ts.
  rewrite Hband.
  assert (Hltb : Nat.ltb dim (ptb_len band) = true).
  {
    apply Nat.ltb_lt.
    exact Hdim.
  }
  rewrite Hltb.
  destruct tau; reflexivity.
Qed.

Lemma project_pluto_bands_component_ip_ext_old_sched_lt :
  forall bands dim tau1 tau2,
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_pluto_bands_component_ip_ext bands dim tau1)
      (project_pluto_bands_component_ip_ext bands dim tau2).
Proof.
  intros bands dim tau1 tau2 Hold.
  unfold Tiling.PL.instr_point_ext_old_sched_lt,
         project_pluto_bands_component_ip_ext in *.
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau1));
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau2));
  destruct tau1, tau2; simpl in *; exact Hold.
Qed.

Lemma project_pluto_bands_component_ip_ext_new_sched_ge :
  forall bands band dim tau1 tau2,
    nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band ->
    nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band ->
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_component_decreases_at band dim tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_pluto_bands_component_ip_ext bands dim tau1)
      (project_pluto_bands_component_ip_ext bands dim tau2).
Proof.
  intros bands band dim tau1 tau2 Hband1 Hband2 Hprefix Hcomponent.
  destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
  rewrite
    (project_pluto_bands_component_ip_ext_eq_single_if_present
       bands band dim tau1 Hband1 Hdim).
  rewrite
    (project_pluto_bands_component_ip_ext_eq_single_if_present
       bands band dim tau2 Hband2 Hdim).
  eapply project_pluto_band_component_ip_ext_new_sched_ge.
  - exact Hprefix.
  - exists x, y.
    repeat split; assumption.
Qed.

Lemma firstn_add_local :
  forall (A: Type) n m (xs: list A),
    firstn (n + m) xs =
    firstn n xs ++ firstn m (skipn n xs).
Proof.
  intros A n.
  induction n as [|n IH]; intros m xs.
  - reflexivity.
  - destruct xs as [|x xs]; simpl.
    + destruct m; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma project_pluto_band_ip_ext_old_sched_lt :
  forall band tau1 tau2,
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_order_lt band tau1 tau2 ->
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_pluto_band_ip_ext band tau1)
      (project_pluto_band_ip_ext band tau2).
Proof.
  intros band tau1 tau2 Hprefix Hband.
  unfold Tiling.PL.instr_point_ext_old_sched_lt,
         project_pluto_band_ip_ext.
  simpl.
  rewrite !firstn_add_local.
  unfold instr_point_ext_same_band_slice,
         instr_point_ext_band_prefix_ts in Hprefix.
  unfold instr_point_ext_band_order_lt,
         instr_point_ext_band_block_ts in Hband.
  rewrite Hprefix.
  rewrite lex_compare_app by reflexivity.
  rewrite lex_compare_reflexive.
  exact Hband.
Qed.

Lemma project_pluto_band_ip_ext_new_sched_ge :
  forall band tau1 tau2,
    instr_point_ext_same_band_slice band tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_pluto_band_ip_ext band tau1)
      (project_pluto_band_ip_ext band tau2).
Proof.
  intros band tau1 tau2 Hprefix.
  unfold Tiling.PL.instr_point_ext_new_sched_ge,
         project_pluto_band_ip_ext.
  simpl.
  unfold instr_point_ext_same_band_slice,
         instr_point_ext_band_prefix_ts in Hprefix.
  rewrite Hprefix.
  left.
  apply lex_compare_reflexive.
Qed.

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
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_component_decreases band tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Definition pprog_pluto_componentwise_permutable_band
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  pprog_pluto_permutable_band envv before_pis after_pis ws band.

Definition pprog_pluto_componentwise_permutable_bands
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  forall ipl_ext tau1 tau2 band,
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band ->
    nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_component_decreases band tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Lemma pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge :
  forall envv before_pis after_pis ws bands,
    pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands ->
    (forall ipl_ext tau1 tau2,
       Tiling.PL.flatten_instrs_ext
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length envv) before_pis after_pis ws)
         ipl_ext ->
       In tau1 ipl_ext ->
       In tau2 ipl_ext ->
       Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
       Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
       exists band,
         nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
         nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
         instr_point_ext_same_band_slice band tau1 tau2 /\
         instr_point_ext_band_component_decreases band tau1 tau2) ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros envv before_pis after_pis ws bands Hperm Hlocal.
  unfold pprog_tiling_reordering_safe, pprog_permutable_tiling_bands.
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (Hlocal ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew)
    as [band [Hband1 [Hband2 [Hprefix Hcomponent]]]].
  eapply Hperm; eauto.
Qed.

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

Lemma check_common_tiling_band_recipe_withb_sound :
  forall sizes ws,
    check_common_tiling_band_recipe_withb sizes ws = true ->
    common_tiling_band_recipe_with sizes ws.
Proof.
  intros sizes ws.
  induction ws as [|w ws IH]; intros Hcheck; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + unfold tile_sizes_of_witness in Hhead.
      symmetry.
      eapply listz_strict_eqb_eq; exact Hhead.
    + eapply IH; exact Htail.
Qed.

Lemma check_common_tiling_band_recipeb_sound :
  forall ws,
    check_common_tiling_band_recipeb ws = true ->
    common_tiling_band_recipe ws.
Proof.
  intros ws Hcheck.
  destruct ws as [|w ws].
  - exists []; constructor.
  - exists (tile_sizes_of_witness w).
    constructor.
    + reflexivity.
    + eapply check_common_tiling_band_recipe_withb_sound.
      exact Hcheck.
Qed.

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

Lemma preserved_equal_length_prefix_reversal_implies_prefix_eq :
  forall prefix1 prefix2 old_rest1 old_rest2 new_rest1 new_rest2,
    List.length prefix1 = List.length prefix2 ->
    lex_compare (prefix1 ++ old_rest1) (prefix2 ++ old_rest2) = Lt ->
    lex_compare (prefix1 ++ new_rest1) (prefix2 ++ new_rest2) <> Lt ->
    prefix1 = prefix2.
Proof.
  intros prefix1 prefix2 old_rest1 old_rest2 new_rest1 new_rest2
         Hlen Hold Hnew.
  destruct (lex_compare prefix1 prefix2) eqn:Hprefix.
  - eapply lex_compare_eq_same_length_implies_eq_local_band; eauto.
  - exfalso. apply Hnew.
    rewrite lex_compare_app by exact Hlen.
    rewrite Hprefix.
    reflexivity.
  - exfalso. rewrite lex_compare_app in Hold by exact Hlen.
    rewrite Hprefix in Hold.
    discriminate.
Qed.

(** The synthetic component schedule characterizes exactly the local Pluto
    band obligation when the selected component exists in both timestamps.
    The length hypotheses are essential because [lex_compare] zero-extends
    lists of different lengths. *)
Lemma project_pluto_band_component_ip_ext_new_sched_ge_iff :
  forall band dim tau1 tau2,
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    (dim < ptb_len band)%nat ->
    (ptb_start band + dim <
       List.length (Tiling.PL.ip_time_stamp1_ext tau1))%nat ->
    (ptb_start band + dim <
       List.length (Tiling.PL.ip_time_stamp1_ext tau2))%nat ->
    (Tiling.PL.instr_point_ext_new_sched_ge
       (project_pluto_band_component_ip_ext band dim tau1)
       (project_pluto_band_component_ip_ext band dim tau2) <->
     instr_point_ext_same_band_slice band tau1 tau2 /\
     instr_point_ext_band_component_decreases_at band dim tau1 tau2).
Proof.
  intros band dim tau1 tau2 Hold Hdim Hlen1 Hlen2.
  split.
  - intro Hnew.
    assert (Hx_some :
      nth_error
        (Tiling.PL.ip_time_stamp1_ext tau1)
        (ptb_start band + dim) <> None).
    {
      apply nth_error_Some.
      lia.
    }
    assert (Hy_some :
      nth_error
        (Tiling.PL.ip_time_stamp1_ext tau2)
        (ptb_start band + dim) <> None).
    {
      apply nth_error_Some.
      lia.
    }
    destruct
      (nth_error
         (Tiling.PL.ip_time_stamp1_ext tau1)
         (ptb_start band + dim)) as [x|] eqn:Hx;
      [|contradiction].
    destruct
      (nth_error
         (Tiling.PL.ip_time_stamp1_ext tau2)
         (ptb_start band + dim)) as [y|] eqn:Hy;
      [|contradiction].
    assert (Hone1 :
      firstn 1
        (skipn (ptb_start band + dim)
           (Tiling.PL.ip_time_stamp1_ext tau1)) = [x]).
    {
      eapply firstn_one_skipn_of_nth_error_local; exact Hx.
    }
    assert (Hone2 :
      firstn 1
        (skipn (ptb_start band + dim)
           (Tiling.PL.ip_time_stamp1_ext tau2)) = [y]).
    {
      eapply firstn_one_skipn_of_nth_error_local; exact Hy.
    }
    assert (Hnew_not_lt :
      lex_compare
        (prioritize_pluto_band_component_ts band dim
           (Tiling.PL.ip_time_stamp1_ext tau1))
        (prioritize_pluto_band_component_ts band dim
           (Tiling.PL.ip_time_stamp1_ext tau2)) <> Lt).
    {
      unfold Tiling.PL.instr_point_ext_new_sched_ge,
             project_pluto_band_component_ip_ext in Hnew.
      simpl in Hnew.
      destruct Hnew; congruence.
    }
    unfold prioritize_pluto_band_component_ts in Hnew_not_lt.
    rewrite Hone1, Hone2 in Hnew_not_lt.
    assert (Hprefix :
      firstn (ptb_start band)
        (Tiling.PL.ip_time_stamp1_ext tau1) =
      firstn (ptb_start band)
        (Tiling.PL.ip_time_stamp1_ext tau2)).
    {
      eapply preserved_equal_length_prefix_reversal_implies_prefix_eq
        with
          (old_rest1 :=
             skipn (ptb_start band)
               (Tiling.PL.ip_time_stamp1_ext tau1))
          (old_rest2 :=
             skipn (ptb_start band)
               (Tiling.PL.ip_time_stamp1_ext tau2))
          (new_rest1 := [x] ++ Tiling.PL.ip_time_stamp1_ext tau1)
          (new_rest2 := [y] ++ Tiling.PL.ip_time_stamp1_ext tau2).
      - rewrite !firstn_length. lia.
      - rewrite !firstn_skipn. exact Hold.
      - exact Hnew_not_lt.
    }
    split.
    + exact Hprefix.
    + exists x, y.
      repeat split; try assumption.
      assert (Hxy : (x > y)%Z).
      {
        rewrite Hprefix in Hnew_not_lt.
        rewrite lex_compare_app in Hnew_not_lt by reflexivity.
        rewrite lex_compare_reflexive in Hnew_not_lt.
        simpl in Hnew_not_lt.
        destruct (Z.compare x y) eqn:Hcmp.
        - exfalso.
          apply Hnew_not_lt.
          exact Hold.
        - exfalso.
          apply Hnew_not_lt.
          reflexivity.
        - apply Z.compare_gt_iff in Hcmp.
          lia.
      }
      exact Hxy.
  - intros [Hprefix Hcomponent].
    eapply project_pluto_band_component_ip_ext_new_sched_ge; eauto.
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

Definition listz_pointwise_le (xs ys: list Z) : Prop :=
  Forall2 Z.le xs ys.

Lemma listz_pointwise_le_length :
  forall xs ys,
    listz_pointwise_le xs ys ->
    List.length xs = List.length ys.
Proof.
  intros xs ys Hle.
  unfold listz_pointwise_le in Hle.
  eapply Forall2_length; exact Hle.
Qed.

Lemma listz_pointwise_le_lex_compare_eq_or_lt :
  forall xs ys,
    listz_pointwise_le xs ys ->
    lex_compare xs ys = Eq \/ lex_compare xs ys = Lt.
Proof.
  intros xs ys Hle.
  unfold listz_pointwise_le in Hle.
  induction Hle as [|x y xs ys Hxy Htail IH].
  - left. reflexivity.
  - simpl.
    destruct (Z.compare x y) eqn:Hcmp.
    + destruct IH as [Heq | Hlt].
      * left. exact Heq.
      * right. exact Hlt.
    + right. reflexivity.
    + apply Z.compare_gt_iff in Hcmp.
      lia.
Qed.

Lemma no_listz_component_decrease_implies_pointwise_le :
  forall xs ys,
    List.length xs = List.length ys ->
    ~ (exists dim x y,
         nth_error xs dim = Some x /\
         nth_error ys dim = Some y /\
         (x > y)%Z) ->
    listz_pointwise_le xs ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen Hnone.
  - destruct ys; [constructor|discriminate].
  - destruct ys as [|y ys]; [discriminate|].
    constructor.
    + assert (Hnot_gt : ~ (x > y)%Z).
      {
        intro Hgt.
        apply Hnone.
        exists O, x, y.
        simpl. repeat split; assumption.
      }
      lia.
    + eapply IH.
      * simpl in Hlen. lia.
      * intros [dim [x' [y' [Hx [Hy Hgt]]]]].
        apply Hnone.
        exists (S dim), x', y'.
        simpl. repeat split; assumption.
Qed.

Lemma listz_component_decrease_or_pointwise_le :
  forall xs ys,
    List.length xs = List.length ys ->
    (exists dim x y,
       nth_error xs dim = Some x /\
       nth_error ys dim = Some y /\
       (x > y)%Z) \/
    listz_pointwise_le xs ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; [right; constructor|discriminate].
  - destruct ys as [|y ys]; [discriminate|].
    destruct (Z_gt_dec x y) as [Hgt|Hnot_gt].
    + left. exists O, x, y. simpl. repeat split; assumption.
    + specialize (IH ys ltac:(simpl in Hlen; lia)).
      destruct IH as [Hdecrease|Htail].
      * left.
        destruct Hdecrease as [dim [x' [y' [Hx [Hy Hgt]]]]].
        exists (S dim), x', y'. simpl. repeat split; assumption.
      * right. constructor; [lia|exact Htail].
Qed.

Lemma stripmined_reversal_implies_decreasing_band_component :
  forall prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2,
    List.length prefix1 = List.length prefix2 ->
    List.length band1 = List.length band2 ->
    (band1 = band2 -> tiles1 = tiles2) ->
    (listz_pointwise_le band1 band2 ->
     listz_pointwise_le tiles1 tiles2) ->
    lex_compare
      (prefix1 ++ band1 ++ suffix1)
      (prefix2 ++ band2 ++ suffix2) = Lt ->
    lex_compare
      (prefix1 ++ tiles1 ++ band1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band2 ++ suffix2) <> Lt ->
    prefix1 = prefix2 /\
    exists dim x y,
      nth_error band1 dim = Some x /\
      nth_error band2 dim = Some y /\
      (x > y)%Z.
Proof.
  intros prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2
         Hprefix_len Hband_len Htiles_eq Htiles_mono Hold Hnew.
  destruct
    (stripmined_reversal_implies_prefix_eq_and_band_lt
       prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Hold Hnew)
    as [Hprefix_eq Hband_lt].
  split; [exact Hprefix_eq|].
  destruct
    (listz_component_decrease_or_pointwise_le band1 band2 Hband_len)
    as [Hdecrease | Hband_le].
  - exact Hdecrease.
  - exfalso.
    pose proof (Htiles_mono Hband_le) as Htiles_le.
    pose proof
      (listz_pointwise_le_lex_compare_eq_or_lt
         tiles1 tiles2 Htiles_le) as Htiles_cmp.
    pose proof (listz_pointwise_le_length _ _ Htiles_le) as Htiles_len.
    apply Hnew.
    subst prefix2.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive.
    rewrite lex_compare_app by exact Htiles_len.
    destruct Htiles_cmp as [Htiles_cmp | Htiles_cmp];
      rewrite Htiles_cmp.
    + rewrite lex_compare_app by exact Hband_len.
      rewrite Hband_lt.
      reflexivity.
    + reflexivity.
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

Lemma positive_tile_sizes_map :
  forall links,
    Forall (fun link => (0 < tl_tile_size link)%Z) links ->
    Forall (fun size => (0 < size)%Z) (List.map tl_tile_size links).
Proof.
  intros links Hpositive.
  induction Hpositive; simpl; constructor; auto.
Qed.

Lemma map_div_combine_preserves_pointwise_le :
  forall xs ys sizes,
    listz_pointwise_le xs ys ->
    Forall (fun size => (0 < size)%Z) sizes ->
    List.length xs = List.length sizes ->
    listz_pointwise_le
      (List.map
         (fun '(v, sz) => Z.div v sz)
         (List.combine xs sizes))
      (List.map
         (fun '(v, sz) => Z.div v sz)
         (List.combine ys sizes)).
Proof.
  intros xs ys sizes Hle.
  unfold listz_pointwise_le in *.
  revert sizes.
  induction Hle as [|x y xs ys Hxy Htail IH];
    intros sizes Hpositive Hlen.
  - destruct sizes; [constructor|discriminate].
  - destruct sizes as [|size sizes]; [discriminate|].
    inversion Hpositive as [|size0 sizes0 Hsize Hsizes]; subst.
    simpl.
    constructor.
    + apply Z.div_le_mono; assumption.
    + eapply IH.
      * exact Hsizes.
      * simpl in Hlen. lia.
Qed.

Lemma listz_pointwise_le_app :
  forall xs1 xs2 ys1 ys2,
    listz_pointwise_le xs1 ys1 ->
    listz_pointwise_le xs2 ys2 ->
    listz_pointwise_le (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  intros xs1 xs2 ys1 ys2 Hle1 Hle2.
  unfold listz_pointwise_le in *.
  induction Hle1; simpl.
  - exact Hle2.
  - constructor; auto.
Qed.

Lemma second_level_band_recipe_spec_lengths :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    List.length (slbr_root_rows recipe) =
      List.length (slbr_root_sizes recipe) /\
    List.length (slbr_root_rows recipe) =
      List.length (slbr_child_sizes recipe).
Proof.
  intros point_dim prefix_len links recipe Hspec.
  induction Hspec; simpl; intuition lia.
Qed.

Lemma second_level_band_recipe_spec_positive_sizes :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links ->
    Forall (fun size => (0 < size)%Z) (slbr_root_sizes recipe) /\
    Forall (fun size => (0 < size)%Z) (slbr_child_sizes recipe).
Proof.
  intros point_dim prefix_len links recipe Hspec Hpositive.
  induction Hspec.
  - split; constructor.
  - inversion Hpositive as [|root0 links0 Hroot_pos Hpositive_tail]; subst.
    inversion Hpositive_tail as
      [|child0 links0 Hchild_pos Hpositive_rest]; subst.
    specialize (IHHspec Hpositive_rest).
    destruct IHHspec as [Hroots Hchildren].
    split; constructor; assumption.
Qed.

Lemma second_level_root_tiles_length :
  forall recipe params point,
    List.length (slbr_root_rows recipe) =
      List.length (slbr_root_sizes recipe) ->
    List.length (second_level_root_tiles recipe params point) =
      List.length (slbr_root_sizes recipe).
Proof.
  intros recipe params point Hlen.
  unfold second_level_root_tiles, affine_product.
  rewrite List.map_length, combine_length, List.map_length, Hlen.
  apply Nat.min_id.
Qed.

Lemma second_level_root_tiles_pointwise_le :
  forall recipe params point1 point2,
    List.length (slbr_root_rows recipe) =
      List.length (slbr_root_sizes recipe) ->
    Forall (fun size => (0 < size)%Z) (slbr_root_sizes recipe) ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe) (params ++ point1))
      (affine_product (slbr_root_rows recipe) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_root_tiles recipe params point1)
      (second_level_root_tiles recipe params point2).
Proof.
  intros recipe params point1 point2 Hlen Hpositive Hle.
  unfold second_level_root_tiles.
  eapply map_div_combine_preserves_pointwise_le; eauto.
  unfold affine_product.
  rewrite List.map_length.
  exact Hlen.
Qed.

Lemma second_level_child_tiles_pointwise_le :
  forall recipe params point1 point2,
    List.length (slbr_root_rows recipe) =
      List.length (slbr_root_sizes recipe) ->
    List.length (slbr_root_rows recipe) =
      List.length (slbr_child_sizes recipe) ->
    Forall (fun size => (0 < size)%Z) (slbr_root_sizes recipe) ->
    Forall (fun size => (0 < size)%Z) (slbr_child_sizes recipe) ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe) (params ++ point1))
      (affine_product (slbr_root_rows recipe) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_child_tiles recipe params point1)
      (second_level_child_tiles recipe params point2).
Proof.
  intros recipe params point1 point2 Hroot_len Hchild_len
         Hroot_positive Hchild_positive Hle.
  unfold second_level_child_tiles.
  eapply map_div_combine_preserves_pointwise_le.
  - eapply second_level_root_tiles_pointwise_le; eauto.
  - exact Hchild_positive.
  - rewrite second_level_root_tiles_length by exact Hroot_len.
    lia.
Qed.

Lemma second_level_schedule_tile_block_pointwise_le :
  forall point_dim prefix_len links recipe params point1 point2,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe) (params ++ point1))
      (affine_product (slbr_root_rows recipe) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_tile_block recipe params point1)
      (second_level_schedule_tile_block recipe params point2).
Proof.
  intros point_dim prefix_len links recipe params point1 point2
         Hspec Hpositive Hle.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec)
    as [Hroot_len Hchild_len].
  destruct
    (second_level_band_recipe_spec_positive_sizes _ _ _ _ Hspec Hpositive)
    as [Hroot_positive Hchild_positive].
  unfold second_level_schedule_tile_block.
  eapply listz_pointwise_le_app.
  - eapply second_level_child_tiles_pointwise_le; eauto.
  - eapply second_level_root_tiles_pointwise_le; eauto.
Qed.

Lemma second_level_schedule_tile_block_eq :
  forall recipe params point1 point2,
    affine_product (slbr_root_rows recipe) (params ++ point1) =
      affine_product (slbr_root_rows recipe) (params ++ point2) ->
    second_level_schedule_tile_block recipe params point1 =
      second_level_schedule_tile_block recipe params point2.
Proof.
  intros recipe params point1 point2 Heq.
  unfold second_level_schedule_tile_block,
         second_level_child_tiles,
         second_level_root_tiles.
  now rewrite Heq.
Qed.

Lemma second_level_schedule_tile_block_eq_common_sizes :
  forall recipe1 recipe2 params point1 point2,
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    affine_product (slbr_root_rows recipe1) (params ++ point1) =
      affine_product (slbr_root_rows recipe2) (params ++ point2) ->
    second_level_schedule_tile_block recipe1 params point1 =
      second_level_schedule_tile_block recipe2 params point2.
Proof.
  intros recipe1 recipe2 params point1 point2
         Hroot_sizes Hchild_sizes Hroots.
  unfold second_level_schedule_tile_block,
         second_level_child_tiles,
         second_level_root_tiles.
  rewrite Hroots, Hroot_sizes, Hchild_sizes.
  reflexivity.
Qed.

Lemma second_level_schedule_tile_block_pointwise_le_common_sizes :
  forall point_dim1 prefix_len1 links1 recipe1
         recipe2 params point1 point2,
    second_level_band_recipe_spec
      point_dim1 prefix_len1 links1 recipe1 ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links1 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe1) (params ++ point1))
      (affine_product (slbr_root_rows recipe2) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_tile_block recipe1 params point1)
      (second_level_schedule_tile_block recipe2 params point2).
Proof.
  intros point_dim1 prefix_len1 links1 recipe1 recipe2
         params point1 point2 Hspec1 Hpositive1
         Hroot_sizes Hchild_sizes Hband_le.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_len1 Hchild_len1].
  destruct
    (second_level_band_recipe_spec_positive_sizes
       _ _ _ _ Hspec1 Hpositive1)
    as [Hroot_positive1 Hchild_positive1].
  assert (Hroot_le :
    listz_pointwise_le
      (second_level_root_tiles recipe1 params point1)
      (second_level_root_tiles recipe2 params point2)).
  {
    unfold second_level_root_tiles.
    rewrite <- Hroot_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    unfold affine_product.
    rewrite List.map_length.
    exact Hroot_len1.
  }
  assert (Hchild_le :
    listz_pointwise_le
      (second_level_child_tiles recipe1 params point1)
      (second_level_child_tiles recipe2 params point2)).
  {
    unfold second_level_child_tiles.
    rewrite <- Hchild_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    rewrite second_level_root_tiles_length by exact Hroot_len1.
    lia.
  }
  unfold second_level_schedule_tile_block.
  eapply listz_pointwise_le_app; eauto.
Qed.

Lemma interleave_root_child_tiles_pointwise_le :
  forall roots1 roots2 children1 children2,
    listz_pointwise_le roots1 roots2 ->
    listz_pointwise_le children1 children2 ->
    listz_pointwise_le
      (interleave_root_child_tiles roots1 children1)
      (interleave_root_child_tiles roots2 children2).
Proof.
  intros roots1 roots2 children1 children2 Hroots.
  unfold listz_pointwise_le in *.
  revert children1 children2.
  induction Hroots as [|root1 root2 roots1 roots2 Hroot Hroots IH];
    intros children1 children2 Hchildren.
  - inversion Hchildren; subst; constructor.
  - destruct Hchildren as [|child1 child2 children1 children2
                            Hchild Hchildren].
    + simpl. constructor.
    + simpl.
      constructor; [exact Hroot|].
      constructor; [exact Hchild|].
      eapply IH. exact Hchildren.
Qed.

Lemma second_level_schedule_interleaved_tile_block_eq_common_sizes :
  forall recipe1 recipe2 params point1 point2,
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    affine_product (slbr_root_rows recipe1) (params ++ point1) =
      affine_product (slbr_root_rows recipe2) (params ++ point2) ->
    second_level_schedule_interleaved_tile_block recipe1 params point1 =
      second_level_schedule_interleaved_tile_block recipe2 params point2.
Proof.
  intros recipe1 recipe2 params point1 point2
         Hroot_sizes Hchild_sizes Hroots.
  unfold second_level_schedule_interleaved_tile_block,
         second_level_child_tiles,
         second_level_root_tiles.
  rewrite Hroots, Hroot_sizes, Hchild_sizes.
  reflexivity.
Qed.

Lemma second_level_schedule_interleaved_tile_block_pointwise_le_common_sizes :
  forall point_dim1 prefix_len1 links1 recipe1
         recipe2 params point1 point2,
    second_level_band_recipe_spec
      point_dim1 prefix_len1 links1 recipe1 ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links1 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe1) (params ++ point1))
      (affine_product (slbr_root_rows recipe2) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_interleaved_tile_block recipe1 params point1)
      (second_level_schedule_interleaved_tile_block recipe2 params point2).
Proof.
  intros point_dim1 prefix_len1 links1 recipe1 recipe2
         params point1 point2 Hspec1 Hpositive1
         Hroot_sizes Hchild_sizes Hband_le.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_len1 Hchild_len1].
  destruct
    (second_level_band_recipe_spec_positive_sizes
       _ _ _ _ Hspec1 Hpositive1)
    as [Hroot_positive1 Hchild_positive1].
  assert (Hroot_le :
    listz_pointwise_le
      (second_level_root_tiles recipe1 params point1)
      (second_level_root_tiles recipe2 params point2)).
  {
    unfold second_level_root_tiles.
    rewrite <- Hroot_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    unfold affine_product.
    rewrite List.map_length.
    exact Hroot_len1.
  }
  assert (Hchild_le :
    listz_pointwise_le
      (second_level_child_tiles recipe1 params point1)
      (second_level_child_tiles recipe2 params point2)).
  {
    unfold second_level_child_tiles.
    rewrite <- Hchild_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    rewrite second_level_root_tiles_length by exact Hroot_len1.
    lia.
  }
  unfold second_level_schedule_interleaved_tile_block.
  eapply interleave_root_child_tiles_pointwise_le; eauto.
Qed.

Lemma second_level_schedule_tile_block_by_layout_eq_common_sizes :
  forall layout recipe1 recipe2 params point1 point2,
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    affine_product (slbr_root_rows recipe1) (params ++ point1) =
      affine_product (slbr_root_rows recipe2) (params ++ point2) ->
    second_level_schedule_tile_block_by_layout
      layout recipe1 params point1 =
    second_level_schedule_tile_block_by_layout
      layout recipe2 params point2.
Proof.
  intros layout.
  destruct layout; simpl; intros.
  - eapply second_level_schedule_tile_block_eq_common_sizes; eauto.
  - eapply second_level_schedule_interleaved_tile_block_eq_common_sizes; eauto.
Qed.

Lemma second_level_schedule_tile_block_by_layout_pointwise_le_common_sizes :
  forall layout point_dim1 prefix_len1 links1 recipe1
         recipe2 params point1 point2,
    second_level_band_recipe_spec
      point_dim1 prefix_len1 links1 recipe1 ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links1 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe1) (params ++ point1))
      (affine_product (slbr_root_rows recipe2) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_tile_block_by_layout
         layout recipe1 params point1)
      (second_level_schedule_tile_block_by_layout
         layout recipe2 params point2).
Proof.
  intros layout.
  destruct layout; simpl; intros.
  - eapply second_level_schedule_tile_block_pointwise_le_common_sizes; eauto.
  - eapply
      second_level_schedule_interleaved_tile_block_pointwise_le_common_sizes;
      eauto.
Qed.

Lemma common_recipe_band_pointwise_le_implies_tiles_pointwise_le :
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
    Forall (fun link => (0 < tl_tile_size link)%Z) (stw_links w1) ->
    listz_pointwise_le
      (affine_product rows1 (params ++ point1))
      (affine_product rows2 (params ++ point2)) ->
    listz_pointwise_le
      (eval_tile_links [] point1 params (stw_links w1))
      (eval_tile_links [] point2 params (stw_links w2)).
Proof.
  intros w1 w2 point1 point2 params rows1 rows2 sizes
         Hpoint1 Hpoint2 Hrows1 Hrows2 Hsizes1 Hsizes2
         Hwf1 Hwf2 Hparams1 Hparams2 Hpositive Hle.
  rewrite (eval_tile_links_from_schedule_rows
             w1 point1 params rows1 sizes
             Hpoint1 Hrows1 Hsizes1 Hwf1 Hparams1).
  rewrite (eval_tile_links_from_schedule_rows
             w2 point2 params rows2 sizes
             Hpoint2 Hrows2 Hsizes2 Hwf2 Hparams2).
  eapply map_div_combine_preserves_pointwise_le.
  - exact Hle.
  - rewrite <- Hsizes1.
    eapply positive_tile_sizes_map; exact Hpositive.
  - unfold affine_product.
    rewrite List.map_length.
    pose proof (schedule_rows_of_links_length _ _ Hrows1) as Hrows_len.
    rewrite Hrows_len.
    rewrite <- Hsizes1.
    rewrite List.map_length.
    reflexivity.
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

Lemma is_eq_app_repeat_zero :
  forall xs n,
    is_eq (xs ++ repeat 0%Z n) xs = true.
Proof.
  intros xs n.
  rewrite <- (app_nil_r xs) at 2.
  rewrite is_eq_app by reflexivity.
  rewrite is_eq_reflexive.
  simpl.
  rewrite is_eq_nil_right.
  apply repeat_zero_is_null.
Qed.

Lemma schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq :
  forall expected actual idx,
    schedule_matches_with_symmetric_trailing_zero_padding expected actual ->
    is_eq (affine_product actual idx) (affine_product expected idx) = true.
Proof.
  intros expected actual idx [Hforward | Hreverse].
  - destruct Hforward as [cols [extra_rows Hactual]].
    subst actual.
    rewrite affine_product_pad_schedule_with_zero_rows.
    apply is_eq_app_repeat_zero.
  - destruct Hreverse as [cols [extra_rows Hexpected]].
    subst expected.
    rewrite affine_product_pad_schedule_with_zero_rows.
    rewrite is_eq_commutative.
    apply is_eq_app_repeat_zero.
Qed.

Lemma lex_compare_app_repeat_zero :
  forall xs ys n m,
    lex_compare
      (xs ++ repeat 0%Z n)
      (ys ++ repeat 0%Z m) =
    lex_compare xs ys.
Proof.
  intros xs ys n m.
  transitivity (lex_compare xs (ys ++ repeat 0%Z m)).
  - apply lex_compare_left_eq.
    apply is_eq_app_repeat_zero.
  - apply lex_compare_right_eq.
    apply is_eq_app_repeat_zero.
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

(** Direct executable checker for the Pluto band condition.  Unlike the
    reduction-based checker below, this constructs the bad-pair region
    explicitly and does not synthesize a second schedule.  The direct runtime
    dispatcher invokes this checker for structurally recognized tilings. *)
Definition make_pluto_band_component_guard_polys
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat)
    : option (list polyhedron * list polyhedron) :=
  let dom_dim1 := (env_size + Tiling.PL.pi_depth_ext pi1)%nat in
  let dom_dim2 := (env_size + Tiling.PL.pi_depth_ext pi2)%nat in
  let sched1 := Tiling.PL.pi_schedule1_ext pi1 in
  let sched2 := Tiling.PL.pi_schedule1_ext pi2 in
  match nth_error sched1 (ptb_start band + dim),
        nth_error sched2 (ptb_start band + dim) with
  | Some row1, Some row2 =>
      let old_order := make_poly_lt sched1 sched2 dom_dim1 dom_dim2 [] in
      let same_prefix :=
        make_poly_eq
          (firstn (ptb_start band) sched1)
          (firstn (ptb_start band) sched2)
          dom_dim1 dom_dim2 [] in
      let component_decreases := make_constr_gt row1 row2 in
      Some (old_order, [[component_decreases] ++ same_prefix])
  | _, _ => None
  end.

Lemma make_pluto_band_component_guard_polys_old_order_sound :
  forall pi1 pi2 band dim env_size old_order bad_component p1 p2,
    make_pluto_band_component_guard_polys
      pi1 pi2 band dim env_size = Some (old_order, bad_component) ->
    List.length p1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length p2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    lex_compare
      (affine_product (Tiling.PL.pi_schedule1_ext pi1) p1)
      (affine_product (Tiling.PL.pi_schedule1_ext pi2) p2) = Lt ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      old_order.
Proof.
  intros pi1 pi2 band dim env_size old_order bad_component p1 p2
         Hmake Hlen1 Hlen2 Hcols Hold.
  unfold make_pluto_band_component_guard_polys in Hmake.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi1) (ptb_start band + dim));
    try discriminate.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi2) (ptb_start band + dim));
    try discriminate.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  eapply make_poly_lt_correct; eauto.
Qed.

Lemma make_pluto_band_component_guard_polys_bad_component_sound :
  forall pi1 pi2 band dim env_size old_order bad_component p1 p2,
    make_pluto_band_component_guard_polys
      pi1 pi2 band dim env_size = Some (old_order, bad_component) ->
    List.length p1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length p2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat
      (Tiling.PL.pi_schedule1_ext pi2) ->
    affine_product
      (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1)) p1 =
    affine_product
      (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2)) p2 ->
    (exists row1 row2,
       nth_error
         (Tiling.PL.pi_schedule1_ext pi1)
         (ptb_start band + dim) = Some row1 /\
       nth_error
         (Tiling.PL.pi_schedule1_ext pi2)
         (ptb_start band + dim) = Some row2 /\
       (Linalg.dot_product (fst row1) p1 + snd row1 >
        Linalg.dot_product (fst row2) p2 + snd row2)%Z) ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      bad_component.
Proof.
  intros pi1 pi2 band dim env_size old_order bad_component p1 p2
         Hmake Hlen1 Hlen2 Hcols1 Hcols2 Hprefix
         [row1 [row2 [Hrow1 [Hrow2 Hcomponent]]]].
  unfold make_pluto_band_component_guard_polys in Hmake.
  rewrite Hrow1, Hrow2 in Hmake.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  destruct row1 as [v1 c1].
  destruct row2 as [v2 c2].
  simpl in Hcomponent.
  assert (Hv1 :
    List.length v1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    eapply Hcols1.
    - eapply nth_error_In. exact Hrow1.
    - reflexivity.
  }
  assert (Hprefix_poly :
    in_poly (p1 ++ p2)
      (make_poly_eq
         (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1))
         (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2))
         (env_size + Tiling.PL.pi_depth_ext pi1)%nat
         (env_size + Tiling.PL.pi_depth_ext pi2)%nat []) = true).
  {
    apply
      (proj2
         (make_poly_eq_correct_true
            (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1))
            (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2))
            (env_size + Tiling.PL.pi_depth_ext pi1)%nat
            (env_size + Tiling.PL.pi_depth_ext pi2)%nat
            p1 p2 Hlen1 Hlen2
            (exact_listzzs_cols_firstn_local
               _ _ _ Hcols1))).
    rewrite Hprefix.
    apply veq_refl.
  }
  assert (Hcomponent_poly :
    satisfies_constraint
      (p1 ++ p2)
      (make_constr_gt (v1, c1) (v2, c2)) = true).
  {
    apply
      (proj2
         (make_constr_gt_correct p1 p2 v1 v2 c1 c2
            (eq_trans Hlen1 (eq_sym Hv1)))).
    exact Hcomponent.
  }
  apply Exists_cons_hd.
  change
    (satisfies_constraint
       (p1 ++ p2) (make_constr_gt (v1, c1) (v2, c2)) &&
     in_poly
       (p1 ++ p2)
       (make_poly_eq
          (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1))
          (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2))
          (env_size + Tiling.PL.pi_depth_ext pi1)%nat
          (env_size + Tiling.PL.pi_depth_ext pi2)%nat []) = true).
  rewrite Hcomponent_poly, Hprefix_poly.
  reflexivity.
Qed.

Lemma make_pluto_band_component_guard_polys_point_sound :
  forall env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim
         old_order bad_component ip1 ip2,
    make_pluto_band_component_guard_polys
      pi1 pi2 band dim (List.length env) =
      Some (old_order, bad_component) ->
    Tiling.PL.wf_pinstr_ext_tiling env pi1 ->
    Tiling.PL.wf_pinstr_ext_tiling env pi2 ->
    List.length env = List.length envv ->
    Tiling.PL.flatten_instr_nth_ext envv nth1 pi1 ipl1 ->
    Tiling.PL.flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    instr_point_ext_same_band_slice band ip1 ip2 ->
    instr_point_ext_band_component_decreases_at band dim ip1 ip2 ->
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      old_order /\
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      bad_component.
Proof.
  intros env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim
         old_order bad_component ip1 ip2
         Hmake Hwf1 Hwf2 Henv Hflat1 Hflat2 Hin1 Hin2
         Hold Hprefix Hcomponent.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth1 pi1 ipl1 ip1 Hflat1 Hin1) as Hts1.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth2 pi2 ipl2 ip2 Hflat2 Hin2) as Hts2.
  assert (Hidx1 :
    List.length (Tiling.PL.ip_index_ext ip1) =
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hidx2 :
    List.length (Tiling.PL.ip_index_ext ip2) =
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hcols1 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1)).
  {
    pose proof
      (Tiling.PL.wf_pinstr_ext_tiling_implies_wf_pinstr_ext
         env pi1 Hwf1) as Hwf.
    firstorder.
  }
  assert (Hcols2 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat
      (Tiling.PL.pi_schedule1_ext pi2)).
  {
    pose proof
      (Tiling.PL.wf_pinstr_ext_tiling_implies_wf_pinstr_ext
         env pi2 Hwf2) as Hwf.
    firstorder.
  }
  split.
  - eapply make_pluto_band_component_guard_polys_old_order_sound;
      eauto.
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hts1, Hts2 in Hold.
    exact Hold.
  - eapply make_pluto_band_component_guard_polys_bad_component_sound;
      eauto.
    + unfold instr_point_ext_same_band_slice,
             instr_point_ext_band_prefix_ts in Hprefix.
      rewrite Hts1, Hts2 in Hprefix.
      rewrite !affine_product_firstn_local.
      exact Hprefix.
    + destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
      rewrite Hts1 in Hx.
      rewrite Hts2 in Hy.
      unfold affine_product in Hx, Hy.
      rewrite nth_error_map_iff in Hx, Hy.
      destruct Hx as [row1 [Hrow1 Hx]].
      destruct Hy as [row2 [Hrow2 Hy]].
      subst x y.
      exists row1, row2.
      repeat split; assumption.
Qed.

Definition validate_two_instrs_pluto_band_component_direct
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  match
    make_pluto_band_component_guard_polys pi1 pi2 band dim env_size
  with
  | None => pure false
  | Some (old_order, bad_component) =>
      BandAffine.validate_two_instrs_under_guards
        pi1 pi2 env_size old_order bad_component
  end.

Fixpoint validate_instr_and_list_pluto_band_component_direct
    (pi: Tiling.PL.PolyInstr_ext)
    (pis: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  match pis with
  | [] => pure true
  | pi' :: pis' =>
      BIND forward <-
        validate_two_instrs_pluto_band_component_direct
          pi pi' band dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instrs_pluto_band_component_direct
            pi' pi band dim env_size -;
        if backward then
          validate_instr_and_list_pluto_band_component_direct
            pi pis' band dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_list_pluto_band_component_direct
    (pis: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  match pis with
  | [] => pure true
  | pi :: pis' =>
      BIND self <-
        validate_two_instrs_pluto_band_component_direct
          pi pi band dim env_size -;
      if self then
        BIND cross <-
          validate_instr_and_list_pluto_band_component_direct
            pi pis' band dim env_size -;
        if cross then
          validate_instr_list_pluto_band_component_direct
            pis' band dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_list_pluto_band_components_direct_from
    (pis: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_instr_list_pluto_band_component_direct
          pis band dim env_size -;
      if component_ok then
        validate_instr_list_pluto_band_components_direct_from
          pis band remaining' (S dim) env_size
      else pure false
  end.

Definition check_pinstr_list_pluto_permutable_band_direct
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : imp bool :=
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      env_size before_pis after_pis ws in
  let aligned :=
    Nat.eqb (List.length before_pis) (List.length after_pis) &&
    Nat.eqb (List.length before_pis) (List.length ws) &&
    Nat.eqb (List.length before_pis) (List.length pis) in
  let valid_access := BandAffine.check_valid_access pis in
  BIND res <-
    validate_instr_list_pluto_band_components_direct_from
      pis band (ptb_len band) O env_size -;
  pure (aligned && res && valid_access).

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

Fixpoint check_pinstr_list_cross_validate_tiling
    (pil_ext: list Tiling.PL.PolyInstr_ext)
    (env_size: nat) : imp bool :=
  match pil_ext with
  | [] => pure true
  | pi_ext :: pil_ext' =>
      BIND res <- BandAffine.validate_instr_and_list pi_ext pil_ext' env_size -;
      if res then
        check_pinstr_list_cross_validate_tiling pil_ext' env_size
      else pure false
  end.

Definition check_pinstr_list_pluto_permutable_band_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : imp bool :=
  let pil_ext :=
    project_pinstrs_ext_with_pluto_band
      (Tiling.compose_tiling_pinstrs_ext_from_after
         env_size before_pis after_pis ws)
      band in
  let valid_access := BandAffine.check_valid_access pil_ext in
  BIND res <- BandAffine.validate_instr_list (rev pil_ext) env_size -;
  pure (res && valid_access).

Definition check_pinstr_list_pluto_permutable_band_component_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band)
    (dim: nat) : imp bool :=
  let pil_ext :=
    project_pinstrs_ext_with_pluto_band_component
      (Tiling.compose_tiling_pinstrs_ext_from_after
         env_size before_pis after_pis ws)
      band dim in
  let valid_access := BandAffine.check_valid_access pil_ext in
  BIND res <- BandAffine.validate_instr_list (rev pil_ext) env_size -;
  pure (res && valid_access).

Fixpoint check_pinstr_list_pluto_permutable_band_components_from
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band)
    (remaining dim: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        check_pinstr_list_pluto_permutable_band_component_via_validate_tiling
          env_size before_pis after_pis ws band dim -;
      if component_ok then
        check_pinstr_list_pluto_permutable_band_components_from
          env_size before_pis after_pis ws band remaining' (S dim)
      else pure false
  end.

Definition check_pinstr_list_pluto_permutable_band_components_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : imp bool :=
  check_pinstr_list_pluto_permutable_band_components_from
    env_size before_pis after_pis ws band (ptb_len band) O.

Definition check_pinstr_list_pluto_permutable_bands_component_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band)
    (dim: nat) : imp bool :=
  let pil_ext :=
    project_pinstrs_ext_with_pluto_bands_component
      (Tiling.compose_tiling_pinstrs_ext_from_after
         env_size before_pis after_pis ws)
      bands dim in
  let valid_access := BandAffine.check_valid_access pil_ext in
  BIND res <- BandAffine.validate_instr_list (rev pil_ext) env_size -;
  pure (res && valid_access).

Fixpoint check_pinstr_list_pluto_permutable_bands_components_from
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band)
    (remaining dim: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        check_pinstr_list_pluto_permutable_bands_component_via_validate_tiling
          env_size before_pis after_pis ws bands dim -;
      if component_ok then
        check_pinstr_list_pluto_permutable_bands_components_from
          env_size before_pis after_pis ws bands remaining' (S dim)
      else pure false
  end.

Definition check_pinstr_list_pluto_permutable_bands_components_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  check_pinstr_list_pluto_permutable_bands_components_from
    env_size before_pis after_pis ws bands (max_tiling_band_len bands) O.

Definition check_pprog_second_level_permutable_bands_via_validate_tiling
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match
      check_pprog_second_level_schedule_stripminedb before after ws
    with
    | Some (bands, _) =>
        check_pinstr_list_pluto_permutable_bands_components_via_validate_tiling
          (List.length before_ctxt) before_pis after_pis ws bands
    | None => pure false
    end
  else pure false.

Definition check_pinstr_list_pluto_permutable_band_via_validate_tiling_old
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : imp bool :=
  check_pinstr_list_pluto_permutable_band_via_validate_tiling
    env_size before_pis after_pis ws band.

Fixpoint check_pinstr_list_single_permutable_tiling_bands_via_validate_tiling
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  match before_pis, after_pis, ws, bands with
  | [], [], [], [] => pure true
  | before_pi :: before_pis',
    after_pi :: after_pis',
    w :: ws',
    band :: bands' =>
      let cutoff := max_pinstr_schedule_len (after_pi :: nil) in
      BIND one <-
        check_pinstr_list_permutable_tiling_band_via_validate_tiling
          env_size
          (before_pi :: nil)
          (after_pi :: nil)
          (w :: nil)
          cutoff -;
      if one then
        check_pinstr_list_single_permutable_tiling_bands_via_validate_tiling
          env_size before_pis' after_pis' ws' bands'
      else pure false
  | _, _, _, _ => pure false
  end.

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

Definition dummy_tiling_band : pinstr_tiling_band :=
  {| ptb_start := O; ptb_len := O |}.

(** A structurally recognized second-level schedule may be permutable as a
    complete lexicographic order even when the componentwise projection is too
    strong.  Keep the existing second-level shape check as the guard, then
    validate the complete composed schedule. *)
Definition check_pprog_structural_second_level_permutability_via_validate_tiling
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, _, _) := before in
  match check_pprog_statementwise_second_level_scheduleb before after ws with
  | Some _ =>
      check_pprog_permutable_tiling_bands_via_validate_tiling
        before after ws
        (repeat dummy_tiling_band (List.length before_pis))
  | None => pure false
  end.

Example structural_second_level_guard_rejects_schedule_mismatch :
  check_pprog_statementwise_second_level_scheduleb
    ([source_like_guard_test_pinstr [([1%Z], 0%Z)]], [], [])
    ([source_like_guard_test_pinstr []], [], [])
    [source_like_guard_test_witness [1%Z]] = None.
Proof. reflexivity. Qed.

Example structural_second_level_guard_accepts_interleaved_schedule :
  match
    check_pprog_statementwise_second_level_scheduleb
      ([source_like_guard_test_pinstr [([1%Z], 0%Z)]], [], [])
      ([source_like_guard_test_pinstr
          [([1%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 1%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 1%Z], 0%Z)]], [], [])
      [source_like_guard_test_witness [1%Z]]
  with
  | Some _ => true
  | None => false
  end = true.
Proof. reflexivity. Qed.

Example structural_second_level_guard_accepts_dropped_trailing_zero :
  match
    check_pprog_statementwise_second_level_scheduleb
      ([source_like_guard_test_pinstr
          [([1%Z], 0%Z); ([0%Z], 0%Z); ([0%Z], 0%Z)]], [], [])
      ([source_like_guard_test_pinstr
          [([0%Z; 1%Z; 0%Z], 0%Z);
           ([1%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 1%Z], 0%Z)]], [], [])
      [source_like_guard_test_witness [1%Z]]
  with
  | Some _ => true
  | None => false
  end = true.
Proof. reflexivity. Qed.

Example structural_second_level_guard_rejects_dropped_internal_zero :
  check_pprog_statementwise_second_level_scheduleb
    ([source_like_guard_test_pinstr
        [([1%Z], 0%Z); ([0%Z], 0%Z); ([2%Z], 0%Z)]], [], [])
    ([source_like_guard_test_pinstr
        [([0%Z; 1%Z; 0%Z], 0%Z);
         ([1%Z; 0%Z; 0%Z], 0%Z);
         ([0%Z; 0%Z; 1%Z], 0%Z);
         ([0%Z; 0%Z; 2%Z], 0%Z)]], [], [])
    [source_like_guard_test_witness [1%Z]] = None.
Proof. reflexivity. Qed.

Example structural_second_level_guard_rejects_wrong_same_arity_schedule :
  check_pprog_statementwise_second_level_scheduleb
    ([source_like_guard_test_pinstr [([1%Z], 0%Z)]], [], [])
    ([source_like_guard_test_pinstr
        [([1%Z; 0%Z; 0%Z], 0%Z);
         ([0%Z; 0%Z; 1%Z], 0%Z);
         ([0%Z; 1%Z; 0%Z], 0%Z)]], [], [])
    [source_like_guard_test_witness [1%Z]] = None.
Proof. reflexivity. Qed.

Definition direct_second_level_guard_test_band : pinstr_tiling_band :=
  {| ptb_start := O; ptb_len := 1 |}.

Definition direct_second_level_guard_grouped_schedule : Schedule :=
  [([0%Z; 1%Z; 0%Z], 0%Z);
   ([1%Z; 0%Z; 0%Z], 0%Z);
   ([0%Z; 0%Z; 1%Z], 0%Z)].

Definition direct_second_level_guard_interleaved_schedule : Schedule :=
  [([1%Z; 0%Z; 0%Z], 0%Z);
   ([0%Z; 1%Z; 0%Z], 0%Z);
   ([0%Z; 0%Z; 1%Z], 0%Z)].

Example direct_second_level_guard_accepts_grouped_reverse_padding :
  check_pinstr_list_second_level_schedule_symmetricb
    SecondLevelGrouped O
    [source_like_guard_test_pinstr
       [([1%Z], 0%Z); ([0%Z], 0%Z); ([0%Z], 0%Z)]]
    [source_like_guard_test_pinstr
       direct_second_level_guard_grouped_schedule]
    [direct_second_level_guard_test_band] = true.
Proof. reflexivity. Qed.

Example direct_second_level_guard_accepts_interleaved_reverse_padding :
  check_pinstr_list_second_level_schedule_symmetricb
    SecondLevelInterleaved O
    [source_like_guard_test_pinstr
       [([1%Z], 0%Z); ([0%Z], 0%Z)]]
    [source_like_guard_test_pinstr
       direct_second_level_guard_interleaved_schedule]
    [direct_second_level_guard_test_band] = true.
Proof. reflexivity. Qed.

Example direct_second_level_guard_rejects_internal_zero_removal :
  check_pinstr_list_second_level_schedule_symmetricb
    SecondLevelGrouped O
    [source_like_guard_test_pinstr
       [([1%Z], 0%Z); ([0%Z], 0%Z); ([2%Z], 0%Z)]]
    [source_like_guard_test_pinstr
       (direct_second_level_guard_grouped_schedule ++
        [([0%Z; 0%Z; 2%Z], 0%Z)])]
    [direct_second_level_guard_test_band] = false.
Proof. reflexivity. Qed.

Example direct_second_level_guard_rejects_mixed_statement_layouts :
  check_pprog_second_level_schedule_symmetricb
    ([source_like_guard_test_pinstr [([1%Z], 0%Z)];
      source_like_guard_test_pinstr [([1%Z], 0%Z)]],
     [], [])
    ([source_like_guard_test_pinstr
        direct_second_level_guard_grouped_schedule;
      source_like_guard_test_pinstr
        direct_second_level_guard_interleaved_schedule],
     [], [])
    [source_like_guard_test_witness [1%Z];
     source_like_guard_test_witness [1%Z]] = None.
Proof. reflexivity. Qed.

Definition structural_guard_test_witness_2d : statement_tiling_witness :=
  {|
    stw_point_dim := 2;
    stw_links :=
      [source_like_guard_test_link [1%Z; 0%Z] 32%Z;
       source_like_guard_test_link [1%Z; 0%Z; 0%Z] 8%Z;
       source_like_guard_test_link [0%Z; 0%Z; 0%Z; 1%Z] 32%Z;
       source_like_guard_test_link [0%Z; 0%Z; 1%Z; 0%Z; 0%Z] 8%Z];
  |}.

Example structural_second_level_guard_accepts_heterogeneous_band_lengths :
  match
    check_pprog_statementwise_second_level_scheduleb
      ([source_like_guard_test_pinstr [([1%Z], 0%Z)];
        source_like_guard_test_pinstr
          [([1%Z; 0%Z], 0%Z); ([0%Z; 1%Z], 0%Z)]],
       [], [])
      ([source_like_guard_test_pinstr
          [([1%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 1%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 1%Z], 0%Z)];
        source_like_guard_test_pinstr
          [([1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z], 0%Z);
           ([0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z], 0%Z)]],
       [], [])
      [source_like_guard_test_witness [1%Z];
       structural_guard_test_witness_2d]
  with
  | Some _ => true
  | None => false
  end = true.
Proof. reflexivity. Qed.

(** Source-like schedules can omit or place strict zero scattering
    rows differently from the roots in a valid second-level tiling witness.
    Require exact equality after erasing those rows, then validate the complete
    reordering directly. *)
Definition check_pprog_source_like_second_level_permutability_via_validate_tiling
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, _, _) := before in
  if check_pprog_source_like_second_level_recipesb before_pis ws then
    check_pprog_permutable_tiling_bands_via_validate_tiling
      before after ws
      (repeat dummy_tiling_band (List.length before_pis))
  else pure false.

(** Whole-program ordinary-tiling permutability mode.  Unlike the common-band
    fast path, this check does not depend on the source schedule retaining
    Pluto's explicit zero scattering rows. *)
Definition check_pprog_ordinary_tiling_permutability_via_validate_tiling
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, _, _) := before in
  if check_ordinary_tiling_witnessesb ws then
    check_pprog_permutable_tiling_bands_via_validate_tiling
      before after ws (repeat dummy_tiling_band (List.length before_pis))
  else pure false.

Definition check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars then
    if Nat.eqb (List.length bands) (List.length before_pis) then
      if check_uniform_schedule_arityb before_pis then
        match infer_common_tiling_band bands with
        | Some band =>
            if check_common_tiling_band_recipeb ws then
              check_pinstr_list_pluto_permutable_band_components_via_validate_tiling
                (List.length before_ctxt) before_pis after_pis ws band
            else pure false
        | None => pure false
        end
      else pure false
    else pure false
  else pure false.

Definition check_pprog_pluto_permutable_tiling_bands_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars then
    if Nat.eqb (List.length bands) (List.length before_pis) then
      if check_uniform_schedule_arityb before_pis then
        match infer_common_tiling_band bands with
        | Some band =>
            if check_common_tiling_band_recipeb ws then
              check_pinstr_list_pluto_permutable_band_direct
                (List.length before_ctxt) before_pis after_pis ws band
            else pure false
        | None => pure false
        end
      else pure false
    else pure false
  else pure false.

Inductive tiling_band_validation_route : Type :=
| TilingBandAccepted
| TilingBandGeneralFallbackAccepted
| TilingBandRejected.

Definition tiling_band_validation_route_acceptsb
    (route: tiling_band_validation_route) : bool :=
  match route with
  | TilingBandAccepted
  | TilingBandGeneralFallbackAccepted => true
  | TilingBandRejected => false
  end.

Definition check_pprog_pluto_permutable_tiling_bands_primary
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  BIND strong_ok <-
    check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling
      before after ws bands -;
  if strong_ok then pure true
  else
    check_pprog_permutable_tiling_bands_via_validate_tiling
      before after ws bands.

Definition checked_tiling_sourceb_first_band_check
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  if TilingCheck.check_pprog_tiling_sourceb before after ws then
  let ordinary_band_check :=
      if check_pprog_tiling_schedule_stripminedb before after ws then
        match infer_pprog_tiling_bands before ws with
        | Some bands =>
            check_pprog_pluto_permutable_tiling_bands_primary
              before after ws bands
        | None => pure false
        end
      else pure false in
    BIND ordinary_ok <- ordinary_band_check -;
    if ordinary_ok then pure true
    else
      BIND ordinary_direct_ok <-
        check_pprog_ordinary_tiling_permutability_via_validate_tiling
          before after ws -;
      if ordinary_direct_ok then pure true
      else
        BIND second_level_ok <-
          check_pprog_second_level_permutable_bands_via_validate_tiling
            before after ws -;
        if second_level_ok then pure true
        else
          BIND structural_second_level_ok <-
            check_pprog_structural_second_level_permutability_via_validate_tiling
              before after ws -;
          if structural_second_level_ok then pure true
          else
            check_pprog_source_like_second_level_permutability_via_validate_tiling
              before after ws
  else pure false.

Definition checked_tiling_schedule_sourceb_first_runtime_validate_route
    (before after: PolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp tiling_band_validation_route :=
  BIND band_ok <-
    checked_tiling_sourceb_first_band_check
      (Base.outer_to_tiling_pprog before)
      (Base.outer_to_tiling_pprog after)
      ws -;
  if band_ok then pure TilingBandGeneralFallbackAccepted
  else
    BIND canonical_ok <-
      Canonical.checked_tiling_schedule_canonical_validate_poly
        before after ws -;
    if canonical_ok then pure TilingBandGeneralFallbackAccepted
    else
      BIND fallback_ok <- Base.checked_tiling_validate_poly before after ws -;
      pure
        (if fallback_ok
         then TilingBandGeneralFallbackAccepted
         else TilingBandRejected).

Definition check_pprog_permutable_tiling_bands_runtime_route
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp tiling_band_validation_route :=
  BIND band_ok <-
    check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling
      before after ws bands -;
  if band_ok then
    pure TilingBandAccepted
  else
    BIND fallback_ok <-
      check_pprog_permutable_tiling_bands_via_validate_tiling
        before after ws bands -;
    pure
      (if fallback_ok
       then TilingBandGeneralFallbackAccepted
       else TilingBandRejected).

Definition check_pprog_permutable_tiling_bands_runtime
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  BIND route <-
    check_pprog_permutable_tiling_bands_runtime_route
      before after ws bands -;
  pure (tiling_band_validation_route_acceptsb route).

Definition checked_tiling_schedule_stripmined_and_runtime_validate_outer
    (before after: PolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp bool :=
  BIND shape_ok <-
    checked_tiling_schedule_stripmined_validate_outer before after ws -;
  if shape_ok then
    let before_tiling := Base.outer_to_tiling_pprog before in
    let after_tiling := Base.outer_to_tiling_pprog after in
    match infer_pprog_tiling_bands before_tiling ws with
    | Some bands =>
        check_pprog_permutable_tiling_bands_runtime
          before_tiling after_tiling ws bands
    | None => pure false
    end
  else pure false.

Definition checked_tiling_schedule_stripmined_and_runtime_validate_poly :=
  checked_tiling_schedule_stripmined_and_runtime_validate_outer.

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

Lemma check_pinstr_list_pluto_permutable_band_component_via_validate_tiling_sound :
  forall before_pis before_ctxt before_vars after_pis ws band dim envv,
    List.length before_ctxt = List.length envv ->
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
      (check_pinstr_list_pluto_permutable_band_component_via_validate_tiling
         (List.length before_ctxt) before_pis after_pis ws band dim)
      true ->
    forall flat_ext point1 point2,
      Tiling.PL.flatten_instrs_ext
        envv
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length before_ctxt) before_pis after_pis ws)
        flat_ext ->
      In point1 flat_ext ->
      In point2 flat_ext ->
      Tiling.PL.instr_point_ext_old_sched_lt point1 point2 ->
      instr_point_ext_same_band_slice band point1 point2 ->
      instr_point_ext_band_component_decreases_at
        band dim point1 point2 ->
      Tiling.PL.Permutable_ext point1 point2.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws band dim envv
         Hlen_env Hwf_before Hwf_after Hdepths Hwits Hcheck
         flat_ext point1 point2 Hflat Hin1 Hin2 Hold Hprefix Hcomponent.
  unfold
    check_pinstr_list_pluto_permutable_band_component_via_validate_tiling
    in Hcheck.
  bind_imp_destruct Hcheck res Hres.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hres_true Hvalid_true].
  set (composed_ext :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length before_ctxt) before_pis after_pis ws).
  set (projected_ext :=
    project_pinstrs_ext_with_pluto_band_component
      composed_ext band dim).
  assert (Hflat_proj :
    Tiling.PL.flatten_instrs_ext
      envv projected_ext
      (List.map
         (project_pluto_band_component_ip_ext band dim) flat_ext)).
  {
    subst projected_ext composed_ext.
    eapply flatten_instrs_ext_project_pluto_band_component.
    exact Hflat.
  }
  assert (Hwf_proj :
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
      projected_ext).
  {
    subst projected_ext composed_ext.
    eapply project_pinstrs_ext_with_pluto_band_component_wf_tiling;
      eauto.
  }
  assert (Hvalid_proj :
    Forall
      (fun pi_ext =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi_ext)
           (Tiling.PL.pi_raccess_ext pi_ext)
           (Tiling.PL.pi_instr_ext pi_ext))
      projected_ext).
  {
    subst projected_ext composed_ext.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  assert (Hin1_proj :
    In (project_pluto_band_component_ip_ext band dim point1)
       (List.map
          (project_pluto_band_component_ip_ext band dim) flat_ext)).
  {
    apply in_map. exact Hin1.
  }
  assert (Hin2_proj :
    In (project_pluto_band_component_ip_ext band dim point2)
       (List.map
          (project_pluto_band_component_ip_ext band dim) flat_ext)).
  {
    apply in_map. exact Hin2.
  }
  assert (Hold_proj :
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_pluto_band_component_ip_ext band dim point1)
      (project_pluto_band_component_ip_ext band dim point2)).
  {
    eapply project_pluto_band_component_ip_ext_old_sched_lt.
    exact Hold.
  }
  assert (Hnew_proj :
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_pluto_band_component_ip_ext band dim point1)
      (project_pluto_band_component_ip_ext band dim point2)).
  {
    eapply project_pluto_band_component_ip_ext_new_sched_ge; eauto.
  }
  assert (Hperm_proj :
    Tiling.PL.Permutable_ext
      (project_pluto_band_component_ip_ext band dim point1)
      (project_pluto_band_component_ip_ext band dim point2)).
  {
    eapply
      (BandAffine.validate_pinstrs_ext_implies_permutability
         projected_ext before_ctxt envv
         (List.map
            (project_pluto_band_component_ip_ext band dim) flat_ext)
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
  eapply project_pluto_band_component_ip_ext_permutable_back.
  exact Hperm_proj.
Qed.

Lemma check_pinstr_list_pluto_permutable_band_components_from_true_component :
  forall env_size before_pis after_pis ws band remaining start,
    mayReturn
      (check_pinstr_list_pluto_permutable_band_components_from
         env_size before_pis after_pis ws band remaining start)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (check_pinstr_list_pluto_permutable_band_component_via_validate_tiling
           env_size before_pis after_pis ws band dim)
        true.
Proof.
  intros env_size before_pis after_pis ws band remaining.
  induction remaining as [|remaining IH]; intros start Hcheck dim Hrange.
  - lia.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck component_ok Hcomponent.
    destruct component_ok.
    + destruct (Nat.eq_dec dim start) as [Heq | Hneq].
      * subst dim. exact Hcomponent.
      * eapply IH.
        -- exact Hcheck.
        -- lia.
    + apply mayReturn_pure in Hcheck.
      discriminate.
Qed.

Lemma check_pinstr_list_pluto_permutable_band_components_sound_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws band envv,
    List.length before_ctxt = List.length envv ->
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
      (check_pinstr_list_pluto_permutable_band_components_via_validate_tiling
         (List.length before_ctxt) before_pis after_pis ws band)
      true ->
    pprog_pluto_componentwise_permutable_band
      envv before_pis after_pis ws band.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws band envv
         Hlen_env Hwf_before Hwf_after Hdepths Hwits Hcheck.
  unfold pprog_pluto_componentwise_permutable_band.
  intros flat_ext point1 point2 Hflat Hin1 Hin2 Hold Hprefix
         [dim Hcomponent].
  destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
  assert (Hcomponent_check :
    mayReturn
      (check_pinstr_list_pluto_permutable_band_component_via_validate_tiling
         (List.length before_ctxt) before_pis after_pis ws band dim)
      true).
  {
    eapply
      check_pinstr_list_pluto_permutable_band_components_from_true_component.
    - exact Hcheck.
    - lia.
  }
  assert (Hflat_ctxt :
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)
      flat_ext).
  {
    rewrite Hlen_env.
    exact Hflat.
  }
  eapply
    (check_pinstr_list_pluto_permutable_band_component_via_validate_tiling_sound
       before_pis before_ctxt before_vars after_pis ws band dim envv);
    eauto.
  exists x, y.
  repeat split; assumption.
Qed.

Lemma check_pinstr_list_pluto_permutable_bands_component_sound :
  forall before_pis after_pis ws bands dim env envv,
    List.length env = List.length envv ->
    List.length
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) =
    List.length bands ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    Forall2
      (fun pi_ext _ => Tiling.PL.pi_schedule1_ext pi_ext <> [])
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws)
      bands ->
    mayReturn
      (check_pinstr_list_pluto_permutable_bands_component_via_validate_tiling
         (List.length env) before_pis after_pis ws bands dim)
      true ->
    forall flat_ext point1 point2 band,
      Tiling.PL.flatten_instrs_ext
        envv
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length env) before_pis after_pis ws)
        flat_ext ->
      In point1 flat_ext ->
      In point2 flat_ext ->
      nth_error bands (Tiling.PL.ip_nth_ext point1) = Some band ->
      nth_error bands (Tiling.PL.ip_nth_ext point2) = Some band ->
      Tiling.PL.instr_point_ext_old_sched_lt point1 point2 ->
      instr_point_ext_same_band_slice band point1 point2 ->
      instr_point_ext_band_component_decreases_at
        band dim point1 point2 ->
      Tiling.PL.Permutable_ext point1 point2.
Proof.
  intros before_pis after_pis ws bands dim env envv
         Hlen_env Hlen_bands Hwf Hnonempty Hcheck
         flat_ext point1 point2 band Hflat Hin1 Hin2
         Hband1 Hband2 Hold Hprefix Hcomponent.
  unfold
    check_pinstr_list_pluto_permutable_bands_component_via_validate_tiling
    in Hcheck.
  bind_imp_destruct Hcheck res Hres.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hres_true Hvalid_true].
  set (composed_ext :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws).
  set (projected_ext :=
    project_pinstrs_ext_with_pluto_bands_component
      composed_ext bands dim).
  assert (Hflat_proj :
    Tiling.PL.flatten_instrs_ext
      envv projected_ext
      (List.map
         (project_pluto_bands_component_ip_ext bands dim) flat_ext)).
  {
    subst projected_ext composed_ext.
    eapply flatten_instrs_ext_project_pluto_bands_component; eauto.
  }
  assert (Hwf_proj :
    Forall (Tiling.PL.wf_pinstr_ext_tiling env) projected_ext).
  {
    subst projected_ext composed_ext.
    eapply project_pinstrs_ext_with_pluto_bands_component_wf_tiling;
      eauto.
  }
  assert (Hvalid_proj :
    Forall
      (fun pi_ext =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi_ext)
           (Tiling.PL.pi_raccess_ext pi_ext)
           (Tiling.PL.pi_instr_ext pi_ext))
      projected_ext).
  {
    subst projected_ext composed_ext.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  assert (Hin1_proj :
    In (project_pluto_bands_component_ip_ext bands dim point1)
       (List.map
          (project_pluto_bands_component_ip_ext bands dim) flat_ext)).
  {
    apply in_map. exact Hin1.
  }
  assert (Hin2_proj :
    In (project_pluto_bands_component_ip_ext bands dim point2)
       (List.map
          (project_pluto_bands_component_ip_ext bands dim) flat_ext)).
  {
    apply in_map. exact Hin2.
  }
  assert (Hold_proj :
    Tiling.PL.instr_point_ext_old_sched_lt
      (project_pluto_bands_component_ip_ext bands dim point1)
      (project_pluto_bands_component_ip_ext bands dim point2)).
  {
    eapply project_pluto_bands_component_ip_ext_old_sched_lt.
    exact Hold.
  }
  assert (Hnew_proj :
    Tiling.PL.instr_point_ext_new_sched_ge
      (project_pluto_bands_component_ip_ext bands dim point1)
      (project_pluto_bands_component_ip_ext bands dim point2)).
  {
    eapply project_pluto_bands_component_ip_ext_new_sched_ge; eauto.
  }
  assert (Hperm_proj :
    Tiling.PL.Permutable_ext
      (project_pluto_bands_component_ip_ext bands dim point1)
      (project_pluto_bands_component_ip_ext bands dim point2)).
  {
    eapply
      (BandAffine.validate_pinstrs_ext_implies_permutability
         projected_ext env envv
         (List.map
            (project_pluto_bands_component_ip_ext bands dim) flat_ext)
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
  eapply project_pluto_bands_component_ip_ext_permutable_back.
  exact Hperm_proj.
Qed.

Lemma check_pinstr_list_pluto_permutable_bands_components_from_true_component :
  forall env_size before_pis after_pis ws bands remaining start,
    mayReturn
      (check_pinstr_list_pluto_permutable_bands_components_from
         env_size before_pis after_pis ws bands remaining start)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (check_pinstr_list_pluto_permutable_bands_component_via_validate_tiling
           env_size before_pis after_pis ws bands dim)
        true.
Proof.
  intros env_size before_pis after_pis ws bands remaining.
  induction remaining as [|remaining IH]; intros start Hcheck dim Hrange.
  - lia.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck component_ok Hcomponent.
    destruct component_ok.
    + destruct (Nat.eq_dec dim start) as [Heq | Hneq].
      * subst dim. exact Hcomponent.
      * eapply IH.
        -- exact Hcheck.
        -- lia.
    + apply mayReturn_pure in Hcheck.
      discriminate.
Qed.

Lemma max_tiling_band_len_ge_nth_error :
  forall bands n band,
    nth_error bands n = Some band ->
    (ptb_len band <= max_tiling_band_len bands)%nat.
Proof.
  induction bands as [|band0 bands IH]; intros n band Hnth.
  - destruct n; discriminate.
  - destruct n as [|n].
    + inversion Hnth; subst.
      simpl. apply Nat.le_max_l.
    + simpl in Hnth.
      simpl.
      eapply Nat.le_trans.
      * eapply IH; exact Hnth.
      * apply Nat.le_max_r.
Qed.

Lemma check_pinstr_list_pluto_permutable_bands_components_sound :
  forall before_pis after_pis ws bands env envv,
    List.length env = List.length envv ->
    List.length
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) =
    List.length bands ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    Forall2
      (fun pi_ext _ => Tiling.PL.pi_schedule1_ext pi_ext <> [])
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws)
      bands ->
    mayReturn
      (check_pinstr_list_pluto_permutable_bands_components_via_validate_tiling
         (List.length env) before_pis after_pis ws bands)
      true ->
    pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands.
Proof.
  intros before_pis after_pis ws bands env envv
         Hlen_env Hlen_bands Hwf Hnonempty Hcheck.
  unfold pprog_pluto_componentwise_permutable_bands.
  intros flat_ext point1 point2 band Hflat Hin1 Hin2 Hband1 Hband2
         Hold Hprefix [dim Hcomponent].
  destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
  assert (Hcomponent_check :
    mayReturn
      (check_pinstr_list_pluto_permutable_bands_component_via_validate_tiling
         (List.length env) before_pis after_pis ws bands dim)
      true).
  {
    eapply
      check_pinstr_list_pluto_permutable_bands_components_from_true_component.
    - exact Hcheck.
    - split; [lia|].
      eapply Nat.lt_le_trans.
      * exact Hdim.
      * eapply max_tiling_band_len_ge_nth_error; exact Hband1.
  }
  assert (Hflat_env :
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws)
      flat_ext).
  {
    rewrite Hlen_env.
    exact Hflat.
  }
  eapply
    (check_pinstr_list_pluto_permutable_bands_component_sound
       before_pis after_pis ws bands dim env envv);
    eauto.
  exists x, y.
  repeat split; assumption.
Qed.

Lemma check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling_sound_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
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
      (check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands)
      true ->
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands /\
    uniform_schedule_arity before_pis.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer_bands Hwf_before Hwf_after Hdepths Hwits Hcheck.
  unfold check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling
    in Hcheck.
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
  rewrite Hctxt_refl, Hvars_refl in Hcheck.
  destruct (infer_pinstr_list_tiling_bands_lengths _ _ _ Hinfer_bands)
    as [_ Hlen_bands].
  rewrite <- Hlen_bands, Nat.eqb_refl in Hcheck.
  destruct (check_uniform_schedule_arityb before_pis) eqn:Huniform.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (infer_common_tiling_band bands) as [band|] eqn:Hcommon.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (check_common_tiling_band_recipeb ws) eqn:Hrecipe.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  simpl in Hcheck.
  split.
  - destruct (check_common_tiling_band_recipeb_sound _ Hrecipe)
      as [sizes Hrecipe_sound].
    exists band, sizes.
    split.
    + eapply infer_common_tiling_band_sound; exact Hcommon.
    + split.
      * exact Hrecipe_sound.
      * eapply
          check_pinstr_list_pluto_permutable_band_components_sound_with_env_len;
          eauto.
  - eapply check_uniform_schedule_arityb_sound.
    exact Huniform.
Qed.

Lemma check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_lengths :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    List.length bands = List.length before_pis ->
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
         Hlen_env Hlen_after Hlen_ws Hlen_bands
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
         Hlen_env Hinfer Hcert Hwf_before Hwf_after Hdepths Hwits Hcheck.
  destruct (pprog_tiling_bands_cert_lengths _ _ _ _ _ Hcert)
    as [Hlen_after [Hlen_ws Hlen_bands]].
  eapply
    (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_lengths
       before_pis before_ctxt before_vars after_pis ws bands envv);
    eauto.
Qed.

Lemma checked_tiling_schedule_stripmined_validate_correct_same_ctxt_with_reordering_checker :
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
    (forall envv,
       List.length before_ctxt = List.length envv ->
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
       Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
       pprog_tiling_reordering_safe envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands st1 st2
         Hcheck_shape Hinfer_bands Hwfbefore_pis Hwfafter_pis
         Hreordering Hsem_after.
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
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands).
  {
    eapply Hreordering.
    - exact Hlen_env.
    - exact Hbands.
    - exact Hprog_full.
    - exact Hwf.
    - exact Hsizes.
    - exact Hdepths.
    - exact Hwits.
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
         Hshape Hinfer Hwf_before Hwf_after Hcheck Hsem.
  eapply
    checked_tiling_schedule_stripmined_validate_correct_same_ctxt_with_reordering_checker;
    eauto.
  intros envv Hlen Hbands _ _ _ Hdepths Hwits.
  eapply
    (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
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
       instr_point_ext_band_component_decreases band tau1 tau2) ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros envv before_pis after_pis ws bands
         Hpluto Hlocal.
  destruct Hpluto as [band [sizes [Hcommon [Hrecipe Hperm]]]].
  unfold pprog_tiling_reordering_safe, pprog_permutable_tiling_bands.
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (Hlocal ipl_ext tau1 tau2 band sizes
              Hcommon Hrecipe Hflat Hin1 Hin2 Hold Hnew)
    as [Hslice Hcomponent].
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer_bands Hbands Hprog_full Hwf_ws Hsizes_ws Hdepths
         Harity_before Hwf_before_pis Hpluto.
  assert (Hwf_ws_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
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
  assert (Htiles_mono :
    listz_pointwise_le band_ts1 band_ts2 ->
    listz_pointwise_le added1 added2).
  {
    intro Hband_le.
    pose proof
      (common_tiling_band_recipe_nth_error ws sizes
         (Tiling.PL.ip_nth_ext tau1) w1 Hrecipe Hw1) as Hsizes_recipe1.
    pose proof
      (common_tiling_band_recipe_nth_error ws sizes
         (Tiling.PL.ip_nth_ext tau2) w2 Hrecipe Hw2) as Hsizes_recipe2.
    rewrite Hadded_eq1, Hadded_eq2.
    eapply common_recipe_band_pointwise_le_implies_tiles_pointwise_le.
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
    - exact Hsizes1.
    - rewrite <- Hband_rows1, <- Hband_rows2.
      exact Hband_le.
  }
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (stripmined_reversal_implies_decreasing_band_component
       prefix1 prefix2 added1 added2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Htiles_mono
       Hold Hnew_expected_not_lt)
    as [Hprefix_eq [dim [x [y [Hx [Hy Hgt]]]]]].
  assert (Hband_ts1_len : List.length band_ts1 = ptb_len band).
  {
    change
      (List.length (instr_point_ext_band_block_ts band tau1) =
       ptb_len band).
    rewrite Hband_rows1.
    unfold affine_product.
    rewrite List.map_length.
    pose proof (schedule_rows_of_links_length _ _ Hrows1) as Hrows_len.
    lia.
  }
  assert (Hdim : (dim < ptb_len band)%nat).
  {
    rewrite <- Hband_ts1_len.
    apply nth_error_Some.
    rewrite Hx.
    discriminate.
  }
  assert (Hx_full :
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau1)
      (ptb_start band + dim)%nat = Some x).
  {
    eapply nth_error_band_block_to_full; [exact Hdim|].
    change (nth_error band_ts1 dim = Some x).
    exact Hx.
  }
  assert (Hy_full :
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau2)
      (ptb_start band + dim)%nat = Some y).
  {
    eapply nth_error_band_block_to_full; [exact Hdim|].
    change (nth_error band_ts2 dim = Some y).
    exact Hy.
  }
  split.
  - exact Hprefix_eq.
  - exists dim, x, y.
    repeat split; assumption.
Qed.

Lemma second_level_local_reversal_bridge_by_layout_wf_with_env_len :
  forall layout before_pis before_ctxt before_vars
         after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    check_pinstr_list_second_level_schedule_symmetricb
      layout (List.length before_ctxt) before_pis after_pis bands = true ->
    common_second_level_recipe_sizes recipes ->
    common_band_start bands ->
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
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
      exists band,
        nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
        instr_point_ext_same_band_slice band tau1 tau2 /\
        instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros layout before_pis before_ctxt before_vars
         after_pis ws bands recipes envv
         Hlen_env Hinfer Hsched Hrecipe_sizes Hcommon
         Hprog Hwf_ws Hsizes_ws Hdepths Hwf_before
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  assert (Hwf_ws_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct (infer_pinstr_list_second_level_bands_lengths _ _ _ _ Hinfer)
    as [Hlen_ws [Hlen_bands Hlen_recipes]].
  destruct
    (flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [Hwf_stmt1 [Hsizes1 [Hpoint_depth1
         [Hpref1 [Hbel1 Hlen1]]]]]]]]]]].
  destruct
    (flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [Hwf_stmt2 [Hsizes2 [Hpoint_depth2
         [Hpref2 [Hbel2 Hlen2]]]]]]]]]]].
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    apply nth_error_None in Hband1.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    apply nth_error_None in Hband2.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Tiling.PL.ip_nth_ext tau1))
    as [recipe1|] eqn:Hrecipe1.
  2:{
    apply nth_error_None in Hrecipe1.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Tiling.PL.ip_nth_ext tau2))
    as [recipe2|] eqn:Hrecipe2.
  2:{
    apply nth_error_None in Hrecipe2.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  pose proof
    (infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band1 recipe1
       Hinfer Hbefore1 Hw1 Hband1 Hrecipe1) as Hinfer1.
  pose proof
    (infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Tiling.PL.ip_nth_ext tau2)
       before_pi2 w2 band2 recipe2
       Hinfer Hbefore2 Hw2 Hband2 Hrecipe2) as Hinfer2.
  destruct (infer_pinstr_second_level_band_sound _ _ _ _ Hinfer1)
    as [Hspec1 [Hband_len1 Hrows_match1]].
  destruct (infer_pinstr_second_level_band_sound _ _ _ _ Hinfer2)
    as [Hspec2 [Hband_len2 Hrows_match2]].
  destruct
    (common_second_level_recipe_sizes_nth_error_equal
       recipes (Tiling.PL.ip_nth_ext tau1) (Tiling.PL.ip_nth_ext tau2)
       recipe1 recipe2 Hrecipe_sizes Hrecipe1 Hrecipe2)
    as [Hroot_sizes_eq Hchild_sizes_eq].
  pose proof
    (common_band_start_nth_error_equal
       bands (Tiling.PL.ip_nth_ext tau1) (Tiling.PL.ip_nth_ext tau2)
       band1 band2 Hcommon Hband1 Hband2) as Hstart_eq.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_size_len1 Hchild_size_len1].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec2)
    as [Hroot_size_len2 Hchild_size_len2].
  assert (Hband_len_eq_nat : ptb_len band1 = ptb_len band2).
  {
    rewrite Hband_len1, Hband_len2.
    rewrite Hroot_size_len1, Hroot_size_len2, Hroot_sizes_eq.
    reflexivity.
  }
  assert (Hband_eq : band1 = band2).
  {
    destruct band1 as [start1 len1], band2 as [start2 len2].
    simpl in Hstart_eq, Hband_len_eq_nat.
    subst start2 len2.
    reflexivity.
  }
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau1) w1 Hw1)) as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau2) w2 Hw2)) as Hstmt2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt1 Hpoint_depth1) as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2
       Hstmt2 Hpoint_depth2) as Hafter_wit2.
  pose proof
    (Tiling.Forall_nth_error
       _ _ before_pis (Tiling.PL.ip_nth_ext tau1) before_pi1
       Hwf_before Hbefore1) as Hwf_before1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ before_pis (Tiling.PL.ip_nth_ext tau2) before_pi2
       Hwf_before Hbefore2) as Hwf_before2.
  pose proof
    (check_pinstr_list_second_level_schedule_symmetricb_nth_error
       layout (List.length before_ctxt) before_pis after_pis bands
       (Tiling.PL.ip_nth_ext tau1) before_pi1 after_pi1 band1
       Hsched Hbefore1 Hafter1 Hband1) as Hsched_match1.
  pose proof
    (check_pinstr_list_second_level_schedule_symmetricb_nth_error
       layout (List.length before_ctxt) before_pis after_pis bands
       (Tiling.PL.ip_nth_ext tau2) before_pi2 after_pi2 band2
       Hsched Hbefore2 Hafter2 Hband2) as Hsched_match2.
  assert (Hstmt1_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi1 after_pi1
      (Tiling.compiled_pinstr_tiling_witness w1)).
  { rewrite <- Hlen_env. exact Hstmt1. }
  assert (Hstmt2_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi2 after_pi2
      (Tiling.compiled_pinstr_tiling_witness w2)).
  { rewrite <- Hlen_env. exact Hstmt2. }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
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
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w1).
    rewrite <- Hafter_depth1 in Hlen1.
    rewrite Hafter_pw1 in Hlen1.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w2).
    rewrite <- Hafter_depth2 in Hlen2.
    rewrite Hafter_pw2 in Hlen2.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite <- Hafter_depth1 in Hlen1.
    rewrite Hafter_pw1 in Hlen1.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite <- Hafter_depth2 in Hlen2.
    rewrite Hafter_pw2 in Hlen2.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
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
    - rewrite Hpref1. reflexivity.
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
    - rewrite Hpref2. reflexivity.
  }
  assert (Hts11_old :
    Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product (Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    rewrite Hts11. cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts12_old :
    Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product (Tiling.PL.pi_schedule before_pi2) (envv ++ point2)).
  {
    rewrite Hts12. cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts21_after :
    Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product (Tiling.PL.pi_schedule after_pi1)
      (Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. cbn [Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hts22_after :
    Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product (Tiling.PL.pi_schedule after_pi2)
      (Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. cbn [Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete1.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete1 Hafter_dom1). tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2 (conj Hwf_stmt2 Hparams2) Hsizes2)
      as Hcomplete2.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete2 Hafter_dom2). tauto.
  }
  set (roots1 := second_level_root_tiles recipe1 envv point1).
  set (children1 := second_level_child_tiles recipe1 envv point1).
  set (roots2 := second_level_root_tiles recipe2 envv point2).
  set (children2 := second_level_child_tiles recipe2 envv point2).
  assert (Hadded_tiles1 :
    added1 = interleave_root_child_tiles roots1 children1).
  {
    rewrite Hadded_eq1.
    subst roots1 children1.
    change
      (eval_tile_links [] point1 envv (stw_links w1) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe1 envv point1)
         (second_level_child_tiles recipe1 envv point1)).
    exact
      (eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec1 [] point1 envv eq_refl Hpoint_len1
         Hwf_stmt1 Hparams1).
  }
  assert (Hadded_tiles2 :
    added2 = interleave_root_child_tiles roots2 children2).
  {
    rewrite Hadded_eq2.
    subst roots2 children2.
    change
      (eval_tile_links [] point2 envv (stw_links w2) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe2 envv point2)
         (second_level_child_tiles recipe2 envv point2)).
    exact
      (eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec2 [] point2 envv eq_refl Hpoint_len2
         Hwf_stmt2 Hparams2).
  }
  assert (Hroots_len1 : List.length roots1 = ptb_len band1).
  {
    subst roots1.
    rewrite second_level_root_tiles_length by exact Hroot_size_len1.
    lia.
  }
  assert (Hroots_len2 : List.length roots2 = ptb_len band2).
  {
    subst roots2.
    rewrite second_level_root_tiles_length by exact Hroot_size_len2.
    lia.
  }
  assert (Hroots_children1 : List.length roots1 = List.length children1).
  {
    subst roots1 children1.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_size_len1.
    lia.
  }
  assert (Hroots_children2 : List.length roots2 = List.length children2).
  {
    subst roots2 children2.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_size_len2.
    lia.
  }
  assert (Hband_rows1 :
    instr_point_ext_band_block_ts band1 tau1 =
    affine_product (slbr_root_rows recipe1) (envv ++ point1)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts11_old, <- affine_product_skipn, <- affine_product_firstn.
    rewrite Hrows_match1. reflexivity.
  }
  assert (Hband_rows2 :
    instr_point_ext_band_block_ts band2 tau2 =
    affine_product (slbr_root_rows recipe2) (envv ++ point2)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts12_old, <- affine_product_skipn, <- affine_product_firstn.
    rewrite Hrows_match2. reflexivity.
  }
  set (prefix1 := instr_point_ext_band_prefix_ts band1 tau1).
  set (prefix2 := instr_point_ext_band_prefix_ts band2 tau2).
  set (band_ts1 := instr_point_ext_band_block_ts band1 tau1).
  set (band_ts2 := instr_point_ext_band_block_ts band2 tau2).
  set (tiles1 :=
    second_level_schedule_tile_block_by_layout layout recipe1 envv point1).
  set (tiles2 :=
    second_level_schedule_tile_block_by_layout layout recipe2 envv point2).
  set (suffix1 :=
    skipn (ptb_start band1 + ptb_len band1)%nat
      (Tiling.PL.ip_time_stamp1_ext tau1)).
  set (suffix2 :=
    skipn (ptb_start band2 + ptb_len band2)%nat
      (Tiling.PL.ip_time_stamp1_ext tau2)).
  assert (Hprefix_len : List.length prefix1 = List.length prefix2).
  {
    subst prefix1 prefix2.
    unfold instr_point_ext_band_prefix_ts.
    rewrite !firstn_length, Hts11_old, Hts12_old.
    unfold affine_product. rewrite !map_length.
    pose proof (infer_pinstr_second_level_band_bound _ _ _ _ Hinfer1).
    pose proof (infer_pinstr_second_level_band_bound _ _ _ _ Hinfer2).
    lia.
  }
  assert (Hold_split1 :
    Tiling.PL.ip_time_stamp1_ext tau1 = prefix1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite <- firstn_skipn with (n := ptb_start band1)
      (l := Tiling.PL.ip_time_stamp1_ext tau1) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band1)
      (l := skipn (ptb_start band1) (Tiling.PL.ip_time_stamp1_ext tau1)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hold_split2 :
    Tiling.PL.ip_time_stamp1_ext tau2 = prefix2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite <- firstn_skipn with (n := ptb_start band2)
      (l := Tiling.PL.ip_time_stamp1_ext tau2) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band2)
      (l := skipn (ptb_start band2) (Tiling.PL.ip_time_stamp1_ext tau2)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hsched_before1_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi1)
      (Tiling.PL.pi_schedule before_pi1)).
  { rewrite <- Hlen_env. exact Hsched_before1. }
  assert (Hsched_before2_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi2)
      (Tiling.PL.pi_schedule before_pi2)).
  { rewrite <- Hlen_env. exact Hsched_before2. }
  assert (Hexpected_ts1 :
    affine_product
      (stripmine_second_level_schedule_after_env_by_layout
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi1) band1)
      (Tiling.PL.ip_index_ext tau1) =
    prefix1 ++ tiles1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1 tiles1.
    unfold instr_point_ext_band_prefix_ts,
           instr_point_ext_band_block_ts,
           second_level_schedule_tile_block_by_layout.
    rewrite Hidx_split1, Hadded_tiles1.
    assert (Henv_cols1 :
      (List.length envv <=
       List.length envv + Tiling.PL.pi_depth before_pi1)%nat) by lia.
    pose proof
      (stripmine_second_level_schedule_after_env_by_layout_eval
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi1) band1
         (List.length envv + Tiling.PL.pi_depth before_pi1)
         envv roots1 children1 point1 Hsched_before1_env Henv_cols1
         eq_refl Hroots_len1 Hroots_children1) as Heval1.
    rewrite <- Hts11_old in Heval1.
    subst roots1 children1.
    repeat rewrite app_assoc in Heval1.
    repeat rewrite app_assoc.
    exact Heval1.
  }
  assert (Hexpected_ts2 :
    affine_product
      (stripmine_second_level_schedule_after_env_by_layout
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi2) band2)
      (Tiling.PL.ip_index_ext tau2) =
    prefix2 ++ tiles2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2 tiles2.
    unfold instr_point_ext_band_prefix_ts,
           instr_point_ext_band_block_ts,
           second_level_schedule_tile_block_by_layout.
    rewrite Hidx_split2, Hadded_tiles2.
    assert (Henv_cols2 :
      (List.length envv <=
       List.length envv + Tiling.PL.pi_depth before_pi2)%nat) by lia.
    pose proof
      (stripmine_second_level_schedule_after_env_by_layout_eval
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi2) band2
         (List.length envv + Tiling.PL.pi_depth before_pi2)
         envv roots2 children2 point2 Hsched_before2_env Henv_cols2
         eq_refl Hroots_len2 Hroots_children2) as Heval2.
    rewrite <- Hts12_old in Heval2.
    subst roots2 children2.
    repeat rewrite app_assoc in Heval2.
    repeat rewrite app_assoc.
    exact Heval2.
  }
  pose proof
    (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ (Tiling.PL.ip_index_ext tau1) Hsched_match1) as Htime_eq1.
  pose proof
    (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ (Tiling.PL.ip_index_ext tau2) Hsched_match2) as Htime_eq2.
  rewrite <- Hts21_after in Htime_eq1.
  rewrite <- Hts22_after in Htime_eq2.
  rewrite Hlen_env, Hexpected_ts1 in Htime_eq1.
  rewrite Hlen_env, Hexpected_ts2 in Htime_eq2.
  assert (Hnew_not_lt :
    lex_compare
      (Tiling.PL.ip_time_stamp2_ext tau1)
      (Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band_ts2 ++ suffix2) <> Lt).
  {
    assert (Hcompare :
      lex_compare
        (Tiling.PL.ip_time_stamp2_ext tau1)
        (Tiling.PL.ip_time_stamp2_ext tau2) =
      lex_compare
        (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
        (prefix2 ++ tiles2 ++ band_ts2 ++ suffix2)).
    {
      transitivity
        (lex_compare
           (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
           (Tiling.PL.ip_time_stamp2_ext tau2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Hprefix_eq : prefix1 = prefix2).
  {
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hold_split1, Hold_split2 in Hold.
    repeat rewrite <- app_assoc in Hnew_expected_not_lt.
    eapply preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  assert (Hband_len : List.length band_ts1 = List.length band_ts2).
  {
    subst band_ts1 band_ts2.
    rewrite Hband_rows1, Hband_rows2.
    unfold affine_product. rewrite !map_length.
    rewrite Hroot_size_len1, Hroot_size_len2, Hroot_sizes_eq.
    reflexivity.
  }
  assert (Htiles_eq : band_ts1 = band_ts2 -> tiles1 = tiles2).
  {
    intro Hband_eq_ts.
    subst tiles1 tiles2 band_ts1 band_ts2.
    eapply second_level_schedule_tile_block_by_layout_eq_common_sizes; eauto.
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
      second_level_schedule_tile_block_by_layout_pointwise_le_common_sizes;
      eauto.
    rewrite <- Hband_rows1, <- Hband_rows2.
    exact Hband_le.
  }
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (stripmined_reversal_implies_decreasing_band_component
       prefix1 prefix2 tiles1 tiles2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Htiles_mono Hold Hnew_expected_not_lt)
    as [Hslice [dim [x [y [Hx [Hy Hgt]]]]]].
  assert (Hband_ts1_len : List.length band_ts1 = ptb_len band1).
  {
    subst band_ts1. rewrite Hband_rows1.
    unfold affine_product. rewrite List.map_length. lia.
  }
  assert (Hdim : (dim < ptb_len band1)%nat).
  {
    rewrite <- Hband_ts1_len.
    apply nth_error_Some. rewrite Hx. discriminate.
  }
  subst band2.
  exists band1.
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - unfold instr_point_ext_same_band_slice. exact Hslice.
  - exists dim, x, y.
    repeat split; try assumption.
    + eapply nth_error_band_block_to_full; eauto.
    + eapply nth_error_band_block_to_full; eauto.
Qed.

Lemma second_level_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    check_pinstr_list_second_level_schedule_stripminedb
      (List.length before_ctxt) before_pis after_pis bands = true ->
    common_second_level_recipe_sizes recipes ->
    common_band_start bands ->
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
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
      exists band,
        nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
        instr_point_ext_same_band_slice band tau1 tau2 /\
        instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros.
  eapply
    (second_level_local_reversal_bridge_by_layout_wf_with_env_len
       SecondLevelGrouped);
    eauto using
      check_pinstr_list_second_level_schedule_by_layoutb_implies_symmetricb.
Qed.

Lemma second_level_local_reversal_bridge_interleaved_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    check_pinstr_list_second_level_schedule_interleavedb
      (List.length before_ctxt) before_pis after_pis bands = true ->
    common_second_level_recipe_sizes recipes ->
    common_band_start bands ->
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
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
      exists band,
        nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
        instr_point_ext_same_band_slice band tau1 tau2 /\
        instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros.
  eapply
    (second_level_local_reversal_bridge_by_layout_wf_with_env_len
       SecondLevelInterleaved);
    eauto using
      check_pinstr_list_second_level_schedule_by_layoutb_implies_symmetricb.
Qed.

Lemma lift_schedule_after_env_nonempty_local :
  forall added_dims env_size sched,
    sched <> [] ->
    Tiling.lift_schedule_after_env added_dims env_size sched <> [].
Proof.
  intros added_dims env_size sched Hsched Hlift.
  unfold Tiling.lift_schedule_after_env,
         Tiling.lift_affine_function_after_env in Hlift.
  apply map_eq_nil in Hlift.
  contradiction.
Qed.

Lemma infer_second_level_bands_compose_schedule1_nonempty :
  forall env_size before_pis after_pis ws bands recipes,
    List.length before_pis = List.length after_pis ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    Forall2
      (fun pi_ext _ => Tiling.PL.pi_schedule1_ext pi_ext <> [])
      (Tiling.compose_tiling_pinstrs_ext_from_after
         env_size before_pis after_pis ws)
      bands.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws bands recipes Hlen Hinfer.
  - destruct after_pis; [|discriminate].
    destruct ws; simpl in Hinfer; try discriminate.
    inversion Hinfer; subst. constructor.
  - destruct after_pis as [|after_pi after_pis]; [discriminate|].
    destruct ws as [|w ws]; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_second_level_band before_pi w)
      as [[band recipe]|] eqn:Hhead; try discriminate.
    destruct (infer_pinstr_list_second_level_bands before_pis ws)
      as [[bands' recipes']|] eqn:Htail; try discriminate.
    inversion Hinfer; subst bands recipes; clear Hinfer.
    simpl.
    constructor.
    + cbn [Tiling.compose_tiling_pinstr_ext].
      pose proof
        (infer_pinstr_second_level_band_positive_len
           before_pi w band recipe Hhead) as Hpositive.
      pose proof
        (infer_pinstr_second_level_band_bound
           before_pi w band recipe Hhead) as Hbound.
      eapply lift_schedule_after_env_nonempty_local.
      intro Hempty.
      rewrite Hempty in Hbound.
      simpl in Hbound.
      lia.
    + eapply IH; eauto.
Qed.

Lemma check_pprog_second_level_permutable_bands_via_validate_tiling_sound_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws envv,
    List.length before_ctxt = List.length envv ->
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    mayReturn
      (check_pprog_second_level_permutable_bands_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    exists bands recipes,
      check_pprog_second_level_schedule_stripminedb
        (before_pis, before_ctxt, before_vars)
        (after_pis, before_ctxt, before_vars)
        ws = Some (bands, recipes) /\
      pprog_tiling_reordering_safe
        envv before_pis after_pis ws bands.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws envv
         Hlen_env Hprog Hwf_ws Hsizes_ws Hdepths Hwf_before Hwf_after Hwits
         Hcheck.
  unfold check_pprog_second_level_permutable_bands_via_validate_tiling
    in Hcheck.
  assert (Hctxt_refl : TilingCheck.ctxt_eqb before_ctxt before_ctxt = true).
  {
    apply (proj2 (TilingCheck.ctxt_eqb_eq before_ctxt before_ctxt)).
    reflexivity.
  }
  assert (Hvars_refl :
    TilingCheck.ctxt_ty_eqb before_vars before_vars = true).
  { apply ctxt_ty_eqb_refl_local. }
  rewrite Hctxt_refl, Hvars_refl in Hcheck.
  destruct
    (check_pprog_second_level_schedule_stripminedb
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws)
    as [[bands recipes]|] eqn:Hshape.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  simpl in Hcheck.
  destruct
    (check_pprog_second_level_schedule_stripminedb_sound
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws bands recipes Hshape)
    as [Hinfer [Hsched [Hrecipe_sizes Hcommon]]].
  destruct (infer_pinstr_list_second_level_bands_lengths _ _ _ _ Hinfer)
    as [Hlen_ws [Hlen_bands _]].
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_lengths
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hprog)
    as [Hlen_after _].
  assert (Hcompose_len :
    List.length
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws) =
    List.length bands).
  {
    rewrite
      (Tiling.compose_tiling_pinstrs_ext_from_after_preserve_length
         (List.length before_ctxt) before_pis after_pis ws
         Hlen_after Hlen_ws).
    exact Hlen_bands.
  }
  assert (Hcomposed_wf :
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  assert (Hschedule1_nonempty :
    Forall2
      (fun pi_ext _ => Tiling.PL.pi_schedule1_ext pi_ext <> [])
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)
      bands).
  {
    eapply infer_second_level_bands_compose_schedule1_nonempty; eauto.
  }
  assert (Hcomponentwise :
    pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands).
  {
    eapply
      (check_pinstr_list_pluto_permutable_bands_components_sound
         before_pis after_pis ws bands before_ctxt envv); eauto.
  }
  exists bands, recipes.
  split; [reflexivity|].
  eapply
    (pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge
       envv before_pis after_pis ws bands); [exact Hcomponentwise|].
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  eapply
    (second_level_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands recipes envv);
    eauto.
Qed.

Lemma tiling_sourceb_validate_correct_with_reordering :
  forall before after ws bands st1 st2,
    TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
    (let '(before_pis, before_ctxt, _) := before in
     let '(after_pis, _, _) := after in
     forall envv,
       List.length before_ctxt = List.length envv ->
       pprog_tiling_reordering_safe envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics after st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws bands st1 st2 Hsource Hperm Hsem_after.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl in *.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hsource)
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
    simpl. repeat split; auto.
  }
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length before_ctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  { rewrite List.map_length in Hlen_ws_map. exact Hlen_ws_map. }
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
  { rewrite <- Hlen_env. exact Hwf. }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
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
       Hlen_after Hlen_ws Hwits (Hperm envv Hlen_env)
       Hlayer Halias Hpoly)
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

Lemma checked_tiling_second_level_band_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_second_level_permutable_bands_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hsource Hwf_before Hwf_after Hcheck Hsem.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  eapply
    (tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws [] st1 st2); [exact Hsource| |exact Hsem].
  simpl.
  intros envv Hlen_env.
  destruct
    (check_pprog_second_level_permutable_bands_via_validate_tiling_sound_with_env_len
       before_pis before_ctxt before_vars after_pis ws envv
       Hlen_env Hprog Hwf_ws Hsizes_ws Hdepths
       Hwf_before Hwf_after Hwits Hcheck)
    as [bands [recipes [_ Hsafe]]].
  unfold pprog_tiling_reordering_safe,
         pprog_permutable_tiling_bands in *.
  exact Hsafe.
Qed.

Lemma checked_tiling_ordinary_band_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws bands st1 st2,
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
    check_pprog_tiling_schedule_stripminedb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
    infer_pprog_tiling_bands
      (before_pis, before_ctxt, before_vars) ws = Some bands ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_pluto_permutable_tiling_bands_primary
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
         Hsource Hschedule Hinfer Hwf_before Hwf_after Hcheck Hsem.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  destruct
    (check_pprog_tiling_schedule_stripminedb_sound_flat
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hschedule)
    as [bands' [Hinfer' [Hbands [_ _]]]].
  unfold infer_pprog_tiling_bands in Hinfer.
  simpl in Hinfer.
  rewrite Hinfer in Hinfer'.
  inversion Hinfer'; subst bands'; clear Hinfer'.
  eapply
    (tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws bands st1 st2); [exact Hsource| |exact Hsem].
  simpl.
  intros envv Hlen_env.
  unfold check_pprog_pluto_permutable_tiling_bands_primary in Hcheck.
  bind_imp_destruct Hcheck strong_ok Hstrong_check.
  destruct strong_ok.
  - apply mayReturn_pure in Hcheck.
    destruct
      (check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling_sound_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer Hwf_before Hwf_after Hdepths Hwits Hstrong_check)
      as [Hstrong Harity].
    eapply
      (pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
  - eapply
      (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
Qed.

Lemma checked_tiling_whole_program_permutability_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
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
         ws (repeat dummy_tiling_band (List.length before_pis)))
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hsource Hwf_before Hwf_after Hcheck Hsem.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [_ [_ Hdepths]]]].
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_lengths
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hprog)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length before_pis = List.length ws).
  {
    rewrite List.map_length in Hlen_ws_map.
    lia.
  }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  eapply
    (tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws (repeat dummy_tiling_band (List.length before_pis)) st1 st2);
    [exact Hsource| |exact Hsem].
  simpl.
  intros envv Hlen_env.
  eapply
    (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_lengths
       before_pis before_ctxt before_vars after_pis ws
       (repeat dummy_tiling_band (List.length before_pis)) envv).
  - exact Hlen_env.
  - exact Hlen_after.
  - exact Hlen_ws.
  - rewrite repeat_length. reflexivity.
  - exact Hwf_before.
  - exact Hwf_after.
  - exact Hdepths.
  - exact Hwits.
  - exact Hcheck.
Qed.

Lemma checked_tiling_ordinary_direct_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_ordinary_tiling_permutability_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hsource Hwf_before Hwf_after Hcheck Hsem.
  unfold check_pprog_ordinary_tiling_permutability_via_validate_tiling in Hcheck.
  destruct (check_ordinary_tiling_witnessesb ws) eqn:Hordinary.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  eapply
    (checked_tiling_whole_program_permutability_validate_correct_same_ctxt
       before_pis before_ctxt before_vars after_pis ws st1 st2); eauto.
Qed.

Lemma checked_tiling_structural_second_level_direct_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_structural_second_level_permutability_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hsource Hwf_before Hwf_after Hcheck Hsem.
  unfold
    check_pprog_structural_second_level_permutability_via_validate_tiling
    in Hcheck.
  destruct
    (check_pprog_statementwise_second_level_scheduleb
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws)
    as [[bands recipes]|] eqn:Hshape.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  eapply
    (checked_tiling_whole_program_permutability_validate_correct_same_ctxt
       before_pis before_ctxt before_vars after_pis ws st1 st2); eauto.
Qed.

Lemma checked_tiling_source_like_second_level_direct_validate_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      ws = true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_pprog_source_like_second_level_permutability_via_validate_tiling
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hsource Hwf_before Hwf_after Hcheck Hsem.
  unfold
    check_pprog_source_like_second_level_permutability_via_validate_tiling
    in Hcheck.
  destruct (check_pprog_source_like_second_level_recipesb before_pis ws)
    eqn:Hrecipes.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  eapply
    (checked_tiling_whole_program_permutability_validate_correct_same_ctxt
       before_pis before_ctxt before_vars after_pis ws st1 st2); eauto.
Qed.

Lemma checked_tiling_sourceb_first_band_check_correct :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_first_band_check
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  unfold checked_tiling_sourceb_first_band_check in Hcheck.
  destruct
    (TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws)
    eqn:Hsource.
  2:{
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  cbn beta iota zeta in Hcheck.
  bind_imp_destruct Hcheck ordinary_ok Hordinary.
  destruct ordinary_ok.
  - apply mayReturn_pure in Hcheck.
    destruct
      (check_pprog_tiling_schedule_stripminedb
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      eqn:Hschedule.
    2:{ apply mayReturn_pure in Hordinary. discriminate. }
    destruct
      (infer_pprog_tiling_bands
         (before_pis, before_ctxt, before_vars) ws)
      as [bands|] eqn:Hinfer.
    2:{ apply mayReturn_pure in Hordinary. discriminate. }
    simpl in Hordinary.
    eapply
      (checked_tiling_ordinary_band_validate_correct_same_ctxt
         before_pis before_ctxt before_vars after_pis ws bands st1 st2);
      eauto.
  - bind_imp_destruct Hcheck ordinary_direct_ok Hordinary_direct.
    destruct ordinary_direct_ok.
    + apply mayReturn_pure in Hcheck.
      eapply
        (checked_tiling_ordinary_direct_validate_correct_same_ctxt
           before_pis before_ctxt before_vars after_pis ws st1 st2);
        eauto.
    + bind_imp_destruct Hcheck second_level_ok Hsecond.
      destruct second_level_ok.
      * apply mayReturn_pure in Hcheck.
        eapply
          (checked_tiling_second_level_band_validate_correct_same_ctxt
             before_pis before_ctxt before_vars after_pis ws st1 st2);
          eauto.
      * bind_imp_destruct Hcheck structural_second_level_ok Hstructural.
        destruct structural_second_level_ok.
        -- apply mayReturn_pure in Hcheck.
           eapply
             (checked_tiling_structural_second_level_direct_validate_correct_same_ctxt
                before_pis before_ctxt before_vars after_pis ws st1 st2);
             eauto.
        -- eapply
             (checked_tiling_source_like_second_level_direct_validate_correct_same_ctxt
                before_pis before_ctxt before_vars after_pis ws st1 st2);
             eauto.
Qed.

Lemma checked_tiling_sourceb_first_band_check_outer_correct :
  forall before after ws st1 st2,
    PolIRs.PolyLang.wf_pprog_affine before ->
    PolIRs.PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_sourceb_first_band_check
         (Base.outer_to_tiling_pprog before)
         (Base.outer_to_tiling_pprog after)
         ws)
      true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hwf_before Hwf_after Hcheck Hsem_after.
  remember (Base.outer_to_tiling_pprog before)
    as before_tiling eqn:Hbefore_tiling_eq.
  remember (Base.outer_to_tiling_pprog after)
    as after_tiling eqn:Hafter_tiling_eq.
  destruct before_tiling as [[before_pis before_ctxt] before_vars].
  destruct after_tiling as [[after_pis after_ctxt] after_vars].
  simpl in Hbefore_tiling_eq, Hafter_tiling_eq.
  assert (Hsource :
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = true).
  {
    pose proof Hcheck as Hcheck_source.
    unfold checked_tiling_sourceb_first_band_check in Hcheck_source.
    destruct
      (TilingCheck.check_pprog_tiling_sourceb
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars) ws)
      eqn:Hsource_check; [reflexivity|].
    apply mayReturn_pure in Hcheck_source.
    discriminate.
  }
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hsource)
    as [Hprog _].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt_eq [Hvars_eq _]].
  subst after_ctxt after_vars.
  pose proof
    (Base.outer_to_tiling_wf_pprog_affine before Hwf_before)
    as Hwf_before_tiling.
  rewrite <- Hbefore_tiling_eq in Hwf_before_tiling.
  destruct Hwf_before_tiling as [_ Hwf_before_tiling].
  assert (Hwfbefore_pis :
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis).
  {
    eapply Forall_forall.
    intros pi Hin.
    eapply Tiling.PL.wf_pinstr_affine_implies_wf_pinstr_tiling.
    eapply Hwf_before_tiling; eauto.
  }
  pose proof
    (Base.outer_to_tiling_wf_pprog_general after Hwf_after)
    as Hwf_after_tiling.
  rewrite <- Hafter_tiling_eq in Hwf_after_tiling.
  destruct Hwf_after_tiling as [_ Hwf_after_tiling].
  assert (Hwfafter_pis :
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis).
  {
    eapply Forall_forall.
    intros pi Hin.
    eapply Hwf_after_tiling; eauto.
  }
  pose proof
    (checked_tiling_sourceb_first_band_check_correct
       before_pis before_ctxt before_vars after_pis ws st1 st2
       Hwfbefore_pis Hwfafter_pis Hcheck) as Hcorr.
  apply Base.outer_to_tiling_instance_list_semantics_iff in Hsem_after.
  rewrite <- Hafter_tiling_eq in Hsem_after.
  specialize (Hcorr Hsem_after).
  destruct Hcorr as [st2' [Hbefore_tiling Heq]].
  rewrite Hbefore_tiling_eq in Hbefore_tiling.
  apply Base.outer_to_tiling_instance_list_semantics_iff in Hbefore_tiling.
  exists st2'. split; assumption.
Qed.

Lemma checked_tiling_schedule_sourceb_first_runtime_validate_route_correct :
  forall before after ws st1 st2 route,
    PolIRs.PolyLang.wf_pprog_affine before ->
    PolIRs.PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_schedule_sourceb_first_runtime_validate_route
         before after ws)
      route ->
    tiling_band_validation_route_acceptsb route = true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 route Hwf_before Hwf_after
         Hroute Haccept Hsem_after.
  unfold checked_tiling_schedule_sourceb_first_runtime_validate_route in Hroute.
  bind_imp_destruct Hroute band_ok Hband.
  destruct band_ok.
  - apply mayReturn_pure in Hroute.
    subst route.
    eapply checked_tiling_sourceb_first_band_check_outer_correct; eauto.
  - bind_imp_destruct Hroute canonical_ok Hcanonical.
    destruct canonical_ok.
    + apply mayReturn_pure in Hroute.
      subst route.
      eapply Canonical.checked_tiling_schedule_canonical_validate_poly_correct;
        eauto.
    + bind_imp_destruct Hroute fallback_ok Hfallback.
      apply mayReturn_pure in Hroute.
      destruct fallback_ok.
      * subst route.
        eapply Base.checked_tiling_validate_poly_correct; eauto.
      * subst route. simpl in Haccept. discriminate.
Qed.

Lemma check_pprog_permutable_tiling_bands_runtime_sound_with_env_len :
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    mayReturn
      (check_pprog_permutable_tiling_bands_runtime
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands)
      true ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer_bands Hbands Hprog_full Hwf_ws Hsizes_ws Hdepths
         Hwf_before Hwf_after Hwits Hcheck.
  unfold check_pprog_permutable_tiling_bands_runtime in Hcheck.
  bind_imp_destruct Hcheck route Hroute.
  apply mayReturn_pure in Hcheck.
  unfold check_pprog_permutable_tiling_bands_runtime_route in Hroute.
  bind_imp_destruct Hroute band_ok Hband_check.
  destruct band_ok.
  - apply mayReturn_pure in Hroute.
    subst route.
    destruct
      (check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling_sound_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer_bands Hwf_before Hwf_after Hdepths Hwits Hband_check)
      as [Hstrong Harity].
    eapply
      (pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
  - bind_imp_destruct Hroute fallback_ok Hfallback_check.
    apply mayReturn_pure in Hroute.
    destruct fallback_ok.
    + subst route.
      eapply
      (check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
    + subst route.
      simpl in Hcheck.
      discriminate.
Qed.

Lemma checked_tiling_schedule_stripmined_and_runtime_validate_correct_same_ctxt :
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
      (check_pprog_permutable_tiling_bands_runtime
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
         Hshape Hinfer Hwf_before Hwf_after Hcheck Hsem.
  eapply
    checked_tiling_schedule_stripmined_validate_correct_same_ctxt_with_reordering_checker;
    eauto.
  intros envv Hlen Hbands Hprog Hwf_ws Hsizes Hdepths Hwits.
  eapply
    (check_pprog_permutable_tiling_bands_runtime_sound_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
Qed.

Lemma checked_tiling_schedule_stripmined_and_runtime_validate_outer_correct :
  forall before after ws st1 st2,
    PolIRs.PolyLang.wf_pprog_affine before ->
    PolIRs.PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_schedule_stripmined_and_runtime_validate_outer
         before after ws)
      true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hwf_before Hwf_after Hcheck Hsem_after.
  unfold checked_tiling_schedule_stripmined_and_runtime_validate_outer in Hcheck.
  bind_imp_destruct Hcheck shape_ok Hshape.
  destruct shape_ok.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  remember (Base.outer_to_tiling_pprog before)
    as before_tiling eqn:Hbefore_tiling_eq.
  remember (Base.outer_to_tiling_pprog after)
    as after_tiling eqn:Hafter_tiling_eq.
  destruct (infer_pprog_tiling_bands before_tiling ws)
    as [bands|] eqn:Hbands.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  pose proof Hshape as Hshape_sched.
  unfold checked_tiling_schedule_stripmined_validate_outer in Hshape.
  unfold checked_tiling_schedule_stripmined_validate_outer,
         checked_tiling_schedule_stripmined_validate
    in Hshape_sched.
  apply mayReturn_pure in Hshape_sched.
  apply andb_true_iff in Hshape_sched.
  destruct Hshape_sched as [_ Hsched_only].
  destruct before_tiling as [[before_pis before_ctxt] before_vars].
  destruct after_tiling as [[after_pis after_ctxt] after_vars].
  simpl in Hbefore_tiling_eq, Hafter_tiling_eq.
  rewrite <- Hbefore_tiling_eq in Hshape, Hsched_only.
  rewrite <- Hafter_tiling_eq in Hshape, Hsched_only.
  simpl in Hshape, Hsched_only, Hbands.
  pose proof
    (check_pprog_tiling_schedule_stripminedb_ctxt_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars)
       ws Hsched_only)
    as [Hctxt_eq Hvars_eq].
  pose proof
    (Base.outer_to_tiling_wf_pprog_affine before Hwf_before)
    as Hwf_before_tiling.
  rewrite <- Hbefore_tiling_eq in Hwf_before_tiling.
  destruct Hwf_before_tiling as [_ Hwf_before_tiling].
  assert (Hwfbefore_pis :
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis).
  {
    eapply Forall_forall.
    intros pi Hin.
    eapply Tiling.PL.wf_pinstr_affine_implies_wf_pinstr_tiling.
    eapply Hwf_before_tiling; eauto.
  }
  pose proof
    (Base.outer_to_tiling_wf_pprog_general after Hwf_after)
    as Hwf_after_tiling.
  rewrite <- Hafter_tiling_eq in Hwf_after_tiling.
  rewrite <- Hctxt_eq, <- Hvars_eq in Hwf_after_tiling.
  destruct Hwf_after_tiling as [_ Hwf_after_tiling].
  assert (Hwfafter_pis :
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis).
  {
    eapply Forall_forall.
    intros pi Hin.
    eapply Hwf_after_tiling; eauto.
  }
  rewrite <- Hctxt_eq, <- Hvars_eq in Hshape, Hcheck.
  pose proof
    (checked_tiling_schedule_stripmined_and_runtime_validate_correct_same_ctxt
       before_pis before_ctxt before_vars after_pis ws bands st1 st2
       Hshape Hbands Hwfbefore_pis Hwfafter_pis Hcheck)
    as Hcorr.
  apply Base.outer_to_tiling_instance_list_semantics_iff in Hsem_after.
  rewrite <- Hafter_tiling_eq in Hsem_after.
  rewrite <- Hctxt_eq, <- Hvars_eq in Hsem_after.
  specialize (Hcorr Hsem_after).
  destruct Hcorr as [st_mid [Hmid_tiling Heq_mid]].
  rewrite Hbefore_tiling_eq in Hmid_tiling.
  apply Base.outer_to_tiling_instance_list_semantics_iff in Hmid_tiling.
  exists st_mid.
  split; assumption.
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
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
         Hcheck Harity_before Hwf_before_pis Hpluto Hsem_after.
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
    - exact Hwf_before_pis.
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
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
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
         Hcheck Harity_before _ Hwf_before_pis Hpluto Hsem_after.
  eapply checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto_wf; eauto.
Qed.

Lemma validate_instr_and_list_pluto_band_component_direct_true_pair :
  forall pi pis band dim env_size,
    mayReturn
      (validate_instr_and_list_pluto_band_component_direct
         pi pis band dim env_size)
      true ->
    forall pi',
      In pi' pis ->
      mayReturn
        (validate_two_instrs_pluto_band_component_direct
           pi pi' band dim env_size)
        true /\
      mayReturn
        (validate_two_instrs_pluto_band_component_direct
           pi' pi band dim env_size)
        true.
Proof.
  intros pi pis.
  induction pis as [|pi' pis IH];
    intros band dim env_size Hcheck target Hin.
  - inversion Hin.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck forward Hforward.
    destruct forward.
    + bind_imp_destruct Hcheck backward Hbackward.
      destruct backward.
      * destruct Hin as [Heq | Hin].
        -- subst target. split; assumption.
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_list_pluto_band_component_direct_true_pair :
  forall pis band dim env_size,
    mayReturn
      (validate_instr_list_pluto_band_component_direct
         pis band dim env_size)
      true ->
    forall pi1 pi2,
      In pi1 pis ->
      In pi2 pis ->
      mayReturn
        (validate_two_instrs_pluto_band_component_direct
           pi1 pi2 band dim env_size)
        true.
Proof.
  intros pis.
  induction pis as [|pi pis IH];
    intros band dim env_size Hcheck pi1 pi2 Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck self Hself.
    destruct self.
    + bind_imp_destruct Hcheck cross Hcross.
      destruct cross.
      * destruct Hin1 as [Heq1 | Hin1];
        destruct Hin2 as [Heq2 | Hin2].
        -- subst pi1 pi2. exact Hself.
        -- subst pi1.
           eapply
             (proj1
                (validate_instr_and_list_pluto_band_component_direct_true_pair
                   pi pis band dim env_size Hcross pi2 Hin2)).
        -- subst pi2.
           eapply
             (proj2
                (validate_instr_and_list_pluto_band_component_direct_true_pair
                   pi pis band dim env_size Hcross pi1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_list_pluto_band_components_direct_from_true_component :
  forall pis band remaining start env_size,
    mayReturn
      (validate_instr_list_pluto_band_components_direct_from
         pis band remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_instr_list_pluto_band_component_direct
           pis band dim env_size)
        true.
Proof.
  intros pis band remaining.
  induction remaining as [|remaining IH];
    intros start env_size Hcheck dim Hrange.
  - lia.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck component_ok Hcomponent.
    destruct component_ok.
    + destruct (Nat.eq_dec dim start) as [Heq | Hneq].
      * subst dim. exact Hcomponent.
      * eapply IH.
        -- exact Hcheck.
        -- lia.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma HdRel_filter_trans_local :
  forall (A: Type) (R: A -> A -> Prop) (keep: A -> bool) xs,
    Relations_1.Transitive R ->
    Sorted R xs ->
    forall x,
      HdRel R x xs ->
      HdRel R x (filter keep xs).
Proof.
  intros A R keep xs Htrans Hsorted.
  induction Hsorted as [|head xs Hsorted IH Hhead].
  - intros x Hbefore. constructor.
  - intros x Hbefore.
    inversion Hbefore as [|? ? Hx_head]; subst.
    simpl.
    destruct (keep head) eqn:Hkeep.
    + constructor. exact Hx_head.
    + eapply IH.
      destruct xs as [|next rest].
      * constructor.
      * inversion Hhead as [|? ? Hhead_next]; subst.
        constructor.
        eapply Htrans; eauto.
Qed.

Lemma Sorted_filter_trans_local :
  forall (A: Type) (R: A -> A -> Prop) (keep: A -> bool) xs,
    Relations_1.Transitive R ->
    Sorted R xs ->
    Sorted R (filter keep xs).
Proof.
  intros A R keep xs Htrans Hsorted.
  induction Hsorted as [|x xs Hsorted IH Hhead].
  - constructor.
  - simpl.
    destruct (keep x) eqn:Hkeep.
    + constructor.
      * exact IH.
      * eapply HdRel_filter_trans_local; eauto.
    + exact IH.
Qed.

Lemma flatten_instrs_ext_member_slice_local :
  forall envv pis ipl ip pi,
    Tiling.PL.flatten_instrs_ext envv pis ipl ->
    In ip ipl ->
    nth_error pis (Tiling.PL.ip_nth_ext ip) = Some pi ->
    exists ipli,
      Tiling.PL.flatten_instr_nth_ext
        envv (Tiling.PL.ip_nth_ext ip) pi ipli /\
      In ip ipli.
Proof.
  intros envv pis ipl ip pi Hflat Hin Hnth.
  destruct Hflat as [Henv [Hmem [Hnodup Hsorted]]].
  exists
    (filter
       (fun candidate =>
          Nat.eqb
            (Tiling.PL.ip_nth_ext candidate)
            (Tiling.PL.ip_nth_ext ip))
       ipl).
  split.
  - split.
    + intros candidate Hcandidate.
      apply filter_In in Hcandidate.
      destruct Hcandidate as [Hcandidate _].
      eapply Henv; eauto.
    + split.
      * intros candidate.
        split; intro Hcandidate.
        -- apply filter_In in Hcandidate.
           destruct Hcandidate as [Hcandidate Hsame].
           apply Nat.eqb_eq in Hsame.
           apply Hmem in Hcandidate.
           destruct Hcandidate as
             [pi' [Hnth' [Hprefix [Hbelongs Hlength]]]].
           rewrite Hsame in Hnth'.
           rewrite Hnth in Hnth'.
           inversion Hnth'; subst pi'.
           split; [exact Hprefix|].
           split; [exact Hbelongs|].
           split; [exact Hsame|exact Hlength].
        -- destruct Hcandidate as
             [Hprefix [Hbelongs [Hsame Hlength]]].
           apply filter_In.
           split.
           ++ apply Hmem.
              exists pi.
              rewrite Hsame.
              split; [exact Hnth|].
              split; [exact Hprefix|].
              split; [exact Hbelongs|exact Hlength].
           ++ apply Nat.eqb_eq. exact Hsame.
      * split.
        -- eapply NoDup_filter; eauto.
        -- eapply Sorted_filter_trans_local; eauto.
           eapply Tiling.PL.np_lt_ext_trans.
  - apply filter_In.
    split; [exact Hin|].
    apply Nat.eqb_refl.
Qed.

Lemma validate_two_instrs_pluto_band_component_direct_sound :
  forall env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim ip1 ip2,
    mayReturn
      (validate_two_instrs_pluto_band_component_direct
         pi1 pi2 band dim (List.length env))
      true ->
    Tiling.PL.wf_pinstr_ext_tiling env pi1 ->
    Tiling.PL.wf_pinstr_ext_tiling env pi2 ->
    List.length env = List.length envv ->
    Tiling.PL.flatten_instr_nth_ext envv nth1 pi1 ipl1 ->
    Tiling.PL.flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1) ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2) ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    instr_point_ext_same_band_slice band ip1 ip2 ->
    instr_point_ext_band_component_decreases_at band dim ip1 ip2 ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim ip1 ip2
         Hcheck Hwf1 Hwf2 Henv Hflat1 Hflat2 Hin1 Hin2
         Hvalid1 Hvalid2 Hold Hprefix Hcomponent.
  unfold validate_two_instrs_pluto_band_component_direct in Hcheck.
  destruct
    (make_pluto_band_component_guard_polys
       pi1 pi2 band dim (List.length env))
    as [[old_order bad_component]|] eqn:Hguards.
  - pose proof
      (make_pluto_band_component_guard_polys_point_sound
         env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim
         old_order bad_component ip1 ip2 Hguards Hwf1 Hwf2 Henv
         Hflat1 Hflat2 Hin1 Hin2 Hold Hprefix Hcomponent)
      as [Horder Hbad].
    assert (Hcollision :
      BandAffine.no_write_collision
        (Tiling.PL.pi_waccess_ext pi1)
        (Tiling.PL.pi_waccess_ext pi2)
        (Tiling.PL.pi_raccess_ext pi1)
        (Tiling.PL.pi_raccess_ext pi2)
        ip1 ip2).
    {
      eapply
        (BandAffine.validate_two_instrs_under_guards_implies_no_write_collision
           pi1 pi2 env nth1 nth2 envv ipl1 ipl2
           old_order bad_component true Hcheck eq_refl);
        eauto.
    }
    assert (Hinstr1 :
      Tiling.PL.ip_instruction_ext ip1 =
      Tiling.PL.pi_instr_ext pi1).
    {
      eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto.
    }
    assert (Hinstr2 :
      Tiling.PL.ip_instruction_ext ip2 =
      Tiling.PL.pi_instr_ext pi2).
    {
      eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto.
    }
    assert (Htf1 :
      Tiling.PL.ip_access_transformation_ext ip1 =
      Tiling.PL.ip_transformation_ext ip1).
    {
      assert (Haccess :
        Tiling.PL.ip_access_transformation_ext ip1 =
        Tiling.PL.pi_access_transformation_ext pi1).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
      assert (Hcurrent :
        Tiling.PL.ip_transformation_ext ip1 =
        Tiling.PL.pi_transformation_ext pi1).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
      destruct Hwf1 as [_ Hpi_eq].
      rewrite Haccess, Hcurrent, Hpi_eq.
      reflexivity.
    }
    assert (Htf2 :
      Tiling.PL.ip_access_transformation_ext ip2 =
      Tiling.PL.ip_transformation_ext ip2).
    {
      assert (Haccess :
        Tiling.PL.ip_access_transformation_ext ip2 =
        Tiling.PL.pi_access_transformation_ext pi2).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
      assert (Hcurrent :
        Tiling.PL.ip_transformation_ext ip2 =
        Tiling.PL.pi_transformation_ext pi2).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
      destruct Hwf2 as [_ Hpi_eq].
      rewrite Haccess, Hcurrent, Hpi_eq.
      reflexivity.
    }
    eapply BandAffine.no_write_collision_implies_permutable; eauto.
    + rewrite Hinstr1. exact Hvalid1.
    + rewrite Hinstr2. exact Hvalid2.
  - apply mayReturn_pure in Hcheck.
    discriminate.
Qed.

Lemma validate_instr_list_pluto_band_component_direct_sound :
  forall env envv pis band dim flat ip1 ip2,
    List.length env = List.length envv ->
    Forall (Tiling.PL.wf_pinstr_ext_tiling env) pis ->
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis ->
    mayReturn
      (validate_instr_list_pluto_band_component_direct
         pis band dim (List.length env))
      true ->
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    instr_point_ext_same_band_slice band ip1 ip2 ->
    instr_point_ext_band_component_decreases_at band dim ip1 ip2 ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros env envv pis band dim flat ip1 ip2 Henv Hwf Hvalid Hcheck
         Hflat Hin1 Hin2 Hold Hprefix Hcomponent.
  pose proof Hflat as Hflat_membership.
  destruct Hflat_membership as [_ [Hmem _]].
  apply Hmem in Hin1 as Hmember1.
  apply Hmem in Hin2 as Hmember2.
  destruct Hmember1 as
    [pi1 [Hnth1 [Henv1 [Hbelongs1 Hlen1]]]].
  destruct Hmember2 as
    [pi2 [Hnth2 [Henv2 [Hbelongs2 Hlen2]]]].
  assert (Hin_pi1 : In pi1 pis).
  { eapply nth_error_In; eauto. }
  assert (Hin_pi2 : In pi2 pis).
  { eapply nth_error_In; eauto. }
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip1 pi1 Hflat Hin1 Hnth1)
    as [slice1 [Hslice1 Hin_slice1]].
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip2 pi2 Hflat Hin2 Hnth2)
    as [slice2 [Hslice2 Hin_slice2]].
  assert (Hpair :
    mayReturn
      (validate_two_instrs_pluto_band_component_direct
         pi1 pi2 band dim (List.length env))
      true).
  {
    eapply validate_instr_list_pluto_band_component_direct_true_pair;
      eauto.
  }
  assert (Hwf1 : Tiling.PL.wf_pinstr_ext_tiling env pi1).
  {
    eapply Tiling.Forall_nth_error;
      eauto.
  }
  assert (Hwf2 : Tiling.PL.wf_pinstr_ext_tiling env pi2).
  {
    eapply Tiling.Forall_nth_error;
      eauto.
  }
  assert (Hvalid1 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip1) pi1 Hvalid Hnth1).
  }
  assert (Hvalid2 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip2) pi2 Hvalid Hnth2).
  }
  eapply
    (validate_two_instrs_pluto_band_component_direct_sound
       env envv
       (Tiling.PL.ip_nth_ext ip1)
       (Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 band dim ip1 ip2);
    eauto.
Qed.

Lemma check_pinstr_list_pluto_permutable_band_direct_sound :
  forall env envv before_pis after_pis ws band,
    List.length env = List.length envv ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    mayReturn
      (check_pinstr_list_pluto_permutable_band_direct
         (List.length env) before_pis after_pis ws band)
      true ->
    pprog_pluto_componentwise_permutable_band
      envv before_pis after_pis ws band.
Proof.
  intros env envv before_pis after_pis ws band Henv Hwf Hcheck.
  unfold check_pinstr_list_pluto_permutable_band_direct in Hcheck.
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[_ Hcomponents_true] Hvalid_true].
  subst components_ok.
  set (pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws).
  assert (Hvalid :
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis).
  {
    unfold pis.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  unfold pprog_pluto_componentwise_permutable_band,
         pprog_pluto_permutable_band.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hprefix Hdecreases.
  destruct Hdecreases as [dim Hcomponent].
  assert (Hcomponent_check :
    mayReturn
      (validate_instr_list_pluto_band_component_direct
         pis band dim (List.length env))
      true).
  {
    eapply
      validate_instr_list_pluto_band_components_direct_from_true_component.
    - exact Hcomponents.
    - destruct Hcomponent as
        [x [y [Hdim [Hx [Hy Hgt]]]]].
      lia.
  }
  assert (Hflat_env : Tiling.PL.flatten_instrs_ext envv pis flat).
  {
    unfold pis.
    rewrite Henv.
    exact Hflat.
  }
  eapply
    (validate_instr_list_pluto_band_component_direct_sound
       env envv pis band dim flat ip1 ip2);
    eauto.
Qed.

Lemma check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
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
      (check_pprog_pluto_permutable_tiling_bands_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands)
      true ->
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands /\
    uniform_schedule_arity before_pis.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Henv Hinfer Hwf_before Hwf_after Hdepths Hwits Hcheck.
  unfold check_pprog_pluto_permutable_tiling_bands_direct in Hcheck.
  assert (Hctxt_refl :
    TilingCheck.ctxt_eqb before_ctxt before_ctxt = true).
  {
    apply (proj2 (TilingCheck.ctxt_eqb_eq before_ctxt before_ctxt)).
    reflexivity.
  }
  assert (Hvars_refl :
    TilingCheck.ctxt_ty_eqb before_vars before_vars = true).
  { apply ctxt_ty_eqb_refl_local. }
  rewrite Hctxt_refl, Hvars_refl in Hcheck.
  destruct (infer_pinstr_list_tiling_bands_lengths _ _ _ Hinfer)
    as [_ Hlen_bands].
  rewrite <- Hlen_bands, Nat.eqb_refl in Hcheck.
  destruct (check_uniform_schedule_arityb before_pis) eqn:Huniform.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (infer_common_tiling_band bands) as [band|] eqn:Hcommon.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (check_common_tiling_band_recipeb ws) eqn:Hrecipe.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  simpl in Hcheck.
  split.
  - destruct (check_common_tiling_band_recipeb_sound _ Hrecipe)
      as [sizes Hrecipe_sound].
    exists band, sizes.
    split.
    + eapply infer_common_tiling_band_sound; exact Hcommon.
    + split.
      * exact Hrecipe_sound.
      * eapply
          (check_pinstr_list_pluto_permutable_band_direct_sound
             before_ctxt envv before_pis after_pis ws band);
          eauto.
        eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  - eapply check_uniform_schedule_arityb_sound.
    exact Huniform.
Qed.

(** Direct componentwise checking for statement-specific bands.  The
    componentwise semantic property only relates instruction points whose
    statements have the same inferred band.  Pairs with distinct bands, and
    components outside that shared band, therefore introduce no obligation. *)
Definition validate_two_instr_band_entries_component_direct
    (entry1 entry2: Tiling.PL.PolyInstr_ext * pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  let '(pi1, band1) := entry1 in
  let '(pi2, band2) := entry2 in
  if pinstr_tiling_band_eqb band1 band2 then
    if Nat.ltb dim (ptb_len band1) then
      validate_two_instrs_pluto_band_component_direct
        pi1 pi2 band1 dim env_size
    else pure true
  else pure true.

Fixpoint validate_instr_band_entry_and_list_component_direct
    (entry: Tiling.PL.PolyInstr_ext * pinstr_tiling_band)
    (entries: list (Tiling.PL.PolyInstr_ext * pinstr_tiling_band))
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry' :: entries' =>
      BIND forward <-
        validate_two_instr_band_entries_component_direct
          entry entry' dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instr_band_entries_component_direct
            entry' entry dim env_size -;
        if backward then
          validate_instr_band_entry_and_list_component_direct
            entry entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_band_entry_list_component_direct
    (entries: list (Tiling.PL.PolyInstr_ext * pinstr_tiling_band))
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry :: entries' =>
      BIND self <-
        validate_two_instr_band_entries_component_direct
          entry entry dim env_size -;
      if self then
        BIND cross <-
          validate_instr_band_entry_and_list_component_direct
            entry entries' dim env_size -;
        if cross then
          validate_instr_band_entry_list_component_direct
            entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_band_entry_list_components_direct_from
    (entries: list (Tiling.PL.PolyInstr_ext * pinstr_tiling_band))
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_instr_band_entry_list_component_direct
          entries dim env_size -;
      if component_ok then
        validate_instr_band_entry_list_components_direct_from
          entries remaining' (S dim) env_size
      else pure false
  end.

Definition check_pinstr_list_pluto_componentwise_permutable_bands_direct
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      env_size before_pis after_pis ws in
  let aligned :=
    Nat.eqb (List.length before_pis) (List.length after_pis) &&
    Nat.eqb (List.length before_pis) (List.length ws) &&
    Nat.eqb (List.length before_pis) (List.length pis) &&
    Nat.eqb (List.length before_pis) (List.length bands) in
  let valid_access := BandAffine.check_valid_access pis in
  let entries := combine pis bands in
  if aligned then
    BIND res <-
      validate_instr_band_entry_list_components_direct_from
        entries (max_tiling_band_len bands) O env_size -;
    pure (res && valid_access)
  else pure false.

Lemma validate_instr_band_entry_and_list_component_direct_true_pair :
  forall entry entries dim env_size,
    mayReturn
      (validate_instr_band_entry_and_list_component_direct
         entry entries dim env_size)
      true ->
    forall entry',
      In entry' entries ->
      mayReturn
        (validate_two_instr_band_entries_component_direct
           entry entry' dim env_size)
        true /\
      mayReturn
        (validate_two_instr_band_entries_component_direct
           entry' entry dim env_size)
        true.
Proof.
  intros entry entries.
  induction entries as [|entry' entries IH];
    intros dim env_size Hcheck target Hin.
  - inversion Hin.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck forward Hforward.
    destruct forward.
    + bind_imp_destruct Hcheck backward Hbackward.
      destruct backward.
      * destruct Hin as [Heq | Hin].
        -- subst target. split; assumption.
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_band_entry_list_component_direct_true_pair :
  forall entries dim env_size,
    mayReturn
      (validate_instr_band_entry_list_component_direct
         entries dim env_size)
      true ->
    forall entry1 entry2,
      In entry1 entries ->
      In entry2 entries ->
      mayReturn
        (validate_two_instr_band_entries_component_direct
           entry1 entry2 dim env_size)
        true.
Proof.
  intros entries.
  induction entries as [|entry entries IH];
    intros dim env_size Hcheck entry1 entry2 Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck self Hself.
    destruct self.
    + bind_imp_destruct Hcheck cross Hcross.
      destruct cross.
      * destruct Hin1 as [Heq1 | Hin1];
        destruct Hin2 as [Heq2 | Hin2].
        -- subst entry1 entry2. exact Hself.
        -- subst entry1.
           eapply
             (proj1
                (validate_instr_band_entry_and_list_component_direct_true_pair
                   entry entries dim env_size Hcross entry2 Hin2)).
        -- subst entry2.
           eapply
             (proj2
                (validate_instr_band_entry_and_list_component_direct_true_pair
                   entry entries dim env_size Hcross entry1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_band_entry_list_components_direct_from_true_component :
  forall entries remaining start env_size,
    mayReturn
      (validate_instr_band_entry_list_components_direct_from
         entries remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_instr_band_entry_list_component_direct
           entries dim env_size)
        true.
Proof.
  intros entries remaining.
  induction remaining as [|remaining IH];
    intros start env_size Hcheck dim Hrange.
  - lia.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck component_ok Hcomponent.
    destruct component_ok.
    + destruct (Nat.eq_dec dim start) as [Heq | Hneq].
      * subst dim. exact Hcomponent.
      * eapply IH.
        -- exact Hcheck.
        -- lia.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma nth_error_combine_some_in_local :
  forall (A B: Type) (xs: list A) (ys: list B) n x y,
    nth_error xs n = Some x ->
    nth_error ys n = Some y ->
    In (x, y) (combine xs ys).
Proof.
  intros A B xs.
  induction xs as [|x0 xs IH]; intros ys n x y Hx Hy.
  - destruct n; discriminate.
  - destruct ys as [|y0 ys]; [destruct n; discriminate|].
    destruct n as [|n].
    + inversion Hx; inversion Hy; subst. simpl. auto.
    + simpl in Hx, Hy. simpl. right. eapply IH; eauto.
Qed.

Lemma pinstr_tiling_band_eqb_refl_local :
  forall band, pinstr_tiling_band_eqb band band = true.
Proof.
  intros [start len].
  unfold pinstr_tiling_band_eqb.
  simpl.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

Lemma check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound :
  forall env envv before_pis after_pis ws bands,
    List.length env = List.length envv ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    mayReturn
      (check_pinstr_list_pluto_componentwise_permutable_bands_direct
         (List.length env) before_pis after_pis ws bands)
      true ->
    pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands.
Proof.
  intros env envv before_pis after_pis ws bands Henv Hwf Hcheck.
  unfold check_pinstr_list_pluto_componentwise_permutable_bands_direct
    in Hcheck.
  destruct
    (Nat.eqb (List.length before_pis) (List.length after_pis) &&
     Nat.eqb (List.length before_pis) (List.length ws) &&
     Nat.eqb
       (List.length before_pis)
       (List.length
          (Tiling.compose_tiling_pinstrs_ext_from_after
             (List.length env) before_pis after_pis ws)) &&
     Nat.eqb (List.length before_pis) (List.length bands))
    eqn:Haligned.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcomponents_true Hvalid_true].
  subst components_ok.
  set (pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws).
  assert (Hvalid :
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis).
  {
    unfold pis.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  unfold pprog_pluto_componentwise_permutable_bands.
  intros flat ip1 ip2 band Hflat Hin1 Hin2 Hband1 Hband2
         Hold Hprefix Hdecreases.
  assert (Hflat_pis : Tiling.PL.flatten_instrs_ext envv pis flat).
  {
    unfold pis.
    rewrite Henv.
    exact Hflat.
  }
  pose proof Hflat_pis as Hflat_membership.
  destruct Hflat_membership as [_ [Hmem _]].
  apply Hmem in Hin1 as Hmember1.
  apply Hmem in Hin2 as Hmember2.
  destruct Hmember1 as
    [pi1 [Hnth1 [Henv1 [Hbelongs1 Hpoint_len1]]]].
  destruct Hmember2 as
    [pi2 [Hnth2 [Henv2 [Hbelongs2 Hpoint_len2]]]].
  assert (Hin_pi1 : In pi1 pis).
  { eapply nth_error_In; eauto. }
  assert (Hin_pi2 : In pi2 pis).
  { eapply nth_error_In; eauto. }
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip1 pi1 Hflat_pis Hin1 Hnth1)
    as [slice1 [Hslice1 Hin_slice1]].
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip2 pi2 Hflat_pis Hin2 Hnth2)
    as [slice2 [Hslice2 Hin_slice2]].
  destruct Hdecreases as [dim Hcomponent].
  destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
  assert (Hcomponent_check :
    mayReturn
      (validate_instr_band_entry_list_component_direct
         (combine pis bands) dim (List.length env))
      true).
  {
    eapply
      validate_instr_band_entry_list_components_direct_from_true_component.
    - exact Hcomponents.
    - split; [lia|].
      eapply Nat.lt_le_trans.
      + exact Hdim.
      + eapply max_tiling_band_len_ge_nth_error; exact Hband1.
  }
  assert (Hentry1 : In (pi1, band) (combine pis bands)).
  {
    eapply nth_error_combine_some_in_local; eauto.
  }
  assert (Hentry2 : In (pi2, band) (combine pis bands)).
  {
    eapply nth_error_combine_some_in_local; eauto.
  }
  assert (Hpair_entry :
    mayReturn
      (validate_two_instr_band_entries_component_direct
         (pi1, band) (pi2, band) dim (List.length env))
      true).
  {
    eapply validate_instr_band_entry_list_component_direct_true_pair;
      eauto.
  }
  unfold validate_two_instr_band_entries_component_direct in Hpair_entry.
  rewrite pinstr_tiling_band_eqb_refl_local in Hpair_entry.
  assert (Hdim_bool : Nat.ltb dim (ptb_len band) = true).
  { apply Nat.ltb_lt. exact Hdim. }
  rewrite Hdim_bool in Hpair_entry.
  assert (Hwf1 : Tiling.PL.wf_pinstr_ext_tiling env pi1).
  { eapply Tiling.Forall_nth_error; eauto. }
  assert (Hwf2 : Tiling.PL.wf_pinstr_ext_tiling env pi2).
  { eapply Tiling.Forall_nth_error; eauto. }
  assert (Hvalid1 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip1) pi1 Hvalid Hnth1).
  }
  assert (Hvalid2 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip2) pi2 Hvalid Hnth2).
  }
  eapply
    (validate_two_instrs_pluto_band_component_direct_sound
       env envv
       (Tiling.PL.ip_nth_ext ip1)
       (Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 band dim ip1 ip2);
    eauto.
  exists x, y.
  repeat split; assumption.
Qed.

End TilingBandScheduleValidator.
