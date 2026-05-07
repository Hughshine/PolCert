Require Import ZArith.
Require Import Lia.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Require Import AffineValidator.
Require Import ParallelValidator.
Require Import PolIRs.

Module JamValidator (PolIRs : POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Instr := PolIRs.Instr.
Module AffineCore := AffineValidator PolIRs.
Module ParallelCore := ParallelValidator PolIRs.

Record jam_plan := {
  jam_outer_dim : nat;
  jam_factor : nat
}.

Record jam_cert := {
  certified_outer_dim : nat;
  certified_factor : nat
}.

Definition pprog_pis := ParallelCore.pprog_pis.
Definition pprog_varctxt := ParallelCore.pprog_varctxt.

Definition current_coord_schedule_row :=
  ParallelCore.current_coord_schedule_row.

Definition adjacent_jam_old_schedule
    (env_dim depth d : nat) : list (list Z * Z) :=
  ParallelCore.current_coord_prefix_schedule env_dim depth d ++
  [ current_coord_schedule_row env_dim depth d;
    current_coord_schedule_row env_dim depth (S d) ].

Definition adjacent_jam_new_schedule
    (env_dim depth d : nat) : list (list Z * Z) :=
  ParallelCore.current_coord_prefix_schedule env_dim depth d ++
  [ current_coord_schedule_row env_dim depth (S d);
    current_coord_schedule_row env_dim depth d ].

Definition adjacent_jam_old_pi
    (env_dim d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      adjacent_jam_old_schedule env_dim pi.(PolyLang.pi_depth) d;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition adjacent_jam_new_pi
    (env_dim d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      adjacent_jam_new_schedule env_dim pi.(PolyLang.pi_depth) d;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition adjacent_jam_old_pprog
    (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  ((List.map (adjacent_jam_old_pi (Datatypes.length varctxt) d) pis,
    varctxt), vars).

Definition adjacent_jam_new_pprog
    (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  ((List.map (adjacent_jam_new_pi (Datatypes.length varctxt) d) pis,
    varctxt), vars).

Definition adjacent_jam_cert_sound
    (pp : PolyLang.t) (cert : jam_cert) : Prop :=
  let d := cert.(certified_outer_dim) in
  forall envv ipl_old ipl_new,
    Datatypes.length (pprog_varctxt pp) = Datatypes.length envv ->
    PolyLang.flatten_instrs
      envv (pprog_pis (adjacent_jam_old_pprog pp d)) ipl_old ->
    PolyLang.flatten_instrs
      envv (pprog_pis (adjacent_jam_new_pprog pp d)) ipl_new ->
    exists ipl_ext,
      PolyLang.new_of_ext_list ipl_ext = ipl_new /\
      PolyLang.old_of_ext_list ipl_ext = ipl_old /\
      (forall ip1_ext ip2_ext,
          In ip1_ext ipl_ext ->
          In ip2_ext ipl_ext ->
          PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
          PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
          PolyLang.Permutable_ext ip1_ext ip2_ext).

Definition adjacent_jam_plan_well_formedb
    (pp : PolyLang.t) (plan : jam_plan) : bool :=
  let d := plan.(jam_outer_dim) in
  Nat.ltb 0 plan.(jam_factor) &&
  Nat.ltb (S d) (PolyLang.pprog_current_dim pp) &&
  ParallelCore.check_current_view_pprogb pp &&
  ParallelCore.all_pinstrs_cover_dimb (S d) pp.

Definition check_pprog_adjacent_jamb
    (pp : PolyLang.t) (plan : jam_plan) : imp bool :=
  if adjacent_jam_plan_well_formedb pp plan
  then
    AffineCore.validate
      (adjacent_jam_old_pprog pp plan.(jam_outer_dim))
      (adjacent_jam_new_pprog pp plan.(jam_outer_dim))
  else pure false.

Definition checked_jam_current
    (pp : PolyLang.t) (plan : jam_plan) : imp (result jam_cert) :=
  BIND ok <- check_pprog_adjacent_jamb pp plan -;
  if ok then
    pure
      (Okk
        {|
          certified_outer_dim := plan.(jam_outer_dim);
          certified_factor := plan.(jam_factor)
        |})
  else pure (Err "Jam validation failed").

Lemma check_pprog_adjacent_jamb_true_inv :
  forall pp plan,
    mayReturn (check_pprog_adjacent_jamb pp plan) true ->
    adjacent_jam_plan_well_formedb pp plan = true /\
    mayReturn
      (AffineCore.validate
         (adjacent_jam_old_pprog pp plan.(jam_outer_dim))
         (adjacent_jam_new_pprog pp plan.(jam_outer_dim)))
      true.
Proof.
  intros pp plan Hcheck.
  unfold check_pprog_adjacent_jamb in Hcheck.
  destruct (adjacent_jam_plan_well_formedb pp plan) eqn:Hwf.
  - split; [reflexivity | exact Hcheck].
  - apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma check_pprog_adjacent_jamb_sound :
  forall pp plan,
    mayReturn (check_pprog_adjacent_jamb pp plan) true ->
    adjacent_jam_cert_sound
      pp
      {|
        certified_outer_dim := plan.(jam_outer_dim);
        certified_factor := plan.(jam_factor)
      |}.
Proof.
  intros [[pis varctxt] vars] [d factor] Hcheck.
  simpl in *.
  destruct (check_pprog_adjacent_jamb_true_inv
              ((pis, varctxt), vars)
              {| jam_outer_dim := d; jam_factor := factor |}
              Hcheck)
    as [_ Hval].
  unfold adjacent_jam_cert_sound.
  simpl.
  intros envv ipl_old ipl_new Henvlen Hflat_old Hflat_new.
  eapply
    (AffineCore.validate_implies_permutability
       (adjacent_jam_old_pprog ((pis, varctxt), vars) d)
       (adjacent_jam_new_pprog ((pis, varctxt), vars) d)
       varctxt varctxt envv vars vars
       (List.map (adjacent_jam_old_pi (Datatypes.length varctxt) d) pis)
       (List.map (adjacent_jam_new_pi (Datatypes.length varctxt) d) pis)
       ipl_old ipl_new true).
  - exact Hval.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Henvlen.
  - exact Hflat_old.
  - exact Hflat_new.
Qed.

Lemma checked_jam_current_sound :
  forall pp plan cert,
    mayReturn (checked_jam_current pp plan) (Okk cert) ->
    adjacent_jam_cert_sound pp cert.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_jam_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok.
  - apply mayReturn_pure in Hret.
    inversion Hret; subst; clear Hret.
    eapply check_pprog_adjacent_jamb_sound.
    exact Hcheck.
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

Lemma checked_jam_current_factor_positive :
  forall pp plan cert,
    mayReturn (checked_jam_current pp plan) (Okk cert) ->
    (0 < cert.(certified_factor))%nat.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_jam_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok.
  - apply mayReturn_pure in Hret.
    inversion Hret; subst; clear Hret.
    destruct (check_pprog_adjacent_jamb_true_inv pp plan Hcheck) as [Hwf _].
    unfold adjacent_jam_plan_well_formedb in Hwf.
    repeat rewrite andb_true_iff in Hwf.
    destruct Hwf as [[[Hfactor _] _] _].
    apply Nat.ltb_lt. exact Hfactor.
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

End JamValidator.
