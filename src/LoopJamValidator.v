Require Import Lia.
Require Import List.
Require Import String.
Require Import ZArith.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Local Open Scope string_scope.
Import ListNotations.

Require Import Extractor.
Require Import AffineValidator.
Require Import JamValidator.
Require Import LoopJamNative.
Require Import PolIRs.
Require Import StrengthenDomain.

Module LoopJamValidator (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module Instr := PolIRs.Instr.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Module ExtractorCore := Extractor PolIRs.
Module AffineCore := AffineValidator PolIRs.
Module StrengthenCore := StrengthenDomain PolIRs.
Module JamCore := JamValidator PolIRs.
Module Native := LoopJamNative PolIRs.

Definition pprog_pis := JamCore.pprog_pis.
Definition pprog_varctxt := JamCore.pprog_varctxt.

Record loop_jam_cert := {
  loop_jam_poly : PolyLang.t;
  loop_jam_core_cert : JamCore.jam_cert
}.

Definition checked_loop_jam_current
    (loop : Loop.t) (plan : JamCore.jam_plan)
  : imp (result loop_jam_cert) :=
  match ExtractorCore.extractor loop with
  | Okk pol0 =>
      let pol := StrengthenCore.strengthen_pprog pol0 in
      BIND cert_res <- JamCore.checked_jam_current pol plan -;
      match cert_res with
      | Okk cert =>
          pure
            (Okk
              {|
                loop_jam_poly := pol;
                loop_jam_core_cert := cert
              |})
      | Err msg => pure (Err msg)
      end
  | Err msg => pure (Err msg)
  end.

Definition loop_jam_cert_sound (cert : loop_jam_cert) : Prop :=
  JamCore.adjacent_jam_cert_sound
    cert.(loop_jam_poly)
    cert.(loop_jam_core_cert).

Theorem checked_loop_jam_current_sound :
  forall loop plan cert,
    mayReturn (checked_loop_jam_current loop plan) (Okk cert) ->
    loop_jam_cert_sound cert.
Proof.
  intros loop plan cert Hchecked.
  unfold checked_loop_jam_current in Hchecked.
  destruct (ExtractorCore.extractor loop) as [pol0|msg] eqn:Hext.
  - apply mayReturn_bind in Hchecked.
    destruct Hchecked as [cert_res [Hcore Hret]].
    destruct cert_res as [core_cert|core_msg].
    + apply mayReturn_pure in Hret.
      inversion Hret; subst; clear Hret.
      unfold loop_jam_cert_sound; simpl.
      eapply JamCore.checked_jam_current_sound.
      exact Hcore.
    + apply mayReturn_pure in Hret.
      discriminate.
  - apply mayReturn_pure in Hchecked.
    discriminate.
Qed.

Theorem checked_loop_jam_current_factor_positive :
  forall loop plan cert,
    mayReturn (checked_loop_jam_current loop plan) (Okk cert) ->
    (0 < JamCore.certified_factor cert.(loop_jam_core_cert))%nat.
Proof.
  intros loop plan cert Hchecked.
  unfold checked_loop_jam_current in Hchecked.
  destruct (ExtractorCore.extractor loop) as [pol0|msg] eqn:Hext.
  - apply mayReturn_bind in Hchecked.
    destruct Hchecked as [cert_res [Hcore Hret]].
    destruct cert_res as [core_cert|core_msg].
    + apply mayReturn_pure in Hret.
      inversion Hret; subst; clear Hret.
      simpl.
      eapply JamCore.checked_jam_current_factor_positive.
      exact Hcore.
    + apply mayReturn_pure in Hret.
      discriminate.
  - apply mayReturn_pure in Hchecked.
    discriminate.
Qed.

Record loop_jam_pair_cert := {
  loop_jam_pair_old_poly : PolyLang.t;
  loop_jam_pair_new_poly : PolyLang.t
}.

Definition loop_jam_pair_old_loop
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) : Loop.t :=
  (Native.unjammed_two_loop lb ub body1 body2, varctxt, vars).

Definition loop_jam_pair_new_loop
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt) : Loop.t :=
  (Native.jammed_two_loop lb ub body1 body2, varctxt, vars).

Definition checked_loop_jam_pair
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (lb ub : Loop.expr) (body1 body2 : Loop.stmt)
  : imp (result loop_jam_pair_cert) :=
  match
    ExtractorCore.extractor
      (loop_jam_pair_old_loop varctxt vars lb ub body1 body2),
    ExtractorCore.extractor
      (loop_jam_pair_new_loop varctxt vars lb ub body1 body2)
  with
  | Okk old_pol, Okk new_pol =>
      BIND ok <- AffineCore.validate old_pol new_pol -;
      if ok then
        pure
          (Okk
             {|
               loop_jam_pair_old_poly := old_pol;
               loop_jam_pair_new_poly := new_pol
             |})
      else pure (Err "Local jam validation failed")
  | Err msg, _ => pure (Err msg)
  | _, Err msg => pure (Err msg)
  end.

Definition loop_jam_pair_cert_sound
    (cert : loop_jam_pair_cert) : Prop :=
  let old_pol := cert.(loop_jam_pair_old_poly) in
  let new_pol := cert.(loop_jam_pair_new_poly) in
  forall envv ipl_old ipl_new,
    Datatypes.length (pprog_varctxt old_pol) = Datatypes.length envv ->
    PolyLang.flatten_instrs envv (pprog_pis old_pol) ipl_old ->
    PolyLang.flatten_instrs envv (pprog_pis new_pol) ipl_new ->
    exists ipl_ext,
      PolyLang.new_of_ext_list ipl_ext = ipl_new /\
      PolyLang.old_of_ext_list ipl_ext = ipl_old /\
      (forall ip1_ext ip2_ext,
          In ip1_ext ipl_ext ->
          In ip2_ext ipl_ext ->
          PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
          PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
          PolyLang.Permutable_ext ip1_ext ip2_ext).

Theorem checked_loop_jam_pair_sound :
  forall varctxt vars lb ub body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair varctxt vars lb ub body1 body2)
      (Okk cert) ->
    loop_jam_pair_cert_sound cert.
Proof.
  intros varctxt vars lb ub body1 body2 cert Hchecked.
  unfold checked_loop_jam_pair in Hchecked.
  destruct
    (ExtractorCore.extractor
       (loop_jam_pair_old_loop varctxt vars lb ub body1 body2))
    as [old_pol|old_msg] eqn:Hold.
  2: {
    apply mayReturn_pure in Hchecked.
    discriminate.
  }
  destruct
    (ExtractorCore.extractor
       (loop_jam_pair_new_loop varctxt vars lb ub body1 body2))
    as [new_pol|new_msg] eqn:Hnew.
  2: {
    apply mayReturn_pure in Hchecked.
    discriminate.
  }
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hval Hret]].
  destruct ok.
  2: {
    apply mayReturn_pure in Hret.
    discriminate.
  }
  apply mayReturn_pure in Hret.
  inversion Hret; subst; clear Hret.
  unfold loop_jam_pair_cert_sound; simpl.
  destruct old_pol as [[old_pis old_varctxt] old_vars].
  destruct new_pol as [[new_pis new_varctxt] new_vars].
  simpl in *.
  intros envv ipl_old ipl_new Henvlen Hflat_old Hflat_new.
  eapply
    (AffineCore.validate_implies_permutability
       ((old_pis, old_varctxt), old_vars)
       ((new_pis, new_varctxt), new_vars)
       old_varctxt new_varctxt envv old_vars new_vars
       old_pis new_pis ipl_old ipl_new true).
  - exact Hval.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Henvlen.
  - exact Hflat_old.
  - exact Hflat_new.
Qed.

Definition local_stmt_order_row (cols pos : nat) : list Z * Z :=
  (repeat 0%Z cols, Z.of_nat pos).

Definition local_loop_coord_row
    (env_dim depth : nat) : list Z * Z :=
  JamCore.current_coord_schedule_row env_dim (S depth) 0.

Definition local_jam_old_prefix
    (env_dim depth pos : nat) : list (list Z * Z) :=
  let cols := (env_dim + S depth)%nat in
  [ local_stmt_order_row cols pos;
    local_loop_coord_row env_dim depth ].

Definition local_jam_new_prefix
    (env_dim depth pos : nat) : list (list Z * Z) :=
  let cols := (env_dim + S depth)%nat in
  [ local_loop_coord_row env_dim depth;
    local_stmt_order_row cols pos ].

Definition local_jam_pair_pprog
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (new_order : bool)
    (body1 body2 : Loop.stmt) : result PolyLang.t :=
  let env_dim := Datatypes.length varctxt in
  let ub :=
    if Nat.ltb depth (env_dim + depth)%nat
    then Loop.Var depth
    else Loop.Constant 8%Z in
  let stmt :=
    if new_order
    then Native.jammed_two_loop (Loop.Constant 0%Z) ub body1 body2
    else Native.unjammed_two_loop (Loop.Constant 0%Z) ub body1 body2 in
  match ExtractorCore.extract_stmt stmt [] env_dim depth [] with
  | Okk pis => Okk (pis, varctxt, vars)
  | Err msg => Err msg
  end.

Definition checked_loop_jam_pair_at_depth
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (body1 body2 : Loop.stmt)
  : imp (result loop_jam_pair_cert) :=
  match
    local_jam_pair_pprog varctxt vars depth false body1 body2,
    local_jam_pair_pprog varctxt vars depth true body1 body2
  with
  | Okk old_pol, Okk new_pol =>
      BIND ok <- AffineCore.validate old_pol new_pol -;
      if ok then
        pure
          (Okk
             {|
               loop_jam_pair_old_poly := old_pol;
               loop_jam_pair_new_poly := new_pol
             |})
      else pure (Err "Local jam validation failed")
  | Err msg, _ => pure (Err msg)
  | _, Err msg => pure (Err msg)
  end.

Theorem checked_loop_jam_pair_at_depth_sound :
  forall varctxt vars depth body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair_at_depth varctxt vars depth body1 body2)
      (Okk cert) ->
    loop_jam_pair_cert_sound cert.
Proof.
  intros varctxt vars depth body1 body2 cert Hchecked.
  unfold checked_loop_jam_pair_at_depth in Hchecked.
  destruct
    (local_jam_pair_pprog varctxt vars depth false body1 body2)
    as [old_pol|old_msg] eqn:Hold.
  2: {
    apply mayReturn_pure in Hchecked.
    discriminate.
  }
  destruct
    (local_jam_pair_pprog varctxt vars depth true body1 body2)
    as [new_pol|new_msg] eqn:Hnew.
  2: {
    apply mayReturn_pure in Hchecked.
    discriminate.
  }
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hval Hret]].
  destruct ok.
  2: {
    apply mayReturn_pure in Hret.
    discriminate.
  }
  apply mayReturn_pure in Hret.
  inversion Hret; subst; clear Hret.
  unfold loop_jam_pair_cert_sound; simpl.
  destruct old_pol as [[old_pis old_varctxt] old_vars].
  destruct new_pol as [[new_pis new_varctxt] new_vars].
  simpl in *.
  intros envv ipl_old ipl_new Henvlen Hflat_old Hflat_new.
  eapply
    (AffineCore.validate_implies_permutability
       ((old_pis, old_varctxt), old_vars)
       ((new_pis, new_varctxt), new_vars)
       old_varctxt new_varctxt envv old_vars new_vars
       old_pis new_pis ipl_old ipl_new true).
  - exact Hval.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Henvlen.
  - exact Hflat_old.
  - exact Hflat_new.
Qed.

End LoopJamValidator.
