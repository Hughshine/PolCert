Require Import Lia.
Require Import List.
Require Import Linalg.
Require Import String.
Require Import ZArith.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Local Open Scope string_scope.
Import ListNotations.

Require Import ExtractorFrontend.
Require Import AffineValidator.
Require Import JamValidator.
Require Import LoopJamNative.
Require Import PolIRs.
Require Import PolyBase.
Require Import StrengthenDomain.

Module LoopJamValidator (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module Instr := PolIRs.Instr.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Module ExtractorCore := ExtractorFrontend PolIRs.
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

(** The at-depth checker deliberately leaves the enclosing loop coordinates
    unconstrained.  Its extracted domains can therefore have infinitely many
    instances for a fixed parameter environment, so a soundness statement
    quantified only over finite [flatten_instrs] witnesses may be vacuous.
    This pointwise endpoint is the one used by a Loop-level trace bridge. *)
Definition loop_jam_pair_cert_pointwise_sound
    (cert : loop_jam_pair_cert) : Prop :=
  let old_pol := cert.(loop_jam_pair_old_poly) in
  let new_pol := cert.(loop_jam_pair_new_poly) in
  let old_pis := pprog_pis old_pol in
  let new_pis := pprog_pis new_pol in
  let env_dim := Datatypes.length (pprog_varctxt old_pol) in
  forall pi1_ext pi2_ext ip1_ext ip2_ext,
    In pi1_ext
      (AffineCore.compose_pinstrs_ext_at env_dim old_pis new_pis) ->
    In pi2_ext
      (AffineCore.compose_pinstrs_ext_at env_dim old_pis new_pis) ->
    Datatypes.length ip1_ext.(PolyLang.ip_index_ext) =
      (env_dim + pi1_ext.(PolyLang.pi_depth_ext))%nat ->
    Datatypes.length ip2_ext.(PolyLang.ip_index_ext) =
      (env_dim + pi2_ext.(PolyLang.pi_depth_ext))%nat ->
    firstn env_dim ip1_ext.(PolyLang.ip_index_ext) =
      firstn env_dim ip2_ext.(PolyLang.ip_index_ext) ->
    PolyLang.belongs_to_ext ip1_ext pi1_ext ->
    PolyLang.belongs_to_ext ip2_ext pi2_ext ->
    PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
    PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
    PolyLang.Permutable_ext ip1_ext ip2_ext.

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

Theorem checked_loop_jam_pair_pointwise_sound :
  forall varctxt vars lb ub body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair varctxt vars lb ub body1 body2)
      (Okk cert) ->
    loop_jam_pair_cert_pointwise_sound cert.
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
  unfold loop_jam_pair_cert_pointwise_sound; simpl.
  destruct old_pol as [[old_pis old_varctxt] old_vars].
  destruct new_pol as [[new_pis new_varctxt] new_vars].
  simpl in *.
  intros pi1_ext pi2_ext ip1_ext ip2_ext
    Hin1 Hin2 Hlen1 Hlen2 Henv Hbel1 Hbel2 Hold_sched Hnew_sched.
  eapply
    (AffineCore.validate_pointwise_implies_permutability
       ((old_pis, old_varctxt), old_vars)
       ((new_pis, new_varctxt), new_vars)
       old_varctxt new_varctxt old_vars new_vars old_pis new_pis
       pi1_ext pi2_ext ip1_ext ip2_ext); eauto.
Qed.

Definition local_stmt_order_row (cols pos : nat) : list Z * Z :=
  (repeat 0%Z cols, Z.of_nat pos).

(** Extraction reverses Loop-environment coefficients when it builds a
    polyhedral instruction.  These rows are therefore stored in reverse and
    become the identity prefix after extraction. *)
Definition local_shared_coord_row
    (cols pos : nat) : list Z * Z :=
  (rev (resize cols (V0 pos ++ [1%Z])), 0%Z).

Fixpoint local_shared_schedule_from
    (cols pos count : nat) : list (list Z * Z) :=
  match count with
  | O => []
  | S count' =>
      local_shared_coord_row cols pos ::
      local_shared_schedule_from cols (S pos) count'
  end.

Definition local_jam_schedule_prefix
    (cols shared group : nat) : list (list Z * Z) :=
  local_shared_schedule_from cols 0 shared ++
  [local_stmt_order_row cols group].

Definition local_jam_pair_pprog
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (new_order : bool) (lb ub : Loop.expr)
    (body1 body2 : Loop.stmt) : result PolyLang.t :=
  (* Parameters and enclosing iterators precede the synthetic group row.  The
     affine checker therefore compares the two bodies only inside a shared
     outer environment, exactly as the native sibling-loop jam does.  Within
     that environment, reversing the group row proves universal cross-body
     independence over the current loop's actual bounds. *)
  let env_dim := Datatypes.length varctxt in
  let cols := (env_dim + depth)%nat in
  match ExtractorCore.lb_to_constr lb cols,
        ExtractorCore.ub_to_constr ub cols with
  | Okk lbc, Okk ubc =>
      let constrs := [lbc; ubc] in
      let point_cols := (env_dim + S depth)%nat in
      let shared_cols := (env_dim + depth)%nat in
      let group1 := if new_order then 1%nat else 0%nat in
      let group2 := if new_order then 0%nat else 1%nat in
      match
        ExtractorCore.extract_stmt body1 constrs env_dim (S depth)
          (local_jam_schedule_prefix point_cols shared_cols group1),
        ExtractorCore.extract_stmt body2 constrs env_dim (S depth)
          (local_jam_schedule_prefix point_cols shared_cols group2)
      with
      | Okk pis1, Okk pis2 => Okk (List.app pis1 pis2, varctxt, vars)
      | Err msg, _ => Err msg
      | _, Err msg => Err msg
      end
  | Err msg, _ => Err msg
  | _, Err msg => Err msg
  end.

Lemma local_jam_pair_pprog_success_inv :
  forall varctxt vars depth new_order lb ub body1 body2 pol,
    local_jam_pair_pprog
      varctxt vars depth new_order lb ub body1 body2 = Okk pol ->
    exists lbc ubc pis1 pis2,
      ExtractorCore.lb_to_constr lb
        (Datatypes.length varctxt + depth)%nat = Okk lbc /\
      ExtractorCore.ub_to_constr ub
        (Datatypes.length varctxt + depth)%nat = Okk ubc /\
      ExtractorCore.extract_stmt body1 [lbc; ubc]
        (Datatypes.length varctxt) (S depth)
        (local_jam_schedule_prefix
           (Datatypes.length varctxt + S depth)%nat
           (Datatypes.length varctxt + depth)%nat
           (if new_order then 1%nat else 0%nat)) = Okk pis1 /\
      ExtractorCore.extract_stmt body2 [lbc; ubc]
        (Datatypes.length varctxt) (S depth)
        (local_jam_schedule_prefix
           (Datatypes.length varctxt + S depth)%nat
           (Datatypes.length varctxt + depth)%nat
           (if new_order then 0%nat else 1%nat)) = Okk pis2 /\
      pol = (List.app pis1 pis2, varctxt, vars).
Proof.
  intros varctxt vars depth new_order lb ub body1 body2 pol Hlocal.
  unfold local_jam_pair_pprog in Hlocal.
  destruct (ExtractorCore.lb_to_constr lb
    (Datatypes.length varctxt + depth)%nat) as [lbc|lb_msg] eqn:Hlb;
    try discriminate.
  destruct (ExtractorCore.ub_to_constr ub
    (Datatypes.length varctxt + depth)%nat) as [ubc|ub_msg] eqn:Hub;
    try discriminate.
  destruct (ExtractorCore.extract_stmt body1 [lbc; ubc]
    (Datatypes.length varctxt) (S depth)
    (local_jam_schedule_prefix
      (Datatypes.length varctxt + S depth)%nat
      (Datatypes.length varctxt + depth)%nat
      (if new_order then 1%nat else 0%nat)))
    as [pis1|body1_msg] eqn:Hbody1; try discriminate.
  destruct (ExtractorCore.extract_stmt body2 [lbc; ubc]
    (Datatypes.length varctxt) (S depth)
    (local_jam_schedule_prefix
      (Datatypes.length varctxt + S depth)%nat
      (Datatypes.length varctxt + depth)%nat
      (if new_order then 0%nat else 1%nat)))
    as [pis2|body2_msg] eqn:Hbody2; try discriminate.
  inversion Hlocal; subst pol; clear Hlocal.
  exists lbc, ubc, pis1, pis2.
  repeat split; assumption.
Qed.

Definition checked_loop_jam_pair_at_depth
    (varctxt : list Instr.ident) (vars : list (Instr.ident * Ty.t))
    (depth : nat) (lb ub : Loop.expr) (body1 body2 : Loop.stmt)
  : imp (result loop_jam_pair_cert) :=
  match
    local_jam_pair_pprog varctxt vars depth false lb ub body1 body2,
    local_jam_pair_pprog varctxt vars depth true lb ub body1 body2
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

Lemma checked_loop_jam_pair_at_depth_success_inv :
  forall varctxt vars depth lb ub body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair_at_depth varctxt vars depth lb ub body1 body2)
      (Okk cert) ->
    exists old_pol new_pol,
      local_jam_pair_pprog
        varctxt vars depth false lb ub body1 body2 = Okk old_pol /\
      local_jam_pair_pprog
        varctxt vars depth true lb ub body1 body2 = Okk new_pol /\
      mayReturn (AffineCore.validate old_pol new_pol) true /\
      cert =
        {| loop_jam_pair_old_poly := old_pol;
           loop_jam_pair_new_poly := new_pol |}.
Proof.
  intros varctxt vars depth lb ub body1 body2 cert Hchecked.
  unfold checked_loop_jam_pair_at_depth in Hchecked.
  destruct
    (local_jam_pair_pprog varctxt vars depth false lb ub body1 body2)
    as [old_pol|old_msg] eqn:Hold; try (apply mayReturn_pure in Hchecked; discriminate).
  destruct
    (local_jam_pair_pprog varctxt vars depth true lb ub body1 body2)
    as [new_pol|new_msg] eqn:Hnew; try (apply mayReturn_pure in Hchecked; discriminate).
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hval Hret]].
  destruct ok; try (apply mayReturn_pure in Hret; discriminate).
  apply mayReturn_pure in Hret.
  inversion Hret; subst; clear Hret.
  exists old_pol, new_pol.
  repeat split; assumption.
Qed.

Theorem checked_loop_jam_pair_at_depth_sound :
  forall varctxt vars depth lb ub body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair_at_depth varctxt vars depth lb ub body1 body2)
      (Okk cert) ->
    loop_jam_pair_cert_sound cert.
Proof.
  intros varctxt vars depth lb ub body1 body2 cert Hchecked.
  unfold checked_loop_jam_pair_at_depth in Hchecked.
  destruct
    (local_jam_pair_pprog varctxt vars depth false lb ub body1 body2)
    as [old_pol|old_msg] eqn:Hold.
  2: {
    apply mayReturn_pure in Hchecked.
    discriminate.
  }
  destruct
    (local_jam_pair_pprog varctxt vars depth true lb ub body1 body2)
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

Theorem checked_loop_jam_pair_at_depth_pointwise_sound :
  forall varctxt vars depth lb ub body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair_at_depth varctxt vars depth lb ub body1 body2)
      (Okk cert) ->
    loop_jam_pair_cert_pointwise_sound cert.
Proof.
  intros varctxt vars depth lb ub body1 body2 cert Hchecked.
  unfold checked_loop_jam_pair_at_depth in Hchecked.
  destruct
    (local_jam_pair_pprog varctxt vars depth false lb ub body1 body2)
    as [old_pol|old_msg] eqn:Hold.
  2: {
    apply mayReturn_pure in Hchecked.
    discriminate.
  }
  destruct
    (local_jam_pair_pprog varctxt vars depth true lb ub body1 body2)
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
  unfold loop_jam_pair_cert_pointwise_sound; simpl.
  destruct old_pol as [[old_pis old_varctxt] old_vars].
  destruct new_pol as [[new_pis new_varctxt] new_vars].
  simpl in *.
  intros pi1_ext pi2_ext ip1_ext ip2_ext
    Hin1 Hin2 Hlen1 Hlen2 Henv Hbel1 Hbel2 Hold_sched Hnew_sched.
  eapply
    (AffineCore.validate_pointwise_implies_permutability
       ((old_pis, old_varctxt), old_vars)
       ((new_pis, new_varctxt), new_vars)
       old_varctxt new_varctxt old_vars new_vars old_pis new_pis
       pi1_ext pi2_ext ip1_ext ip2_ext); eauto.
Qed.

Definition loop_jam_pair_cert_correspondence_sound
    (cert : loop_jam_pair_cert) : Prop :=
  PolyLang.eqdom_pprog
    cert.(loop_jam_pair_old_poly)
    cert.(loop_jam_pair_new_poly).

Theorem checked_loop_jam_pair_at_depth_correspondence_sound :
  forall varctxt vars depth lb ub body1 body2 cert,
    mayReturn
      (checked_loop_jam_pair_at_depth varctxt vars depth lb ub body1 body2)
      (Okk cert) ->
    loop_jam_pair_cert_correspondence_sound cert.
Proof.
  intros varctxt vars depth lb ub body1 body2 cert Hchecked.
  unfold checked_loop_jam_pair_at_depth in Hchecked.
  destruct
    (local_jam_pair_pprog varctxt vars depth false lb ub body1 body2)
    as [old_pol|old_msg] eqn:Hold; try (apply mayReturn_pure in Hchecked; discriminate).
  destruct
    (local_jam_pair_pprog varctxt vars depth true lb ub body1 body2)
    as [new_pol|new_msg] eqn:Hnew; try (apply mayReturn_pure in Hchecked; discriminate).
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hval Hret]].
  destruct ok; try (apply mayReturn_pure in Hret; discriminate).
  apply mayReturn_pure in Hret.
  inversion Hret; subst; clear Hret.
  unfold loop_jam_pair_cert_correspondence_sound; simpl.
  destruct old_pol as [[old_pis old_varctxt] old_vars].
  destruct new_pol as [[new_pis new_varctxt] new_vars].
  eapply AffineCore.validate_implies_correspondence; eauto.
Qed.

End LoopJamValidator.
