(** * Footprint disjointness of raw annotated parallel code

    Lifts [ParallelValidator.parallel_disjoint_dim_pointwise] (appended to
    ParallelValidator.v) to the instruction points of raw annotated code.

    - [point_same_call]: a generated point issues exactly the instruction
      call (instruction and argument vector) of its source instance.  The
      existing origin theorem packages only state-level equivalence
      ([point_sema_equiv]); the exact version below re-runs its proof and
      records the call equality, so footprints transfer.
    - [annotated_codegen_many_raw_slice_disjoint]: in every target trace,
      two points whose iteration vectors agree on the outer coordinates of a
      certified dimension and differ at that dimension have disjoint
      footprints.  Distinct iterations of a [ParMode] loop owned by that
      certificate are such pairs ([par_trace_point_extends_env]).

    Scope: raw annotated code ([annotated_codegen_many_raw]); the result is
    not transported through the cleanup and postpass stages. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Misc.
Require Import Linalg.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import PolIRs.
Require Import PolyBase.
Require Import PrepareCodegen.
Require Import RawCodegenOrigin.
Require Import ParallelLoop.
Require Import ParallelValidator.
Require Import ParallelCodegenCorrect.

Import ListNotations.

Module ParallelCodegenDisjoint (PolIRs : POLIRS).

Module PCC := ParallelCodegenCorrect PolIRs.
Import PCC.

(** Exact call correspondence between a generated and a source point. *)
Definition point_same_call
    (g : ParallelLoop.InstrPoint) (s : PolyLang.InstrPoint) : Prop :=
  g.(ParallelLoop.ILSema.ip_instruction) = s.(PolyLang.ip_instruction) /\
  affine_product g.(ParallelLoop.ILSema.ip_transformation)
    g.(ParallelLoop.ILSema.ip_index) =
  affine_product s.(PolyLang.ip_transformation) s.(PolyLang.ip_index).

(** Bernstein's conditions on the footprints of two generated points, for
    every execution of each from any state. *)
Definition generated_footprint_disjoint
    (g1 g2 : ParallelLoop.InstrPoint) : Prop :=
  forall wcs1 rcs1 st1 st1' wcs2 rcs2 st2 st2',
    Instr.instr_semantics g1.(ParallelLoop.ILSema.ip_instruction)
      (affine_product g1.(ParallelLoop.ILSema.ip_transformation)
         g1.(ParallelLoop.ILSema.ip_index))
      wcs1 rcs1 st1 st1' ->
    Instr.instr_semantics g2.(ParallelLoop.ILSema.ip_instruction)
      (affine_product g2.(ParallelLoop.ILSema.ip_transformation)
         g2.(ParallelLoop.ILSema.ip_index))
      wcs2 rcs2 st2 st2' ->
    ParallelValidator.cells_disjoint wcs1 wcs2 /\
    ParallelValidator.cells_disjoint wcs1 rcs2 /\
    ParallelValidator.cells_disjoint rcs1 wcs2.

Lemma same_call_footprint_disjoint :
  forall g1 g2 s1 s2,
    point_same_call g1 s1 ->
    point_same_call g2 s2 ->
    ParallelValidator.footprint_disjoint s1 s2 ->
    generated_footprint_disjoint g1 g2.
Proof.
  intros g1 g2 s1 s2 [Hi1 Ha1] [Hi2 Ha2] H.
  unfold generated_footprint_disjoint.
  rewrite Hi1, Ha1, Hi2, Ha2.
  exact H.
Qed.

(** Certificate facts consumed by code generation, disjointness variant of
    [parallel_codegen_cert_sound]. *)
Definition parallel_codegen_cert_disjoint
    (pp : PolyLang.t) (cert : ParallelValidator.parallel_cert) : Prop :=
  ParallelValidator.parallel_disjoint_dim_pointwise pp
    cert.(ParallelValidator.certified_dim) /\
  (cert.(ParallelValidator.certified_dim) <
   ParallelValidator.schedule_width pp)%nat.

Lemma checked_parallelize_current_codegen_disjoint :
  forall pp plan cert,
    mayReturn (ParallelValidator.checked_parallelize_current pp plan)
      (Okk cert) ->
    parallel_codegen_cert_disjoint pp cert.
Proof.
  intros pp plan cert Hchecked.
  split.
  - eapply ParallelValidator.checked_parallelize_current_disjoint; eauto.
  - eapply ParallelValidator.checked_parallelize_current_implies_dim_in_range;
      eauto.
Qed.

Theorem prepared_event_to_source_point_exact :
  forall pis varctxt vars cols width ip ev,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    point_matches_event ip ev ->
    RawOrigin.prepared_source_event
      (map (PrepareCore.prepare_pi (Datatypes.length varctxt) cols) pis)
      (Datatypes.length varctxt) cols width ev ->
    ev = generated_event ip ->
    exists source_ip,
      generated_source_point_full
        ((pis, varctxt), vars) width ip source_ip /\
      point_same_call ip source_ip.
Proof.
  intros pis varctxt vars cols width ip ev Hwf Hdim Hmatch Hprepared Hev.
  (* Recover the original instruction and current point hidden by [prepare_pi]
     and schedule elimination. *)
  destruct Hmatch as [Hevent_point Heffect].
  destruct Hprepared as
    [m [prep_pi
      [Hprep_lookup
       [Hp_len
        [Hprep_domain
         [Hevent_instr
          [Hevent_args [Henv_prefix Hschedule]]]]]]]].
  rewrite nth_error_map_iff in Hprep_lookup.
  destruct Hprep_lookup as [pi [Hpi Hprep_pi]].
  subst prep_pi.
  set (env_dim := Datatypes.length varctxt).
  set (p := RawOrigin.drop_schedule_coords env_dim width
    ev.(RawOrigin.se_point)).
  assert (Henv_cols : (env_dim <= cols)%nat).
  {
    pose proof
      (PolyLang.pprog_current_dim_ge_pinstr
        pis varctxt vars pi (nth_error_In _ _ Hpi)) as Hpi_dim.
    unfold PolyLang.pinstr_current_dim in Hpi_dim.
    unfold env_dim.
    lia.
  }
  assert (Hp_resize : p =v= resize cols p).
  {
    rewrite resize_length_eq by exact Hp_len.
    reflexivity.
  }
  set (envv := resize env_dim p).
  assert (Henvv_len : Datatypes.length envv = Datatypes.length varctxt).
  {
    unfold envv, env_dim. rewrite resize_length. reflexivity.
  }
  assert (Hscan :
    PolyLang.env_scan
      (map (PrepareCore.prepare_pi (Datatypes.length varctxt) cols) pis)
      envv cols m p = true).
  {
    unfold PolyLang.env_scan.
    rewrite map_nth_error with (d := pi); [|exact Hpi].
    simpl.
    apply andb_true_intro. split.
    - apply andb_true_intro. split.
      + unfold envv, env_dim. rewrite resize_length. apply is_eq_reflexive.
      + rewrite is_eq_veq. exact Hp_resize.
    - exact Hprep_domain.
  }
  (* Preparation's scan theorem supplies source membership, depth, and the
     environment prefix. *)
  pose proof
    (PrepareCore.prepare_env_scan_true_implies_source_ip_props
      pis varctxt vars cols envv m p pi Hwf Hdim Henvv_len Hpi Hscan)
    as Hprops.
  change (
    firstn (Datatypes.length varctxt)
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p).(PolyLang.ip_index) = envv /\
    PolyLang.belongs_to
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p) pi /\
    Datatypes.length
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p).(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth))%nat /\
    is_eq p (resize cols p) = true /\
    is_null
      (skipn (Datatypes.length varctxt + pi.(PolyLang.pi_depth))
        (resize cols p)) = true) in Hprops.
  destruct Hprops as [Hprefix [Hbelongs [Hsource_len [_ _]]]].
  set (source_ip :=
    PrepareCore.source_ip_of (Datatypes.length varctxt) m pi p).
  assert (Hfull :
    generated_source_point_full ((pis, varctxt), vars) width ip source_ip).
  {
  (* Package semantic equivalence, the source witness, and both coordinate
     correspondences needed by the parallel certificate proof. *)
  constructor.
  - split.
    + subst source_ip.
      eapply point_sema_equiv_of_prepared_effect; eauto.
      unfold point_has_effect in *.
      intros st1 st2.
      specialize (Heffect st1 st2).
      change
        (ev.(RawOrigin.se_args) =
         PolyLang.current_src_args_in_dim cols
           (PrepareCore.prepare_pi
             (Datatypes.length varctxt) cols pi) p)
        in Hevent_args.
      rewrite <- Hevent_instr, <- Hevent_args.
      exact Heffect.
    + exists pi.
      subst source_ip. simpl.
      split; [exact Hpi|].
      split; assumption.
  - subst source_ip.
    transitivity envv.
    + exact Hprefix.
    + unfold envv, p, env_dim, RawOrigin.drop_schedule_coords.
      rewrite resize_app.
      * rewrite Hevent_point. reflexivity.
      * rewrite resize_length. reflexivity.
  - subst source_ip.
    transitivity
      (resize width
        (affine_product
          (PrepareCore.prepare_pi
            (Datatypes.length varctxt) cols pi).(PolyLang.pi_schedule) p)).
    + rewrite <- Hevent_point.
      exact Hschedule.
    + rewrite <- PrepareCore.source_ip_of_timestamp_prepare
        with (pis := pis) (varctxt := varctxt) (vars := vars)
             (cols := cols) (n := m) (pi := pi) (p := p); eauto.
  }
  exists source_ip. split; [exact Hfull|].
  (* Generated and source points issue the same instruction call. *)
  assert (Hgi : ev.(RawOrigin.se_instr) =
                ip.(ParallelLoop.ILSema.ip_instruction))
    by (rewrite Hev; reflexivity).
  assert (Hga : ev.(RawOrigin.se_args) =
                affine_product ip.(ParallelLoop.ILSema.ip_transformation)
                  ip.(ParallelLoop.ILSema.ip_index))
    by (rewrite Hev; reflexivity).
  unfold point_same_call. split.
  - rewrite <- Hgi, Hevent_instr. subst source_ip. reflexivity.
  - rewrite <- Hga.
    change
      (ev.(RawOrigin.se_args) =
       PolyLang.current_src_args_in_dim cols
         (PrepareCore.prepare_pi
           (Datatypes.length varctxt) cols pi) p)
      in Hevent_args.
    rewrite Hevent_args.
    rewrite
      (prepare_source_args_eq
        pis varctxt vars cols m pi p Hwf Hdim Hpi Hp_resize).
    subst source_ip. reflexivity.
Qed.
Theorem annotated_codegen_many_raw_root_origin_exact :
  forall pis varctxt vars certs pl env root_tr,
    mayReturn
      (annotated_codegen_many_raw
        ((pis, varctxt), vars) certs) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    ParallelLoop.trace_safe pl ->
    program_par_trace pl env root_tr ->
    Datatypes.length env = Datatypes.length varctxt ->
    forall ip,
      In ip root_tr ->
      exists source_ip,
        generated_source_point_full
          ((pis, varctxt), vars)
          (ParallelValidator.schedule_width ((pis, varctxt), vars))
          ip source_ip /\
        point_same_call ip source_ip.
Proof.
  intros pis varctxt vars certs pl env root_tr
    Hcodegen Hwf Hsafe Htrace Henv ip Hin.
  (* Recover preparation invariants and the exact raw generator result. *)
  pose proof
    (PrepareCore.prepare_codegen_target_dim_preserved
       ((pis, varctxt), vars) Hwf) as Hprepdim.
  pose proof
    (PrepareCore.prepare_codegen_preserves_wf_at
       ((pis, varctxt), vars) Hwf) as Hcgwf.
  destruct Hcgwf as [Hctxt [Hdim Hsched]].
  set (env_dim := Datatypes.length varctxt).
  set (cols := PrepareCore.codegen_target_dim ((pis, varctxt), vars)).
  set (prep_pis :=
    map (PrepareCore.prepare_pi env_dim cols) pis).
  assert (Hsource_dim :
    (PolyLang.pprog_current_dim ((pis, varctxt), vars) <= cols)%nat).
  {
    subst cols.
    apply PrepareCore.wf_pprog_affine_implies_pprog_current_dim_le_target.
    exact Hwf.
  }
  assert (Henvdim :
    forall pi, In pi prep_pis ->
      PolyLang.current_env_dim_in_dim cols
        pi.(PolyLang.pi_point_witness) = env_dim).
  {
    intros prep_pi Hprep_pi.
    subst prep_pis env_dim cols.
    exact
      (PrepareCore.prepared_pi_current_env_dim_for_codegen
        pis varctxt vars prep_pi Hwf Hprep_pi).
  }
  unfold annotated_codegen_many_raw in Hcodegen.
  apply mayReturn_bind in Hcodegen.
  destruct Hcodegen as [tagged [Htagged Hpure]].
  apply mayReturn_pure in Hpure. subst pl.
  unfold tagged_prepared_codegen_raw in Htagged.
  apply mayReturn_bind in Htagged.
  destruct Htagged as [loop [Hprepared Hpure]].
  apply mayReturn_pure in Hpure. subst tagged.
  unfold PrepareCore.prepared_codegen_raw in Hprepared.
  unfold PrepareCore.CodeGen.codegen in Hprepared.
  simpl in Hprepared.
  bind_imp_destruct Hprepared raw_stmt Hgen.
  apply mayReturn_pure in Hprepared. subst loop.
  change
    (ParallelLoop.trace_safe
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars))) in Hsafe.
  change
    (program_par_trace
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars))
      env root_tr) in Htrace.
  rewrite parallelize_certified_dims_program_eq in Hsafe.
  rewrite parallelize_certified_dims_program_eq in Htrace.
  simpl in Hsafe, Htrace.
  (* Cover the actual interleaving by a sequential trace, then erase the
     annotation passes without changing its instruction points. *)
  destruct
    (par_trace_seq_cover
       (parallelize_certified_dims_stmt certs
         (tag_loop_stmt_at 0 raw_stmt))
       env root_tr Hsafe Htrace)
    as [seq_tr [Hseq Hcover]].
  pose proof
    (seq_trace_parallelize_certified_dims_inv
       certs (tag_loop_stmt_at 0 raw_stmt) env seq_tr Hseq)
    as Htag_seq.
  assert (Htag_safe :
    ParallelLoop.trace_safe_stmt (tag_loop_stmt_at 0 raw_stmt)).
  {
    eapply trace_safe_parallelize_certified_dims_inv.
    exact Hsafe.
  }
  pose proof
    (tagged_seq_trace_origin
       raw_stmt 0 env seq_tr Htag_safe Htag_seq) as Hraw_trace.
  assert (Hevent_in :
    In (generated_event ip) (map generated_event seq_tr)).
  {
    apply in_map. eapply Hcover. exact Hin.
  }
  assert (Hctxt' : (env_dim <= cols)%nat).
  {
    subst env_dim cols. exact Hctxt.
  }
  assert (Hdim' : PrepareCore.ASTGen.pis_have_dimension prep_pis cols).
  {
    subst prep_pis env_dim cols. exact Hdim.
  }
  assert (Hsched' :
    forall pi, In pi prep_pis ->
      (poly_nrl pi.(PolyLang.pi_schedule) <= cols)%nat).
  {
    subst prep_pis env_dim cols. exact Hsched.
  }
  assert (Hgen' :
    mayReturn
      (PrepareCore.CodeGen.complete_generate_many
        env_dim cols prep_pis) raw_stmt).
  {
    subst env_dim cols prep_pis.
    change
      (mayReturn
        (PrepareCore.CodeGen.complete_generate_many
          (Datatypes.length varctxt)
          (PrepareCore.codegen_target_dim
            (PrepareCore.prepare_codegen ((pis, varctxt), vars)))
          (map
            (PrepareCore.prepare_pi
              (Datatypes.length varctxt)
              (PrepareCore.codegen_target_dim
                ((pis, varctxt), vars))) pis))
        raw_stmt) in Hgen.
    rewrite Hprepdim in Hgen.
    exact Hgen.
  }
  pose proof
    (RawOrigin.complete_generate_many_event_source
      env_dim cols prep_pis raw_stmt env
      (map generated_event seq_tr) (generated_event ip)
      Hctxt' Hgen' Henv Hdim' Henvdim Hsched'
      Hraw_trace Hevent_in) as Hsource_event.
  (* Convert the neutral raw event witness to an original source point. *)
  assert (Hwidth :
    list_max
      (map (fun pi => Datatypes.length pi.(PolyLang.pi_schedule))
        prep_pis) =
    ParallelValidator.schedule_width ((pis, varctxt), vars)).
  {
    subst prep_pis env_dim cols.
    apply prepared_schedule_width_eq.
  }
  rewrite Hwidth in Hsource_event.
  eapply prepared_event_to_source_point_exact;
    eauto using generated_event_matches.
Qed.
(** L2 for raw annotated code: pairs in one parallel slice of a certified
    dimension have disjoint footprints in every target trace. *)
Theorem annotated_codegen_many_raw_slice_disjoint :
  forall pis varctxt vars certs pl env root_tr,
    mayReturn
      (annotated_codegen_many_raw ((pis, varctxt), vars) certs) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    Forall
      (parallel_codegen_cert_disjoint ((pis, varctxt), vars)) certs ->
    ParallelLoop.trace_safe pl ->
    program_par_trace pl env root_tr ->
    Datatypes.length env = Datatypes.length varctxt ->
    forall cert outer z1 z2 suffix1 suffix2 ip1 ip2,
      In cert certs ->
      Datatypes.length outer =
        (Datatypes.length varctxt +
         cert.(ParallelValidator.certified_dim))%nat ->
      z1 <> z2 ->
      In ip1 root_tr ->
      In ip2 root_tr ->
      ip1.(ParallelLoop.ILSema.ip_index) = suffix1 ++ z1 :: outer ->
      ip2.(ParallelLoop.ILSema.ip_index) = suffix2 ++ z2 :: outer ->
      generated_footprint_disjoint ip1 ip2.
Proof.
  intros pis varctxt vars certs pl env root_tr
    Hgen Hwf Hcerts Hsafe Htrace Henv
    cert outer z1 z2 suffix1 suffix2 ip1 ip2
    Hcert Houter Hzneq Hin1 Hin2 Hidx1 Hidx2.
  destruct
    (annotated_codegen_many_raw_root_origin_exact
      pis varctxt vars certs pl env root_tr
      Hgen Hwf Hsafe Htrace Henv ip1 Hin1)
    as [s1 [Hfull1 Hcall1]].
  destruct
    (annotated_codegen_many_raw_root_origin_exact
      pis varctxt vars certs pl env root_tr
      Hgen Hwf Hsafe Htrace Henv ip2 Hin2)
    as [s2 [Hfull2 Hcall2]].
  rewrite Forall_forall in Hcerts.
  destruct (Hcerts cert Hcert) as [Hdisj Hbound].
  pose proof Hfull1 as Hf1.
  pose proof Hfull2 as Hf2.
  destruct Hf1 as [[_ [pi1 [Hpi1 [Hbel1 Hlen1]]]] _ _].
  destruct Hf2 as [[_ [pi2 [Hpi2 [Hbel2 Hlen2]]]] _ _].
  eapply same_call_footprint_disjoint;
    [exact Hcall1 | exact Hcall2 |].
  eapply Hdisj with (pi1 := pi1) (pi2 := pi2); try eassumption.
  eapply generated_source_siblings_same_slice
    with (width := ParallelValidator.schedule_width ((pis, varctxt), vars))
         (env := outer) (z1 := z1) (z2 := z2)
         (suffix1 := suffix1) (suffix2 := suffix2)
         (generated1 := ip1) (generated2 := ip2);
    try eassumption.
  reflexivity.
Qed.

(** * Parallel-loop siblings in every derivation *)

(** [par_siblings s env ip1 ip2]: some reachable [ParMode] loop of [s]
    may execute [ip1] and [ip2] in two distinct iterations.  The relation
    ranges over all traces of each iteration, so it does not fix one
    interleaving or one derivation. *)
Inductive par_siblings :
    ParallelLoop.stmt -> list Z ->
    ParallelLoop.InstrPoint -> ParallelLoop.InstrPoint -> Prop :=
| PSHere : forall d lb ub body env z1 z2 tr1 tr2 ip1 ip2,
    In z1 (Zrange (ParallelLoop.BaseLoop.eval_expr env lb)
                  (ParallelLoop.BaseLoop.eval_expr env ub)) ->
    In z2 (Zrange (ParallelLoop.BaseLoop.eval_expr env lb)
                  (ParallelLoop.BaseLoop.eval_expr env ub)) ->
    z1 <> z2 ->
    ParallelLoop.par_trace body (z1 :: env) tr1 ->
    ParallelLoop.par_trace body (z2 :: env) tr2 ->
    In ip1 tr1 ->
    In ip2 tr2 ->
    par_siblings
      (ParallelLoop.Loop ParallelLoop.ParMode (Some d) lb ub body) env ip1 ip2
| PSLoop : forall mode od lb ub body env z ip1 ip2,
    In z (Zrange (ParallelLoop.BaseLoop.eval_expr env lb)
                 (ParallelLoop.BaseLoop.eval_expr env ub)) ->
    par_siblings body (z :: env) ip1 ip2 ->
    par_siblings (ParallelLoop.Loop mode od lb ub body) env ip1 ip2
| PSSeq : forall ss env ip1 ip2,
    par_siblings_list ss env ip1 ip2 ->
    par_siblings (ParallelLoop.Seq ss) env ip1 ip2
| PSGuard : forall tst body env ip1 ip2,
    ParallelLoop.BaseLoop.eval_test env tst = true ->
    par_siblings body env ip1 ip2 ->
    par_siblings (ParallelLoop.Guard tst body) env ip1 ip2
with par_siblings_list :
    ParallelLoop.stmt_list -> list Z ->
    ParallelLoop.InstrPoint -> ParallelLoop.InstrPoint -> Prop :=
| PSHead : forall s ss env ip1 ip2,
    par_siblings s env ip1 ip2 ->
    par_siblings_list (ParallelLoop.SCons s ss) env ip1 ip2
| PSTail : forall s ss env ip1 ip2,
    par_siblings_list ss env ip1 ip2 ->
    par_siblings_list (ParallelLoop.SCons s ss) env ip1 ip2.

Scheme par_siblings_mutind := Induction for par_siblings Sort Prop
with par_siblings_list_mutind := Induction for par_siblings_list Sort Prop.
Combined Scheme par_siblings_comb
  from par_siblings_mutind, par_siblings_list_mutind.

(** ** Every statement with owned parallel loops has a trace *)

Lemma Forall2_exists_local :
  forall A B (R : A -> B -> Prop) xs,
    (forall x, In x xs -> exists y, R x y) ->
    exists ys, Forall2 R xs ys.
Proof.
  intros A B R xs.
  induction xs as [|x xs IH]; intros Hall.
  - exists []. constructor.
  - destruct (Hall x (or_introl eq_refl)) as [y Hy].
    destruct IH as [ys Hys].
    { intros x' Hx'. apply Hall. right. exact Hx'. }
    exists (y :: ys). constructor; assumption.
Qed.

Lemma Forall2_in_left_local :
  forall A B (R : A -> B -> Prop) xs ys x,
    Forall2 R xs ys ->
    In x xs ->
    exists y, In y ys /\ R x y.
Proof.
  intros A B R xs ys x Hfor.
  induction Hfor; intro Hin.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + exists y. split; [left; reflexivity|assumption].
    + destruct (IHHfor Hin) as [y' [Hin' HR]].
      exists y'. split; [right; exact Hin'|exact HR].
Qed.

Lemma Forall2_impl_local :
  forall A B (P Q : A -> B -> Prop) xs ys,
    (forall x y, P x y -> Q x y) ->
    Forall2 P xs ys ->
    Forall2 Q xs ys.
Proof.
  intros A B P Q xs ys Himp Hfor.
  induction Hfor; constructor; auto.
Qed.

Lemma interleave_family_concat_local :
  forall trs, ParallelLoop.interleave_family trs (List.concat trs).
Proof.
  induction trs as [|tr trs IH].
  - constructor.
  - induction tr as [|x xs IHxs].
    + simpl. constructor. exact IH.
    + simpl.
      apply (ParallelLoop.IF_take [] x xs trs).
      exact IHxs.
Qed.

Definition par_trace_total_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall certs env,
    par_modes_certified_stmt certs s ->
    exists tr, ParallelLoop.par_trace s env tr.

Definition par_trace_total_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall certs env,
    par_modes_certified_stmts certs ss ->
    exists tr, ParallelLoop.par_traces ss env tr.

Lemma par_trace_total_mutual :
  (forall s, par_trace_total_stmt_goal s) /\
  (forall ss, par_trace_total_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold par_trace_total_stmt_goal, par_trace_total_stmts_goal.
  - intros mode od lb ub body IH certs env Hmodes.
    simpl in Hmodes. destruct Hmodes as [Hmode Hbody].
    set (zs := Zrange (ParallelLoop.BaseLoop.eval_expr env lb)
                      (ParallelLoop.BaseLoop.eval_expr env ub)).
    destruct
      (Forall2_exists_local _ _
        (fun z tri => ParallelLoop.par_trace body (z :: env) tri) zs
        (fun z _ => IH certs (z :: env) Hbody))
      as [trs Htrs].
    destruct mode.
    + exists (List.concat trs). eapply ParallelLoop.PTLoopSeq; eauto.
    + destruct Hmode as [cert [_ Hod]]. subst od.
      exists (List.concat trs). eapply ParallelLoop.PTLoopPar; eauto.
      apply interleave_family_concat_local.
    + exists (List.concat trs). eapply ParallelLoop.PTLoopVec; eauto.
  - intros i es certs env _.
    eexists. constructor.
  - intros ss IH certs env Hmodes.
    destruct (IH certs env Hmodes) as [tr Htr].
    exists tr. constructor. exact Htr.
  - intros tst body IH certs env Hmodes.
    destruct (ParallelLoop.BaseLoop.eval_test env tst) eqn:Htest.
    + destruct (IH certs env Hmodes) as [tr Htr].
      exists tr. eapply ParallelLoop.PTGuardTrue; eauto.
    + exists []. eapply ParallelLoop.PTGuardFalse; eauto.
  - intros certs env _. exists []. constructor.
  - intros s IHs ss IHss certs env Hmodes.
    destruct Hmodes as [Hs Hss].
    destruct (IHs certs env Hs) as [tr1 Htr1].
    destruct (IHss certs env Hss) as [tr2 Htr2].
    exists (tr1 ++ tr2). constructor; assumption.
Qed.

(** Any trace of one iteration is part of a trace of its loop. *)
Lemma loop_trace_contains_iteration :
  forall certs mode od lb ub body env z trb,
    par_modes_certified_stmt certs (ParallelLoop.Loop mode od lb ub body) ->
    In z (Zrange (ParallelLoop.BaseLoop.eval_expr env lb)
                 (ParallelLoop.BaseLoop.eval_expr env ub)) ->
    ParallelLoop.par_trace body (z :: env) trb ->
    exists tr,
      ParallelLoop.par_trace (ParallelLoop.Loop mode od lb ub body) env tr /\
      (forall ip, In ip trb -> In ip tr).
Proof.
  intros certs mode od lb ub body env z trb Hmodes Hz Htrb.
  simpl in Hmodes. destruct Hmodes as [Hmode Hbody].
  set (zs := Zrange (ParallelLoop.BaseLoop.eval_expr env lb)
                    (ParallelLoop.BaseLoop.eval_expr env ub)) in *.
  destruct
    (Forall2_exists_local _ _
      (fun z' tri =>
        ParallelLoop.par_trace body (z' :: env) tri /\
        (z' = z -> tri = trb)) zs)
    as [trs Htrs].
  {
    intros z' _.
    destruct (Z.eq_dec z' z) as [-> | Hneq].
    - exists trb. split; [exact Htrb|reflexivity].
    - destruct (proj1 par_trace_total_mutual body certs (z' :: env) Hbody)
        as [tri Htri].
      exists tri. split; [exact Htri|]. intro Heq. contradiction.
  }
  assert (Htraces :
    Forall2 (fun z' tri => ParallelLoop.par_trace body (z' :: env) tri)
      zs trs).
  { eapply Forall2_impl_local; [|exact Htrs]. intros a b [H _]. exact H. }
  assert (Hin_trb : In trb trs).
  {
    destruct (Forall2_in_left_local _ _ _ _ _ _ Htrs Hz)
      as [tri [Hin [_ Heq]]].
    rewrite <- (Heq eq_refl). exact Hin.
  }
  exists (List.concat trs). split.
  - destruct mode.
    + eapply ParallelLoop.PTLoopSeq; eauto.
    + destruct Hmode as [cert [_ Hod]]. subst od.
      eapply ParallelLoop.PTLoopPar; eauto.
      apply interleave_family_concat_local.
    + eapply ParallelLoop.PTLoopVec; eauto.
  - intros ip Hip. apply in_concat. exists trb. split; assumption.
Qed.

(** ** Siblings of a certified loop have disjoint footprints *)

Definition embeds_in
    (O : ParallelLoop.InstrPoint -> Prop)
    (s : ParallelLoop.stmt) (env : list Z) : Prop :=
  forall tr, ParallelLoop.par_trace s env tr -> forall ip, In ip tr -> O ip.

Definition embeds_in_list
    (O : ParallelLoop.InstrPoint -> Prop)
    (ss : ParallelLoop.stmt_list) (env : list Z) : Prop :=
  forall tr, ParallelLoop.par_traces ss env tr -> forall ip, In ip tr -> O ip.

Lemma par_siblings_disjoint_mutual :
  forall pp certs (O : ParallelLoop.InstrPoint -> Prop),
    (forall ip, O ip ->
      exists source,
        generated_source_point_full
          pp (ParallelValidator.schedule_width pp) ip source /\
        point_same_call ip source) ->
    Forall (parallel_codegen_cert_disjoint pp) certs ->
    (forall s env ip1 ip2,
      par_siblings s env ip1 ip2 ->
      forall depth,
        tagged_from_depth_stmt depth s ->
        par_modes_certified_stmt certs s ->
        ParallelLoop.trace_safe_stmt s ->
        Datatypes.length env =
          (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
        embeds_in O s env ->
        generated_footprint_disjoint ip1 ip2) /\
    (forall ss env ip1 ip2,
      par_siblings_list ss env ip1 ip2 ->
      forall depth,
        tagged_from_depth_stmts depth ss ->
        par_modes_certified_stmts certs ss ->
        ParallelLoop.trace_safe_stmts ss ->
        Datatypes.length env =
          (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
        embeds_in_list O ss env ->
        generated_footprint_disjoint ip1 ip2).
Proof.
  intros pp certs O HO Hcerts.
  apply (par_siblings_comb
      (fun s env ip1 ip2 _ =>
        forall depth,
          tagged_from_depth_stmt depth s ->
          par_modes_certified_stmt certs s ->
          ParallelLoop.trace_safe_stmt s ->
          Datatypes.length env =
            (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
          embeds_in O s env ->
          generated_footprint_disjoint ip1 ip2)
      (fun ss env ip1 ip2 _ =>
        forall depth,
          tagged_from_depth_stmts depth ss ->
          par_modes_certified_stmts certs ss ->
          ParallelLoop.trace_safe_stmts ss ->
          Datatypes.length env =
            (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
          embeds_in_list O ss env ->
          generated_footprint_disjoint ip1 ip2)).
    + (* PSHere *)
      intros d lb ub body env z1 z2 tr1 tr2 ip1 ip2
        Hz1 Hz2 Hzneq Htr1 Htr2 Hin1 Hin2 depth Htag Hmodes Hsafe Henv Hemb.
      pose proof Hmodes as Hmodes_loop.
      simpl in Htag, Hmodes, Hsafe.
      destruct Htag as [Hd _].
      inversion Hd; subst d.
      destruct Hmodes as [[cert [Hcert Hod]] _].
      inversion Hod as [Hdepth].
      destruct
        (loop_trace_contains_iteration
          certs _ _ _ _ _ _ _ _ Hmodes_loop Hz1 Htr1)
        as [ltr1 [Hltr1 Hsub1]].
      destruct
        (loop_trace_contains_iteration
          certs _ _ _ _ _ _ _ _ Hmodes_loop Hz2 Htr2)
        as [ltr2 [Hltr2 Hsub2]].
      destruct (HO ip1 (Hemb ltr1 Hltr1 ip1 (Hsub1 ip1 Hin1)))
        as [s1 [Hfull1 Hcall1]].
      destruct (HO ip2 (Hemb ltr2 Hltr2 ip2 (Hsub2 ip2 Hin2)))
        as [s2 [Hfull2 Hcall2]].
      destruct (par_trace_point_extends_env body (z1 :: env) tr1 ip1
                  Hsafe Htr1 Hin1) as [suffix1 Hidx1].
      destruct (par_trace_point_extends_env body (z2 :: env) tr2 ip2
                  Hsafe Htr2 Hin2) as [suffix2 Hidx2].
      rewrite Forall_forall in Hcerts.
      destruct (Hcerts cert Hcert) as [Hdisj Hbound].
      pose proof Hfull1 as Hf1.
      pose proof Hfull2 as Hf2.
      destruct Hf1 as [[_ [pi1 [Hpi1 [Hbel1 Hlen1]]]] _ _].
      destruct Hf2 as [[_ [pi2 [Hpi2 [Hbel2 Hlen2]]]] _ _].
      eapply same_call_footprint_disjoint;
        [exact Hcall1 | exact Hcall2 |].
      eapply Hdisj with (pi1 := pi1) (pi2 := pi2); try eassumption.
      rewrite <- Hdepth.
      eapply generated_source_siblings_same_slice
        with (width := ParallelValidator.schedule_width pp)
             (env := env) (z1 := z1) (z2 := z2)
             (suffix1 := suffix1) (suffix2 := suffix2)
             (generated1 := ip1) (generated2 := ip2);
        try eassumption.
      * reflexivity.
      * rewrite Hdepth. exact Hbound.
    + (* PSLoop *)
      intros mode od lb ub body env z ip1 ip2 Hz Hsib IH
        depth Htag Hmodes Hsafe Henv Hemb.
      pose proof Hmodes as Hmodes_loop.
      simpl in Htag, Hmodes, Hsafe.
      destruct Htag as [_ Htag_body].
      destruct Hmodes as [_ Hmodes_body].
      eapply IH with (depth := S depth); eauto.
      * simpl. rewrite Henv. lia.
      * intros trb Htrb ip Hip.
        destruct
          (loop_trace_contains_iteration
            certs _ _ _ _ _ _ _ _ Hmodes_loop Hz Htrb)
          as [ltr [Hltr Hsub]].
        exact (Hemb ltr Hltr ip (Hsub ip Hip)).
    + (* PSSeq *)
      intros ss env ip1 ip2 Hsib IH depth Htag Hmodes Hsafe Henv Hemb.
      simpl in Htag, Hmodes, Hsafe.
      eapply IH; eauto.
      intros tr Htr ip Hip.
      eapply Hemb; [constructor; exact Htr|exact Hip].
    + (* PSGuard *)
      intros tst body env ip1 ip2 Htest Hsib IH
        depth Htag Hmodes Hsafe Henv Hemb.
      simpl in Htag, Hmodes, Hsafe.
      eapply IH; eauto.
      intros tr Htr ip Hip.
      eapply Hemb; [eapply ParallelLoop.PTGuardTrue; eauto|exact Hip].
    + (* PSHead *)
      intros s ss env ip1 ip2 Hsib IH depth Htag Hmodes Hsafe Henv Hemb.
      simpl in Htag, Hmodes, Hsafe.
      destruct Htag as [Htag_s _].
      destruct Hmodes as [Hmodes_s Hmodes_ss].
      destruct Hsafe as [Hsafe_s _].
      eapply IH; eauto.
      intros tr Htr ip Hip.
      destruct (proj2 par_trace_total_mutual ss certs env Hmodes_ss)
        as [tr2 Htr2].
      eapply Hemb.
      * econstructor; [exact Htr|exact Htr2].
      * apply in_or_app. left. exact Hip.
    + (* PSTail *)
      intros s ss env ip1 ip2 Hsib IH depth Htag Hmodes Hsafe Henv Hemb.
      simpl in Htag, Hmodes, Hsafe.
      destruct Htag as [_ Htag_ss].
      destruct Hmodes as [Hmodes_s Hmodes_ss].
      destruct Hsafe as [_ Hsafe_ss].
      eapply IH; eauto.
      intros tr Htr ip Hip.
      destruct (proj1 par_trace_total_mutual s certs env Hmodes_s)
        as [tr1 Htr1].
      eapply Hemb.
      * econstructor; [exact Htr1|exact Htr].
      * apply in_or_app. right. exact Hip.
Qed.

(** L2 for raw annotated code, structural form: any two instruction points
    that distinct iterations of the same parallel loop may execute have
    disjoint footprints. *)
Definition program_par_siblings
    (pl : ParallelLoop.t) (env : list Z)
    (ip1 ip2 : ParallelLoop.InstrPoint) : Prop :=
  let '((s, _), _) := pl in par_siblings s env ip1 ip2.

Theorem annotated_codegen_many_raw_par_siblings_disjoint :
  forall pis varctxt vars certs pl env ip1 ip2,
    mayReturn
      (annotated_codegen_many_raw ((pis, varctxt), vars) certs) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    Forall
      (parallel_codegen_cert_disjoint ((pis, varctxt), vars)) certs ->
    ParallelLoop.trace_safe pl ->
    Datatypes.length env = Datatypes.length varctxt ->
    program_par_siblings pl env ip1 ip2 ->
    generated_footprint_disjoint ip1 ip2.
Proof.
  intros pis varctxt vars certs pl env ip1 ip2
    Hgen Hwf Hcerts Hsafe Henv Hsib.
  pose proof Hgen as Hgen_root.
  set (O := fun ip =>
    exists root_tr, program_par_trace pl env root_tr /\ In ip root_tr).
  assert (HO :
    forall ip, O ip ->
      exists source,
        generated_source_point_full ((pis, varctxt), vars)
          (ParallelValidator.schedule_width ((pis, varctxt), vars))
          ip source /\
        point_same_call ip source).
  {
    intros ip [root_tr [Hroot Hin]].
    eapply annotated_codegen_many_raw_root_origin_exact; eauto.
  }
  unfold annotated_codegen_many_raw in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htagged Hpure]].
  apply mayReturn_pure in Hpure. subst pl.
  unfold tagged_prepared_codegen_raw in Htagged.
  apply mayReturn_bind in Htagged.
  destruct Htagged as [loop [Hloop Hpure]].
  apply mayReturn_pure in Hpure. subst tagged.
  unfold PrepareCore.prepared_codegen_raw in Hloop.
  unfold PrepareCore.CodeGen.codegen in Hloop.
  simpl in Hloop.
  apply mayReturn_bind in Hloop.
  destruct Hloop as [raw_stmt [Hraw Hpure]].
  apply mayReturn_pure in Hpure. subst loop.
  change
    (ParallelLoop.trace_safe
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars))) in Hsafe.
  change
    (program_par_siblings
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars)) env ip1 ip2) in Hsib.
  change
    (forall ip, O ip ->
      exists source,
        generated_source_point_full ((pis, varctxt), vars)
          (ParallelValidator.schedule_width ((pis, varctxt), vars))
          ip source /\
        point_same_call ip source) in HO.
  pose proof
    (parallelize_certified_dims_tagged certs raw_stmt varctxt vars)
    as Htag.
  pose proof
    (parallelize_certified_dims_modes certs raw_stmt varctxt vars)
    as Hmodes.
  assert (Hemb :
    embeds_in O
      (parallelize_certified_dims_stmt certs (tag_loop_stmt_at 0 raw_stmt))
      env).
  {
    intros tr Htr ip Hip.
    exists tr. split; [|exact Hip].
    change
      (program_par_trace
        (parallelize_certified_dims certs
          ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars)) env tr).
    rewrite parallelize_certified_dims_program_eq.
    exact Htr.
  }
  rewrite parallelize_certified_dims_program_eq in Htag, Hmodes, Hsafe, Hsib.
  simpl in Htag, Hmodes, Hsafe, Hsib.
  refine
    (proj1 (par_siblings_disjoint_mutual
              ((pis, varctxt), vars) certs O HO Hcerts)
       _ env ip1 ip2 Hsib 0%nat Htag Hmodes Hsafe _ Hemb).
  simpl. rewrite Henv, Nat.add_0_r. reflexivity.
Qed.

End ParallelCodegenDisjoint.
