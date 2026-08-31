Require Import Lia.
Require Import List.
Require Import ZArith.
Import ListNotations.

Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import Base.
Require Import ExtractorFrontend.
Require Import LoopJamContext.
Require Import LoopJamLower.
Require Import LoopJamNative.
Require Import LoopJamValidator.
Require Import Linalg.
Require Import Misc.
Require Import PolIRs.
Require Import PolyBase.
Require Import PointWitness.
Require Import Result.

(** * From local affine validation to Loop unroll-jam refinement

    The local checker extracts the sibling-loop bodies twice.  Both schedules
    first retain the shared parameter and enclosing-iterator coordinates.  The
    old program then orders every point of body 1 before every point of body 2;
    the new program reverses those constant group rows.  Successful affine
    validation therefore proves universal cross-body independence inside each
    shared outer environment and over the loops' actual bounds.

    This file recovers the polyhedral origin of every dynamic trace point,
    applies pointwise affine soundness to paired old/new origins, lifts point
    permutability to the native jam trace premise, and covers both shapes
    accepted by the extracted pair checker.  [LoopJamContext] then lifts
    [checked_pair_refines_sound] through recursive unroll-jam lowering. *)
Module LoopJamBridge (PolIRs : POLIRS).

Module Loop := PolIRs.Loop.
Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module Context := LoopJamContext PolIRs.
Module Lower := Context.Lower.
Module Validator := Lower.Validator.
Module Native := Lower.Native.
Module Extractor := ExtractorFrontend PolIRs.

(** ** Semantic transport between native and polyhedral points *)

Definition point_sema_equiv
    (loop_point : Native.InstrPoint)
    (poly_point : PolyLang.InstrPoint) : Prop :=
  forall mem1 mem2,
    Native.ILSema.instr_point_sema loop_point mem1 mem2 <->
    PolyLang.instr_point_sema poly_point mem1 mem2.

Lemma permutable_of_point_sema_equiv :
  forall loop1 poly1 loop2 poly2,
    point_sema_equiv loop1 poly1 ->
    point_sema_equiv loop2 poly2 ->
    PolyLang.Permutable poly1 poly2 ->
    Native.ILSema.Permutable loop1 loop2.
Proof.
  intros loop1 poly1 loop2 poly2 Hequiv1 Hequiv2 Hperm mem1 Hna.
  specialize (Hperm mem1 Hna) as [Hforward Hbackward].
  split.
  - intros mem2 mem3 Hloop1 Hloop2.
    apply (proj1 (Hequiv1 mem1 mem2)) in Hloop1.
    apply (proj1 (Hequiv2 mem2 mem3)) in Hloop2.
    destruct (Hforward _ _ Hloop1 Hloop2)
      as [mem2' [mem3' [Hpoly2 [Hpoly1 Heq]]]].
    exists mem2', mem3'.
    repeat split; try exact Heq.
    + apply (proj2 (Hequiv2 mem1 mem2')). exact Hpoly2.
    + apply (proj2 (Hequiv1 mem2' mem3')). exact Hpoly1.
  - intros mem2 mem3 Hloop2 Hloop1.
    apply (proj1 (Hequiv2 mem1 mem2)) in Hloop2.
    apply (proj1 (Hequiv1 mem2 mem3)) in Hloop1.
    destruct (Hbackward _ _ Hloop2 Hloop1)
      as [mem2' [mem3' [Hpoly1 [Hpoly2 Heq]]]].
    exists mem2', mem3'.
    repeat split; try exact Heq.
    + apply (proj2 (Hequiv1 mem1 mem2')). exact Hpoly1.
    + apply (proj2 (Hequiv2 mem2' mem3')). exact Hpoly2.
Qed.

Definition source_point
    (env_dim nth : nat) (pi : PolyLang.PolyInstr)
    (loop_point : Native.InstrPoint) : PolyLang.InstrPoint :=
  let idx := rev loop_point.(Native.ILSema.ip_index) in
  {|
    PolyLang.ip_nth := nth;
    PolyLang.ip_index := idx;
    PolyLang.ip_transformation :=
      PolyLang.current_transformation_at env_dim pi;
    PolyLang.ip_time_stamp :=
      affine_product pi.(PolyLang.pi_schedule) idx;
    PolyLang.ip_instruction := pi.(PolyLang.pi_instr);
    PolyLang.ip_depth := pi.(PolyLang.pi_depth)
  |}.

Definition trace_point_origin
    (env_dim : nat) (pis : list PolyLang.PolyInstr)
    (loop_point : Native.InstrPoint) : Prop :=
  exists nth pi,
    nth_error pis nth = Some pi /\
    PolyLang.belongs_to (source_point env_dim nth pi loop_point) pi /\
    Datatypes.length
      (source_point env_dim nth pi loop_point).(PolyLang.ip_index) =
      (env_dim + pi.(PolyLang.pi_depth))%nat /\
    point_sema_equiv loop_point (source_point env_dim nth pi loop_point).

Lemma instr_point_sema_same_effect :
  forall p1 p2,
    p1.(Native.ILSema.ip_instruction) = p2.(PolyLang.ip_instruction) ->
    affine_product
      p1.(Native.ILSema.ip_transformation) p1.(Native.ILSema.ip_index) =
    affine_product p2.(PolyLang.ip_transformation) p2.(PolyLang.ip_index) ->
    point_sema_equiv p1 p2.
Proof.
  intros p1 p2 Hinstr Hargs mem1 mem2.
  split; intro Hsem; inversion Hsem as [wcs rcs Hstep]; subst;
    econstructor; simpl in *.
  - rewrite <- Hinstr, <- Hargs. exact Hstep.
  - rewrite Hinstr, Hargs. exact Hstep.
Qed.

Lemma Forall2_in_right :
  forall A B (R : A -> B -> Prop) xs ys y,
    Forall2 R xs ys ->
    In y ys ->
    exists x, In x xs /\ R x y.
Proof.
  intros A B R xs ys y Hfor.
  induction Hfor; intro Hin.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [<-|Hin].
    + exists x. split; [left; reflexivity|assumption].
    + destruct (IHHfor Hin) as [x' [Hin' HR]].
      exists x'. split; [right; exact Hin'|exact HR].
Qed.

Scheme bridge_stmt_ind := Induction for Loop.stmt Sort Prop
with bridge_stmts_ind := Induction for Loop.stmt_list Sort Prop.
Combined Scheme bridge_stmt_stmts_ind
  from bridge_stmt_ind, bridge_stmts_ind.

(** ** Extraction success and dynamic trace origins

    The first mutual induction derives native trace safety from the same
    successful extraction result accepted by the validator.  The second maps
    each native trace point back to its extracted [PolyInstr], including domain,
    dimension, and instruction-semantics evidence. *)

Lemma extractor_exprlist_success_implies_native :
  forall es cols tf,
    Extractor.exprlist_to_aff es cols = Okk tf ->
    exists native_tf, Loop.exprlist_to_aff es = Okk native_tf.
Proof.
  induction es as [|e es IH]; intros cols tf Hext.
  - simpl in Hext. inversion Hext; subst.
    exists []. reflexivity.
  - simpl in Hext.
    unfold Extractor.expr_to_aff in Hext.
    destruct (Loop.expr_to_aff e) as [[v c]|msg] eqn:He; try discriminate.
    destruct (Extractor.exprlist_to_aff es cols) as [tail|tail_msg]
      eqn:Htail; try discriminate.
    inversion Hext; subst; clear Hext.
    destruct (IH _ _ Htail) as [native_tail Hnative_tail].
    simpl. rewrite He, Hnative_tail.
    eauto.
Qed.

Definition extract_safe_stmt_goal (st : Loop.stmt) : Prop :=
  forall constrs env_dim iter_depth sched_prefix pis,
    Extractor.extract_stmt
      st constrs env_dim iter_depth sched_prefix = Okk pis ->
    Native.trace_safe_stmt st.

Definition extract_safe_stmts_goal (sts : Loop.stmt_list) : Prop :=
  forall constrs env_dim iter_depth sched_prefix pos pis,
    Extractor.extract_stmts
      sts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    Native.trace_safe_stmts sts.

Lemma extract_success_implies_trace_safe_mutual :
  (forall st, extract_safe_stmt_goal st) /\
  (forall sts, extract_safe_stmts_goal sts).
Proof.
  apply (bridge_stmt_stmts_ind extract_safe_stmt_goal extract_safe_stmts_goal).
  - intros lb ub body IH constrs env_dim iter_depth sched_prefix pis Hext.
    eapply Extractor.extract_stmt_loop_success_inv in Hext.
    destruct Hext as (lbc & ubc & Hlb & Hub & Hbody).
    simpl. eapply IH; eauto.
  - intros i es constrs env_dim iter_depth sched_prefix pis Hext.
    eapply Extractor.extract_stmt_instr_success_inv in Hext.
    destruct Hext as (tf & w & r & Htf & Haccess & Hpis).
    simpl.
    eapply extractor_exprlist_success_implies_native; eauto.
  - intros sts IH constrs env_dim iter_depth sched_prefix pis Hext.
    eapply Extractor.extract_stmt_seq_success_inv in Hext.
    eapply IH; eauto.
  - intros tst body IH constrs env_dim iter_depth sched_prefix pis Hext.
    eapply Extractor.extract_stmt_guard_success_inv in Hext.
    destruct Hext as (test_constrs & Htest & Hbody).
    simpl. eapply IH; eauto.
  - intros constrs env_dim iter_depth sched_prefix pos pis Hext.
    simpl. exact I.
  - intros st IHst sts IHsts constrs env_dim iter_depth sched_prefix pos pis Hext.
    eapply Extractor.extract_stmts_cons_success_inv in Hext.
    destruct Hext as (pis1 & pis2 & Hst & Hsts & Hpis).
    simpl. split; [eapply IHst | eapply IHsts]; eauto.
Qed.

Lemma extract_stmt_success_implies_trace_safe :
  forall st, extract_safe_stmt_goal st.
Proof.
  exact (proj1 extract_success_implies_trace_safe_mutual).
Qed.

Definition trace_origin_stmt_goal
    (st : Loop.stmt) : Prop :=
  forall env tr,
    Native.seq_trace st env tr ->
    forall constrs env_dim iter_depth sched_prefix pis,
      Datatypes.length env = (env_dim + iter_depth)%nat ->
      in_poly env constrs = true ->
      Extractor.extract_stmt
        st constrs env_dim iter_depth sched_prefix = Okk pis ->
      Native.trace_safe_stmt st ->
      forall ip, In ip tr -> trace_point_origin env_dim pis ip.

Definition trace_origin_stmts_goal
    (sts : Loop.stmt_list) : Prop :=
  forall env tr,
    Native.seq_traces sts env tr ->
    forall constrs env_dim iter_depth sched_prefix pos pis,
      Datatypes.length env = (env_dim + iter_depth)%nat ->
      in_poly env constrs = true ->
      Extractor.extract_stmts
        sts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
      Native.trace_safe_stmts sts ->
      forall ip, In ip tr -> trace_point_origin env_dim pis ip.

Lemma seq_trace_loop_inv :
  forall lb ub body env tr,
    Native.seq_trace (Loop.Loop lb ub body) env tr ->
    exists zs traces,
      zs = Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub) /\
      Forall2 (fun z tri => Native.seq_trace body (z :: env) tri) zs traces /\
      tr = concat traces.
Proof.
  intros lb ub body env tr Htr.
  inversion Htr; subst.
  eauto.
Qed.

Lemma seq_trace_extract_origin_mutual :
  (forall st, trace_origin_stmt_goal st) /\
  (forall sts, trace_origin_stmts_goal sts).
Proof.
  apply (bridge_stmt_stmts_ind trace_origin_stmt_goal trace_origin_stmts_goal).
  - intros lb ub body IH env tr Htr constrs env_dim iter_depth sched_prefix pis
      Hlen Hdom Hext Hsafe ip Hin.
    destruct (seq_trace_loop_inv _ _ _ _ _ Htr)
      as (zs & traces & Hzs & Hfor & Hconcat).
    subst tr.
    apply in_concat in Hin.
    destruct Hin as [tri [Htri_in Hip]].
    destruct (Forall2_in_right _ _ _ _ _ _ Hfor Htri_in)
      as [z [Hz_in Hbodytrace]].
    eapply Extractor.extract_stmt_loop_success_inv in Hext.
    destruct Hext as (lbc & ubc & Hlb & Hub & Hbodyext).
    simpl in Hsafe.
    refine
      (IH (z :: env) tri Hbodytrace
        (Extractor.lift_affine_list constrs ++ [lbc; ubc])
        env_dim (S iter_depth)
        (Extractor.lift_affine_list sched_prefix ++
          [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)])
        pis _ _ Hbodyext Hsafe ip Hip).
    + simpl. lia.
    + eapply Extractor.loop_constraints_sound_lifted; eauto.
      rewrite Hzs in Hz_in.
      apply Zrange_in. exact Hz_in.
  - intros i es env tr Htr constrs env_dim iter_depth sched_prefix pis
      Hlen Hdom Hext Hsafe ip Hin.
    inversion Htr; subst; clear Htr.
    simpl in Hin.
    destruct Hin as [Hip|Hin]; [subst ip|contradiction].
    eapply Extractor.extract_stmt_instr_success_inv in Hext.
    destruct Hext as (tf & w & r & Htf & Haccess & Hpis).
    subst pis.
    exists 0%nat.
    exists
      {|
        PolyLang.pi_depth := iter_depth;
        PolyLang.pi_instr := i;
        PolyLang.pi_poly :=
          Extractor.normalize_affine_list_rev
            (env_dim + iter_depth)%nat constrs;
        PolyLang.pi_schedule :=
          Extractor.normalize_affine_list_rev
            (env_dim + iter_depth)%nat sched_prefix;
        PolyLang.pi_point_witness := PSWIdentity iter_depth;
        PolyLang.pi_transformation :=
          Extractor.normalize_affine_list_rev
            (env_dim + iter_depth)%nat tf;
        PolyLang.pi_access_transformation :=
          Extractor.normalize_affine_list_rev
            (env_dim + iter_depth)%nat tf;
        PolyLang.pi_waccess := Extractor.normalize_access_list
          (env_dim + iter_depth)%nat w;
        PolyLang.pi_raccess := Extractor.normalize_access_list
          (env_dim + iter_depth)%nat r
      |}.
    split; [reflexivity|].
    assert (Hrevlen : Datatypes.length (rev env) =
      (env_dim + iter_depth)%nat).
    { rewrite rev_length. exact Hlen. }
    assert (Hdomrev :
      in_poly (rev env)
        (Extractor.normalize_affine_list_rev
           (env_dim + iter_depth)%nat constrs) = true).
    {
      unfold in_poly in *.
      rewrite Extractor.normalize_affine_list_rev_satisfies_constraint;
        [rewrite rev_involutive; exact Hdom|exact Hrevlen].
    }
    destruct Hsafe as [native_tf Hnative_tf].
    split.
    + unfold PolyLang.belongs_to, source_point, Loop.mk_instr_point.
      rewrite Hnative_tf. simpl.
      repeat split; try reflexivity.
      exact Hdomrev.
    + split.
      * unfold source_point, Loop.mk_instr_point.
        rewrite Hnative_tf. simpl. rewrite rev_length. exact Hlen.
      * unfold source_point, Loop.mk_instr_point.
        rewrite Hnative_tf. simpl.
        apply instr_point_sema_same_effect; [reflexivity|].
        change
          (affine_product native_tf env =
           affine_product
             (Extractor.normalize_affine_list_rev
                (env_dim + iter_depth)%nat tf)
             (rev env)).
        rewrite Extractor.normalize_affine_list_rev_affine_product;
          [|exact Hrevlen].
        rewrite rev_involutive.
        rewrite <- (Extractor.exprlist_to_aff_correct es env
          (env_dim + iter_depth)%nat tf Htf Hlen).
        symmetry.
        eapply Loop.exprlist_to_aff_correct.
        exact Hnative_tf.
  - intros sts IH env tr Htr constrs env_dim iter_depth sched_prefix pis
      Hlen Hdom Hext Hsafe ip Hin.
    inversion Htr as [|env' sts' tr' Htrs| | |]; subst; clear Htr.
    eapply Extractor.extract_stmt_seq_success_inv in Hext.
    eapply IH; eauto.
  - intros tst st IH env tr Htr constrs env_dim iter_depth
      sched_prefix pis Hlen Hdom Hext Hsafe ip Hin.
    eapply Extractor.extract_stmt_guard_success_inv in Hext.
    destruct Hext as (test_constrs & Htestaff & Hbodyext).
    simpl in Hsafe.
    inversion Htr as
      [| |env' tst' st' tr' Htest Hbodytrace|env' tst' st' Htest|];
      subst; clear Htr.
    + refine
        (IH env tr Hbodytrace
          (constrs ++
            Extractor.normalize_affine_list
              (env_dim + iter_depth)%nat test_constrs)
          env_dim iter_depth sched_prefix pis
          Hlen _ Hbodyext Hsafe ip Hin).
      eapply Extractor.guard_constraints_sound_in_poly; eauto.
    + contradiction.
  - intros env tr Htr constrs env_dim iter_depth sched_prefix pos pis
      Hlen Hdom Hext Hsafe ip Hin.
    inversion Htr; subst; clear Htr.
    contradiction.
  - intros st IH1 sts IH2 env tr Htr constrs env_dim
      iter_depth sched_prefix pos pis Hlen Hdom Hext Hsafe ip Hin.
    inversion Htr as [|env' st' sts' tr1 tr2 Htr1 Htr2];
      subst; clear Htr.
    eapply Extractor.extract_stmts_cons_success_inv in Hext.
    destruct Hext as (pis1 & pis2 & Hext1 & Hext2 & Hpis).
    subst pis.
    simpl in Hsafe.
    destruct Hsafe as [Hsafe1 Hsafe2].
    apply in_app_or in Hin.
    destruct Hin as [Hin1|Hin2].
    + destruct (IH1 _ _ Htr1 constrs env_dim iter_depth
        (sched_prefix ++
          [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)])
        pis1 Hlen Hdom Hext1 Hsafe1 ip Hin1)
        as (n & pi & Hnth & Hbel & Hpointlen & Hequiv).
      exists n, pi.
      split.
      * rewrite nth_error_app1; [exact Hnth|].
        eapply nth_error_Some. rewrite Hnth. discriminate.
      * split; [exact Hbel|].
        split; assumption.
    + destruct (IH2 _ _ Htr2 constrs env_dim iter_depth sched_prefix
        (S pos) pis2 Hlen Hdom Hext2 Hsafe2 ip Hin2)
        as (n & pi & Hnth & Hbel & Hpointlen & Hequiv).
      exists (Datatypes.length pis1 + n)%nat, pi.
      split.
      * rewrite nth_error_app2 by lia.
        replace (Datatypes.length pis1 + n - Datatypes.length pis1)%nat
          with n by lia.
        exact Hnth.
      * unfold source_point in Hbel, Hequiv |- *.
        simpl in *.
        split.
        -- unfold PolyLang.belongs_to in *; simpl in *.
           exact Hbel.
        -- split; [exact Hpointlen|].
           unfold point_sema_equiv in *; simpl in *.
           intros mem1 mem2.
           specialize (Hequiv mem1 mem2).
           split; intro Hsem.
           ++ apply (proj1 Hequiv) in Hsem.
              inversion Hsem as [wcs rcs Hinstr]; subst.
              econstructor. simpl in *. exact Hinstr.
           ++ apply (proj2 Hequiv).
              inversion Hsem as [wcs rcs Hinstr]; subst.
              econstructor. simpl in *. exact Hinstr.
Qed.

Lemma seq_trace_extract_origin :
  forall st, trace_origin_stmt_goal st.
Proof.
  exact (proj1 seq_trace_extract_origin_mutual).
Qed.

(** ** Schedule-shape and environment invariants

    Changing only the group row after the shared-coordinate prefix preserves
    instruction positions.  Nested extraction lifts the prefix while retaining
    its coordinate and constant timestamps.  Native indices are
    innermost-first, so reversing them exposes the shared parameter and outer
    iterator prefix required by pointwise validation. *)

Definition extract_same_length_stmt_goal (st : Loop.stmt) : Prop :=
  forall constrs env_dim iter_depth sched1 sched2 pis1 pis2,
    Extractor.extract_stmt st constrs env_dim iter_depth sched1 = Okk pis1 ->
    Extractor.extract_stmt st constrs env_dim iter_depth sched2 = Okk pis2 ->
    Datatypes.length pis1 = Datatypes.length pis2.

Definition extract_same_length_stmts_goal (sts : Loop.stmt_list) : Prop :=
  forall constrs env_dim iter_depth sched1 sched2 pos pis1 pis2,
    Extractor.extract_stmts
      sts constrs env_dim iter_depth sched1 pos = Okk pis1 ->
    Extractor.extract_stmts
      sts constrs env_dim iter_depth sched2 pos = Okk pis2 ->
    Datatypes.length pis1 = Datatypes.length pis2.

Lemma extract_same_length_mutual :
  (forall st, extract_same_length_stmt_goal st) /\
  (forall sts, extract_same_length_stmts_goal sts).
Proof.
  apply
    (bridge_stmt_stmts_ind
       extract_same_length_stmt_goal extract_same_length_stmts_goal).
  - intros lb ub body IH constrs env_dim iter_depth sched1 sched2 pis1 pis2
      Hext1 Hext2.
    eapply Extractor.extract_stmt_loop_success_inv in Hext1.
    eapply Extractor.extract_stmt_loop_success_inv in Hext2.
    destruct Hext1 as (lbc1 & ubc1 & Hlb1 & Hub1 & Hbody1).
    destruct Hext2 as (lbc2 & ubc2 & Hlb2 & Hub2 & Hbody2).
    rewrite Hlb1 in Hlb2. inversion Hlb2; subst lbc2.
    rewrite Hub1 in Hub2. inversion Hub2; subst ubc2.
    eapply IH; eauto.
  - intros i es constrs env_dim iter_depth sched1 sched2 pis1 pis2
      Hext1 Hext2.
    eapply Extractor.extract_stmt_instr_success_inv in Hext1.
    eapply Extractor.extract_stmt_instr_success_inv in Hext2.
    destruct Hext1 as (tf1 & w1 & r1 & Htf1 & Haccess1 & Hpis1).
    destruct Hext2 as (tf2 & w2 & r2 & Htf2 & Haccess2 & Hpis2).
    subst pis1 pis2. reflexivity.
  - intros sts IH constrs env_dim iter_depth sched1 sched2 pis1 pis2
      Hext1 Hext2.
    eapply Extractor.extract_stmt_seq_success_inv in Hext1.
    eapply Extractor.extract_stmt_seq_success_inv in Hext2.
    eapply IH; eauto.
  - intros tst body IH constrs env_dim iter_depth sched1 sched2 pis1 pis2
      Hext1 Hext2.
    eapply Extractor.extract_stmt_guard_success_inv in Hext1.
    eapply Extractor.extract_stmt_guard_success_inv in Hext2.
    destruct Hext1 as (test1 & Htest1 & Hbody1).
    destruct Hext2 as (test2 & Htest2 & Hbody2).
    rewrite Htest1 in Htest2. inversion Htest2; subst test2.
    eapply IH; eauto.
  - intros constrs env_dim iter_depth sched1 sched2 pos pis1 pis2
      Hext1 Hext2.
    eapply Extractor.extract_stmts_nil_success_inv in Hext1.
    eapply Extractor.extract_stmts_nil_success_inv in Hext2.
    subst pis1 pis2. reflexivity.
  - intros st IHst sts IHsts constrs env_dim iter_depth sched1 sched2 pos
      pis1 pis2 Hext1 Hext2.
    eapply Extractor.extract_stmts_cons_success_inv in Hext1.
    eapply Extractor.extract_stmts_cons_success_inv in Hext2.
    destruct Hext1 as (head1 & tail1 & Hhead1 & Htail1 & Hpis1).
    destruct Hext2 as (head2 & tail2 & Hhead2 & Htail2 & Hpis2).
    subst pis1 pis2.
    rewrite !app_length.
    pose proof (IHst _ _ _ _ _ _ _ Hhead1 Hhead2) as Hheads.
    pose proof (IHsts _ _ _ _ _ _ _ _ Htail1 Htail2) as Htails.
    lia.
Qed.

Lemma extract_stmt_same_length :
  forall st, extract_same_length_stmt_goal st.
Proof.
  exact (proj1 extract_same_length_mutual).
Qed.

Lemma local_shared_coord_row_eval :
  forall cols pos idx,
    Datatypes.length idx = cols ->
    (pos < cols)%nat ->
    affine_product [Validator.local_shared_coord_row cols pos] (rev idx) =
    [nth pos idx 0%Z].
Proof.
  intros cols pos idx Hlen Hpos.
  unfold Validator.local_shared_coord_row.
  simpl.
  rewrite Extractor.dot_product_rev.
  2: { rewrite resize_length. symmetry. exact Hlen. }
  rewrite Validator.JamCore.ParallelCore.dot_product_select_coord by lia.
  f_equal. lia.
Qed.

Lemma local_shared_schedule_from_eval :
  forall cols pos count idx,
    Datatypes.length idx = cols ->
    (pos + count <= cols)%nat ->
    affine_product
      (Validator.local_shared_schedule_from cols pos count) (rev idx) =
    firstn count (skipn pos idx).
Proof.
  intros cols pos count.
  revert pos.
  induction count as [|count IH]; intros pos idx Hlen Hcols.
  - reflexivity.
  - simpl Validator.local_shared_schedule_from.
    replace
      (Validator.local_shared_coord_row cols pos ::
       Validator.local_shared_schedule_from cols (S pos) count)
      with
      ([Validator.local_shared_coord_row cols pos] ++
       Validator.local_shared_schedule_from cols (S pos) count)
      by reflexivity.
    rewrite Extractor.affine_product_app.
    rewrite local_shared_coord_row_eval; [|exact Hlen|lia].
    rewrite IH; [|exact Hlen|lia].
    destruct (skipn pos idx) as [|x xs] eqn:Hskip.
    + assert (Hskip_len : Datatypes.length (skipn pos idx) = 0%nat).
      { rewrite Hskip. reflexivity. }
      rewrite skipn_length in Hskip_len. lia.
    + assert (Hnth : nth pos idx 0%Z = x).
      {
        replace pos with (pos + 0)%nat at 1 by lia.
        rewrite <- Misc.nth_skipn with (m := pos) (n := 0%nat) (d := 0%Z).
        rewrite Hskip. reflexivity.
      }
      assert (Htail : skipn (S pos) idx = xs).
      {
        replace (S pos) with (1 + pos)%nat by lia.
        rewrite <- skipn_skipn with (n := 1%nat) (m := pos) (l := idx).
        rewrite Hskip. reflexivity.
      }
      simpl. rewrite Hnth.
      replace
        match idx with
        | [] => []
        | _ :: rest => skipn pos rest
        end
        with (skipn (S pos) idx).
      2: { destruct idx; reflexivity. }
      rewrite Htail. reflexivity.
Qed.

Lemma local_jam_schedule_prefix_eval :
  forall cols shared group idx,
    Datatypes.length idx = cols ->
    (shared < cols)%nat ->
    affine_product
      (Validator.local_jam_schedule_prefix cols shared group) (rev idx) =
    firstn shared idx ++ [Z.of_nat group].
Proof.
  intros cols shared group idx Hlen Hshared.
  unfold Validator.local_jam_schedule_prefix.
  rewrite Extractor.affine_product_app.
  rewrite local_shared_schedule_from_eval; [|exact Hlen|lia].
  simpl.
  unfold Validator.local_stmt_order_row.
  simpl.
  rewrite dot_product_repeat_zero_left.
  f_equal.
Qed.

Lemma skipn_rev_to_rev_firstn :
  forall A (idx : list A) k cols,
    Datatypes.length idx = (k + cols)%nat ->
    skipn k (rev idx) = rev (firstn cols idx).
Proof.
  intros A idx k cols Hlen.
  rewrite <- (firstn_skipn cols idx) at 1.
  rewrite rev_app_distr.
  replace k with (Datatypes.length (rev (skipn cols idx))).
  - rewrite skipn_app by reflexivity. reflexivity.
  - rewrite rev_length, skipn_length, Hlen. lia.
Qed.

Lemma lifted_local_jam_schedule_prefix_eval :
  forall k cols shared group idx,
    Datatypes.length idx = (k + cols)%nat ->
    (shared < cols)%nat ->
    affine_product
      (Extractor.lift_affine_list_n k
         (Validator.local_jam_schedule_prefix cols shared group))
      (rev idx) =
    firstn shared idx ++ [Z.of_nat group].
Proof.
  intros k cols shared group idx Hlen Hshared.
  rewrite <- (firstn_skipn k (rev idx)) at 1.
  replace k with (Datatypes.length (firstn k (rev idx))) at 1.
  2: { rewrite firstn_length, rev_length, Hlen. lia. }
  rewrite Extractor.affine_product_lift_affine_list_n_app.
  rewrite (skipn_rev_to_rev_firstn Z idx k cols Hlen).
  rewrite local_jam_schedule_prefix_eval.
  - rewrite firstn_firstn.
    replace (Nat.min shared cols) with shared by lia.
    reflexivity.
  - rewrite firstn_length. lia.
  - exact Hshared.
Qed.

Lemma extracted_group_schedule_prefix :
  forall body constrs env_dim iter_depth shared group pis pi idx,
    Extractor.extract_stmt body constrs env_dim iter_depth
      (Validator.local_jam_schedule_prefix
         (env_dim + iter_depth)%nat shared group) = Okk pis ->
    In pi pis ->
    Datatypes.length idx = (env_dim + pi.(PolyLang.pi_depth))%nat ->
    (shared < env_dim + iter_depth)%nat ->
    exists tail,
      affine_product pi.(PolyLang.pi_schedule) idx =
        firstn shared idx ++ Z.of_nat group :: tail.
Proof.
  intros body constrs env_dim iter_depth shared group pis pi idx
    Hext Hin Hidxlen Hshared.
  pose proof Hext as Hprefix.
  eapply Extractor.extract_stmt_has_lifted_sched_prefix in Hprefix; eauto.
  destruct Hprefix as (k & tail & Hdepth & Hschedule).
  rewrite Hschedule.
  rewrite Extractor.normalize_affine_list_rev_affine_product by exact Hidxlen.
  rewrite Extractor.affine_product_app.
  rewrite lifted_local_jam_schedule_prefix_eval.
  2: { rewrite Hdepth in Hidxlen. lia. }
  2: exact Hshared.
  exists (affine_product tail (rev idx)).
  change
    ((firstn shared idx ++ [Z.of_nat group]) ++
       affine_product tail (rev idx) =
     firstn shared idx ++
       ([Z.of_nat group] ++ affine_product tail (rev idx))).
  symmetry. apply app_assoc.
Qed.

Definition trace_index_suffix_stmt_goal (st : Loop.stmt) : Prop :=
  forall env tr,
    Native.trace_safe_stmt st ->
    Native.seq_trace st env tr ->
    forall ip, In ip tr ->
    exists prefix,
      ip.(Native.ILSema.ip_index) = prefix ++ env.

Definition trace_index_suffix_stmts_goal (sts : Loop.stmt_list) : Prop :=
  forall env tr,
    Native.trace_safe_stmts sts ->
    Native.seq_traces sts env tr ->
    forall ip, In ip tr ->
    exists prefix,
      ip.(Native.ILSema.ip_index) = prefix ++ env.

Lemma trace_index_suffix_mutual :
  (forall st, trace_index_suffix_stmt_goal st) /\
  (forall sts, trace_index_suffix_stmts_goal sts).
Proof.
  apply
    (bridge_stmt_stmts_ind
       trace_index_suffix_stmt_goal trace_index_suffix_stmts_goal).
  - intros lb ub body IH env tr Hsafe Htr ip Hin.
    destruct (seq_trace_loop_inv _ _ _ _ _ Htr)
      as (zs & traces & Hzs & Hfor & Hconcat).
    subst tr.
    apply in_concat in Hin.
    destruct Hin as [tri [Htri_in Hip]].
    destruct (Forall2_in_right _ _ _ _ _ _ Hfor Htri_in)
      as [z [Hz Hbody]].
    simpl in Hsafe.
    destruct (IH _ _ Hsafe Hbody _ Hip) as [prefix Hindex].
    exists (prefix ++ [z]).
    rewrite Hindex. simpl.
    rewrite <- app_assoc. reflexivity.
  - intros i es env tr Hsafe Htr ip Hin.
    inversion Htr; subst; clear Htr.
    simpl in Hin.
    destruct Hin as [<-|Hin]; [|contradiction].
    destruct Hsafe as [tf Htf].
    exists [].
    unfold Loop.mk_instr_point. rewrite Htf. reflexivity.
  - intros sts IH env tr Hsafe Htr ip Hin.
    inversion Htr as [|env' sts' tr' Htrs| | |]; subst; clear Htr.
    eapply IH; eauto.
  - intros tst body IH env tr Hsafe Htr ip Hin.
    inversion Htr as
      [| |env' tst' body' tr' Htest Hbody|env' tst' body' Htest|];
      subst; clear Htr.
    + simpl in Hsafe. eapply IH; eauto.
    + contradiction.
  - intros env tr Hsafe Htr ip Hin.
    inversion Htr; subst; clear Htr.
    contradiction.
  - intros st IHst sts IHsts env tr Hsafe Htr ip Hin.
    inversion Htr as [|env' st' sts' tr1 tr2 Htr1 Htr2];
      subst; clear Htr.
    apply in_app_or in Hin.
    simpl in Hsafe. destruct Hsafe as [Hsafe_st Hsafe_sts].
    destruct Hin as [Hin|Hin].
    + eapply IHst; eauto.
    + eapply IHsts; eauto.
Qed.

Lemma trace_point_rev_env_prefix :
  forall st env tr ip,
    Native.trace_safe_stmt st ->
    Native.seq_trace st env tr ->
    In ip tr ->
    forall n,
      (n <= Datatypes.length env)%nat ->
      firstn n (rev ip.(Native.ILSema.ip_index)) = firstn n (rev env).
Proof.
  intros st env tr ip Hsafe Htr Hin n Hn.
  destruct ((proj1 trace_index_suffix_mutual) _ _ _ Hsafe Htr _ Hin)
    as [prefix Hindex].
  rewrite Hindex, rev_app_distr.
  rewrite firstn_app.
  rewrite rev_length.
  replace (n - Datatypes.length env)%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

(** ** Paired points and pointwise certificate soundness *)

Definition paired_source_point
    (env_dim nth : nat) (old_pi new_pi : PolyLang.PolyInstr)
    (loop_point : Native.InstrPoint) : PolyLang.InstrPoint_ext :=
  let idx := rev loop_point.(Native.ILSema.ip_index) in
  {|
    PolyLang.ip_nth_ext := nth;
    PolyLang.ip_index_ext := idx;
    PolyLang.ip_transformation_ext :=
      PolyLang.current_transformation_at env_dim old_pi;
    PolyLang.ip_access_transformation_ext :=
      PolyLang.current_access_transformation_at env_dim old_pi;
    PolyLang.ip_time_stamp1_ext :=
      affine_product old_pi.(PolyLang.pi_schedule) idx;
    PolyLang.ip_time_stamp2_ext :=
      affine_product new_pi.(PolyLang.pi_schedule) idx;
    PolyLang.ip_instruction_ext := old_pi.(PolyLang.pi_instr);
    PolyLang.ip_depth_ext := old_pi.(PolyLang.pi_depth)
  |}.

Lemma source_point_nth_irrelevant_belongs :
  forall env_dim n m pi loop_point,
    PolyLang.belongs_to (source_point env_dim n pi loop_point) pi ->
    PolyLang.belongs_to (source_point env_dim m pi loop_point) pi.
Proof.
  intros env_dim n m pi loop_point Hbel.
  unfold PolyLang.belongs_to, source_point in *.
  simpl in *. exact Hbel.
Qed.

Lemma source_point_nth_irrelevant_sema :
  forall env_dim n m pi loop_point,
    point_sema_equiv loop_point (source_point env_dim n pi loop_point) ->
    point_sema_equiv loop_point (source_point env_dim m pi loop_point).
Proof.
  intros env_dim n m pi loop_point Hequiv mem1 mem2.
  specialize (Hequiv mem1 mem2).
  split; intro Hsem.
  - apply (proj1 Hequiv) in Hsem.
    inversion Hsem as [wcs rcs Hinstr]; subst.
    econstructor. simpl in *. exact Hinstr.
  - apply (proj2 Hequiv).
    inversion Hsem as [wcs rcs Hinstr]; subst.
    econstructor. simpl in *. exact Hinstr.
Qed.

Lemma paired_source_belongs :
  forall env_dim nth old_pi new_pi loop_point,
    PolyLang.belongs_to (source_point env_dim nth old_pi loop_point) old_pi ->
    PolyLang.belongs_to_ext
      (paired_source_point env_dim nth old_pi new_pi loop_point)
      (Validator.AffineCore.compose_pinstr_ext_at env_dim old_pi new_pi).
Proof.
  intros env_dim nth old_pi new_pi loop_point Hbel.
  unfold PolyLang.belongs_to in Hbel.
  unfold PolyLang.belongs_to_ext, paired_source_point,
    Validator.AffineCore.compose_pinstr_ext_at, source_point.
  simpl in *.
  destruct Hbel as (Hpoly & Htf & Hts & Hinstr & Hdepth).
  repeat split; try reflexivity; assumption.
Qed.

Lemma compose_pinstrs_ext_nth_error :
  forall env_dim old_pis new_pis n old_pi new_pi,
    nth_error old_pis n = Some old_pi ->
    nth_error new_pis n = Some new_pi ->
    nth_error
      (Validator.AffineCore.compose_pinstrs_ext_at
         env_dim old_pis new_pis) n =
      Some (Validator.AffineCore.compose_pinstr_ext_at
              env_dim old_pi new_pi).
Proof.
  intros env_dim old_pis.
  induction old_pis as [|old_hd old_tl IH];
    intros [|new_hd new_tl] [|n] old_pi new_pi Hold Hnew;
    simpl in *; try discriminate.
  - inversion Hold; inversion Hnew; subst. reflexivity.
  - eapply IH; eauto.
Qed.

Lemma nth_error_exists_of_length_eq :
  forall A (xs ys : list A) n x,
    Datatypes.length xs = Datatypes.length ys ->
    nth_error xs n = Some x ->
    exists y, nth_error ys n = Some y.
Proof.
  intros A xs ys n x Hlen Hnth.
  assert (Hlt : (n < Datatypes.length ys)%nat).
  {
    rewrite <- Hlen.
    eapply nth_error_Some.
    rewrite Hnth. discriminate.
  }
  destruct (nth_error ys n) as [y|] eqn:Hyn; [eauto|].
  rewrite nth_error_None in Hyn. lia.
Qed.

Lemma paired_source_permutable_native :
  forall env_dim nth1 old_pi1 new_pi1 loop_point1
         nth2 old_pi2 new_pi2 loop_point2,
    point_sema_equiv
      loop_point1 (source_point env_dim nth1 old_pi1 loop_point1) ->
    point_sema_equiv
      loop_point2 (source_point env_dim nth2 old_pi2 loop_point2) ->
    PolyLang.Permutable_ext
      (paired_source_point env_dim nth1 old_pi1 new_pi1 loop_point1)
      (paired_source_point env_dim nth2 old_pi2 new_pi2 loop_point2) ->
    Native.ILSema.Permutable loop_point1 loop_point2.
Proof.
  intros env_dim nth1 old_pi1 new_pi1 loop_point1
    nth2 old_pi2 new_pi2 loop_point2 Hequiv1 Hequiv2 Hperm.
  unfold PolyLang.Permutable_ext, PolyLang.old_of_ext,
    paired_source_point in Hperm.
  simpl in Hperm.
  eapply permutable_of_point_sema_equiv; eauto.
Qed.

Lemma checked_pair_cross_points_permutable :
  forall varctxt vars depth lb ub body1 body2 cert env
         z1 tr1 ip1 z2 tr2 ip2,
    mayReturn
      (Validator.checked_loop_jam_pair_at_depth
         varctxt vars depth lb ub body1 body2)
      (Okk cert) ->
    Datatypes.length env = (Datatypes.length varctxt + depth)%nat ->
    In z1 (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub)) ->
    In z2 (Zrange (Loop.eval_expr env lb) (Loop.eval_expr env ub)) ->
    Native.seq_trace body1 (z1 :: env) tr1 ->
    Native.seq_trace body2 (z2 :: env) tr2 ->
    In ip1 tr1 ->
    In ip2 tr2 ->
    Native.ILSema.Permutable ip1 ip2.
Proof.
  intros varctxt vars depth lb ub body1 body2 cert env
    z1 tr1 ip1 z2 tr2 ip2 Hchecked Henvlen Hz1 Hz2 Htr1 Htr2 Hip1 Hip2.
  pose proof
    (Validator.checked_loop_jam_pair_at_depth_success_inv
       _ _ _ _ _ _ _ _ Hchecked) as Haccepted.
  destruct Haccepted as
    (old_pol & new_pol & Hold & Hnew & Hvalidate & Hcert).
  pose proof
    (Validator.local_jam_pair_pprog_success_inv
       _ _ _ false _ _ _ _ _ Hold) as Hold_inv.
  pose proof
    (Validator.local_jam_pair_pprog_success_inv
       _ _ _ true _ _ _ _ _ Hnew) as Hnew_inv.
  destruct Hold_inv as
    (old_lbc & old_ubc & old_pis1 & old_pis2 &
     Hold_lb & Hold_ub & Hold_ext1 & Hold_ext2 & Hold_pol).
  destruct Hnew_inv as
    (new_lbc & new_ubc & new_pis1 & new_pis2 &
     Hnew_lb & Hnew_ub & Hnew_ext1 & Hnew_ext2 & Hnew_pol).
  rewrite Hold_lb in Hnew_lb. inversion Hnew_lb; subst new_lbc.
  rewrite Hold_ub in Hnew_ub. inversion Hnew_ub; subst new_ubc.
  simpl in Hold_ext1, Hold_ext2, Hnew_ext1, Hnew_ext2.
  pose proof
    (extract_stmt_success_implies_trace_safe _ _ _ _ _ _ Hold_ext1)
    as Hsafe1.
  pose proof
    (extract_stmt_success_implies_trace_safe _ _ _ _ _ _ Hold_ext2)
    as Hsafe2.
  assert (Hdom1 : in_poly (z1 :: env) [old_lbc; old_ubc] = true).
  {
    change
      (in_poly (z1 :: env)
        (Extractor.lift_affine_list [] ++ [old_lbc; old_ubc]) = true).
    eapply Extractor.loop_constraints_sound_lifted.
    - exact Henvlen.
    - exact Hold_lb.
    - exact Hold_ub.
    - reflexivity.
    - apply Zrange_in. exact Hz1.
  }
  assert (Hdom2 : in_poly (z2 :: env) [old_lbc; old_ubc] = true).
  {
    change
      (in_poly (z2 :: env)
        (Extractor.lift_affine_list [] ++ [old_lbc; old_ubc]) = true).
    eapply Extractor.loop_constraints_sound_lifted.
    - exact Henvlen.
    - exact Hold_lb.
    - exact Hold_ub.
    - reflexivity.
    - apply Zrange_in. exact Hz2.
  }
  destruct
    (seq_trace_extract_origin body1 (z1 :: env) tr1 Htr1
       [old_lbc; old_ubc] (Datatypes.length varctxt) (S depth)
       (Validator.local_jam_schedule_prefix
          (Datatypes.length varctxt + S depth)%nat
          (Datatypes.length varctxt + depth)%nat 0)
       old_pis1 (ltac:(simpl; lia)) Hdom1 Hold_ext1 Hsafe1 ip1 Hip1)
    as (n1 & old_pi1 & Hold_nth1 & Hbel1 & Hidxlen1 & Hequiv1).
  destruct
    (seq_trace_extract_origin body2 (z2 :: env) tr2 Htr2
       [old_lbc; old_ubc] (Datatypes.length varctxt) (S depth)
       (Validator.local_jam_schedule_prefix
          (Datatypes.length varctxt + S depth)%nat
          (Datatypes.length varctxt + depth)%nat 1)
       old_pis2 (ltac:(simpl; lia)) Hdom2 Hold_ext2 Hsafe2 ip2 Hip2)
    as (n2 & old_pi2 & Hold_nth2 & Hbel2 & Hidxlen2 & Hequiv2).
  pose proof
    (extract_stmt_same_length body1 _ _ _ _ _ _ _
       Hold_ext1 Hnew_ext1) as Hlen_pis1.
  pose proof
    (extract_stmt_same_length body2 _ _ _ _ _ _ _
       Hold_ext2 Hnew_ext2) as Hlen_pis2.
  destruct
    (nth_error_exists_of_length_eq _ old_pis1 new_pis1 n1 old_pi1
       Hlen_pis1 Hold_nth1) as [new_pi1 Hnew_nth1].
  destruct
    (nth_error_exists_of_length_eq _ old_pis2 new_pis2 n2 old_pi2
       Hlen_pis2 Hold_nth2) as [new_pi2 Hnew_nth2].
  assert (Hold_full_nth1 :
    nth_error (old_pis1 ++ old_pis2) n1 = Some old_pi1).
  {
    rewrite nth_error_app1; [exact Hold_nth1|].
    eapply nth_error_Some. rewrite Hold_nth1. discriminate.
  }
  assert (Hnew_full_nth1 :
    nth_error (new_pis1 ++ new_pis2) n1 = Some new_pi1).
  {
    rewrite nth_error_app1; [exact Hnew_nth1|].
    eapply nth_error_Some. rewrite Hnew_nth1. discriminate.
  }
  set (full_n2 := (Datatypes.length old_pis1 + n2)%nat).
  assert (Hold_full_nth2 :
    nth_error (old_pis1 ++ old_pis2) full_n2 = Some old_pi2).
  {
    unfold full_n2. rewrite nth_error_app2 by lia.
    replace (Datatypes.length old_pis1 + n2 - Datatypes.length old_pis1)%nat
      with n2 by lia.
    exact Hold_nth2.
  }
  assert (Hnew_full_nth2 :
    nth_error (new_pis1 ++ new_pis2) full_n2 = Some new_pi2).
  {
    unfold full_n2. rewrite Hlen_pis1.
    rewrite nth_error_app2 by lia.
    replace (Datatypes.length new_pis1 + n2 - Datatypes.length new_pis1)%nat
      with n2 by lia.
    exact Hnew_nth2.
  }
  subst cert.
  pose proof
    (Validator.checked_loop_jam_pair_at_depth_pointwise_sound
       _ _ _ _ _ _ _ _ Hchecked) as Hpointwise.
  pose proof
    (Validator.checked_loop_jam_pair_at_depth_correspondence_sound
       _ _ _ _ _ _ _ _ Hchecked) as Hcorr.
  rewrite Hold_pol, Hnew_pol in Hpointwise, Hcorr.
  unfold Validator.loop_jam_pair_cert_pointwise_sound in Hpointwise.
  unfold Validator.loop_jam_pair_cert_correspondence_sound in Hcorr.
  simpl in Hpointwise, Hcorr.
  destruct
    (Hcorr _ _ _ _ _ _ eq_refl eq_refl)
    as (Hctxt & Hvars & Hfull_len & Hrel).
  assert (Heqdom1 : PolyLang.eqdom_pinstr old_pi1 new_pi1).
  {
    eapply rel_list_implies_rel_nth; eauto.
  }
  assert (Heqdom2 : PolyLang.eqdom_pinstr old_pi2 new_pi2).
  {
    eapply rel_list_implies_rel_nth; eauto.
  }
  assert (Hnew_idxlen1 :
    Datatypes.length (rev ip1.(Native.ILSema.ip_index)) =
      (Datatypes.length varctxt + new_pi1.(PolyLang.pi_depth))%nat).
  {
    destruct Heqdom1 as [Hdepth _]. rewrite <- Hdepth. exact Hidxlen1.
  }
  assert (Hnew_idxlen2 :
    Datatypes.length (rev ip2.(Native.ILSema.ip_index)) =
      (Datatypes.length varctxt + new_pi2.(PolyLang.pi_depth))%nat).
  {
    destruct Heqdom2 as [Hdepth _]. rewrite <- Hdepth. exact Hidxlen2.
  }
  assert (Hpi_ext1 : In
    (Validator.AffineCore.compose_pinstr_ext_at
       (Datatypes.length varctxt) old_pi1 new_pi1)
    (Validator.AffineCore.compose_pinstrs_ext_at
       (Datatypes.length varctxt)
       (old_pis1 ++ old_pis2) (new_pis1 ++ new_pis2))).
  {
    apply nth_error_In with (n := n1).
    eapply compose_pinstrs_ext_nth_error; eauto.
  }
  assert (Hpi_ext2 : In
    (Validator.AffineCore.compose_pinstr_ext_at
       (Datatypes.length varctxt) old_pi2 new_pi2)
    (Validator.AffineCore.compose_pinstrs_ext_at
       (Datatypes.length varctxt)
       (old_pis1 ++ old_pis2) (new_pis1 ++ new_pis2))).
  {
    apply nth_error_In with (n := full_n2).
    eapply compose_pinstrs_ext_nth_error; eauto.
  }
  set (ip1_ext := paired_source_point
    (Datatypes.length varctxt) n1 old_pi1 new_pi1 ip1).
  set (ip2_ext := paired_source_point
    (Datatypes.length varctxt) full_n2 old_pi2 new_pi2 ip2).
  assert (Hbel_ext1 : PolyLang.belongs_to_ext ip1_ext
    (Validator.AffineCore.compose_pinstr_ext_at
       (Datatypes.length varctxt) old_pi1 new_pi1)).
  {
    unfold ip1_ext.
    apply paired_source_belongs.
    exact Hbel1.
  }
  assert (Hbel_ext2 : PolyLang.belongs_to_ext ip2_ext
    (Validator.AffineCore.compose_pinstr_ext_at
       (Datatypes.length varctxt) old_pi2 new_pi2)).
  {
    unfold ip2_ext.
    apply paired_source_belongs.
    eapply source_point_nth_irrelevant_belongs; eauto.
  }
  assert (Hsame_params :
    firstn (Datatypes.length varctxt) ip1_ext.(PolyLang.ip_index_ext) =
    firstn (Datatypes.length varctxt) ip2_ext.(PolyLang.ip_index_ext)).
  {
    unfold ip1_ext, ip2_ext, paired_source_point. simpl.
    rewrite (trace_point_rev_env_prefix
      body1 (z1 :: env) tr1 ip1 Hsafe1 Htr1 Hip1
      (Datatypes.length varctxt)) by (simpl; lia).
    rewrite (trace_point_rev_env_prefix
      body2 (z2 :: env) tr2 ip2 Hsafe2 Htr2 Hip2
      (Datatypes.length varctxt)) by (simpl; lia).
    simpl.
    rewrite !firstn_app, !rev_length.
    replace (Datatypes.length varctxt - Datatypes.length env)%nat
      with 0%nat by lia.
    simpl. reflexivity.
  }
  assert (Hsame_shared :
    firstn (Datatypes.length varctxt + depth)%nat
      ip1_ext.(PolyLang.ip_index_ext) =
    firstn (Datatypes.length varctxt + depth)%nat
      ip2_ext.(PolyLang.ip_index_ext)).
  {
    unfold ip1_ext, ip2_ext, paired_source_point. simpl.
    rewrite <- Henvlen.
    rewrite (trace_point_rev_env_prefix
      body1 (z1 :: env) tr1 ip1 Hsafe1 Htr1 Hip1
      (Datatypes.length env)) by (simpl; lia).
    rewrite (trace_point_rev_env_prefix
      body2 (z2 :: env) tr2 ip2 Hsafe2 Htr2 Hip2
      (Datatypes.length env)) by (simpl; lia).
    simpl.
    rewrite !firstn_app, !rev_length.
    replace (Datatypes.length env - Datatypes.length env)%nat with 0%nat by lia.
    simpl. reflexivity.
  }
  assert (Hold_in1 : In old_pi1 old_pis1)
    by (eapply nth_error_In; eauto).
  assert (Hold_in2 : In old_pi2 old_pis2)
    by (eapply nth_error_In; eauto).
  assert (Hnew_in1 : In new_pi1 new_pis1)
    by (eapply nth_error_In; eauto).
  assert (Hnew_in2 : In new_pi2 new_pis2)
    by (eapply nth_error_In; eauto).
  destruct
    (extracted_group_schedule_prefix body1 [old_lbc; old_ubc]
       (Datatypes.length varctxt) (S depth)
       (Datatypes.length varctxt + depth)%nat 0 old_pis1 old_pi1
       (rev ip1.(Native.ILSema.ip_index)) Hold_ext1
       Hold_in1 Hidxlen1 (ltac:(lia))) as [old_tail1 Hold_head1].
  destruct
    (extracted_group_schedule_prefix body2 [old_lbc; old_ubc]
       (Datatypes.length varctxt) (S depth)
       (Datatypes.length varctxt + depth)%nat 1 old_pis2 old_pi2
       (rev ip2.(Native.ILSema.ip_index)) Hold_ext2
       Hold_in2 Hidxlen2 (ltac:(lia))) as [old_tail2 Hold_head2].
  destruct
    (extracted_group_schedule_prefix body1 [old_lbc; old_ubc]
       (Datatypes.length varctxt) (S depth)
       (Datatypes.length varctxt + depth)%nat 1 new_pis1 new_pi1
       (rev ip1.(Native.ILSema.ip_index)) Hnew_ext1
       Hnew_in1 Hnew_idxlen1 (ltac:(lia))) as [new_tail1 Hnew_head1].
  destruct
    (extracted_group_schedule_prefix body2 [old_lbc; old_ubc]
       (Datatypes.length varctxt) (S depth)
       (Datatypes.length varctxt + depth)%nat 0 new_pis2 new_pi2
       (rev ip2.(Native.ILSema.ip_index)) Hnew_ext2
       Hnew_in2 Hnew_idxlen2 (ltac:(lia))) as [new_tail2 Hnew_head2].
  assert (Hold_sched :
    PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext).
  {
    unfold PolyLang.instr_point_ext_old_sched_lt, ip1_ext, ip2_ext,
      paired_source_point. simpl.
    rewrite Hold_head1, Hold_head2.
    unfold ip1_ext, ip2_ext, paired_source_point in Hsame_shared.
    simpl in Hsame_shared. rewrite Hsame_shared.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive. reflexivity.
  }
  assert (Hnew_sched :
    PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext).
  {
    unfold PolyLang.instr_point_ext_new_sched_ge, ip1_ext, ip2_ext,
      paired_source_point. simpl.
    rewrite Hnew_head1, Hnew_head2.
    unfold ip1_ext, ip2_ext, paired_source_point in Hsame_shared.
    simpl in Hsame_shared. rewrite Hsame_shared.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive. right. reflexivity.
  }
  assert (Hperm_ext : PolyLang.Permutable_ext ip1_ext ip2_ext).
  {
    eapply Hpointwise with
      (pi1_ext := Validator.AffineCore.compose_pinstr_ext_at
        (Datatypes.length varctxt) old_pi1 new_pi1)
      (pi2_ext := Validator.AffineCore.compose_pinstr_ext_at
        (Datatypes.length varctxt) old_pi2 new_pi2);
      try eassumption.
    all: unfold ip1_ext, ip2_ext, paired_source_point in *;
      simpl in *; eauto.
  }
  unfold ip1_ext, ip2_ext in Hperm_ext.
  eapply paired_source_permutable_native.
  - exact Hequiv1.
  - eapply source_point_nth_irrelevant_sema; eauto.
  - exact Hperm_ext.
Qed.

(** ** From pointwise independence to the native jam trace premise *)

Lemma forall2_universal_cross_implies_jam_cross :
  forall body1 body2 env zs traces1,
    Forall2 (fun z tr => Native.seq_trace body1 (z :: env) tr) zs traces1 ->
    forall traces2,
      Forall2 (fun z tr => Native.seq_trace body2 (z :: env) tr) zs traces2 ->
      (forall z1 tr1 ip1 z2 tr2 ip2,
          In z1 zs ->
          In z2 zs ->
          Native.seq_trace body1 (z1 :: env) tr1 ->
          Native.seq_trace body2 (z2 :: env) tr2 ->
          In ip1 tr1 ->
          In ip2 tr2 ->
          Native.ILSema.Permutable ip1 ip2) ->
      Native.jam_cross_permutable traces1 traces2.
Proof.
  intros body1 body2 env zs traces1 Hfor1.
  induction Hfor1 as [|z1 tr1 zs' traces1' Htr1 Hfor1' IH];
    intros traces2 Hfor2 Hcross.
  - inversion Hfor2. reflexivity.
  - inversion Hfor2 as [|z2 tr2 zs2 traces2' Htr2 Hfor2'];
      subst; clear Hfor2.
    simpl. split.
    + intros ip1 ip2 Hin1 Hin2.
      apply in_concat in Hin1.
      destruct Hin1 as [tr1' [Htr1'_in Hip1]].
      destruct (Forall2_in_right _ _ _ _ _ _ Hfor1' Htr1'_in)
        as [z1' [Hz1' Htr1']].
      eapply Hcross; eauto; simpl; auto.
    + eapply IH; eauto.
      intros z1' tr1' ip1 z2' tr2' ip2
        Hz1' Hz2' Htr1' Htr2' Hip1 Hip2.
      eapply Hcross; eauto; simpl; auto.
Qed.

Lemma checked_pair_same_range_trace_cross_permutable :
  forall varctxt vars depth lb ub body1 body2 cert env,
    mayReturn
      (Validator.checked_loop_jam_pair_at_depth
         varctxt vars depth lb ub body1 body2)
      (Okk cert) ->
    Datatypes.length env = (Datatypes.length varctxt + depth)%nat ->
    Native.same_range_trace_cross_permutable lb ub body1 body2 env.
Proof.
  intros varctxt vars depth lb ub body1 body2 cert env Hchecked Henvlen
    zs traces1 traces2 Hzs Hfor1 Hfor2.
  eapply forall2_universal_cross_implies_jam_cross; eauto.
  intros z1 tr1 ip1 z2 tr2 ip2 Hz1 Hz2 Htr1 Htr2 Hip1 Hip2.
  eapply checked_pair_cross_points_permutable; eauto.
  - rewrite <- Hzs. exact Hz1.
  - rewrite <- Hzs. exact Hz2.
Qed.

(** ** Accepted checker results refine their source pairs

    These lemmas expose the instance-list execution consumed by the native jam
    theorem, reflect the checker's syntactic equality tests, and cover plain as
    well as equally guarded sibling loops. *)

Definition loop_to_aux_stmt_goal (st : Loop.stmt) : Prop :=
  forall env mem1 mem2,
    Loop.loop_semantics st env mem1 mem2 ->
    Loop.loop_semantics_aux st env mem1 mem2.

Definition loop_to_aux_stmts_goal (sts : Loop.stmt_list) : Prop :=
  forall env mem1 mem2,
    Loop.loop_semantics (Loop.Seq sts) env mem1 mem2 ->
    Loop.loop_semantics_aux (Loop.Seq sts) env mem1 mem2.

Lemma loop_semantics_to_aux_mutual :
  (forall st, loop_to_aux_stmt_goal st) /\
  (forall sts, loop_to_aux_stmts_goal sts).
Proof.
  apply (bridge_stmt_stmts_ind loop_to_aux_stmt_goal loop_to_aux_stmts_goal).
  - intros lb ub body IH env mem1 mem2 Hsem.
    inversion Hsem as [| | | | |env' lb' ub' body' mem1' mem2' Hiter];
      subst; clear Hsem.
    apply Loop.LSAuxLoop.
    induction Hiter.
    + constructor.
    + econstructor.
      * eapply IH; eauto.
      * exact IHHiter.
  - intros i es env mem1 mem2 Hsem.
    inversion Hsem as [i' es' env' mem1' mem2' wcs rcs Hinstr| | | | |];
      subst; clear Hsem.
    econstructor. exact Hinstr.
  - intros sts IH env mem1 mem2 Hsem.
    eapply IH; eauto.
  - intros tst body IH env mem1 mem2 Hsem.
    inversion Hsem as
      [| | |env' tst' body' mem1' mem2' Hbody Htest
       |env' tst' body' mem Htest|]; subst; clear Hsem.
    + eapply Loop.LSAuxGuardTrue; eauto.
    + eapply Loop.LSAuxGuardFalse; eauto.
  - intros env mem1 mem2 Hsem.
    inversion Hsem; subst; clear Hsem.
    constructor.
  - intros st IHst sts IHsts env mem1 mem3 Hsem.
    inversion Hsem as
      [| |env' st' sts' mem1' mem2 mem3' Hhead Htail| | |];
      subst; clear Hsem.
    econstructor.
    + eapply IHst; eauto.
    + eapply IHsts; eauto.
Qed.

Lemma loop_semantics_implies_instance_list :
  forall st env mem1 mem2,
    Loop.loop_semantics st env mem1 mem2 ->
    exists il,
      Loop.loop_instance_list_semantics st env il mem1 mem2.
Proof.
  intros st env mem1 mem2 Hsem.
  eapply Loop.loop_semantics_aux_implies_instance_list.
  eapply (proj1 loop_semantics_to_aux_mutual); eauto.
Qed.

Lemma expr_eqb_true_eq :
  forall e1 e2,
    Lower.Subst.expr_eqb e1 e2 = true ->
    e1 = e2.
Proof.
  induction e1; destruct e2; simpl; intro Heq; try discriminate.
  - apply Z.eqb_eq in Heq. subst. reflexivity.
  - apply andb_true_iff in Heq as [H1 H2].
    f_equal; eauto.
  - apply andb_true_iff in Heq as [H1 H2].
    apply Z.eqb_eq in H1. f_equal; eauto.
  - apply andb_true_iff in Heq as [H1 H2].
    apply Z.eqb_eq in H2. f_equal; eauto.
  - apply andb_true_iff in Heq as [H1 H2].
    apply Z.eqb_eq in H2. f_equal; eauto.
  - apply Nat.eqb_eq in Heq. subst. reflexivity.
  - apply andb_true_iff in Heq as [H1 H2].
    f_equal; eauto.
  - apply andb_true_iff in Heq as [H1 H2].
    f_equal; eauto.
Qed.

Lemma same_loop_boundsb_true_eq :
  forall lb1 ub1 lb2 ub2,
    Lower.same_loop_boundsb lb1 ub1 lb2 ub2 = true ->
    lb1 = lb2 /\ ub1 = ub2.
Proof.
  intros lb1 ub1 lb2 ub2 Hsame.
  unfold Lower.same_loop_boundsb in Hsame.
  apply andb_true_iff in Hsame as [Hlb Hub].
  split; eapply expr_eqb_true_eq; eauto.
Qed.

Lemma same_testb_true_eq :
  forall tst1 tst2,
    Lower.same_testb tst1 tst2 = true ->
    tst1 = tst2.
Proof.
  induction tst1; destruct tst2; simpl; intro Hsame; try discriminate.
  - apply andb_true_iff in Hsame as [H1 H2].
    f_equal; eapply expr_eqb_true_eq; eauto.
  - apply andb_true_iff in Hsame as [H1 H2].
    f_equal; eapply expr_eqb_true_eq; eauto.
  - apply andb_true_iff in Hsame as [H1 H2].
    f_equal; eauto.
  - apply andb_true_iff in Hsame as [H1 H2].
    f_equal; eauto.
  - f_equal. eauto.
  - destruct b, b0; simpl in Hsame; try discriminate; reflexivity.
Qed.

Lemma checked_pair_accepts_success_inv :
  forall varctxt vars depth lb ub body1 body2,
    mayReturn
      (Lower.checked_pair_accepts varctxt vars depth lb ub body1 body2)
      true ->
    exists cert,
      mayReturn
        (Validator.checked_loop_jam_pair_at_depth
           varctxt vars depth lb ub body1 body2)
        (Okk cert).
Proof.
  intros varctxt vars depth lb ub body1 body2 Haccept.
  unfold Lower.checked_pair_accepts in Haccept.
  apply mayReturn_bind in Haccept.
  destruct Haccept as [cert_res [Hcert Hret]].
  destruct cert_res as [cert|msg].
  - apply mayReturn_pure in Hret. inversion Hret; subst.
    exists cert. exact Hcert.
  - apply mayReturn_pure in Hret. discriminate.
Qed.

Lemma checked_pair_accepts_native_sound :
  forall varctxt vars depth lb ub body1 body2 env,
    mayReturn
      (Lower.checked_pair_accepts varctxt vars depth lb ub body1 body2)
      true ->
    Datatypes.length env = (Datatypes.length varctxt + depth)%nat ->
    Native.trace_safe_stmt
      (Native.unjammed_two_loop lb ub body1 body2) /\
    Native.same_range_trace_cross_permutable lb ub body1 body2 env.
Proof.
  intros varctxt vars depth lb ub body1 body2 env Haccept Henvlen.
  destruct (checked_pair_accepts_success_inv _ _ _ _ _ _ _ Haccept)
    as [cert Hchecked].
  pose proof
    (Validator.checked_loop_jam_pair_at_depth_success_inv
       _ _ _ _ _ _ _ _ Hchecked) as Haccepted.
  destruct Haccepted as
    (old_pol & new_pol & Hold & Hnew & Hvalidate & Hcert).
  pose proof
    (Validator.local_jam_pair_pprog_success_inv
       _ _ _ false _ _ _ _ _ Hold) as Hold_inv.
  destruct Hold_inv as
    (lbc & ubc & pis1 & pis2 & Hlb & Hub & Hext1 & Hext2 & Hpol).
  split.
  - simpl. repeat split; try exact I.
    + eapply extract_stmt_success_implies_trace_safe; eauto.
    + eapply extract_stmt_success_implies_trace_safe; eauto.
  - eapply checked_pair_same_range_trace_cross_permutable; eauto.
Qed.

Lemma checked_plain_pair_refines :
  forall varctxt vars depth lb ub body1 body2,
    mayReturn
      (Lower.checked_pair_accepts varctxt vars depth lb ub body1 body2)
      true ->
    Context.stmt_refines_at varctxt depth
      (Native.jammed_two_loop lb ub body1 body2)
      (Native.unjammed_two_loop lb ub body1 body2).
Proof.
  intros varctxt vars depth lb ub body1 body2 Haccept
    env Henvlen mem1 mem2 Hna Hsem.
  destruct
    (checked_pair_accepts_native_sound
       varctxt vars depth lb ub body1 body2 env Haccept Henvlen)
    as [Hsafe Hcross].
  destruct (loop_semantics_implies_instance_list _ _ _ _ Hsem)
    as [il Hinst].
  eapply Native.jammed_two_loop_instance_refines_unjammed; eauto.
Qed.

Lemma guard_seq2_refines_seq2_guards :
  forall tst st1 st2,
    Context.stmt_refines
      (Loop.Guard tst (Native.seq2 st1 st2))
      (Native.seq2 (Loop.Guard tst st1) (Loop.Guard tst st2)).
Proof.
  intros tst st1 st2 env mem1 mem2 Hna Hsem.
  inversion Hsem as
    [| | |env' tst' body' mem1' mem2' Hbody Htest
     |env' tst' body' mem Htest|]; subst; clear Hsem.
  - apply Lower.Unroll.seq_two_semantics in Hbody.
    destruct Hbody as [mem_mid [Hst1 Hst2]].
    exists mem2.
    split.
    + apply Lower.Unroll.seq_two_semantics.
      exists mem_mid. split.
      * eapply Loop.LGuardTrue; eauto.
      * eapply Loop.LGuardTrue; eauto.
    + apply Instr.State.eq_refl.
  - eexists.
    split.
    + apply Lower.Unroll.seq_two_semantics.
      eexists. split.
      * eapply Loop.LGuardFalse; eauto.
      * eapply Loop.LGuardFalse; eauto.
    + apply Instr.State.eq_refl.
Qed.

Theorem checked_pair_refines_sound :
  forall varctxt vars,
    Context.checked_pair_refines varctxt vars.
Proof.
  intros varctxt vars depth st1 st2 fused Hchecked.
  destruct st1 as [lb1 ub1 body1|i1 es1|sts1|tst1 guarded1];
    destruct st2 as [lb2 ub2 body2|i2 es2|sts2|tst2 guarded2];
    cbn [Lower.checked_try_jam_pair] in Hchecked;
    try solve [apply mayReturn_pure in Hchecked; discriminate].
  all: try destruct guarded1 as
      [lb1 ub1 body1|i1 es1|sts1|inner_tst1 inner1].
  all: try destruct guarded2 as
      [lb2 ub2 body2|i2 es2|sts2|inner_tst2 inner2].
  all: cbn [Lower.checked_try_jam_pair] in Hchecked.
  all: try solve [apply mayReturn_pure in Hchecked; discriminate].
  - destruct (Lower.same_loop_boundsb lb1 ub1 lb2 ub2) eqn:Hbounds.
    2: { apply mayReturn_pure in Hchecked. discriminate. }
    apply mayReturn_bind in Hchecked.
    destruct Hchecked as [ok [Haccept Hret]].
    destruct ok.
    2: { apply mayReturn_pure in Hret. discriminate. }
    apply mayReturn_pure in Hret.
    inversion Hret; subst fused; clear Hret.
    destruct (same_loop_boundsb_true_eq _ _ _ _ Hbounds) as [Hlb Hub].
    subst lb2 ub2.
    eapply checked_plain_pair_refines; eauto.
  - destruct
      (Lower.same_testb tst1 tst2 &&
       Lower.same_loop_boundsb lb1 ub1 lb2 ub2) eqn:Hcondition.
  2: { apply mayReturn_pure in Hchecked. discriminate. }
  apply andb_true_iff in Hcondition as [Htests Hbounds].
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Haccept Hret]].
  destruct ok.
  2: { apply mayReturn_pure in Hret. discriminate. }
  apply mayReturn_pure in Hret.
  inversion Hret; subst fused; clear Hret.
  pose proof (same_testb_true_eq _ _ Htests) as Htst.
  destruct (same_loop_boundsb_true_eq _ _ _ _ Hbounds) as [Hlb Hub].
  subst tst2 lb2 ub2.
  eapply Context.stmt_refines_at_trans.
  + eapply Context.stmt_refines_at_guard.
    eapply checked_plain_pair_refines; eauto.
  + eapply Context.stmt_refines_to_at.
    apply guard_seq2_refines_seq2_guards.
Qed.

End LoopJamBridge.
