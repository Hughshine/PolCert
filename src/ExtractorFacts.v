Require Import ZArith.
Require Import Bool.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import String.

Require Import PolIRs.

Require Import AST.
Require Import Base.
Require Import PolyBase.
Require Import List.
Require Import SetoidList.
Import ListNotations.

Require Import Linalg.
Require Import Lia.
Require Import LibTactics.
Require Import sflib.
Require Import Misc.
Require Import AffineValidator.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import PointWitness.

Require Import ExtractorFrontend.

Module ExtractorFacts (PolIRs : POLIRS).
Module Frontend := ExtractorFrontend PolIRs.
Include Frontend.

(** * Flattened-instance witnesses *)

Lemma flatten_instrs_in_intro:
    forall envv pis ipl ip pi,
    PolyLang.flatten_instrs envv pis ipl ->
    firstn (Datatypes.length envv) (PolyLang.ip_index ip) = envv ->
    nth_error pis (PolyLang.ip_nth ip) = Some pi ->
    PolyLang.belongs_to ip pi ->
    Datatypes.length (PolyLang.ip_index ip) = (Datatypes.length envv + PolyLang.pi_depth pi)%nat ->
    In ip ipl.
Proof.
    intros envv pis ipl ip pi Hflat Hpre Hnth Hbel Hlen.
    destruct Hflat as (_ & Hchar & _ & _).
    apply (proj2 (Hchar ip)).
    exists pi.
    split; [exact Hnth|].
    split; [exact Hpre|].
    split; [exact Hbel| exact Hlen].
Qed.

Definition flatten_instrs_prefix_slice
    (envv prefix: list Z)
    (pis: list PolyLang.PolyInstr)
    (ipl: list PolyLang.InstrPoint) : Prop :=
  (forall ip,
      In ip ipl <->
      exists pi suf,
        nth_error pis (PolyLang.ip_nth ip) = Some pi /\
        PolyLang.belongs_to ip pi /\
        (Datatypes.length prefix <= PolyLang.pi_depth pi)%nat /\
        PolyLang.ip_index ip = envv ++ prefix ++ suf /\
        Datatypes.length suf = (PolyLang.pi_depth pi - Datatypes.length prefix)%nat) /\
  NoDup ipl /\
  Sorted PolyLang.np_lt ipl.

Lemma flatten_instrs_prefix_slice_nil:
    forall envv pis ipl,
    PolyLang.flatten_instrs envv pis ipl ->
    flatten_instrs_prefix_slice envv [] pis ipl.
Proof.
    intros envv pis ipl Hflat.
    destruct Hflat as [Hprefix [Hchar [Hnodup Hsorted]]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        pose proof (proj1 (Hchar ip) Hin) as Hmem.
        destruct Hmem as [pi [Hnth [_ [Hbel Hlenidx]]]].
        pose proof (Hprefix ip Hin) as Hpre.
        pose proof (firstn_length_decompose envv (PolyLang.ip_index ip) (PolyLang.pi_depth pi) Hpre Hlenidx)
          as Hsplit.
        destruct Hsplit as [suf [Hidx Hsuflen]].
        exists pi.
        exists suf.
        split; [exact Hnth|].
        split; [exact Hbel|].
        split.
        * simpl. lia.
        * split; [exact Hidx|].
          { simpl.
            rewrite Nat.sub_0_r.
            exact Hsuflen. }
      + intros (pi & suf & Hnth & Hbel & _ & Hidx & Hsuflen).
        simpl in Hidx.
        assert (firstn (Datatypes.length envv) (PolyLang.ip_index ip) = envv) as Hpre.
        {
          rewrite Hidx.
          rewrite firstn_app.
          rewrite firstn_all.
          replace ((Datatypes.length envv - Datatypes.length envv)%nat) with 0%nat by lia.
          simpl.
          rewrite app_nil_r.
          reflexivity.
        }
        apply (proj2 (Hchar ip)).
        exists pi.
        split; [exact Hnth|].
        split; [exact Hpre|].
        split; [exact Hbel|].
        rewrite Hidx.
        rewrite app_length.
        simpl.
        rewrite Hsuflen.
        rewrite Nat.sub_0_r.
        reflexivity.
    - split; auto.
Qed.

Lemma flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice:
    forall lb ub body constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists i suf tsuf,
      PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf /\
      (Loop.eval_expr (rev (envv ++ prefix)) lb <= i < Loop.eval_expr (rev (envv ++ prefix)) ub)%Z /\
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [i] ++ tsuf.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    eapply extract_stmt_loop_success_inv in Hext.
    destruct Hext as (lbc & ubc & Hlb & Hub & Hbodyext).
    pose proof Hbodyext as Hbodyext_sched.
    pose proof Hbodyext as Hbodyext_dom.
    destruct Hslice as [Hchar [_ _]].
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & suf0 & Hnth & Hbel & Hgepref & Hidx & Hsuflen).
    assert (In pi pis) as Hpin.
    { eapply nth_error_In; eauto. }
    eapply extract_stmt_has_lifted_sched_prefix in Hbodyext_sched.
    2: { exact Hpin. }
    destruct Hbodyext_sched as (ks & tail_sched & Hdepth_sched & Hsched).
    eapply extract_stmt_has_lifted_prefix in Hbodyext_dom.
    2: { exact Hpin. }
    destruct Hbodyext_dom as (kd & tail_dom & Hdepth_dom & Hpoly).
    assert (kd = ks) as Hk by lia.
    subst kd.
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (Hindom & _ & Hts & _ & _).
    assert (Hlenidx_var:
      Datatypes.length (PolyLang.ip_index ip) =
      (env_dim + PolyLang.pi_depth pi)%nat).
    {
      rewrite Hidx.
      repeat rewrite app_length.
      simpl.
      rewrite Hprefixlen, Hlenenv, Hsuflen.
      lia.
    }
    rewrite Hdepth_sched in Hsuflen.
    rewrite Hprefixlen in Hsuflen.
    replace ((S iter_depth + ks - iter_depth)%nat) with (S ks)%nat in Hsuflen by lia.
    assert (Datatypes.length (rev suf0) = S ks)%nat as Hlenrev.
    { rewrite rev_length. exact Hsuflen. }
    assert (
      rev suf0 ++ rev prefix ++ rev envv =
      firstn ks (rev suf0) ++ (skipn ks (rev suf0) ++ rev prefix ++ rev envv)
    ) as Hsplit.
    {
      replace (rev suf0) with (firstn ks (rev suf0) ++ skipn ks (rev suf0)) at 1 by
        (eapply firstn_skipn).
      repeat rewrite app_assoc.
      reflexivity.
    }
    assert (Datatypes.length (firstn ks (rev suf0)) = ks)%nat as Hlenfirst.
    {
      rewrite firstn_length.
      lia.
    }
    eapply skipn_length_S_singleton in Hlenrev.
    destruct Hlenrev as [i Hskip].

    rewrite Hsched in Hts.
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: { exact Hlenidx_var. }
    rewrite Hidx in Hts.
    repeat rewrite rev_app_distr in Hts.
    rewrite <- app_assoc in Hts.
    rewrite affine_product_app in Hts.
    rewrite Hsplit in Hts.
    assert (Hlift_sched:
      affine_product
        (lift_affine_list_n ks
          (lift_affine_list sched_prefix ++
           [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)]))
        (firstn ks (rev suf0) ++
         (skipn ks (rev suf0) ++ rev prefix ++ rev envv)) =
      affine_product
        (lift_affine_list sched_prefix ++
         [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat), 0%Z)])
        (skipn ks (rev suf0) ++ rev prefix ++ rev envv)).
    {
      replace ks with (Datatypes.length (firstn ks (rev suf0))) at 1
        by (symmetry; exact Hlenfirst).
      eapply affine_product_lift_affine_list_n_app.
    }
    rewrite Hlift_sched in Hts.
    rewrite Hskip in Hts.
    simpl in Hts.
    rewrite affine_product_sched_prefix_loop in Hts.
    replace (rev prefix ++ rev envv) with (rev (envv ++ prefix)) in Hts.
    2: { rewrite rev_app_distr. reflexivity. }
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=(env_dim + iter_depth)%nat)
           (env:=envv ++ prefix)
           (affs:=sched_prefix) in Hts.
    2: {
      rewrite app_length.
      rewrite Hlenenv, Hprefixlen.
      lia.
    }
    rewrite <- app_assoc in Hts.

    rewrite Hpoly in Hindom.
    eapply in_poly_normalize_affine_list_rev_app_inv
      with (cols:=(env_dim + PolyLang.pi_depth pi)%nat)
           (env:=PolyLang.ip_index ip)
           (pol1:=lift_affine_list_n ks (lift_affine_list constrs ++ [lbc; ubc]))
           (pol2:=tail_dom) in Hindom.
    2: { exact Hlenidx_var. }
    destruct Hindom as [Hbase _].
    rewrite Hidx in Hbase.
    repeat rewrite rev_app_distr in Hbase.
    rewrite <- app_assoc in Hbase.
    rewrite Hsplit in Hbase.
    set (pref := firstn ks (rev suf0)) in *.
    set (suff := skipn ks (rev suf0) ++ rev prefix ++ rev envv) in *.
    assert (Datatypes.length pref = ks)%nat as Hlenpref.
    {
      unfold pref.
      exact Hlenfirst.
    }
    change (in_poly (pref ++ suff)
      (lift_affine_list_n ks (lift_affine_list constrs ++ [lbc; ubc])) = true) in Hbase.
    rewrite <- Hlenpref in Hbase.
    rewrite in_poly_lift_affine_list_n_app in Hbase.
    unfold suff in Hbase.
    rewrite Hskip in Hbase.
    simpl in Hbase.
    assert (Hlenrevprefix:
      Datatypes.length (rev prefix ++ rev envv) = (env_dim + iter_depth)%nat).
    {
      rewrite app_length.
      repeat rewrite rev_length.
      rewrite Hprefixlen, Hlenenv.
      lia.
    }
    eapply loop_constraints_complete_lifted in Hbase.
    2: { exact Hlenrevprefix. }
    2: { exact Hlb. }
    2: { exact Hub. }
    destruct Hbase as [_ Hbounds].
    assert (Hrevsuf:
      rev suf0 = pref ++ [i]).
    {
      rewrite <- Hskip.
      symmetry.
      eapply firstn_skipn.
    }
    assert (Hsuf0:
      suf0 = [i] ++ rev pref).
    {
      apply (f_equal (@rev Z)) in Hrevsuf.
      rewrite rev_involutive in Hrevsuf.
      rewrite rev_app_distr in Hrevsuf.
      simpl in Hrevsuf.
      exact Hrevsuf.
    }
    assert (Hbounds':
      (Loop.eval_expr (rev (envv ++ prefix)) lb <= i <
       Loop.eval_expr (rev (envv ++ prefix)) ub)%Z).
    {
      replace (rev (envv ++ prefix)) with (rev prefix ++ rev envv).
      2: { rewrite rev_app_distr. reflexivity. }
      exact Hbounds.
    }
    exists i.
    exists (rev pref).
    exists (affine_product tail_sched (pref ++ i :: rev (envv ++ prefix))).
    split.
    - rewrite Hidx.
      rewrite Hsuf0.
      rewrite app_assoc.
      reflexivity.
    - split.
      + exact Hbounds'.
      + exact Hts.
Qed.

Lemma loop_slice_point_fixed_prefix_slice:
    forall lb ub body constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip i,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip
      (filter
        (fun ip =>
          Z.eqb
            (nth
              (Datatypes.length
                (affine_product
                  (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                  (envv ++ prefix)))
              (PolyLang.ip_time_stamp ip) 0%Z)
            i)
        ipl) ->
    exists suf tsuf,
      PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf /\
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [i] ++ tsuf.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip i Hprefixlen Hext Hslice Hlenenv Hin.
    apply filter_In in Hin.
    destruct Hin as [Hip Hheq].
    destruct (
      flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
        lb ub body constrs env_dim iter_depth sched_prefix prefix
        pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip
    ) as [j [suf [tsuf [Hidx [_ Hts]]]]].
    replace (PolyLang.ip_time_stamp ip)
      with
        (affine_product
           (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
           (envv ++ prefix) ++ [j] ++ tsuf) in Hheq by exact Hts.
    assert (
      nth
        (Datatypes.length
          (affine_product
            (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
            (envv ++ prefix)))
        (affine_product
           (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
           (envv ++ prefix) ++ [j] ++ tsuf) 0%Z = j) as Hnthj.
    {
      clear.
      induction (affine_product
        (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
        (envv ++ prefix)) as [|z zs IH]; simpl.
      - reflexivity.
      - exact IH.
    }
    rewrite Hnthj in Hheq.
    apply Z.eqb_eq in Hheq.
    subst j.
    exists suf.
    exists tsuf.
    split; auto.
Qed.

Lemma flattened_point_loop_fixed_prefix_implies_timestamp_head_slice:
    forall lb ub body constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip i suf,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [i] ++ tsuf.
Proof.
    intros lb ub body constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip i suf Hprefixlen Hext Hslice Hlenenv Hip Hidxi.
    destruct (
      flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
        lb ub body constrs env_dim iter_depth sched_prefix prefix
        pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip
    ) as [j [suf' [tsuf [Hidx [_ Hts]]]]].
    assert (Hidx':
      (envv ++ prefix) ++ [j] ++ suf' =
      (envv ++ prefix) ++ [i] ++ suf).
    {
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      rewrite <- Hidx.
      exact Hidxi.
    }
    apply app_inv_head in Hidx'.
    inversion Hidx'; subst.
    exists tsuf.
    exact Hts.
Qed.

Lemma loop_slice_filter_prefix_slice_gen:
    forall lb ub body constrs sched_prefix env_dim iter_depth prefix
           pis envv ipl i,
    Datatypes.length prefix = iter_depth ->
    extract_stmt (PolIRs.Loop.Loop lb ub body) constrs
      env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    flatten_instrs_prefix_slice envv (prefix ++ [i]) pis
      (filter
        (fun ip =>
          Z.eqb
            (nth
              (Datatypes.length
                (affine_product
                  (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                  (envv ++ prefix)))
              (PolyLang.ip_time_stamp ip) 0%Z)
            i)
        ipl).
Proof.
    intros lb ub body constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl i Hprefixlen Hext Hslice Hlenenv.
    destruct Hslice as [Hchar [Hnodup Hsorted]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        apply filter_In in Hin.
        destruct Hin as [Hip Hpred].
        pose proof (proj1 (Hchar ip) Hip) as Hmem.
        destruct Hmem as (pi & suf0 & Hnth & Hbel & Hge0 & Hidx0 & Hlen0).
        assert (Hin_filter:
          In ip
            (filter
              (fun ip =>
                Z.eqb
                  (nth
                    (Datatypes.length
                      (affine_product
                        (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                        (envv ++ prefix)))
                    (PolyLang.ip_time_stamp ip) 0%Z)
                  i) ipl)).
        {
          apply filter_In.
          split; assumption.
        }
        destruct (
          loop_slice_point_fixed_prefix_slice
            lb ub body constrs env_dim iter_depth sched_prefix prefix
            pis envv ipl ip i Hprefixlen Hext
            ((conj Hchar (conj Hnodup Hsorted))) Hlenenv
            Hin_filter
        ) as [suf [tsuf [Hidx Hts]]].
        assert (Htail: suf0 = [i] ++ suf).
        {
          assert ((envv ++ prefix) ++ suf0 = (envv ++ prefix) ++ [i] ++ suf) as Heq.
          {
            rewrite <- app_assoc.
            rewrite <- app_assoc.
            rewrite <- Hidx0.
            exact Hidx.
          }
          apply app_inv_head in Heq.
          exact Heq.
        }
        exists pi.
        exists suf.
        split.
        * exact Hnth.
        * split; [exact Hbel|].
          split.
          { rewrite Htail in Hlen0.
            simpl in Hlen0.
            rewrite Hprefixlen in Hlen0.
            rewrite app_length.
            simpl.
            rewrite Hprefixlen.
            lia. }
          split.
          { rewrite <- app_assoc. exact Hidx. }
          { rewrite Htail in Hlen0.
            simpl in Hlen0.
            rewrite Hprefixlen in Hlen0.
            assert (Hlen_suf:
              Datatypes.length suf = Nat.pred (PolyLang.pi_depth pi - iter_depth)%nat).
            {
              remember (PolyLang.pi_depth pi - iter_depth)%nat as d.
              destruct d as [|d'].
              - simpl in Hlen0. lia.
              - simpl.
                inversion Hlen0.
                reflexivity.
            }
            rewrite app_length.
            simpl.
            rewrite Hprefixlen.
            replace (PolyLang.pi_depth pi - (iter_depth + 1))%nat
              with (Nat.pred (PolyLang.pi_depth pi - iter_depth)) by lia.
            exact Hlen_suf. }
      + intros (pi & suf & Hnth & Hbel & Hge & Hidx & Hlen).
        apply filter_In.
        split.
        * apply (proj2 (Hchar ip)).
          exists pi.
          exists ([i] ++ suf).
          split.
          { exact Hnth. }
          split.
          { exact Hbel. }
          split.
          { rewrite app_length in Hge. simpl in Hge. lia. }
          split.
          { rewrite <- app_assoc in Hidx.
            exact Hidx. }
          { simpl.
            rewrite Hlen.
            rewrite app_length.
            simpl.
            rewrite Hprefixlen.
            rewrite app_length in Hge.
            simpl in Hge.
            rewrite Hprefixlen in Hge.
            replace (PolyLang.pi_depth pi - iter_depth)%nat
              with (S (PolyLang.pi_depth pi - (iter_depth + 1))) by lia.
            reflexivity. }
        * assert (Hip_plain: In ip ipl).
          {
            apply (proj2 (Hchar ip)).
            exists pi.
            exists ([i] ++ suf).
            split.
            { exact Hnth. }
            split.
            { exact Hbel. }
            split.
            { rewrite app_length in Hge. simpl in Hge. lia. }
            split.
            { rewrite <- app_assoc in Hidx.
              exact Hidx. }
            { simpl.
              rewrite Hlen.
              rewrite app_length.
              simpl.
              rewrite Hprefixlen.
              rewrite app_length in Hge.
              simpl in Hge.
              rewrite Hprefixlen in Hge.
              replace (PolyLang.pi_depth pi - iter_depth)%nat
                with (S (PolyLang.pi_depth pi - (iter_depth + 1))) by lia.
              reflexivity. }
          }
          assert (Hidx_plain:
            PolyLang.ip_index ip = envv ++ prefix ++ [i] ++ suf).
          {
            rewrite <- app_assoc in Hidx.
            exact Hidx.
          }
          destruct (
            flattened_point_loop_fixed_prefix_implies_timestamp_head_slice
              lb ub body constrs env_dim iter_depth sched_prefix prefix
              pis envv ipl ip i suf Hprefixlen Hext
              ((conj Hchar (conj Hnodup Hsorted))) Hlenenv
              Hip_plain Hidx_plain
          ) as [tsuf Hts].
          replace (PolyLang.ip_time_stamp ip)
            with
              (affine_product
                 (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                 (envv ++ prefix) ++ [i] ++ tsuf) by exact Hts.
          assert (
            nth
              (Datatypes.length
                (affine_product
                  (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                  (envv ++ prefix)))
              (affine_product
                 (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
                 (envv ++ prefix) ++ [i] ++ tsuf) 0%Z = i) as Hnthi.
          {
            clear.
            induction (affine_product
              (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
              (envv ++ prefix)) as [|z zs IH]; simpl.
            - reflexivity.
            - exact IH.
          }
          rewrite Hnthi.
          apply Z.eqb_eq.
          reflexivity.
    - split.
      + eapply NoDup_filter.
        exact Hnodup.
      + eapply filter_sort; eauto.
        * eapply PolyLang.np_eq_equivalence.
        * eapply PolyLang.np_lt_strict.
        * eapply PolyLang.np_lt_proper.
Qed.

Lemma flatten_instrs_prefix_slice_filter_left:
    forall envv prefix pis1 pis2 ipl,
    flatten_instrs_prefix_slice envv prefix (pis1 ++ pis2) ipl ->
    flatten_instrs_prefix_slice envv prefix pis1
      (filter (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)) ipl).
Proof.
    intros envv prefix pis1 pis2 ipl Hslice.
    destruct Hslice as [Hchar [Hnodup Hsorted]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        apply filter_In in Hin.
        destruct Hin as [Hip Hlt].
        pose proof (proj1 (Hchar ip) Hip) as Hmem.
        destruct Hmem as (pi & suf & Hnth & Hbel & Hge & Hidx & Hsuflen).
        exists pi.
        exists suf.
        split.
        * rewrite nth_error_app1 in Hnth.
          2: { apply Nat.ltb_lt in Hlt; exact Hlt. }
          exact Hnth.
        * split; [exact Hbel|].
          split; [exact Hge|].
          split; [exact Hidx|exact Hsuflen].
      + intros (pi & suf & Hnth & Hbel & Hge & Hidx & Hsuflen).
        apply filter_In.
        split.
        * apply (proj2 (Hchar ip)).
          exists pi.
          exists suf.
          split.
          { rewrite nth_error_app1.
            - exact Hnth.
            - eapply nth_error_Some.
              rewrite Hnth.
              discriminate. }
          split; [exact Hbel|].
          split; [exact Hge|].
          split; [exact Hidx|exact Hsuflen].
        * apply Nat.ltb_lt.
          eapply nth_error_Some.
          rewrite Hnth.
          discriminate.
    - split.
      + eapply NoDup_filter.
        exact Hnodup.
      + eapply filter_sort; eauto.
        * eapply PolyLang.np_eq_equivalence.
        * eapply PolyLang.np_lt_strict.
        * eapply PolyLang.np_lt_proper.
Qed.


Lemma flattened_point_schedule_has_top_prefix_slice:
    forall stmt constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ tsuf.
Proof.
    intros stmt constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    destruct Hslice as [Hchar [_ _]].
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & suf & Hnth & Hbel & Hgeprefix & Hidx & Hsuflen).
    eapply extract_stmt_has_lifted_sched_prefix in Hext.
    2: { eapply nth_error_In; eauto. }
    destruct Hext as (k & tail & Hdepth & Hsched).
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (_ & _ & Hts & _ & _).
    rewrite Hsched in Hts.
    assert (Hlenidx:
      Datatypes.length (PolyLang.ip_index ip) =
      (env_dim + PolyLang.pi_depth pi)%nat).
    {
      rewrite Hdepth in Hsuflen.
      rewrite Hprefixlen in Hsuflen.
      replace ((iter_depth + k - iter_depth)%nat) with k in Hsuflen by lia.
      rewrite Hidx.
      repeat rewrite app_length.
      simpl.
      rewrite Hsuflen.
      rewrite Hdepth.
      rewrite Hprefixlen.
      rewrite <- Hlenenv.
      lia.
    }
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: { exact Hlenidx. }
    assert (Hidx_app: PolyLang.ip_index ip = (envv ++ prefix) ++ suf).
    { rewrite <- app_assoc. exact Hidx. }
    rewrite Hidx_app in Hts.
    rewrite rev_app_distr in Hts.
    assert (Datatypes.length (rev suf) = k)%nat as Hlenrev.
    { rewrite rev_length. lia. }
    rewrite affine_product_app in Hts.
    rewrite <- Hlenrev in Hts.
    rewrite affine_product_lift_affine_list_n_app in Hts.
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=(env_dim + iter_depth)%nat) (env:=envv ++ prefix) (affs:=sched_prefix) in Hts.
    2: {
      rewrite app_length.
      rewrite Hprefixlen.
      rewrite Hlenenv.
      lia.
    }
    exists (affine_product tail (rev suf ++ rev (envv ++ prefix))).
    exact Hts.
Qed.

Lemma flattened_point_satisfies_top_constraints_slice:
    forall stmt constrs env_dim iter_depth sched_prefix prefix
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    in_poly (rev (envv ++ prefix)) constrs = true.
Proof.
    intros stmt constrs env_dim iter_depth sched_prefix prefix
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    destruct Hslice as [Hchar [_ _]].
    pose proof (proj1 (Hchar ip) Hip) as Hm.
    destruct Hm as (pi & suf & Hnth & Hbel & Hgeprefix & Hidx & Hsuflen).
    eapply extract_stmt_has_lifted_prefix in Hext.
    2: { eapply nth_error_In; eauto. }
    destruct Hext as (k & tail & Hdepth & Hpoly).
    unfold PolyLang.belongs_to in Hbel.
    destruct Hbel as (Hindom & _ & _ & _ & _).
    rewrite Hpoly in Hindom.
    assert (Hlenidx:
      Datatypes.length (PolyLang.ip_index ip) =
      (env_dim + PolyLang.pi_depth pi)%nat).
    {
      rewrite Hdepth in Hsuflen.
      rewrite Hprefixlen in Hsuflen.
      rewrite Hidx.
      repeat rewrite app_length.
      simpl.
      rewrite Hsuflen.
      rewrite Hdepth.
      rewrite Hprefixlen.
      lia.
    }
    eapply in_poly_normalize_affine_list_rev_app_inv
      with (cols:=(env_dim + PolyLang.pi_depth pi)%nat)
           (env:=PolyLang.ip_index ip)
           (pol1:=lift_affine_list_n k constrs)
           (pol2:=tail) in Hindom.
    2: { exact Hlenidx. }
    destruct Hindom as [Hbase _].
    rewrite Hdepth in Hsuflen.
    rewrite Hprefixlen in Hsuflen.
    replace ((iter_depth + k - iter_depth)%nat) with k in Hsuflen by lia.
    assert (Hidx_app: PolyLang.ip_index ip = (envv ++ prefix) ++ suf).
    { rewrite <- app_assoc. exact Hidx. }
    rewrite Hidx_app in Hbase.
    rewrite rev_app_distr in Hbase.
    assert (Datatypes.length (rev suf) = k)%nat as Hlenrev.
    { rewrite rev_length. exact Hsuflen. }
    rewrite <- Hlenrev in Hbase.
    rewrite in_poly_lift_affine_list_n_app in Hbase.
    exact Hbase.
Qed.

Lemma flattened_point_seq_pos_timestamp_with_prefix_slice:
    forall stmt constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth
      (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, pos)]) = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [pos] ++ tsuf.
Proof.
    intros stmt constrs env_dim iter_depth sched_prefix prefix pos
      pis envv ipl ip Hprefixlen Hext Hslice Hlenenv Hip.
    eapply flattened_point_schedule_has_top_prefix_slice
      with (ip:=ip) in Hext; eauto.
    destruct Hext as [tsuf Hts].
    rewrite normalize_affine_list_rev_affine_product in Hts.
    2: {
      rewrite app_length.
      rewrite Hprefixlen.
      rewrite Hlenenv.
      lia.
    }
    rewrite affine_product_sched_prefix_seq in Hts.
    rewrite <- normalize_affine_list_rev_affine_product
      with (cols:=(env_dim + iter_depth)%nat) (env:=envv ++ prefix) (affs:=sched_prefix) in Hts.
    2: {
      rewrite app_length.
      rewrite Hprefixlen.
      rewrite Hlenenv.
      lia.
    }
    rewrite <- app_assoc in Hts.
    exists tsuf.
    exact Hts.
Qed.

Lemma lex_compare_cons_head_lt:
    forall h1 h2 t1 t2,
    (h1 < h2)%Z ->
    lex_compare (h1 :: t1) (h2 :: t2) = Lt.
Proof.
    intros h1 h2 t1 t2 Hlt.
    simpl.
    destruct (h1 ?= h2) eqn:Hcmp; simpl.
    - eapply Z.compare_eq_iff in Hcmp. lia.
    - reflexivity.
    - eapply Z.compare_gt_iff in Hcmp. lia.
Qed.

Lemma lex_compare_prefix_cons_head_lt:
    forall pref h1 h2 t1 t2,
    (h1 < h2)%Z ->
    lex_compare (pref ++ (h1 :: t1)) (pref ++ (h2 :: t2)) = Lt.
Proof.
    induction pref as [|p pref IH]; intros h1 h2 t1 t2 Hlt; simpl.
    - eapply lex_compare_cons_head_lt; eauto.
    - rewrite Z.compare_refl.
      eapply IH; eauto.
Qed.

Lemma filter_all_false_nil:
    forall A (f: A -> bool) l,
    (forall x, In x l -> f x = false) ->
    filter f l = [].
Proof.
    intros A f l Hall.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; left; reflexivity).
      apply IH.
      intros x Hin.
      eapply Hall.
      simpl. right. exact Hin.
Qed.

Lemma filter_all_true_id:
    forall A (f: A -> bool) l,
    (forall x, In x l -> f x = true) ->
    filter f l = l.
Proof.
    intros A f l Hall.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; left; reflexivity).
      f_equal.
      apply IH.
      intros x Hin.
      eapply Hall.
      simpl. right. exact Hin.
Qed.

Lemma filter_andb:
    forall A (f g: A -> bool) l,
    filter (fun x => andb (f x) (g x)) l = filter g (filter f l).
Proof.
    intros A f g l.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - destruct (f a) eqn:Hfa; simpl.
      + destruct (g a); simpl; rewrite IH; reflexivity.
      + rewrite IH; reflexivity.
Qed.

Lemma filter_negb_all_false_id:
    forall A (f: A -> bool) l,
    (forall x, In x l -> f x = false) ->
    filter (fun x => negb (f x)) l = l.
Proof.
    intros A f l Hall.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; left; reflexivity).
      simpl.
      f_equal.
      apply IH.
      intros x Hin.
      eapply Hall.
      simpl. right. exact Hin.
Qed.

Lemma sched_lt_not_sched_le_rev:
    forall ip1 ip2,
    lex_compare (PolyLang.ip_time_stamp ip1) (PolyLang.ip_time_stamp ip2) = Lt ->
    ~ PolyLang.instr_point_sched_le ip2 ip1.
Proof.
    intros ip1 ip2 Hlt Hle.
    unfold PolyLang.instr_point_sched_le in Hle.
    destruct Hle as [Hrevlt|Hreveq].
    - rewrite lex_compare_antisym in Hrevlt.
      rewrite Hlt in Hrevlt.
      discriminate.
    - rewrite lex_compare_antisym in Hreveq.
      rewrite Hlt in Hreveq.
      discriminate.
Qed.

Lemma sorted_sched_head_le_all:
    forall a l x,
    Sorted PolyLang.instr_point_sched_le (a :: l) ->
    In x l ->
    PolyLang.instr_point_sched_le a x.
Proof.
    intros a l x Hsorted Hin.
    pose proof (Sorted_extends PolyLang.instr_point_sched_le_trans Hsorted) as Hall.
    eapply Forall_forall in Hall; eauto.
Qed.

Lemma sorted_sched_filter_split_if_cross_lt:
    forall l (f: PolyLang.InstrPoint -> bool),
    Sorted PolyLang.instr_point_sched_le l ->
    (forall x y,
      In x l ->
      In y l ->
      f x = true ->
      f y = false ->
      lex_compare (PolyLang.ip_time_stamp x) (PolyLang.ip_time_stamp y) = Lt) ->
    l = filter f l ++ filter (fun x => negb (f x)) l.
Proof.
    intros l f Hsorted Hcross.
    induction l as [|a l IH]; simpl.
    - reflexivity.
    - inversion Hsorted as [|a0 l0 Hsorted_tl Hhd]; subst.
      destruct (f a) eqn:Hfa.
      + simpl.
        f_equal.
        eapply IH.
        * exact Hsorted_tl.
        * intros x y Hinx Hiny Hfx Hfy.
          eapply Hcross.
          -- simpl. right. exact Hinx.
          -- simpl. right. exact Hiny.
          -- exact Hfx.
          -- exact Hfy.
      + assert (forall x, In x l -> f x = false) as Hallfalse.
        {
          intros x Hinx.
          destruct (f x) eqn:Hfx; auto.
          exfalso.
          pose proof (Hcross x a) as Hlt.
          specialize (Hlt (or_intror Hinx) (or_introl eq_refl) Hfx Hfa).
          pose proof (sorted_sched_head_le_all a l x) as Hleax.
          specialize (Hleax).
          assert (Sorted PolyLang.instr_point_sched_le (a :: l)) as Hsorted_cons.
          { constructor; assumption. }
          specialize (Hleax Hsorted_cons Hinx).
          eapply (sched_lt_not_sched_le_rev x a) in Hlt.
          contradiction.
        }
        assert (filter f l = []) as Hnil.
        { eapply filter_all_false_nil; eauto. }
        assert (filter (fun x => negb (f x)) l = l) as Hnegb_id.
        { eapply filter_negb_all_false_id; eauto. }
        rewrite Hnil.
        rewrite Hnegb_id.
        reflexivity.
Qed.

Lemma sorted_filter_trans:
    forall A (R: A -> A -> Prop) (f: A -> bool) l,
    Transitive R ->
    Sorted R l ->
    Sorted R (filter f l).
Proof.
    intros A R f l Htrans Hsorted.
    induction Hsorted as [|a l Hsorted_tl IH Hhd].
    - simpl. constructor.
    - simpl.
      destruct (f a) eqn:Hfa.
      + constructor.
        * exact IH.
        * destruct (filter f l) as [|b l'] eqn:Hfilter.
          { constructor. }
          { apply HdRel_cons.
            assert (Forall (R a) l) as Hforall.
            {
              eapply Sorted_extends.
              - exact Htrans.
              - constructor; eauto.
            }
            assert (In b (filter f l)) as Hin_filter.
            { rewrite Hfilter. simpl. left. reflexivity. }
            apply filter_In in Hin_filter.
            destruct Hin_filter as [Hin_l _].
            eapply Forall_forall; eauto.
          }
      + exact IH.
Qed.

Lemma sorted_sched_filter:
    forall l (f: PolyLang.InstrPoint -> bool),
    Sorted PolyLang.instr_point_sched_le l ->
    Sorted PolyLang.instr_point_sched_le (filter f l).
Proof.
    intros l f Hsorted.
    eapply sorted_filter_trans.
    intros x y z Hxy Hyz.
    eapply PolyLang.instr_point_sched_le_trans; eauto.
    exact Hsorted.
Qed.

Lemma nth_after_prefix_singleton:
    forall (pfx tsuf: list Z) (i d: Z),
    nth (Datatypes.length pfx) (pfx ++ [i] ++ tsuf) d = i.
Proof.
    intros pfx tsuf i d.
    change (nth (Datatypes.length pfx) (pfx ++ i :: tsuf) d = i).
    apply nth_middle.
Qed.

Lemma sorted_sched_filter_split_by_prefix_head_eq:
    forall l pfx v,
    Sorted PolyLang.instr_point_sched_le l ->
    (forall ip, In ip l ->
      exists i tsuf, PolyLang.ip_time_stamp ip = pfx ++ [i] ++ tsuf) ->
    l =
      filter (fun ip => Z.ltb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) v) l ++
      filter (fun ip => Z.eqb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) v) l ++
      filter (fun ip => Z.ltb v (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z)) l.
Proof.
    intros l pfx v Hsorted Hhead.
    set (head := fun ip : PolyLang.InstrPoint =>
      nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z).
    pose proof (
      sorted_sched_filter_split_if_cross_lt
        l
        (fun ip => Z.ltb (head ip) v)
        Hsorted
    ) as Hsplit_lt.
    assert (Hcross_lt:
      forall x y,
      In x l ->
      In y l ->
      Z.ltb (head x) v = true ->
      Z.ltb (head y) v = false ->
      lex_compare (PolyLang.ip_time_stamp x) (PolyLang.ip_time_stamp y) = Lt).
    {
      intros x y Hinx Hiny Hfx Hfy.
      destruct (Hhead x Hinx) as [ix [tx Htsx]].
      destruct (Hhead y Hiny) as [iy [ty Htsy]].
      unfold head in Hfx, Hfy.
      rewrite Htsx in Hfx.
      rewrite Htsy in Hfy.
      rewrite nth_after_prefix_singleton in Hfx.
      rewrite nth_after_prefix_singleton in Hfy.
      eapply Z.ltb_lt in Hfx.
      eapply Z.ltb_ge in Hfy.
      assert ((ix < iy)%Z) as Hlt by lia.
      rewrite Htsx, Htsy.
      replace (pfx ++ [ix] ++ tx) with (pfx ++ (ix :: tx)) by reflexivity.
      replace (pfx ++ [iy] ++ ty) with (pfx ++ (iy :: ty)) by reflexivity.
      eapply lex_compare_prefix_cons_head_lt.
      exact Hlt.
    }
    specialize (Hsplit_lt Hcross_lt).
    set (l_ge :=
      filter (fun ip => negb (Z.ltb (head ip) v)) l).
    assert (Hsorted_ge:
      Sorted PolyLang.instr_point_sched_le l_ge).
    {
      unfold l_ge.
      eapply sorted_sched_filter.
      exact Hsorted.
    }
    pose proof (
      sorted_sched_filter_split_if_cross_lt
        l_ge
        (fun ip => Z.eqb (head ip) v)
        Hsorted_ge
    ) as Hsplit_eq_in_ge.
    assert (Hcross_eq:
      forall x y,
      In x l_ge ->
      In y l_ge ->
      Z.eqb (head x) v = true ->
      Z.eqb (head y) v = false ->
      lex_compare (PolyLang.ip_time_stamp x) (PolyLang.ip_time_stamp y) = Lt).
    {
      intros x y Hinx Hiny Hfx Hfy.
      apply filter_In in Hinx.
      apply filter_In in Hiny.
      destruct Hinx as [Hinx Hxge].
      destruct Hiny as [Hiny Hyge].
      destruct (Hhead x Hinx) as [ix [tx Htsx]].
      destruct (Hhead y Hiny) as [iy [ty Htsy]].
      unfold head in Hfx, Hfy, Hxge, Hyge.
      rewrite Htsx in Hfx.
      rewrite Htsy in Hfy.
      rewrite Htsx in Hxge.
      rewrite Htsy in Hyge.
      rewrite nth_after_prefix_singleton in Hfx.
      rewrite nth_after_prefix_singleton in Hfy.
      rewrite nth_after_prefix_singleton in Hxge.
      rewrite nth_after_prefix_singleton in Hyge.
      eapply Z.eqb_eq in Hfx.
      eapply Z.eqb_neq in Hfy.
      eapply Bool.negb_true_iff in Hxge.
      eapply Bool.negb_true_iff in Hyge.
      eapply Z.ltb_ge in Hxge.
      eapply Z.ltb_ge in Hyge.
      assert ((ix < iy)%Z) as Hlt by lia.
      rewrite Htsx, Htsy.
      replace (pfx ++ [ix] ++ tx) with (pfx ++ (ix :: tx)) by reflexivity.
      replace (pfx ++ [iy] ++ ty) with (pfx ++ (iy :: ty)) by reflexivity.
      eapply lex_compare_prefix_cons_head_lt.
      exact Hlt.
    }
    specialize (Hsplit_eq_in_ge Hcross_eq).
    unfold l_ge in Hsplit_eq_in_ge.
    rewrite Hsplit_lt at 1.
    rewrite Hsplit_eq_in_ge at 1.
    repeat rewrite app_assoc.
    f_equal.
    - f_equal.
      rewrite <- filter_andb.
      eapply filter_ext_in.
      intros ip Hin.
      destruct (Z.eqb (head ip) v) eqn:Heq; simpl.
      + eapply Z.eqb_eq in Heq.
        subst.
        rewrite Z.ltb_irrefl.
        rewrite Z.eqb_refl.
        simpl.
        reflexivity.
      + unfold head in Heq.
        rewrite Heq.
        rewrite andb_false_r.
        reflexivity.
    - rewrite <- filter_andb.
      eapply filter_ext_in.
      intros ip Hin.
      destruct (Z.ltb (head ip) v) eqn:Hltv; simpl.
      + eapply Z.ltb_lt in Hltv.
        assert ((v <? head ip)%Z = false) as Hn.
        { eapply Z.ltb_ge. lia. }
        unfold head in Hn |- *.
        rewrite Hn.
        reflexivity.
      + destruct (Z.eqb (head ip) v) eqn:Heq; simpl.
        * eapply Z.eqb_eq in Heq.
          subst.
          rewrite Z.ltb_irrefl.
          reflexivity.
        * eapply Z.ltb_ge in Hltv.
          eapply Z.eqb_neq in Heq.
          assert ((v < head ip)%Z) as Hgt by lia.
          assert ((v <? head ip)%Z = true) as Hv.
          { eapply Z.ltb_lt. exact Hgt. }
          unfold head in Hv |- *.
          rewrite Hv.
          reflexivity.
Qed.

Lemma sorted_sched_filter_ltb_succ_by_prefix_head:
    forall l pfx i,
    Sorted PolyLang.instr_point_sched_le l ->
    (forall ip, In ip l ->
      exists j tsuf, PolyLang.ip_time_stamp ip = pfx ++ [j] ++ tsuf) ->
    filter (fun ip => Z.ltb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) (i + 1)) l =
      filter (fun ip => Z.ltb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) i) l ++
      filter (fun ip => Z.eqb (nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z) i) l.
Proof.
    intros l pfx i Hsorted Hhead.
    set (head := fun ip : PolyLang.InstrPoint =>
      nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z).
    set (flt_succ := fun ip : PolyLang.InstrPoint => Z.ltb (head ip) (i + 1)).
    set (flt_lt := fun ip : PolyLang.InstrPoint => Z.ltb (head ip) i).
    set (flt_eq := fun ip : PolyLang.InstrPoint => Z.eqb (head ip) i).
    set (flt_gt := fun ip : PolyLang.InstrPoint => Z.ltb i (head ip)).
    pose proof (sorted_sched_filter_split_by_prefix_head_eq l pfx i Hsorted Hhead) as Hsplit.
    unfold head in Hsplit.
    rewrite Hsplit at 1.
    repeat rewrite filter_app.
    change (
      filter flt_succ (filter flt_lt l) ++
      filter flt_succ (filter flt_eq l) ++
      filter flt_succ (filter flt_gt l) =
      filter flt_lt l ++ filter flt_eq l).
    assert (Hsucc_lt:
      filter flt_succ (filter flt_lt l) = filter flt_lt l).
    {
      eapply filter_all_true_id.
      intros ip Hin.
      apply filter_In in Hin.
      destruct Hin as [_ Hlt].
      unfold flt_succ, flt_lt in *.
      eapply Z.ltb_lt in Hlt.
      eapply Z.ltb_lt.
      lia.
    }
    assert (Hsucc_eq:
      filter flt_succ (filter flt_eq l) = filter flt_eq l).
    {
      eapply filter_all_true_id.
      intros ip Hin.
      apply filter_In in Hin.
      destruct Hin as [_ Heq].
      unfold flt_succ, flt_eq in *.
      eapply Z.eqb_eq in Heq.
      subst.
      eapply Z.ltb_lt.
      lia.
    }
    assert (Hsucc_gt_nil:
      filter flt_succ (filter flt_gt l) = []).
    {
      eapply filter_all_false_nil.
      intros ip Hin.
      apply filter_In in Hin.
      destruct Hin as [_ Hgt].
      unfold flt_succ, flt_gt in *.
      eapply Z.ltb_lt in Hgt.
      eapply Z.ltb_ge.
      lia.
    }
    rewrite Hsucc_lt.
    rewrite Hsucc_eq.
    rewrite Hsucc_gt_nil.
    rewrite app_nil_r.
    reflexivity.
Qed.


Lemma permutation_singleton:
    forall A (x: A) l,
    Permutation [x] l ->
    l = [x].
Proof.
    exact Permutation_length_1_inv.
Qed.

Lemma instr_point_list_semantics_singleton_inv:
    forall ip st1 st2,
    PolyLang.instr_point_list_semantics [ip] st1 st2 ->
    exists stmid,
      PolyLang.instr_point_sema ip st1 stmid /\
      State.eq stmid st2.
Proof.
  exact PolyLang.ILSema.instr_point_list_semantics_singleton_decompose.
Qed.

Lemma instr_point_list_semantics_nil_inv:
    forall st1 st2,
    PolyLang.instr_point_list_semantics [] st1 st2 ->
    State.eq st1 st2.
Proof.
  exact PolyLang.ILSema.instr_point_list_semantics_nil_inv.
Qed.

Lemma instr_point_list_semantics_app_inv:
    forall l1 l2 st1 st3,
    PolyLang.instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      PolyLang.instr_point_list_semantics l1 st1 st2 /\
      PolyLang.instr_point_list_semantics l2 st2 st3.
Proof.
  exact PolyLang.ILSema.instr_point_list_semantics_app_inv.
Qed.


End ExtractorFacts.
