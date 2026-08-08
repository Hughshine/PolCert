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

Require Import ExtractorFacts.

Module ExtractorCorrect (PolIRs : POLIRS).
Module Facts := ExtractorFacts PolIRs.
Include Facts.

(** * Statement-number rebasing *)

Definition rebase_ip_nth (base: nat) (ip: PolyLang.InstrPoint): PolyLang.InstrPoint :=
  {|
    PolyLang.ip_nth := (PolyLang.ip_nth ip - base)%nat;
    PolyLang.ip_index := PolyLang.ip_index ip;
    PolyLang.ip_transformation := PolyLang.ip_transformation ip;
    PolyLang.ip_time_stamp := PolyLang.ip_time_stamp ip;
    PolyLang.ip_instruction := PolyLang.ip_instruction ip;
    PolyLang.ip_depth := PolyLang.ip_depth ip;
  |}.

Lemma rebase_ip_nth_injective_ge:
    forall base ip1 ip2,
    (base <= PolyLang.ip_nth ip1)%nat ->
    (base <= PolyLang.ip_nth ip2)%nat ->
    rebase_ip_nth base ip1 = rebase_ip_nth base ip2 ->
    ip1 = ip2.
Proof.
    intros base ip1 ip2 Hge1 Hge2 Heq.
    destruct ip1 as [n1 idx1 tf1 ts1 instr1 d1].
    destruct ip2 as [n2 idx2 tf2 ts2 instr2 d2].
    simpl in *.
    inversion Heq; subst.
    assert (Hnsub: (n1 - base)%nat = (n2 - base)%nat) by exact H0.
    assert (Hnadd: ((n1 - base + base)%nat = (n2 - base + base)%nat)).
    { now rewrite Hnsub. }
    rewrite Nat.sub_add in Hnadd by exact Hge1.
    rewrite Nat.sub_add in Hnadd by exact Hge2.
    subst.
    f_equal; auto.
Qed.

Lemma np_lt_rebase_ip_nth_iff:
    forall base ip1 ip2,
    (base <= PolyLang.ip_nth ip1)%nat ->
    (base <= PolyLang.ip_nth ip2)%nat ->
    PolyLang.np_lt (rebase_ip_nth base ip1) (rebase_ip_nth base ip2) <->
    PolyLang.np_lt ip1 ip2.
Proof.
    intros base ip1 ip2 Hge1 Hge2.
    unfold PolyLang.np_lt.
    split; intro Hlt.
    - destruct Hlt as [Hlt|[Heq Hlex]].
      + left.
        simpl in Hlt.
        assert (Hplus: ((PolyLang.ip_nth ip1 - base + base < PolyLang.ip_nth ip2 - base + base)%nat)).
        { apply (proj1 (Nat.add_lt_mono_r _ _ base)); exact Hlt. }
        rewrite Nat.sub_add in Hplus by exact Hge1.
        rewrite Nat.sub_add in Hplus by exact Hge2.
        exact Hplus.
      + right. split.
        * simpl in Heq.
          assert (Hplus: ((PolyLang.ip_nth ip1 - base + base)%nat = (PolyLang.ip_nth ip2 - base + base)%nat)).
          { now rewrite Heq. }
          rewrite Nat.sub_add in Hplus by exact Hge1.
          rewrite Nat.sub_add in Hplus by exact Hge2.
          exact Hplus.
        * exact Hlex.
    - destruct Hlt as [Hlt|[Heq Hlex]].
      + left.
        assert (Hplus: ((PolyLang.ip_nth ip1 - base + base < PolyLang.ip_nth ip2 - base + base)%nat)).
        { rewrite Nat.sub_add by exact Hge1.
          rewrite Nat.sub_add by exact Hge2.
          exact Hlt. }
        apply (proj2 (Nat.add_lt_mono_r _ _ base)).
        exact Hplus.
      + right. split.
        * simpl. now rewrite Heq.
        * exact Hlex.
Qed.

Lemma instr_point_sema_rebase_ip_nth:
    forall base ip st1 st2,
    PolyLang.instr_point_sema (rebase_ip_nth base ip) st1 st2 <->
    PolyLang.instr_point_sema ip st1 st2.
Proof.
    intros base ip st1 st2.
    split; intro Hsema.
    - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
      econstructor.
      simpl in *.
      exact Hsem.
    - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
      econstructor.
      simpl in *.
      exact Hsem.
Qed.

Lemma instr_point_sched_le_rebase_ip_nth:
    forall base ip1 ip2,
    PolyLang.instr_point_sched_le (rebase_ip_nth base ip1) (rebase_ip_nth base ip2) <->
    PolyLang.instr_point_sched_le ip1 ip2.
Proof.
    intros base ip1 ip2.
    unfold PolyLang.instr_point_sched_le.
    simpl.
    tauto.
Qed.

Lemma sorted_sched_le_map_rebase_ip_nth:
    forall base ipl,
    Sorted PolyLang.instr_point_sched_le ipl ->
    Sorted PolyLang.instr_point_sched_le (map (rebase_ip_nth base) ipl).
Proof.
    intros base ipl Hsorted.
    induction Hsorted.
    - simpl. constructor.
    - simpl. constructor.
      + exact IHHsorted.
      + destruct H as [|b l0 Hle].
        * constructor.
        * constructor.
          eapply (proj2 (instr_point_sched_le_rebase_ip_nth base a b)).
          exact Hle.
Qed.

Lemma instr_point_list_semantics_map_rebase_ip_nth:
    forall base ipl st1 st2,
    PolyLang.instr_point_list_semantics (map (rebase_ip_nth base) ipl) st1 st2 <->
    PolyLang.instr_point_list_semantics ipl st1 st2.
Proof.
    intros base ipl.
    induction ipl as [|ip ipl IH]; intros st1 st2; split; intro Hsema.
    - inversion Hsema; subst.
      constructor.
      exact H.
    - inversion Hsema; subst.
      constructor.
      exact H.
    - simpl in Hsema.
      inversion Hsema; subst.
      econstructor.
      + eapply (proj1 (instr_point_sema_rebase_ip_nth base ip st1 st3)); eauto.
      + eapply (proj1 (IH st3 st2)); eauto.
    - simpl.
      inversion Hsema; subst.
      econstructor.
      + eapply (proj2 (instr_point_sema_rebase_ip_nth base ip st1 st3)); eauto.
      + eapply (proj2 (IH st3 st2)); eauto.
Qed.

Lemma instr_point_list_semantics_split_by_eq_app:
    forall l1 l2 l st1 st2,
    l = l1 ++ l2 ->
    PolyLang.instr_point_list_semantics l st1 st2 ->
    exists stmid,
      PolyLang.instr_point_list_semantics l1 st1 stmid /\
      PolyLang.instr_point_list_semantics l2 stmid st2.
Proof.
    intros l1 l2 l st1 st2 Heq Hsema.
    subst l.
    eapply instr_point_list_semantics_app_inv in Hsema.
    exact Hsema.
Qed.

Lemma instr_point_list_semantics_split_by_eq_app_rebase_right:
    forall base l1 l2 l st1 st2,
    l = l1 ++ l2 ->
    PolyLang.instr_point_list_semantics l st1 st2 ->
    exists stmid,
      PolyLang.instr_point_list_semantics l1 st1 stmid /\
      PolyLang.instr_point_list_semantics (map (rebase_ip_nth base) l2) stmid st2.
Proof.
    intros base l1 l2 l st1 st2 Heq Hsema.
    pose proof (
      instr_point_list_semantics_split_by_eq_app
        l1 l2 l st1 st2 Heq Hsema
    ) as Hsplit.
    destruct Hsplit as [stmid [Hleft Hright]].
    exists stmid.
    split.
    - exact Hleft.
    - eapply (proj2 (instr_point_list_semantics_map_rebase_ip_nth base l2 stmid st2)).
      exact Hright.
Qed.

Lemma sorted_np_lt_map_rebase_ip_nth:
    forall base ipl,
    (forall ip, In ip ipl -> (base <= PolyLang.ip_nth ip)%nat) ->
    Sorted PolyLang.np_lt ipl ->
    Sorted PolyLang.np_lt (map (rebase_ip_nth base) ipl).
Proof.
    intros base ipl Hge Hsorted.
    induction Hsorted.
    - simpl. constructor.
    - simpl. constructor.
      + eapply IHHsorted.
        intros ip Hin.
        eapply Hge.
        simpl. right. exact Hin.
      + destruct H as [|b l0 Hlt].
        * constructor.
        * constructor.
          assert ((base <= PolyLang.ip_nth a)%nat) as Hgea.
          { eapply Hge. simpl. left. reflexivity. }
          assert ((base <= PolyLang.ip_nth b)%nat) as Hgeb.
          { eapply Hge. simpl. right. left. reflexivity. }
          eapply (proj2 (np_lt_rebase_ip_nth_iff base a b Hgea Hgeb)).
          exact Hlt.
Qed.

Lemma nodup_map_rebase_ip_nth:
    forall base ipl,
    (forall ip, In ip ipl -> (base <= PolyLang.ip_nth ip)%nat) ->
    NoDup ipl ->
    NoDup (map (rebase_ip_nth base) ipl).
Proof.
    intros base ipl Hge Hnodup.
    induction Hnodup as [|x l Hnin Hnodup IH].
    - simpl. constructor.
    - simpl. constructor.
      + intro Hin.
        eapply in_map_iff in Hin.
        destruct Hin as (y & Heq & Hyin).
        assert ((base <= PolyLang.ip_nth y)%nat) as Hgey.
        { eapply Hge. simpl. right. exact Hyin. }
        assert ((base <= PolyLang.ip_nth x)%nat) as Hgex.
        { eapply Hge. simpl. left. reflexivity. }
        assert (y = x).
        { eapply rebase_ip_nth_injective_ge; eauto. }
        subst.
        eapply Hnin.
        exact Hyin.
      + eapply IH.
        intros ip Hin.
        eapply Hge.
        simpl. right. exact Hin.
Qed.

Lemma flatten_instrs_prefix_slice_filter_right_rebase:
    forall envv prefix pis1 pis2 ipl,
    flatten_instrs_prefix_slice envv prefix (pis1 ++ pis2) ipl ->
    flatten_instrs_prefix_slice envv prefix pis2
      (map (rebase_ip_nth (Datatypes.length pis1))
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)).
Proof.
    intros envv prefix pis1 pis2 ipl Hslice.
    destruct Hslice as [Hchar [Hnodup Hsorted]].
    unfold flatten_instrs_prefix_slice.
    split.
    - intros ip.
      split.
      + intro Hin.
        eapply in_map_iff in Hin.
        destruct Hin as (ip0 & Hip & Hip0in).
        subst ip.
        apply filter_In in Hip0in.
        destruct Hip0in as [Hip0in Hge0].
        apply negb_true_iff in Hge0.
        apply Nat.ltb_ge in Hge0.
        pose proof (proj1 (Hchar ip0) Hip0in) as Hmem.
        destruct Hmem as (pi & suf & Hnth & Hbel & Hgepref & Hidx & Hsuflen).
        exists pi.
        exists suf.
        split.
        * rewrite nth_error_app2 in Hnth by exact Hge0.
          exact Hnth.
        * split.
          { exact Hbel. }
          split.
          { exact Hgepref. }
          split.
          { exact Hidx. }
          { exact Hsuflen. }
      + intros (pi & suf & Hnth & Hbel & Hgepref & Hidx & Hsuflen).
        set (base := Datatypes.length pis1).
        set (ip0 := {|
          PolyLang.ip_nth := (PolyLang.ip_nth ip + base)%nat;
          PolyLang.ip_index := PolyLang.ip_index ip;
          PolyLang.ip_transformation := PolyLang.ip_transformation ip;
          PolyLang.ip_time_stamp := PolyLang.ip_time_stamp ip;
          PolyLang.ip_instruction := PolyLang.ip_instruction ip;
          PolyLang.ip_depth := PolyLang.ip_depth ip;
        |}).
        assert (Hip0in : In ip0 ipl).
        {
          apply (proj2 (Hchar ip0)).
          exists pi.
          exists suf.
          split.
	          { subst base ip0.
	            destruct ip.
	            simpl in *.
	            rewrite nth_error_app2 by lia.
	            replace
	              (ip_nth + Datatypes.length pis1 - Datatypes.length pis1)%nat
	              with ip_nth by lia.
	            exact Hnth. }
          split.
          { exact Hbel. }
          split.
          { exact Hgepref. }
          split.
          { exact Hidx. }
          { exact Hsuflen. }
        }
        eapply in_map_iff.
	        exists ip0.
	        split.
	        * subst base ip0.
	          destruct ip.
	          unfold rebase_ip_nth.
	          simpl.
	          replace
	            (ip_nth + Datatypes.length pis1 - Datatypes.length pis1)%nat
	            with ip_nth by lia.
	          reflexivity.
        * apply filter_In.
          split.
          { exact Hip0in. }
          { apply negb_true_iff.
            apply Nat.ltb_ge.
            subst base ip0.
            destruct ip.
            simpl.
            lia. }
    - split.
      + assert (Hgeall:
          forall ip,
            In
              ip
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl) ->
            (Datatypes.length pis1 <= PolyLang.ip_nth ip)%nat).
        {
          intros ip Hin.
          apply filter_In in Hin.
          destruct Hin as [_ Hge].
          apply negb_true_iff in Hge.
          apply Nat.ltb_ge in Hge.
          exact Hge.
        }
        eapply nodup_map_rebase_ip_nth.
        * exact Hgeall.
        * eapply NoDup_filter.
          exact Hnodup.
      + assert (Hsorted_filter:
          Sorted PolyLang.np_lt
            (filter
              (fun ip : PolyLang.InstrPoint =>
                negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
              ipl)).
        {
          eapply filter_sort; eauto.
          - eapply PolyLang.np_eq_equivalence.
          - eapply PolyLang.np_lt_strict.
          - eapply PolyLang.np_lt_proper.
        }
        assert (Hgeall:
          forall ip,
            In
              ip
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl) ->
            (Datatypes.length pis1 <= PolyLang.ip_nth ip)%nat).
        {
          intros ip Hin.
          apply filter_In in Hin.
          destruct Hin as [_ Hge].
          apply negb_true_iff in Hge.
          apply Nat.ltb_ge in Hge.
          exact Hge.
        }
        eapply sorted_np_lt_map_rebase_ip_nth.
        * exact Hgeall.
        * exact Hsorted_filter.
Qed.

Lemma flattened_stmts_pos_ge_with_prefix_slice:
    forall stmts constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl ip,
    Datatypes.length prefix = iter_depth ->
    extract_stmts stmts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    In ip ipl ->
    exists h tsuf,
      PolyLang.ip_time_stamp ip =
        affine_product
          (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
          (envv ++ prefix) ++ [h] ++ tsuf /\
      (Z.of_nat pos <= h)%Z.
Proof.
    induction stmts as [|stmt stmts' IH];
      intros constrs env_dim iter_depth sched_prefix prefix pos
        pis envv ipl ip Hprefixlen Hext Hslice Hlen Hip.
    - eapply extract_stmts_nil_success_inv in Hext.
      subst pis.
      destruct Hslice as [Hchar _].
      exfalso.
      pose proof (proj1 (Hchar ip) Hip) as Hmem.
      destruct Hmem as (pi & suf & Hnth & _).
      destruct (PolyLang.ip_nth ip); simpl in Hnth; inversion Hnth.
    - eapply extract_stmts_cons_success_inv in Hext.
      destruct Hext as (pis1 & pis2 & Hhdext & Htlext & Hpis).
      subst pis.
      destruct (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)) eqn:Hlt.
      + assert (Hin_left:
          In ip
            (filter
              (fun ip0 : PolyLang.InstrPoint =>
                Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1))
              ipl)).
        {
          apply filter_In.
          split; auto.
        }
        assert (Hhdslice:
          flatten_instrs_prefix_slice envv prefix pis1
            (filter
              (fun ip0 : PolyLang.InstrPoint =>
                Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1))
              ipl)).
        {
          eapply flatten_instrs_prefix_slice_filter_left.
          exact Hslice.
        }
        assert (Hhdext0:
          extract_stmt stmt constrs env_dim iter_depth
            (sched_prefix ++
             [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1).
        { exact Hhdext. }
        eapply flattened_point_seq_pos_timestamp_with_prefix_slice
          with (ip:=ip) in Hhdext0; eauto.
        destruct Hhdext0 as [tsuf Hts].
        exists (Z.of_nat pos).
        exists tsuf.
        split; [exact Hts|lia].
      + assert (Hin_right:
          In ip
            (filter
              (fun ip0 : PolyLang.InstrPoint =>
                negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
              ipl)).
        {
          apply filter_In.
          split; auto.
          apply negb_true_iff.
          exact Hlt.
        }
        assert (Hin_right_map:
          In (rebase_ip_nth (Datatypes.length pis1) ip)
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl))).
        {
          eapply in_map.
          exact Hin_right.
        }
        assert (Htlslice:
          flatten_instrs_prefix_slice envv prefix pis2
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip0 : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                ipl))).
        {
          eapply flatten_instrs_prefix_slice_filter_right_rebase.
          exact Hslice.
        }
        eapply IH
          with (sched_prefix:=sched_prefix)
               (pos:=S pos)
               (pis:=pis2)
               (envv:=envv)
               (ipl:=map (rebase_ip_nth (Datatypes.length pis1))
                      (filter
                        (fun ip0 : PolyLang.InstrPoint =>
                          negb (Nat.ltb (PolyLang.ip_nth ip0) (Datatypes.length pis1)))
                        ipl))
               (ip:=rebase_ip_nth (Datatypes.length pis1) ip)
          in Htlext; eauto.
        destruct Htlext as [h [tsuf [Hts Hge]]].
        exists h.
        exists tsuf.
        split.
        * simpl in Hts.
          exact Hts.
        * lia.
Qed.

Lemma seq_cons_cross_lt_by_nth_with_prefix_slice:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
           pis1 pis2 envv ipl1 ipl2 ip1 ip2,
    Datatypes.length prefix = iter_depth ->
    extract_stmt stmt constrs env_dim iter_depth
      (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 ->
    extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 ->
    flatten_instrs_prefix_slice envv prefix pis1 ipl1 ->
    flatten_instrs_prefix_slice envv prefix pis2
      (map (rebase_ip_nth (Datatypes.length pis1)) ipl2) ->
    Datatypes.length envv = env_dim ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    lex_compare (PolyLang.ip_time_stamp ip1) (PolyLang.ip_time_stamp ip2) = Lt.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
      pis1 pis2 envv ipl1 ipl2 ip1 ip2
      Hprefixlen Hhdext Htlext Hflat1 Hflat2 Hlen Hip1 Hip2.
    eapply flattened_point_seq_pos_timestamp_with_prefix_slice
      with (ip:=ip1) in Hhdext; eauto.
    destruct Hhdext as [tsuf1 Hts1].
    assert (Hin2':
      In (rebase_ip_nth (Datatypes.length pis1) ip2)
        (map (rebase_ip_nth (Datatypes.length pis1)) ipl2)).
    {
      eapply in_map.
      exact Hip2.
    }
    eapply flattened_stmts_pos_ge_with_prefix_slice
      with (ip:=rebase_ip_nth (Datatypes.length pis1) ip2) in Htlext;
      eauto.
    destruct Htlext as [h [tsuf2 [Hts2 Hge]]].
    simpl in Hts2.
    rewrite Hts1, Hts2.
    eapply lex_compare_prefix_cons_head_lt.
    lia.
Qed.

Lemma permutation_filter:
    forall A (f: A -> bool) l1 l2,
    Permutation l1 l2 ->
    Permutation (filter f l1) (filter f l2).
Proof.
    intros A f l1 l2 Hperm.
    induction Hperm; simpl.
    - constructor.
    - destruct (f x); simpl.
      + apply perm_skip. exact IHHperm.
      + exact IHHperm.
    - destruct (f x), (f y); simpl.
      + apply perm_swap.
      + apply Permutation_refl.
      + apply Permutation_refl.
      + apply Permutation_refl.
    - eapply Permutation_trans; eauto.
Qed.

Lemma extract_stmts_cons_sorted_split_by_nth_prefix_slice:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl sorted_ipl,
    Datatypes.length prefix = iter_depth ->
    extract_stmts (PolIRs.Loop.SCons stmt stmts') constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    exists pis1 pis2,
      extract_stmt stmt constrs env_dim iter_depth
        (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 /\
      extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 /\
      pis = pis1 ++ pis2 /\
      flatten_instrs_prefix_slice envv prefix pis1
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl) /\
      flatten_instrs_prefix_slice envv prefix pis2
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl)) /\
      Permutation
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl) /\
      Permutation
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl) /\
      sorted_ipl =
        filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl ++
        filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
      pis envv ipl sorted_ipl Hprefixlen Hext Hslice Hlen Hperm Hsorted.
    eapply extract_stmts_cons_success_inv in Hext.
    destruct Hext as (pis1 & pis2 & Hhdext & Htlext & Hpis).
    subst pis.
    assert (Hhdslice:
      flatten_instrs_prefix_slice envv prefix pis1
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)).
    {
      eapply flatten_instrs_prefix_slice_filter_left.
      exact Hslice.
    }
    assert (Htlslice:
      flatten_instrs_prefix_slice envv prefix pis2
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl))).
    {
      eapply flatten_instrs_prefix_slice_filter_right_rebase.
      exact Hslice.
    }
    assert (HpermL:
      Permutation
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    assert (HpermR:
      Permutation
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)
        (filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    assert (Hsplit_sorted:
      sorted_ipl =
        filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl ++
        filter
          (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl).
    {
      eapply sorted_sched_filter_split_if_cross_lt; eauto.
      intros x y Hinx Hiny Hfx Hfy.
      assert (HxinF:
        In x
          (filter
            (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
            sorted_ipl)).
	      {
	        apply filter_In.
	        split.
	        - exact Hinx.
	        - exact Hfx.
	      }
      assert (HyinF:
        In y
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl)).
	      {
	        apply filter_In.
	        split.
	        - exact Hiny.
	        - rewrite Hfy.
	          reflexivity.
	      }
      assert (Hxin1:
        In x
          (filter
            (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
            ipl)).
      {
        eapply Permutation_in.
        2: { exact HxinF. }
        exact (Permutation_sym HpermL).
      }
      assert (Hyin2:
        In y
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl)).
      {
        eapply Permutation_in.
        2: { exact HyinF. }
        exact (Permutation_sym HpermR).
      }
      eapply seq_cons_cross_lt_by_nth_with_prefix_slice
        with (stmt:=stmt) (stmts':=stmts') (constrs:=constrs)
             (env_dim:=env_dim) (iter_depth:=iter_depth)
             (sched_prefix:=sched_prefix) (prefix:=prefix) (pos:=pos)
             (pis1:=pis1) (pis2:=pis2)
             (envv:=envv)
             (ipl1:=filter
                (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
                ipl)
             (ipl2:=filter
                (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
                ipl).
      - exact Hprefixlen.
      - exact Hhdext.
      - exact Htlext.
      - exact Hhdslice.
      - exact Htlslice.
      - exact Hlen.
      - exact Hxin1.
      - exact Hyin2.
    }
    exists pis1.
    exists pis2.
    split.
    - exact Hhdext.
    - split.
      + exact Htlext.
      + split.
        * reflexivity.
        * split.
          { exact Hhdslice. }
          split.
          { exact Htlslice. }
          split.
          { exact HpermL. }
          split.
          { exact HpermR. }
          { exact Hsplit_sorted. }
Qed.

Lemma extract_stmts_cons_semantics_split_by_nth_prefix_slice:
    forall stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
           pis envv ipl sorted_ipl st1 st2,
    Datatypes.length prefix = iter_depth ->
    extract_stmts (PolIRs.Loop.SCons stmt stmts') constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Datatypes.length envv = env_dim ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    exists pis1 pis2 stmid,
      extract_stmt stmt constrs env_dim iter_depth
        (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)]) = Okk pis1 /\
      extract_stmts stmts' constrs env_dim iter_depth sched_prefix (S pos) = Okk pis2 /\
      pis = pis1 ++ pis2 /\
      flatten_instrs_prefix_slice envv prefix pis1
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl) /\
      flatten_instrs_prefix_slice envv prefix pis2
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl)) /\
      PolyLang.instr_point_list_semantics
        (filter
          (fun ip => Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)
        st1 stmid /\
      PolyLang.instr_point_list_semantics
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip => negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))
        stmid st2.
Proof.
    intros stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hext Hslice Hlen Hperm Hsorted Hipls.
    pose proof (
      extract_stmts_cons_sorted_split_by_nth_prefix_slice
        stmt stmts' constrs env_dim iter_depth sched_prefix prefix pos
        pis envv ipl sorted_ipl
        Hprefixlen Hext Hslice Hlen Hperm Hsorted
    ) as Hsplit.
    destruct Hsplit as
      (pis1 & pis2 & Hhdext & Htlext & Hpis &
       Hflat1 & Hflat2 & Hperm1 & Hperm2 & Hsplit_sorted).
    pose proof (
      instr_point_list_semantics_split_by_eq_app_rebase_right
        (Datatypes.length pis1)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)
        sorted_ipl st1 st2 Hsplit_sorted Hipls
    ) as Hsemsplit.
    destruct Hsemsplit as [stmid [Hsem1 Hsem2]].
    exists pis1.
    exists pis2.
    exists stmid.
    split.
    - exact Hhdext.
    - split.
      + exact Htlext.
      + split.
        * exact Hpis.
        * split.
          { exact Hflat1. }
          split.
          { exact Hflat2. }
          split.
          { exact Hsem1. }
          { exact Hsem2. }
Qed.

Lemma nodup_all_eq_singleton:
    forall A (x: A) l,
    NoDup l ->
    (forall y, In y l -> y = x) ->
    In x l ->
    l = [x].
Proof.
    intros A x l Hnd Hall Hin.
    destruct l as [|a l']; [contradiction|].
    assert (a = x) as Ha.
    { eapply Hall. simpl. left. reflexivity. }
    subst a.
    destruct l' as [|b l''].
    - reflexivity.
    - exfalso.
      assert (b = x) as Hb.
      { eapply Hall. simpl. right. left. reflexivity. }
      subst b.
      inversion Hnd; subst.
      eapply H1.
      simpl. left. reflexivity.
Qed.

Lemma instance_list_semantics_inv:
    forall pprog st1 st2,
    PolyLang.instance_list_semantics pprog st1 st2 ->
    exists pis varctxt vars envv,
      pprog = (pis, varctxt, vars) /\
      Instr.Compat vars st1 /\
      Instr.NonAlias st1 /\
      Instr.InitEnv varctxt envv st1 /\
      PolyLang.poly_instance_list_semantics envv pprog st1 st2.
Proof.
    intros pprog st1 st2 Hsem.
    destruct Hsem as [pprog' pis varctxt vars envv st1' st2' Hpprog Hcompat Hnonalias Hinit Hpoly].
    subst.
    exists pis.
    exists varctxt.
    exists vars.
    exists envv.
    repeat split; auto.
Qed.

Lemma poly_instance_list_semantics_inv:
    forall envv pprog st1 st2,
    PolyLang.poly_instance_list_semantics envv pprog st1 st2 ->
    exists pis varctxt vars ipl sorted_ipl,
      pprog = (pis, varctxt, vars) /\
      PolyLang.flatten_instrs envv pis ipl /\
      Permutation ipl sorted_ipl /\
      Sorted PolyLang.instr_point_sched_le sorted_ipl /\
      PolyLang.instr_point_list_semantics sorted_ipl st1 st2.
Proof.
    intros envv pprog st1 st2 Hsem.
    inversion Hsem; subst; clear Hsem.
    exists pis.
    exists varctxt.
    exists vars.
    exists ipl.
    exists sorted_ipl.
    split.
    - reflexivity.
    - split.
      + exact H0.
      + split.
        * exact H1.
        * split.
          { exact H2. }
          { exact H3. }
Qed.

Lemma loop_semantics_intro_from_envv:
    forall stmt varctxt vars envv st1 st2,
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    Loop.loop_semantics stmt (rev envv) st1 st2 ->
    Loop.semantics (stmt, varctxt, vars) st1 st2.
Proof.
    intros stmt varctxt vars envv st1 st2 Hcompat Hnonalias Hinit Hloop.
    eapply Loop.LSemaIntro
      with (loop:=stmt) (ctxt:=varctxt) (vars:=vars) (env:=rev envv).
    - reflexivity.
    - exact Hcompat.
    - exact Hnonalias.
    - replace (rev (rev envv)) with envv.
      + exact Hinit.
      + symmetry; eapply rev_involutive.
    - exact Hloop.
Qed.

Lemma iter_semantics_app:
    forall A (P: A -> State.t -> State.t -> Prop)
           xs ys st1 st2 st3,
    Instr.IterSem.iter_semantics P xs st1 st2 ->
    Instr.IterSem.iter_semantics P ys st2 st3 ->
    Instr.IterSem.iter_semantics P (xs ++ ys) st1 st3.
Proof.
    intros A P xs ys st1 st2 st3 Hxs Hys.
    induction Hxs.
    - simpl.
      exact Hys.
    - simpl.
      econstructor.
      + exact H.
      + eapply IHHxs.
        exact Hys.
Qed.

Lemma seq_cons_semantics_with_eq:
    forall st sts env st1 st2 st3 st3',
    Loop.loop_semantics st env st1 st2 ->
    Loop.loop_semantics (PolIRs.Loop.Seq sts) env st2 st3 ->
    State.eq st3' st3 ->
    exists stmid,
      Loop.loop_semantics (PolIRs.Loop.Seq (PolIRs.Loop.SCons st sts)) env st1 stmid /\
      State.eq st3' stmid.
Proof.
    intros st sts env st1 st2 st3 st3' Hhd Htl Heq.
    exists st3.
    split.
    - eapply Loop.LSeq; eauto.
    - exact Heq.
Qed.

Lemma flatten_instr_prefix_slice_singleton_if_in_poly:
    forall envv prefix pi ipl,
    Datatypes.length prefix = PolyLang.pi_depth pi ->
    in_poly (envv ++ prefix) (PolyLang.pi_poly pi) = true ->
    flatten_instrs_prefix_slice envv prefix [pi] ipl ->
    exists ip0,
      ipl = [ip0] /\
      PolyLang.ip_nth ip0 = 0%nat /\
      PolyLang.ip_index ip0 = envv ++ prefix /\
      PolyLang.ip_transformation ip0 = PolyLang.current_transformation_of pi (envv ++ prefix) /\
      PolyLang.ip_time_stamp ip0 = affine_product (PolyLang.pi_schedule pi) (envv ++ prefix) /\
      PolyLang.ip_instruction ip0 = PolyLang.pi_instr pi /\
      PolyLang.ip_depth ip0 = PolyLang.pi_depth pi.
Proof.
    intros envv prefix pi ipl Hprefixlen Hpolyin Hslice.
    destruct Hslice as [Hchar [Hnodup _]].
    set (ip0 := {|
      PolyLang.ip_nth := 0%nat;
      PolyLang.ip_index := envv ++ prefix;
      PolyLang.ip_transformation :=
        PolyLang.current_transformation_of pi (envv ++ prefix);
      PolyLang.ip_time_stamp := affine_product (PolyLang.pi_schedule pi) (envv ++ prefix);
      PolyLang.ip_instruction := PolyLang.pi_instr pi;
      PolyLang.ip_depth := PolyLang.pi_depth pi;
    |}).
    assert (Hin0: In ip0 ipl).
    {
      eapply (proj2 (Hchar ip0)).
      exists pi.
      exists ([]: list Z).
      split; [reflexivity|].
      split.
      - unfold PolyLang.belongs_to.
        simpl.
        rewrite Hpolyin.
        repeat split; reflexivity.
      - split; [lia|].
        split.
        + rewrite app_nil_r.
          reflexivity.
        + rewrite Hprefixlen.
          simpl.
          lia.
    }
    assert (Hall: forall ip, In ip ipl -> ip = ip0).
    {
      intros ip Hin.
      pose proof (proj1 (Hchar ip) Hin) as Hm.
      destruct Hm as (pi' & suf & Hnth & Hbel & _ & Hidx & Hsuflen).
      assert (Hnth_some: nth_error [pi] (PolyLang.ip_nth ip) <> None).
      { rewrite Hnth. discriminate. }
      eapply nth_error_Some in Hnth_some.
      simpl in Hnth_some.
      assert (Hnth0: PolyLang.ip_nth ip = 0%nat) by lia.
      rewrite Hnth0 in Hnth.
      simpl in Hnth.
      inversion Hnth; subst pi'; clear Hnth.
      rewrite Hprefixlen in Hsuflen.
      destruct suf as [|z suf'] eqn:Hsuf; simpl in Hsuflen; try lia.
      rewrite app_nil_r in Hidx.
      unfold PolyLang.belongs_to in Hbel.
      destruct Hbel as (_ & Htf & Hts & Hinstr & Hdepth).
      destruct ip as [n' idx tf ts instr depth].
      simpl in *.
      subst.
      reflexivity.
    }
    exists ip0.
    split.
    - eapply nodup_all_eq_singleton; eauto.
    - repeat split; reflexivity.
Qed.

Local Lemma instr_branch_core_prefix:
    forall i es constrs sched_prefix env_dim iter_depth prefix envv
           ipl sorted_ipl st1 st2 tf w r,
    Datatypes.length prefix = iter_depth ->
    exprlist_to_aff es (env_dim + iter_depth)%nat = Okk tf ->
    resolve_access_functions i = Some (w, r) ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix
      [{|
        PolyLang.pi_depth := iter_depth;
        PolyLang.pi_instr := i;
        PolyLang.pi_poly := normalize_affine_list_rev (env_dim + iter_depth)%nat constrs;
        PolyLang.pi_schedule := normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix;
        PolyLang.pi_point_witness := PSWIdentity iter_depth;
        PolyLang.pi_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_access_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_waccess := normalize_access_list (env_dim + iter_depth)%nat w;
        PolyLang.pi_raccess := normalize_access_list (env_dim + iter_depth)%nat r;
      |}] ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics (Loop.Instr i es) (rev (envv ++ prefix)) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros i es constrs sched_prefix env_dim iter_depth prefix envv
      ipl sorted_ipl st1 st2 tf w r
      Hprefixlen Htf Hacc Hconstr Hflat Hperm _ Hipls Hlenenv.
    assert (Hlenenvprefix:
      Datatypes.length (envv ++ prefix) = (env_dim + iter_depth)%nat).
    {
      rewrite app_length, Hlenenv, Hprefixlen.
      lia.
    }
    assert (Hdom:
      in_poly (envv ++ prefix)
        (normalize_affine_list_rev (env_dim + iter_depth)%nat constrs) = true).
    {
      unfold in_poly in *.
      rewrite normalize_affine_list_rev_satisfies_constraint
        with (cols := (env_dim + iter_depth)%nat)
             (env := envv ++ prefix)
             (affs := constrs).
      - exact Hconstr.
      - exact Hlenenvprefix.
    }
    assert (Haff:
      affine_product
        (normalize_affine_list_rev (env_dim + iter_depth)%nat tf)
        (envv ++ prefix) =
      map (Loop.eval_expr (rev (envv ++ prefix))) es).
    {
      eapply exprlist_to_aff_rev_normalized_correct; eauto.
    }
    eapply flatten_instr_prefix_slice_singleton_if_in_poly in Hflat.
    2: { simpl. exact Hprefixlen. }
    2: { exact Hdom. }
    destruct Hflat as (ip0 & Hipl & _ & Hidx & Htr & _ & Hinstr & _).
    subst ipl.
    eapply permutation_singleton in Hperm.
    subst sorted_ipl.
    eapply instr_point_list_semantics_singleton_inv in Hipls.
    destruct Hipls as (stmid & Hipsema & Heq).
    inversion Hipsema as [wcs rcs Hipinstr]; clear Hipsema.
    assert (Hargs:
      affine_product (PolyLang.ip_transformation ip0) (PolyLang.ip_index ip0) =
      map (Loop.eval_expr (rev (envv ++ prefix))) es).
    {
      rewrite Htr, Hidx.
      exact Haff.
    }
    rewrite Hargs, Hinstr in Hipinstr.
    exists stmid.
    split.
    - eapply Loop.LInstr.
      exact Hipinstr.
    - eapply State.eq_sym.
      exact Heq.
Qed.

Lemma flatten_instrs_prefix_slice_nil_implies_nil:
    forall envv prefix ipl,
    flatten_instrs_prefix_slice envv prefix [] ipl ->
    ipl = [].
Proof.
    intros envv prefix ipl Hslice.
    destruct Hslice as [Hchar [_ _]].
    destruct ipl as [|ip ipl'].
    - reflexivity.
    - exfalso.
      pose proof (proj1 (Hchar ip) (or_introl eq_refl)) as Hm.
      destruct Hm as (pi & suf & Hnth & _).
      destruct (PolyLang.ip_nth ip); simpl in Hnth; discriminate.
Qed.

Lemma instr_branch_core_with_constrs_prefix_len:
    forall i es constrs sched_prefix env_dim iter_depth prefix envv
           ipl sorted_ipl st1 st2 tf w r,
    Datatypes.length prefix = iter_depth ->
    exprlist_to_aff es (env_dim + iter_depth)%nat = Okk tf ->
    resolve_access_functions i = Some (w, r) ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix
      [{|
        PolyLang.pi_depth := iter_depth;
        PolyLang.pi_instr := i;
        PolyLang.pi_poly := normalize_affine_list_rev (env_dim + iter_depth)%nat constrs;
        PolyLang.pi_schedule := normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix;
        PolyLang.pi_point_witness := PSWIdentity iter_depth;
        PolyLang.pi_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_access_transformation := normalize_affine_list_rev (env_dim + iter_depth)%nat tf;
        PolyLang.pi_waccess := normalize_access_list (env_dim + iter_depth)%nat w;
        PolyLang.pi_raccess := normalize_access_list (env_dim + iter_depth)%nat r;
      |}] ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics (Loop.Instr i es) (rev (envv ++ prefix)) st1 st2' /\ State.eq st2 st2'.
Proof.
    exact instr_branch_core_prefix.
Qed.

Lemma iter_semantics_shift_start_with_state_eq:
    forall A (P: A -> State.t -> State.t -> Prop),
    (forall x st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      P x st1 st2 ->
      P x st1' st2') ->
    forall xs st1 st2 st1',
      Instr.IterSem.iter_semantics P xs st1 st2 ->
      State.eq st1 st1' ->
      exists st2',
        Instr.IterSem.iter_semantics P xs st1' st2' /\
        State.eq st2 st2'.
Proof.
    intros A P Hstable xs st1 st2 st1' Hiter.
    revert st1'.
    induction Hiter; intros st1' Heqstart.
    - exists st1'.
      split.
      + constructor.
      + exact Heqstart.
    - assert (HP':
          P x st1' st2).
      {
        eapply Hstable with (st1 := st1) (st2 := st2).
        - exact Heqstart.
        - eapply State.eq_refl.
        - exact H.
      }
      destruct (IHHiter st2 (State.eq_refl st2)) as [st3' [Htail' Heq3]].
      exists st3'.
      split.
      + econstructor; eauto.
      + exact Heq3.
Qed.

Lemma iter_semantics_refine_with_state_eq:
    forall A (P Q: A -> State.t -> State.t -> Prop),
    (forall x st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      P x st1 st2 ->
      P x st1' st2') ->
    forall xs st1 st2,
      Instr.IterSem.iter_semantics P xs st1 st2 ->
      (forall x stA stB, In x xs -> P x stA stB ->
        exists stB', Q x stA stB' /\ State.eq stB stB') ->
      exists st2',
        Instr.IterSem.iter_semantics Q xs st1 st2' /\
        State.eq st2 st2'.
Proof.
    intros A P Q Hstable xs.
    induction xs as [|x xs IH]; intros st1 st2 Hiter Hbridge.
    - inversion Hiter; subst; clear Hiter.
      eexists.
      split.
      + constructor.
      + eapply State.eq_refl.
    - inversion Hiter as [|x' xs' st1a st2a st3a HP Htail]; subst; clear Hiter.
      destruct (Hbridge x st1 st2a (or_introl eq_refl) HP)
        as [st2' [HQx Heq2']].
      destruct (
        iter_semantics_shift_start_with_state_eq
          A P Hstable xs st2a st2 st2' Htail Heq2'
      ) as [st3' [HtailP' Heq3']].
      destruct (IH st2' st3' HtailP')
        as [st3'' [HtailQ Heq3'']].
      {
        intros y stA stB Hyin HyP.
        eapply Hbridge.
        - right. exact Hyin.
        - exact HyP.
      }
      exists st3''.
      split.
      + econstructor; eauto.
      + eapply State.eq_trans.
        * exact Heq3'.
        * exact Heq3''.
Qed.

Scheme loop_stmt_mutind_prefix := Induction for PolIRs.Loop.stmt Sort Prop
with loop_stmts_mutind_prefix := Induction for PolIRs.Loop.stmt_list Sort Prop.
Combined Scheme loop_stmt_stmts_mutind_prefix
  from loop_stmt_mutind_prefix, loop_stmts_mutind_prefix.

Definition stmt_constrs_prefix_goal (stmt: PolIRs.Loop.stmt): Prop :=
  forall constrs sched_prefix env_dim iter_depth prefix
         pis envv ipl sorted_ipl st1 st2,
    Datatypes.length prefix = iter_depth ->
    wf_scop_stmt stmt = true ->
    extract_stmt stmt constrs env_dim iter_depth sched_prefix = Okk pis ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics stmt (rev (envv ++ prefix)) st1 st2' /\ State.eq st2 st2'.

Definition stmts_constrs_prefix_goal (stmts: PolIRs.Loop.stmt_list): Prop :=
  forall constrs sched_prefix env_dim iter_depth prefix pos
         pis envv ipl sorted_ipl st1 st2,
    Datatypes.length prefix = iter_depth ->
    wf_scop_stmts stmts = true ->
    extract_stmts stmts constrs env_dim iter_depth sched_prefix pos = Okk pis ->
    in_poly (rev (envv ++ prefix)) constrs = true ->
    flatten_instrs_prefix_slice envv prefix pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = env_dim ->
    exists st2',
      Loop.loop_semantics (PolIRs.Loop.Seq stmts) (rev (envv ++ prefix)) st1 st2' /\
      State.eq st2 st2'.

Lemma core_sched_stmt_stmts_constrs_prefix_mutual:
  (forall stmt, stmt_constrs_prefix_goal stmt) /\
  (forall stmts, stmts_constrs_prefix_goal stmts).
Proof.
  apply
    (loop_stmt_stmts_mutind_prefix
       stmt_constrs_prefix_goal stmts_constrs_prefix_goal).
  - (* Loop *)
    intros lb ub body IHbody constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    pose proof Hextract as Hextract_loop.
    eapply extract_stmt_loop_success_inv in Hextract.
    destruct Hextract as (lbc & ubc & Hlb & Hub & Hbodyext).
    eapply wf_scop_loop_inv in Hwf.
    destruct Hwf as (_ & _ & Hwf_body).
    assert (Hpoint_ts_head:
      forall ip, In ip sorted_ipl ->
      exists i tsuf,
        PolyLang.ip_time_stamp ip =
          affine_product
            (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
            (envv ++ prefix) ++ [i] ++ tsuf).
    {
      intros ip Hin.
      eapply Permutation_in in Hin.
      2: { exact (Permutation_sym Hperm). }
      destruct (
        flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
          lb ub body constrs env_dim iter_depth sched_prefix prefix
          pis envv ipl ip Hprefixlen Hextract_loop Hflat Hlenenv Hin
      ) as [i [suf [tsuf [_ [_ Hts]]]]].
      exists i.
      exists tsuf.
      exact Hts.
    }
    set (pfx :=
      affine_product
        (normalize_affine_list_rev (env_dim + iter_depth)%nat sched_prefix)
        (envv ++ prefix)).
    set (head_ts := fun ip : PolyLang.InstrPoint =>
      nth (Datatypes.length pfx) (PolyLang.ip_time_stamp ip) 0%Z).
    set (lbv := Loop.eval_expr (rev (envv ++ prefix)) lb).
    set (ubv := Loop.eval_expr (rev (envv ++ prefix)) ub).
    assert (Hpoint_head_in_bounds:
      forall ip, In ip sorted_ipl ->
      (lbv <= head_ts ip < ubv)%Z).
    {
      intros ip Hin.
      eapply Permutation_in in Hin.
      2: { exact (Permutation_sym Hperm). }
      destruct (
        flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice
          lb ub body constrs env_dim iter_depth sched_prefix prefix
          pis envv ipl ip Hprefixlen Hextract_loop Hflat Hlenenv Hin
      ) as [i [suf [tsuf [_ [Hbounds Hts]]]]].
      unfold head_ts.
      rewrite Hts.
      unfold pfx.
      rewrite nth_after_prefix_singleton.
      exact Hbounds.
    }
    assert (Hlt_lb_nil:
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) lbv) sorted_ipl = []).
    {
      eapply filter_all_false_nil.
      intros ip Hin.
      pose proof (Hpoint_head_in_bounds ip Hin) as Hbounds.
      eapply Z.ltb_ge.
      lia.
    }
    assert (Hlt_ub_eq_sorted:
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) ubv) sorted_ipl = sorted_ipl).
    {
      assert (Halltrue:
        forall ip, In ip sorted_ipl ->
          Z.ltb (head_ts ip) ubv = true).
      {
        intros ip Hin.
        pose proof (Hpoint_head_in_bounds ip Hin) as Hbounds.
        eapply Z.ltb_lt.
        lia.
      }
      eapply filter_all_true_id.
      exact Halltrue.
    }
    assert (Hlt_succ_split:
      forall i,
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (i + 1)) sorted_ipl =
      filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl ++
      filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) i) sorted_ipl).
    {
      intros i.
      unfold head_ts.
      eapply sorted_sched_filter_ltb_succ_by_prefix_head.
      - exact Hsorted.
      - intros ip Hin.
        destruct (Hpoint_ts_head ip Hin) as [j [tsuf Hts]].
        exists j.
        exists tsuf.
        rewrite Hts.
        unfold pfx.
        reflexivity.
    }
    assert (Hsem_prefix_step:
      forall i st_next,
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (i + 1)) sorted_ipl)
        st1 st_next ->
      exists st_prev,
        PolyLang.instr_point_list_semantics
          (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl)
          st1 st_prev /\
        PolyLang.instr_point_list_semantics
          (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) i) sorted_ipl)
          st_prev st_next).
    {
      intros i st_next Hsem_next.
      pose proof (Hlt_succ_split i) as Hsplit_succ.
      eapply instr_point_list_semantics_split_by_eq_app
        with
          (l1 := filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl)
          (l2 := filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) i) sorted_ipl)
          (l := filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (i + 1)) sorted_ipl)
          (st1 := st1) (st2 := st_next)
        in Hsem_next.
      2: { exact Hsplit_succ. }
      exact Hsem_next.
    }
    assert (Hpref_lb_eq_st1:
      forall st_lb,
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) lbv) sorted_ipl)
        st1 st_lb ->
      State.eq st1 st_lb).
    {
      intros st_lb Hsem_lb.
      rewrite Hlt_lb_nil in Hsem_lb.
      eapply instr_point_list_semantics_nil_inv in Hsem_lb.
      exact Hsem_lb.
    }

    assert (Hsem_pref_ub:
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) ubv) sorted_ipl)
        st1 st2).
    {
      rewrite Hlt_ub_eq_sorted.
      exact Hipls.
    }
    assert (Hiter_prefix_eq:
      forall i st_i,
      (lbv <= i <= ubv)%Z ->
      PolyLang.instr_point_list_semantics
        (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) i) sorted_ipl)
        st1 st_i ->
      exists st_i',
        Instr.IterSem.iter_semantics
          (fun x stA stB =>
            PolyLang.instr_point_list_semantics
              (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
              stA stB)
          (Zrange lbv i) st1 st_i' /\
        State.eq st_i st_i').
    {
      intros i st_i Hrange Hpref_i.
      remember (Z.to_nat (i - lbv)) as n eqn:Hn.
      assert (Hi: i = lbv + Z.of_nat n).
      {
        subst n.
        rewrite Z2Nat.id; lia.
      }
      clear Hn.
      revert i st_i Hrange Hpref_i Hi.
      induction n as [|n IH]; intros i st_i Hrange Hpref_i Hi.
      - rewrite Hi in Hpref_i.
        replace (lbv + Z.of_nat 0)%Z with lbv in Hpref_i by lia.
        exists st1.
        split.
        + rewrite Zrange_empty by lia.
          constructor.
        + pose proof (Hpref_lb_eq_st1 st_i Hpref_i) as Heq.
          eapply State.eq_sym.
          exact Heq.
      - assert (Hlt_i: (lbv < i)%Z) by lia.
        set (iprev := (i - 1)%Z).
        assert (Hiprev_range: (lbv <= iprev <= ubv)%Z) by (unfold iprev; lia).
        assert (Hpref_prev_input:
          PolyLang.instr_point_list_semantics
            (filter (fun ip : PolyLang.InstrPoint => Z.ltb (head_ts ip) (iprev + 1)) sorted_ipl)
            st1 st_i).
        {
          unfold iprev.
          replace (i - 1 + 1)%Z with i by lia.
          exact Hpref_i.
        }
        destruct (Hsem_prefix_step iprev st_i Hpref_prev_input)
          as [st_prev [Hpref_prev Heq_prev]].
        assert (Hiprev_eq: iprev = lbv + Z.of_nat n).
        { unfold iprev. lia. }
        specialize (IH iprev st_prev Hiprev_range Hpref_prev Hiprev_eq).
        destruct IH as [st_prev' [Hiter_prev Heq_prev_state]].
        assert (Heq_prev_from_prev':
          PolyLang.instr_point_list_semantics
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) iprev) sorted_ipl)
            st_prev' st_i).
        {
          eapply PolyLang.instr_point_list_sema_stable_under_state_eq
            with (st1:=st_prev) (st2:=st_i) (st1':=st_prev') (st2':=st_i) in Heq_prev.
          2: { exact Heq_prev_state. }
          2: { eapply State.eq_refl. }
          exact Heq_prev.
        }
        assert (Hiter_single:
          Instr.IterSem.iter_semantics
            (fun x stA stB =>
              PolyLang.instr_point_list_semantics
                (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
                stA stB)
            [iprev] st_prev' st_i).
        {
          econstructor.
          - exact Heq_prev_from_prev'.
          - constructor.
        }
        exists st_i.
        split.
        + assert (Hiter_cat:
            Instr.IterSem.iter_semantics
              (fun x stA stB =>
                PolyLang.instr_point_list_semantics
                  (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
                  stA stB)
              (Zrange lbv iprev ++ [iprev]) st1 st_i).
          {
            eapply iter_semantics_app; eauto.
          }
          unfold iprev in Hiter_cat.
          replace (Zrange lbv i) with (Zrange lbv (i - 1) ++ [(i - 1)%Z]) by
            (symmetry; eapply Zrange_end; exact Hlt_i).
          exact Hiter_cat.
        + eapply State.eq_refl.
    }
    assert (Hiter_eq_range_from_st1:
      (lbv <= ubv)%Z ->
      exists st2',
        Instr.IterSem.iter_semantics
          (fun x stA stB =>
            PolyLang.instr_point_list_semantics
              (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
              stA stB)
          (Zrange lbv ubv) st1 st2' /\
        State.eq st2 st2').
    {
      intros Hle.
      eapply Hiter_prefix_eq.
      - split; lia.
      - exact Hsem_pref_ub.
    }
    destruct (Z_lt_ge_dec lbv ubv) as [Hlb_lt_ub | Hlb_ge_ub].
    2: {
      assert (sorted_ipl = []) as Hsorted_nil.
      {
        destruct sorted_ipl as [|ip tl].
        + reflexivity.
        + exfalso.
          pose proof (Hpoint_head_in_bounds ip (or_introl eq_refl)) as Hb.
          lia.
      }
      subst sorted_ipl.
      assert (State.eq st1 st2) as Heq12.
      { eapply instr_point_list_semantics_nil_inv; eauto. }
      exists st1.
      split.
      + eapply Loop.LLoop.
        rewrite Zrange_empty by lia.
        constructor.
      + eapply State.eq_sym.
        exact Heq12.
    }
    assert (Hiter_loop_refined:
      forall stA stB,
      Instr.IterSem.iter_semantics
        (fun x stX stY =>
          PolyLang.instr_point_list_semantics
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
            stX stY)
        (Zrange lbv ubv) stA stB ->
      exists stB',
        Instr.IterSem.iter_semantics
          (fun x stX stY =>
            Loop.loop_semantics body (x :: rev (envv ++ prefix)) stX stY)
          (Zrange lbv ubv) stA stB' /\
        State.eq stB stB').
    {
      intros stA stB Hiter.
      eapply iter_semantics_refine_with_state_eq
        with
          (P := fun x stX stY =>
                  PolyLang.instr_point_list_semantics
                    (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
                    stX stY)
          (Q := fun x stX stY =>
                  Loop.loop_semantics body (x :: rev (envv ++ prefix)) stX stY)
          (xs := Zrange lbv ubv) (st1 := stA) (st2 := stB).
      - intros x stX stY stX' stY' HeqX HeqY Hslice0.
        eapply PolyLang.instr_point_list_sema_stable_under_state_eq; eauto.
      - exact Hiter.
      - intros x stX stY Hin Hslice0.
        eapply Zrange_in in Hin.
        assert (Hprefixlen':
          Datatypes.length (prefix ++ [x]) = S iter_depth).
        {
          rewrite app_length.
          simpl.
          rewrite Hprefixlen.
          lia.
        }
        assert (Hconstr_body:
          in_poly (rev (envv ++ (prefix ++ [x])))
            (lift_affine_list constrs ++ [lbc; ubc]) = true).
        {
          replace (rev (envv ++ (prefix ++ [x]))) with (x :: rev (envv ++ prefix)).
          2: {
            symmetry.
            rewrite app_assoc.
            apply rev_unit.
          }
          eapply loop_constraints_sound_lifted
            with (lb:=lb) (ub:=ub) (depth:=(env_dim + iter_depth)%nat).
          - rewrite rev_length.
            rewrite app_length, Hlenenv, Hprefixlen.
            lia.
          - exact Hlb.
          - exact Hub.
          - exact Hconstr.
          - exact Hin.
        }
        assert (Hslice_flat:
          flatten_instrs_prefix_slice envv (prefix ++ [x]) pis
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) ipl)).
        {
          eapply loop_slice_filter_prefix_slice_gen
            with (lb:=lb) (ub:=ub) (body:=body) (constrs:=constrs)
                 (sched_prefix:=sched_prefix) (env_dim:=env_dim)
                 (iter_depth:=iter_depth) (prefix:=prefix) (pis:=pis); eauto.
        }
        assert (Hperm_slice:
          Permutation
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) ipl)
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)).
        {
          eapply permutation_filter.
          exact Hperm.
        }
        assert (Hsorted_slice:
          Sorted PolyLang.instr_point_sched_le
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)).
        {
          eapply sorted_sched_filter.
          exact Hsorted.
        }
        destruct (
          IHbody
            (lift_affine_list constrs ++ [lbc; ubc])
            (lift_affine_list sched_prefix ++
             [((1%Z :: repeat 0%Z (env_dim + iter_depth)%nat)%list, 0%Z)])
            env_dim (S iter_depth) (prefix ++ [x])
            pis envv
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) ipl)
            (filter (fun ip : PolyLang.InstrPoint => Z.eqb (head_ts ip) x) sorted_ipl)
            stX stY
            Hprefixlen'
            Hwf_body
            Hbodyext
            Hconstr_body
            Hslice_flat
            Hperm_slice
            Hsorted_slice
            Hslice0
            Hlenenv
        ) as [stY' [Hbody_loop HeqY']].
        replace (rev (envv ++ (prefix ++ [x]))) with (x :: rev (envv ++ prefix)) in Hbody_loop.
        2: {
          symmetry.
          rewrite app_assoc.
          apply rev_unit.
        }
        exists stY'.
        split.
        + exact Hbody_loop.
        + exact HeqY'.
    }
    destruct (Hiter_eq_range_from_st1 (ltac:(lia))) as [st2_mid [Hiter_range Heq2_mid]].
    destruct (Hiter_loop_refined st1 st2_mid Hiter_range)
      as [st2' [Hiter_loop Heq2']].
    exists st2'.
    split.
    + eapply Loop.LLoop.
      exact Hiter_loop.
    + eapply State.eq_trans.
      * exact Heq2_mid.
      * exact Heq2'.
  - (* Instr *)
    intros i es constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply extract_stmt_instr_success_inv in Hextract.
    destruct Hextract as (tf & w & r & Htf & Hacc & Hpis).
    subst pis.
    eapply instr_branch_core_with_constrs_prefix_len
      with (tf:=tf) (w:=w) (r:=r); eauto.
  - (* Seq *)
    intros stmts IHstmts constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply wf_scop_seq_inv in Hwf.
    eapply extract_stmt_seq_success_inv in Hextract.
    exact (
      IHstmts constrs sched_prefix env_dim iter_depth prefix 0%nat
              pis envv ipl sorted_ipl st1 st2
              Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv
    ).
  - (* Guard *)
    intros test body IHbody constrs sched_prefix env_dim iter_depth prefix
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply extract_stmt_guard_success_inv in Hextract.
    destruct Hextract as (test_constrs & Htest & Hbodyext).
    eapply wf_scop_guard_inv in Hwf.
    destruct Hwf as [_ Hwf_body].
    destruct (Loop.eval_test (rev (envv ++ prefix)) test) eqn:Heval.
    + assert (Hconstr_body:
        in_poly (rev (envv ++ prefix))
          (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs) = true).
      {
        eapply guard_constraints_sound_in_poly
          with (test:=test) (cols:=(env_dim + iter_depth)%nat); eauto.
        rewrite rev_length.
        rewrite app_length, Hlenenv, Hprefixlen.
        lia.
      }
      pose proof (
        IHbody
          (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs)
          sched_prefix env_dim iter_depth prefix
          pis envv ipl sorted_ipl st1 st2
          Hprefixlen Hwf_body Hbodyext Hconstr_body Hflat Hperm Hsorted Hipls Hlenenv
      ) as Hbody_sem.
      destruct Hbody_sem as [st2' [Hloop_body Heq_body]].
      exists st2'.
      split.
      * eapply Loop.LGuardTrue.
        -- exact Hloop_body.
        -- exact Heval.
      * exact Heq_body.
    + assert (Hnil: ipl = []).
      {
        replace (rev prefix ++ rev envv) with (rev (envv ++ prefix)) in Heval.
        2: { rewrite rev_app_distr. reflexivity. }
        destruct ipl as [|ip ipl'].
        - reflexivity.
        - exfalso.
          assert (Hguardall:
            in_poly (rev (envv ++ prefix))
              (constrs ++ normalize_affine_list (env_dim + iter_depth)%nat test_constrs) = true).
          {
            eapply flattened_point_satisfies_top_constraints_slice
              with (stmt:=body)
                   (env_dim:=env_dim)
                   (iter_depth:=iter_depth)
                   (sched_prefix:=sched_prefix)
                   (prefix:=prefix)
                   (pis:=pis)
                   (envv:=envv)
                   (ipl:=ip :: ipl')
                   (ip:=ip); eauto.
            simpl. left. reflexivity.
          }
          eapply in_poly_guard_split in Hguardall.
          destruct Hguardall as [_ Hguardnorm].
          assert (Hguardin:
            in_poly (rev (envv ++ prefix))
              (normalize_affine_list (env_dim + iter_depth)%nat test_constrs) = true).
          {
            unfold in_poly.
            exact Hguardnorm.
          }
          assert (Hlenrevprefix:
            Datatypes.length (rev (envv ++ prefix)) = (env_dim + iter_depth)%nat).
          {
            rewrite rev_length.
            rewrite app_length, Hlenenv, Hprefixlen.
            lia.
          }
          pose proof
            (test_false_implies_not_in_poly_normalized
               test
               (rev (envv ++ prefix))
               (env_dim + iter_depth)%nat
               test_constrs
               Htest
               Hlenrevprefix
               Heval) as Hguardfalse.
          rewrite Hguardin in Hguardfalse.
          discriminate.
      }
      subst ipl.
      eapply Permutation_nil in Hperm.
      subst sorted_ipl.
      assert (State.eq st1 st2) as Heq12.
      { eapply instr_point_list_semantics_nil_inv; eauto. }
      exists st1.
      split.
      * eapply Loop.LGuardFalse.
        exact Heval.
      * eapply State.eq_sym.
        exact Heq12.
  - (* SNil *)
    intros constrs sched_prefix env_dim iter_depth prefix pos
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply extract_stmts_nil_success_inv in Hextract.
    subst pis.
    eapply flatten_instrs_prefix_slice_nil_implies_nil in Hflat.
    subst ipl.
    eapply Permutation_nil in Hperm.
    subst sorted_ipl.
    assert (State.eq st1 st2) as Heq12.
    { eapply instr_point_list_semantics_nil_inv; eauto. }
    exists st1.
    split.
    + constructor.
    + eapply State.eq_sym.
      exact Heq12.
  - (* SCons *)
    intros st IHstmt sts IHsts
      constrs sched_prefix env_dim iter_depth prefix pos
      pis envv ipl sorted_ipl st1 st2
      Hprefixlen Hwf Hextract Hconstr Hflat Hperm Hsorted Hipls Hlenenv.
    eapply wf_scop_stmts_cons_inv in Hwf.
    destruct Hwf as [Hwf_hd Hwf_tl].
    pose proof (
      extract_stmts_cons_semantics_split_by_nth_prefix_slice
        st sts constrs env_dim iter_depth sched_prefix prefix pos
        pis envv ipl sorted_ipl st1 st2
        Hprefixlen Hextract Hflat Hlenenv Hperm Hsorted Hipls
    ) as Hsplit.
    destruct Hsplit as
      (pis1 & pis2 & stmid &
       Hhdext & Htlext & _ &
       Hflat1 & Hflat2 & Hsem1 & Hsem2).
    assert (Hperm1:
      Permutation
        (filter
          (fun ip : PolyLang.InstrPoint =>
            Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          ipl)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    pose proof (
      IHstmt constrs
             (sched_prefix ++ [(repeat 0%Z (env_dim + iter_depth)%nat, Z.of_nat pos)])
             env_dim iter_depth prefix
             pis1 envv
             (filter
               (fun ip : PolyLang.InstrPoint =>
                 Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
               ipl)
             (filter
               (fun ip : PolyLang.InstrPoint =>
                 Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1))
               sorted_ipl)
             st1 stmid
             Hprefixlen Hwf_hd Hhdext Hconstr
             Hflat1
             Hperm1
             (sorted_sched_filter _ _ Hsorted)
             Hsem1 Hlenenv
    ) as Hhead.
    destruct Hhead as [sth [Hloop_hd Heq_mid_h]].
    assert (Hsem2_from_sth:
      PolyLang.instr_point_list_semantics
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))
        sth st2).
    {
      eapply PolyLang.instr_point_list_sema_stable_under_state_eq
        with (st1:=stmid) (st2:=st2) (st1':=sth) (st2':=st2) in Hsem2.
      2: { exact Heq_mid_h. }
      2: { eapply State.eq_refl. }
      exact Hsem2.
    }
    assert (Hsorted2_base:
      Sorted PolyLang.instr_point_sched_le
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)).
    { eapply sorted_sched_filter; eauto. }
    assert (Hsorted2:
      Sorted PolyLang.instr_point_sched_le
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))).
    {
      eapply sorted_sched_le_map_rebase_ip_nth.
      exact Hsorted2_base.
    }
    assert (Hperm2:
      Permutation
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          ipl)
        (filter
          (fun ip : PolyLang.InstrPoint =>
            negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
          sorted_ipl)).
    {
      eapply permutation_filter.
      exact Hperm.
    }
    assert (Hperm2_map:
      Permutation
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            ipl))
        (map (rebase_ip_nth (Datatypes.length pis1))
          (filter
            (fun ip : PolyLang.InstrPoint =>
              negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
            sorted_ipl))).
    {
      eapply Permutation_map.
      exact Hperm2.
    }
    pose proof (
      IHsts constrs sched_prefix env_dim iter_depth prefix (S pos)
            pis2 envv
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
                ipl))
            (map (rebase_ip_nth (Datatypes.length pis1))
              (filter
                (fun ip : PolyLang.InstrPoint =>
                  negb (Nat.ltb (PolyLang.ip_nth ip) (Datatypes.length pis1)))
                sorted_ipl))
            sth st2
            Hprefixlen Hwf_tl Htlext Hconstr
            Hflat2
            Hperm2_map
            Hsorted2 Hsem2_from_sth Hlenenv
    ) as Htail.
    destruct Htail as [stt [Hloop_tl Heq_tl]].
    eapply seq_cons_semantics_with_eq
      with (st:=st) (sts:=sts) (env:=rev (envv ++ prefix))
           (st1:=st1) (st2:=sth) (st3:=stt) (st3':=st2); eauto.
Qed.

(** Empty-prefix specializations of the mutual reconstruction theorem.  These
    two private bridges are the only way the compatibility layer below enters
    the main proof. *)
Local Lemma extracted_stmt_core_from_prefix:
    forall stmt constrs sched_prefix (varctxt: list ident) (vars: list (ident * Ty.t))
           pis (envv: list Z) (ipl sorted_ipl: list PolyLang.InstrPoint) st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt constrs (Datatypes.length varctxt) 0 sched_prefix = Okk pis ->
    in_poly (rev envv) constrs = true ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = Datatypes.length varctxt ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros stmt constrs sched_prefix varctxt vars pis envv ipl sorted_ipl st1 st2
      Hwf Hextract Hconstr _ Hflat Hperm Hsorted Hipls Hlenenv.
    pose proof (flatten_instrs_prefix_slice_nil envv pis ipl Hflat) as Hslice.
    assert (Hconstr_nil : in_poly (rev (envv ++ [])) constrs = true).
    { rewrite app_nil_r. exact Hconstr. }
    destruct core_sched_stmt_stmts_constrs_prefix_mutual as [Hstmt _].
    specialize
      (Hstmt stmt constrs sched_prefix
         (Datatypes.length varctxt) 0%nat []
         pis envv ipl sorted_ipl st1 st2
         eq_refl Hwf Hextract Hconstr_nil Hslice Hperm Hsorted Hipls Hlenenv).
    repeat rewrite app_nil_r in Hstmt.
    exact Hstmt.
Qed.

Lemma extract_stmt_to_loop_semantics_core_sched_constrs:
    forall stmt constrs sched_prefix (varctxt: list ident) (vars: list (ident * Ty.t))
           pis (envv: list Z) (ipl sorted_ipl: list PolyLang.InstrPoint) st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt constrs (Datatypes.length varctxt) 0 sched_prefix = Okk pis ->
    in_poly (rev envv) constrs = true ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Datatypes.length envv = Datatypes.length varctxt ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    exact extracted_stmt_core_from_prefix.
Qed.

Lemma extract_stmt_to_loop_semantics_core_sched:
    forall stmt sched_prefix varctxt vars pis envv ipl sorted_ipl st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt [] (Datatypes.length varctxt) 0 sched_prefix = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros stmt sched_prefix varctxt vars pis envv ipl sorted_ipl st1 st2
      Hwf Hextract Hchk Hflat Hperm Hsorted Hipls _ _ Hinit.
    assert (Hlenenv : Datatypes.length envv = Datatypes.length varctxt).
    {
      symmetry.
      eapply Instr.init_env_samelen.
      exact Hinit.
    }
    eapply extract_stmt_to_loop_semantics_core_sched_constrs
      with (constrs:=[]) (sched_prefix:=sched_prefix)
           (varctxt:=varctxt) (vars:=vars) (pis:=pis)
           (envv:=envv) (ipl:=ipl) (sorted_ipl:=sorted_ipl)
           (st1:=st1) (st2:=st2); eauto.
Qed.

Lemma extract_stmt_to_loop_semantics_core:
    forall stmt varctxt vars pis envv ipl sorted_ipl st1 st2,
    wf_scop_stmt stmt = true ->
    extract_stmt stmt [] (Datatypes.length varctxt) 0 [] = Okk pis ->
    check_extracted_wf pis varctxt vars = true ->
    PolyLang.flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl ->
    PolyLang.instr_point_list_semantics sorted_ipl st1 st2 ->
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 ->
    Instr.InitEnv varctxt envv st1 ->
    exists st2',
      Loop.loop_semantics stmt (rev envv) st1 st2' /\ State.eq st2 st2'.
Proof.
    intros.
    eapply extract_stmt_to_loop_semantics_core_sched with (sched_prefix:=[]); eauto.
Qed.


(* Lemma extract_stmt_correct: 
    forall stmt constrs depth sched_prefix, 
        extract_stmt stmt constrs depth sched_prefix = Okk [] ->
        PolyLang.instance_list_semantics constrs [] []. *)

Theorem extractor_correct: 
  forall loop pol st1 st2, 
    extractor loop = Okk pol ->
    PolyLang.instance_list_semantics pol st1 st2 -> 
    exists st2',
    Loop.semantics loop st1 st2' /\ State.eq st2 st2'.
Proof.
    intros loop pol st1 st2 Hext Hsema.
    destruct loop as [[stmt varctxt] vars].
    assert (Hscop: wf_scop_stmt stmt = true).
    { eapply extractor_success_implies_wf_scop; eauto. }
    eapply extractor_success_inv in Hext.
    destruct Hext as [pis [Hextract [Hwf Hpol]]].
    subst pol.
    eapply instance_list_semantics_inv in Hsema.
    destruct Hsema as (pis0 & varctxt0 & vars0 & envv &
      Hpprog & Hcompat & Hnonalias & Hinitenv & Hpolysema).
    inversion Hpprog; subst; clear Hpprog.
    eapply poly_instance_list_semantics_inv in Hpolysema.
    destruct Hpolysema as (pis1 & varctxt1 & vars1 & ipl & sorted_ipl &
      Hpprog' & Hflatten & Hperm & Hsorted & Hipls).
    inversion Hpprog'; subst; clear Hpprog'.
    pose proof (
      extract_stmt_to_loop_semantics_core
        _ _ _ _ _ _ _ _ _
        Hscop Hextract Hwf Hflatten Hperm Hsorted Hipls
        Hcompat Hnonalias Hinitenv
    ) as Hcore.
    destruct Hcore as (st2' & Hloop & Heq).
    exists st2'.
    split.
    - eapply loop_semantics_intro_from_envv; eauto.
    - exact Heq.
Qed.



End ExtractorCorrect.
