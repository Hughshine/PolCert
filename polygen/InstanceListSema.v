(** instance list semantics *)

Require Import Bool.
Require Import Base.
Require Import List.
Require Import SetoidList.
Require Import MSets.
Require Import Coq.MSets.MSetProperties.
Require Import Setoid Morphisms.
Require Import Linalg.
Require Import Base.
Require Import LinalgExt.
Require Import Classical.
Require Import ZArith.
Require Import PolyBase.
Require Import Misc.
Require Import Sorting.Sorted.
Require Import Permutation.
Require Import Coqlib.
Require Import LibTactics.
Require Import sflib.
Import ListNotations.

Require Import StateTy.
Require Import InstrTy.

Require Import AST.
Require Import OpenScop.
Require Import Result.

Import ListNotations.

Module ILSema (Instr: INSTR).

Module State := Instr.State.

Record InstrPoint := {
  ip_nth: nat;  (** belongs to nth polyhedral instruction *)
  ip_index: DomIndex;  (** index of the domain, i.e., iterator's value *)
  ip_transformation: Transformation; (** transformation function *)
  ip_time_stamp: TimeStamp;  (** schedule *)
  ip_instruction: Instr.t;  (** basic instruction *)
  ip_depth: nat;  (** surrounded iterator depth *)
}.

Definition naive_instr_point: InstrPoint := 
{|
ip_nth := 0;
ip_index := nil;
ip_transformation := nil;
ip_time_stamp := nil;
ip_instruction := Instr.dummy_instr;
ip_depth := 0;
|}.


Definition eq_except_sched (ip1 ip2: InstrPoint): Prop := 
  ip1.(ip_nth) = ip2.(ip_nth) /\ 
  ip1.(ip_index) = ip2.(ip_index) /\ 
  ip1.(ip_transformation) = ip2.(ip_transformation) /\
  ip1.(ip_instruction) = ip2.(ip_instruction) /\ 
  ip1.(ip_depth) = ip2.(ip_depth).

Lemma eq_except_sched_refl :
  forall ip,
    eq_except_sched ip ip.
Proof.
  intros ip.
  unfold eq_except_sched.
  repeat split; reflexivity.
Qed.

Lemma eq_except_sched_symm :
  forall ip1 ip2,
    eq_except_sched ip1 ip2 ->
    eq_except_sched ip2 ip1.
Proof.
  intros ip1 ip2 (Hnth & Hidx & Htf & Hins & Hdepth).
  unfold eq_except_sched.
  repeat split; symmetry; assumption.
Qed.

Lemma eq_except_sched_trans :
  forall ip1 ip2 ip3,
    eq_except_sched ip1 ip2 ->
    eq_except_sched ip2 ip3 ->
    eq_except_sched ip1 ip3.
Proof.
  intros ip1 ip2 ip3
         (Hnth12 & Hidx12 & Htf12 & Hins12 & Hdepth12)
         (Hnth23 & Hidx23 & Htf23 & Hins23 & Hdepth23).
  unfold eq_except_sched.
  repeat split; congruence.
Qed.

Inductive instr_point_sema (ip: InstrPoint) 
  (st1 st2: State.t): Prop :=
  | ip_sema_intro: forall wcs rcs,
    Instr.instr_semantics ip.(ip_instruction) 
      (affine_product ip.(ip_transformation) ip.(ip_index)) wcs rcs st1 st2 -> 
    instr_point_sema ip st1 st2.

Lemma instr_point_sema_stable_under_state_eq :
  forall ip st1 st2 st1' st2',
    State.eq st1 st1' ->
    State.eq st2 st2' ->
    instr_point_sema ip st1 st2 ->
    instr_point_sema ip st1' st2'.
Proof.
  intros ip st1 st2 st1' st2' Heq1 Heq2 Hsem.
  inversion Hsem as [wcs rcs Hinstr]; subst.
  econstructor.
  eapply Instr.instr_semantics_stable_under_state_eq; eauto.
Qed.

Lemma instr_point_sema_eq_except_sched_iff :
  forall ip1 ip2 st1 st2,
    eq_except_sched ip1 ip2 ->
    (instr_point_sema ip1 st1 st2 <->
     instr_point_sema ip2 st1 st2).
Proof.
  intros ip1 ip2 st1 st2 (_ & Hidx & Htf & Hins & _).
  split; intro Hsem; inversion Hsem as [wcs rcs Hinstr]; subst.
  - econstructor.
    rewrite <- Hidx, <- Htf, <- Hins.
    exact Hinstr.
  - econstructor.
    rewrite Hidx, Htf, Hins.
    exact Hinstr.
Qed.

Definition instr_point_sched_le (ip1 ip2: InstrPoint): Prop := 
  lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp) = Lt \/ 
  lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp) = Eq. 

Lemma instr_point_sched_le_trans:
  forall ip1 ip2 ip3,
    instr_point_sched_le ip1 ip2 ->
    instr_point_sched_le ip2 ip3 ->
    instr_point_sched_le ip1 ip3.
Proof.
  intros. unfolds instr_point_sched_le.
  destruct H; destruct H0. 
  - left. eapply lex_compare_trans; eauto.
  - left.
    rewrite <- is_eq_iff_cmp_eq in H0.
    eapply lex_compare_right_eq with (t1:=ip_time_stamp ip1) in H0; eauto.
    rewrite <- H0; trivial. 
  - left.
    rewrite <- is_eq_iff_cmp_eq in H.
    eapply lex_compare_left_eq with (t3:=ip_time_stamp ip3) in H; eauto.
    rewrite H; trivial.
  - right. eapply lex_compare_trans; eauto.
Qed. 


Definition instr_point_sched_ltb (ip1 ip2: InstrPoint): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp)) Lt.

Definition instr_point_sched_eqb (ip1 ip2: InstrPoint): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp)) Eq.

Definition instr_point_sched_lt (ip1 ip2: InstrPoint): Prop := 
  instr_point_sched_ltb ip1 ip2 = true. 

Definition instr_point_sched_eq (ip1 ip2: InstrPoint): Prop := 
  instr_point_sched_eqb ip1 ip2 = true. 


Definition Permutable (ip1 ip2: InstrPoint) := 
    forall st1, 
        Instr.NonAlias st1 ->
        (forall st2' st3,
        instr_point_sema ip1 st1 st2' ->
        instr_point_sema ip2 st2' st3 ->
        exists st2'' st3',
        instr_point_sema ip2 st1 st2'' /\
        instr_point_sema ip1 st2'' st3' /\
        Instr.State.eq st3 st3'
        ) /\
        (forall st2' st3,
        instr_point_sema ip2 st1 st2' ->
        instr_point_sema ip1 st2' st3 ->
        exists st2'' st3',
        instr_point_sema ip1 st1 st2'' /\
        instr_point_sema ip2 st2'' st3' /\
        Instr.State.eq st3 st3'
        ).
    
Lemma Permutable_symm: 
forall ip1 ip2, 
    Permutable ip1 ip2 -> 
    Permutable ip2 ip1.
Proof.
intros.
unfolds Permutable.
intros.
split. 
eapply H; eauto.
eapply H; eauto.
Qed.

Lemma permutable_eq_except_sched :
  forall ip1 ip1' ip2 ip2',
    eq_except_sched ip1 ip1' ->
    eq_except_sched ip2 ip2' ->
    Permutable ip1 ip2 ->
    Permutable ip1' ip2'.
Proof.
  intros ip1 ip1' ip2 ip2' Heq1 Heq2 Hperm st1 Halias.
  specialize (Hperm st1 Halias) as [Hforward Hbackward].
  split.
  - intros st2 st3 Hsem1 Hsem2.
    apply (proj2
      (instr_point_sema_eq_except_sched_iff ip1 ip1' st1 st2 Heq1))
      in Hsem1.
    apply (proj2
      (instr_point_sema_eq_except_sched_iff ip2 ip2' st2 st3 Heq2))
      in Hsem2.
    destruct (Hforward _ _ Hsem1 Hsem2)
      as (st2' & st3' & Hswap2 & Hswap1 & Hstate).
    exists st2'.
    exists st3'.
    repeat split; try exact Hstate.
    + apply (proj1
        (instr_point_sema_eq_except_sched_iff ip2 ip2' st1 st2' Heq2)).
      exact Hswap2.
    + apply (proj1
        (instr_point_sema_eq_except_sched_iff ip1 ip1' st2' st3' Heq1)).
      exact Hswap1.
  - intros st2 st3 Hsem2 Hsem1.
    apply (proj2
      (instr_point_sema_eq_except_sched_iff ip2 ip2' st1 st2 Heq2))
      in Hsem2.
    apply (proj2
      (instr_point_sema_eq_except_sched_iff ip1 ip1' st2 st3 Heq1))
      in Hsem1.
    destruct (Hbackward _ _ Hsem2 Hsem1)
      as (st2' & st3' & Hswap1 & Hswap2 & Hstate).
    exists st2'.
    exists st3'.
    repeat split; try exact Hstate.
    + apply (proj1
        (instr_point_sema_eq_except_sched_iff ip1 ip1' st1 st2' Heq1)).
      exact Hswap1.
    + apply (proj1
        (instr_point_sema_eq_except_sched_iff ip2 ip2' st2' st3' Heq2)).
      exact Hswap2.
Qed.
    
Inductive instr_point_list_semantics: list InstrPoint ->
State.t -> State.t -> Prop:=
| IPLS_nil: forall st st', 
Instr.State.eq st st' ->
instr_point_list_semantics [] st st'
| IPLS_cons: forall st1 st2 st3 ip il,
instr_point_sema ip st1 st2 ->
instr_point_list_semantics il st2 st3 ->
instr_point_list_semantics (ip::il) st1 st3.

Lemma instr_point_list_sema_stable_under_state_eq:
  forall l st1 st2 st1' st2',
    instr_point_list_semantics l st1 st2 ->
    Instr.State.eq st1 st1' ->
    Instr.State.eq st2 st2' ->
    instr_point_list_semantics l st1' st2'.
Proof.
  induction l.
  - 
  intros. 
  inv H. 
  simpls. econs; eauto. 
  eapply Instr.State.eq_sym in H0.
  eapply Instr.State.eq_trans; eauto.
  eapply Instr.State.eq_trans; eauto.
  -
  intros. inv H.
  inv H4. 
  eapply Instr.instr_semantics_stable_under_state_eq 
    with (st1':=st1') (st2:=st3) (st2':=st3) in H; eauto.
  2: {eapply Instr.State.eq_refl. }
  econs; eauto. instantiate (1:=st3). econs; eauto.
  eapply IHl; eauto. eapply Instr.State.eq_refl.  
Qed.

Lemma instr_point_list_semantics_nil_inv :
  forall st1 st2,
    instr_point_list_semantics [] st1 st2 ->
    State.eq st1 st2.
Proof.
  intros st1 st2 Hsem.
  inversion Hsem; subst; assumption.
Qed.

Lemma instr_point_list_semantics_cons_inv :
  forall ip rest st1 st2,
    instr_point_list_semantics (ip :: rest) st1 st2 ->
    exists stmid,
      instr_point_sema ip st1 stmid /\
      instr_point_list_semantics rest stmid st2.
Proof.
  intros ip rest st1 st2 Hsem.
  inversion Hsem as [|st1' stmid st2' ip' rest' Hip Htail]; subst.
  exists stmid.
  split; assumption.
Qed.

Lemma instr_point_list_semantics_singleton_decompose :
  forall ip st1 st2,
    instr_point_list_semantics [ip] st1 st2 ->
    exists stmid,
      instr_point_sema ip st1 stmid /\
      State.eq stmid st2.
Proof.
  intros ip st1 st2 Hsem.
  destruct (instr_point_list_semantics_cons_inv _ _ _ _ Hsem)
    as [stmid [Hip Hnil]].
  exists stmid.
  split; [exact Hip|].
  eapply instr_point_list_semantics_nil_inv.
  exact Hnil.
Qed.

Lemma instr_point_list_semantics_singleton_inv :
  forall ip st1 st2,
    instr_point_list_semantics [ip] st1 st2 ->
    instr_point_sema ip st1 st2.
Proof.
  intros ip st1 st2 Hsem.
  destruct (instr_point_list_semantics_singleton_decompose _ _ _ Hsem)
    as [stmid [Hip Heq]].
  eapply instr_point_sema_stable_under_state_eq
    with (st1 := st1) (st2 := stmid).
  - apply State.eq_refl.
  - exact Heq.
  - exact Hip.
Qed.

Lemma instr_point_list_semantics_app_inv :
  forall l1 l2 st1 st3,
    instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      instr_point_list_semantics l1 st1 st2 /\
      instr_point_list_semantics l2 st2 st3.
Proof.
  induction l1 as [|ip l1 IH]; intros l2 st1 st3 Hsem.
  - exists st1.
    split.
    + constructor. apply State.eq_refl.
    + exact Hsem.
  - simpl in Hsem.
    destruct (instr_point_list_semantics_cons_inv _ _ _ _ Hsem)
      as [stmid [Hip Htail]].
    destruct (IH _ _ _ Htail) as [st2 [Hleft Hright]].
    exists st2.
    split.
    + econstructor; eauto.
    + exact Hright.
Qed.

Definition veq_instance (ip1 ip2: InstrPoint): Prop :=
  ip1.(ip_nth) = ip2.(ip_nth) 
  /\ veq ip1.(ip_index) ip2.(ip_index) 
  /\ ip1.(ip_transformation) = ip2.(ip_transformation)
  /\ ip1.(ip_time_stamp) = ip2.(ip_time_stamp)
  /\ ip1.(ip_instruction) = ip2.(ip_instruction)
  /\ ip1.(ip_depth) = ip2.(ip_depth)
.

Lemma veq_instance_refl:
  forall ip,
    veq_instance ip ip.
Proof.
  intros. destruct ip. unfold veq_instance; splits; simpls; trivial.
  eapply veq_refl.
Qed.


Instance ip_ts_eq: Equivalence instr_point_sched_eq.
Proof.
  constructor.
  - intros x. unfold instr_point_sched_eq. 
    unfold instr_point_sched_eqb.
    rewrite lex_compare_reflexive. unfold comparison_eqb. simpl. trivial. 
  - intros x y Hxy. unfold instr_point_sched_eq in *.
    unfold instr_point_sched_eqb in *.  
    rewrite lex_compare_antisym.  
    rewrite comparison_eqb_iff_eq in Hxy.
    rewrite Hxy. simpl. trivial.
  - intros x y z Hxy Hyz. unfold instr_point_sched_eq in *. unfolds instr_point_sched_eqb.
    rewrite  comparison_eqb_iff_eq in Hxy.
    rewrite  comparison_eqb_iff_eq in Hyz.
    rewrite  comparison_eqb_iff_eq.
    eapply lex_compare_trans; eauto.
Qed.


Lemma instr_point_sched_le_antisym:
forall x1 x2,
instr_point_sched_le x1 x2 ->
instr_point_sched_le x2 x1 ->
instr_point_sched_eq x1 x2.
Proof.
  intros.
  unfolds instr_point_sched_le.
  unfold instr_point_sched_eq.
  unfold instr_point_sched_eqb.
  rewrite comparison_eqb_iff_eq.
  destruct H; destruct H0; try contradiction; eauto.
  - 
  rewrite lex_compare_antisym in H.
  rewrite H0 in H. 
  unfold CompOpp in H. trivial.
  discriminate.
  - 
  rewrite lex_compare_antisym in H.
  rewrite H0 in H. 
  unfold CompOpp in H. trivial.
  discriminate.
Qed.

Lemma strongly_sorted_lists_by_timestamp_equal :
  forall l1 l2,
    StronglySorted instr_point_sched_le l1 ->
    StronglySorted instr_point_sched_le l2 ->
    NoDupA instr_point_sched_eq l1 ->
    NoDupA instr_point_sched_eq l2 ->
    (forall x, In x l1 <-> In x l2) ->
    l1 = l2.
Proof.
  induction l1 as [|x1 l1 IH]; intros l2 Hs1 Hs2 Hnd1 Hnd2 Hin.
  - destruct l2; [reflexivity |].
    exfalso. apply (Hin i). apply in_eq.
  - destruct l2 as [|x2 l2']; [> exfalso; apply (Hin x1); left; reflexivity |].
    rename l1 into l1'.
    assert (x1 = x2).
    {
      assert (Hin1: In x1 (x1:: l1')) by apply in_eq.
      assert (Hin2: In x2 (x2 :: l2')) by apply in_eq.
      assert (In x1 (x2 :: l2')). {
        eapply Hin; eauto.
      } 
      destruct H as [Heq | Hin_tail]; symmetry; trivial.
      - 

        (* use NoDup to derive contradiction *)
        assert (Hback: In x2 (x1 :: l1')). {
          eapply Hin; eauto.
        }
        destruct Hback as [Heq' | Hin_tail'].
        + symmetry in Heq'. trivial.
        + 
          assert (instr_point_sched_le x1 x2).
          { 
            inv Hs1.
            eapply Forall_forall with (x:=x2) in H2; eauto.
          }
          assert (instr_point_sched_le x2 x1).
          { 
            inv Hs2.
            eapply Forall_forall with (x:=x1) in H3; eauto.
          }
          assert (instr_point_sched_eq x1 x2). {
            eapply instr_point_sched_le_antisym; eauto.
          }
          inv Hnd1.
          eapply In_InA with (eqA:=instr_point_sched_eq) in Hin_tail'. 2: {eapply ip_ts_eq. }
          clear - Hin_tail' H4 H1.
          eapply InA_eqA with (y:=x1) in Hin_tail'; eauto.
          {try contradiction. }
          {eapply ip_ts_eq. }
          {eapply ip_ts_eq. trivial. }
    }
    subst x2.
    f_equal.
    apply IH.
    + eapply StronglySorted_inv; eauto.
    + eapply StronglySorted_inv; eauto.
    + 
      replace l1' with ([] ++ l1'); trivial.
      eapply NoDupA_split; eauto.
    + 
      replace l2' with ([] ++ l2'); trivial.
      eapply NoDupA_split; eauto.
    + intros x. split; intro Hx.
      * assert (In x (x1 :: l1')). { eapply in_cons; trivial. }
        eapply Hin in H; eauto.
        destruct H as [Hx1 | Hx1].
        -- subst. 
          clear - Hnd1 Hx.
          inv Hnd1. eapply In_InA with (eqA := instr_point_sched_eq ) in Hx; eauto. contradiction.
          eapply ip_ts_eq.
        -- trivial.
      * assert (In x (x1 :: l2')). { eapply in_cons; trivial. }
        eapply Hin in H; eauto.
        destruct H as [Hx1 | Hx1].
        -- subst. 
          clear - Hnd2 Hx.
          inv Hnd2. eapply In_InA with (eqA := instr_point_sched_eq ) in Hx; eauto. contradiction.
          eapply ip_ts_eq.
        -- trivial.   
Qed.


Lemma Sorted_incl_eq :
  forall l1 l2,
    Sorted instr_point_sched_le l1 ->
    Sorted instr_point_sched_le l2 ->
    (forall x, In x l1 <-> In x l2) ->
    NoDupA instr_point_sched_eq l1 ->
    NoDupA instr_point_sched_eq l2 ->
    l1 = l2.
Proof.
  intros l1 l2  Hs1 Hs2 Heq Hinj1 Hinj2.
  pose proof instr_point_sched_le_trans as Htrans.
  apply Sorted_StronglySorted in Hs1; auto.
  apply Sorted_StronglySorted in Hs2; auto.
  eapply strongly_sorted_lists_by_timestamp_equal; eauto.
Qed.

Lemma Sorted_same_ele_nodup_implies_sema_eq:
  forall l1 l2 st1 st2,
    Sorted instr_point_sched_le l1 ->
    Sorted instr_point_sched_le l2 ->
    NoDupA instr_point_sched_eq l1 ->
    NoDupA instr_point_sched_eq l2 ->
    (forall x, In x l1 <-> In x l2) ->
    instr_point_list_semantics l1 st1 st2 -> 
    instr_point_list_semantics l2 st1 st2.
Proof.
  intros l1 l2 st1 st2 Hs1 Hs2 Hd1 Hd2 Hin Hsem1.
  assert (l1 = l2). 
  { eapply Sorted_incl_eq; eauto. }
  subst. trivial.
Qed.

Lemma Sorted_same_ele_nodup_implies_sema_eq_stable:
  forall l1 l2 st1 st2 st1' st2',
    Sorted instr_point_sched_le l1 ->
    Sorted instr_point_sched_le l2 ->
    NoDupA instr_point_sched_eq l1 ->
    NoDupA instr_point_sched_eq l2 ->
    (forall x, In x l1 <-> In x l2) ->
    instr_point_list_semantics l1 st1 st2 -> 
    State.eq st1 st1' ->
    State.eq st2 st2' ->
    instr_point_list_semantics l2 st1' st2'.
Proof.
  intros l1 l2 st1 st2 st1' st2' Hs1 Hs2 Hd1 Hd2 Hin Hsem1 Hst1 Hst2.
  assert (l1 = l2). 
  { eapply Sorted_incl_eq; eauto. } 
  eapply instr_point_list_sema_stable_under_state_eq with (st1':=st1') (st2':=st2') in Hsem1; eauto. 
  subst. trivial.
Qed.

Lemma instr_point_list_sema_concat:
  forall l1 l2 st1 st2 st3,
    instr_point_list_semantics l1 st1 st2 ->
    instr_point_list_semantics l2 st2 st3 ->
    instr_point_list_semantics (l1 ++ l2) st1 st3.
Proof.
intros l1 l2 st1 st2 st3 Hsem1 Hsem2.
induction Hsem1.
- (* Base case: l1 = [] *)
  simpl. eapply instr_point_list_sema_stable_under_state_eq; eauto.
  + eapply Instr.State.eq_sym. trivial.
  + eapply Instr.State.eq_refl.
- (* Inductive case: l1 = ip :: il *)
  simpl. econstructor; eauto.
Qed.
End ILSema.
