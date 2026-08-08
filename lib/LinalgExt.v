Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.
Require Import RelationPairs.
Require Import BinPos.

Require Import Misc.
Require Import Linalg.
Require Import Base.
Require Import LibTactics.
Import List.ListNotations.

Open Scope Z_scope.
Open Scope list_scope.
Open Scope vector_scope.

Definition insert_zeros_at (added index : nat) (values : list Z) : list Z :=
  resize index values ++ repeat 0%Z added ++ skipn index values.

Lemma insert_zeros_at_commute :
  forall added d index values,
    insert_zeros_at added (index + d) (insert_zeros_at d index values) =
    insert_zeros_at d index (insert_zeros_at added index values).
Proof.
  intros added d index values.
  unfold insert_zeros_at.
  rewrite Linalg.resize_app_le by (rewrite Linalg.resize_length; lia).
  rewrite Linalg.resize_length.
  replace (index + d - index)%nat with d by lia.
  rewrite List.skipn_app by lia.
  replace (d - d)%nat with 0%nat by lia.
  simpl.
  rewrite Linalg.resize_app_le by (rewrite List.repeat_length; lia).
  rewrite Linalg.resize_length.
  rewrite List.skipn_app by lia.
  replace (d - d)%nat with 0%nat by lia.
  replace (0 - added)%nat with 0%nat by lia.
  simpl.
  replace (index + d - index)%nat with d by lia.
  replace (d - length (repeat 0%Z d))%nat with 0%nat by
    (rewrite List.repeat_length; lia).
  simpl.
  replace (skipn (index + d) (resize index values)) with ([] : list Z).
  2:{ rewrite List.skipn_all2; [reflexivity|rewrite Linalg.resize_length; lia]. }
  replace (skipn d (repeat 0%Z d)) with ([] : list Z).
  2:{ rewrite List.skipn_all2; [reflexivity|rewrite List.repeat_length; lia]. }
  rewrite Linalg.resize_app_le by (rewrite Linalg.resize_length; lia).
  rewrite Linalg.resize_length.
  rewrite List.skipn_app by lia.
  replace (index - index)%nat with 0%nat by lia.
  replace (0 - added)%nat with 0%nat by lia.
  simpl.
  replace (skipn index (resize index values)) with ([] : list Z).
  2:{ rewrite List.skipn_all2; [reflexivity|rewrite Linalg.resize_length; lia]. }
  replace (index - length (resize index values))%nat with 0%nat by
    (rewrite Linalg.resize_length; lia).
  replace (index + d - index)%nat with d by lia.
  replace (d - length (repeat 0%Z d))%nat with 0%nat by
    (rewrite List.repeat_length; lia).
  simpl.
  replace (skipn d (repeat 0%Z d)) with ([] : list Z).
  2:{ rewrite List.skipn_all2; [reflexivity|rewrite List.repeat_length; lia]. }
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Definition vector_zero (n: nat) : list Z := repeat 0%Z n.

Definition vector_opp (v: list Z) : list Z := map Z.opp v.

Lemma vector_opp_app :
  forall v1 v2,
    vector_opp (v1 ++ v2) = vector_opp v1 ++ vector_opp v2.
Proof.
  intros v1 v2.
  unfold vector_opp.
  apply map_app.
Qed.

Lemma vector_opp_involutive :
  forall v,
    vector_opp (vector_opp v) = v.
Proof.
  induction v as [|x v IH]; simpl; [reflexivity|].
  rewrite IH, Z.opp_involutive.
  reflexivity.
Qed.

Lemma vector_opp_zero :
  forall n,
    vector_opp (vector_zero n) = vector_zero n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  unfold vector_opp, vector_zero in *.
  simpl.
  f_equal.
  exact IH.
Qed.

Lemma dot_product_vector_opp_l :
  forall v1 v2,
    dot_product (vector_opp v1) v2 = Z.opp (dot_product v1 v2).
Proof.
  induction v1 as [|x v1 IH]; intros [|y v2]; simpl; try lia.
  rewrite IH.
  lia.
Qed.

Lemma dot_product_vector_opp_r :
  forall v1 v2,
    dot_product v1 (vector_opp v2) = Z.opp (dot_product v1 v2).
Proof.
  induction v1 as [|x v1 IH]; intros [|y v2]; simpl; try lia.
  rewrite IH.
  lia.
Qed.

Lemma dot_product_select_coordinate_base :
  forall n xs,
    dot_product (vector_zero n ++ [1%Z]) xs = nth n xs 0%Z.
Proof.
  unfold vector_zero.
  induction n as [|n IH]; intros xs.
  - destruct xs as [|x xs]; simpl; [reflexivity|].
    cbn [dot_product].
    destruct x; destruct xs; reflexivity.
  - destruct xs as [|x xs]; simpl.
    + reflexivity.
    + apply IH.
Qed.

Lemma dot_product_select_coordinate :
  forall cols n xs,
    (S n <= cols)%nat ->
    dot_product (resize cols (vector_zero n ++ [1%Z])) xs = nth n xs 0%Z.
Proof.
  intros cols n xs Hcols.
  assert (Hresize :
    resize cols (vector_zero n ++ [1%Z]) =
    (vector_zero n ++ [1%Z]) ++ repeat 0%Z (cols - S n)).
  {
    rewrite resize_app_le.
    2:{ unfold vector_zero. rewrite repeat_length. lia. }
    replace (length (vector_zero n)) with n.
    2:{ unfold vector_zero. symmetry. apply repeat_length. }
    replace (cols - n)%nat with (S (cols - S n)) by lia.
    simpl.
    rewrite resize_null_repeat by reflexivity.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hresize, dot_product_app_left, dot_product_repeat_zero_left.
  replace (length (vector_zero n ++ [1%Z])) with (S n).
  2:{ unfold vector_zero. rewrite app_length, repeat_length. simpl. lia. }
  rewrite dot_product_select_coordinate_base.
  rewrite nth_resize.
  assert ((n <? S n)%nat = true) as Hlt.
  { apply Nat.ltb_lt. lia. }
  rewrite Hlt.
  lia.
Qed.

Lemma is_eq_iff_cmp_eq: 
    forall t1 t2,
        is_eq t1 t2 = true <-> lex_compare t1 t2 = Eq.
Proof.
    induction t1.
    {
        intros.
        split.
        {
            intro.
            simpls.
            destruct t2; simpls; trivial.
            destruct z; simpls; trivial; tryfalse.
            {
                eapply lex_compare_nil_is_null; trivial.
            }
        }
        {
            intro.
            simpls.
            destruct t2; simpls; trivial.
            destruct z; simpls; trivial; tryfalse.
            eapply is_null_lex_compare_nil; eauto.
        }
    }
    {
        intros.
        split.
        {
            intro.
            simpls. 
            destruct t2; simpls; trivial.
            {
                eapply andb_true_iff in H.
                destruct H.
                eapply lex_compare_nil_is_null in H0.
                rewrite H0.
                assert (a = 0). {try lia. }
                rewrite H1; simpls; trivial.
            }
            {
                eapply andb_true_iff in H.
                destruct H.
                eapply IHt1 in H0.
                (* eapply lex_compare_nil_is_null in H0. *)
                rewrite H0.
                assert (a = z). {try lia. }
                subst; trivial.
                rewrite Z.compare_refl; trivial.
            }
        }
        {
            intro.
            simpls. 
            destruct t2; simpls; trivial.
            {
                reflect.
                destruct a; simpls; trivial; tryfalse.
                split; trivial.
                eapply is_null_lex_compare_nil; eauto.
                destruct (lex_compare_nil t1); tryfalse.
                trivial.
            }
            {
                eapply andb_true_iff.
                rewrite (IHt1 t2).
                destruct (a?=z) eqn:G; try discriminate.
                split.
                {
                    eapply Z.compare_eq in G.
                    subst.
                    eapply Z.eqb_refl.
                }
                {
                    trivial.
                }
            }
        }
    }
Qed.


Lemma lex_compare_nil_trans: 
    forall l1 l2 cmp,
        CompOpp (lex_compare_nil l1) = cmp -> (** l1 < nil *)
        lex_compare_nil l2 = cmp ->           (** nil < l2 *)
        lex_compare l1 l2 = cmp.              (** l1 < l2 *)
Proof. 
    induction l1.
    {
        intros.
        destruct cmp.
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
        }
    }
    {
        intros.
        destruct cmp.
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
            destruct z eqn:Hz; simpls; tryfalse; trivial.
            destruct a eqn:Ha; simpls; tryfalse; trivial.
            eapply IHl1; eauto.
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
            destruct z eqn:Hz; simpls; tryfalse; trivial.
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
                eapply IHl1; eauto.    
            }
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
            }
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
            destruct z eqn:Hz; simpls; tryfalse; trivial.
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
                eapply IHl1; eauto.    
            }
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
            }
        }
    }
Qed.

Local Lemma lex_compare_uncons :
  forall a b,
    lex_compare a b =
    match hd 0 a ?= hd 0 b with
    | Eq => lex_compare (tl a) (tl b)
    | cmp => cmp
    end.
Proof.
  intros [|x xs] [|y ys]; simpl.
  - reflexivity.
  - destruct y; destruct ys; reflexivity.
  - destruct x; destruct xs; reflexivity.
  - reflexivity.
Qed.

Local Lemma compare_step_lt_inv :
  forall cmp tail,
    (match cmp with Eq => tail | Lt => Lt | Gt => Gt end) = Lt ->
    cmp = Lt \/ (cmp = Eq /\ tail = Lt).
Proof.
  intros [| |] tail Hstep; simpl in Hstep; intuition discriminate.
Qed.

Local Lemma lex_compare_lt_trans :
  forall b a c,
    lex_compare a b = Lt ->
    lex_compare b c = Lt ->
    lex_compare a c = Lt.
Proof.
  induction b as [|y ys IH]; intros a c Hab Hbc.
  - rewrite lex_compare_nil_right in Hab.
    rewrite lex_compare_nil_left in Hbc.
    eapply lex_compare_nil_trans; eauto.
  - rewrite lex_compare_uncons in Hab, Hbc |- *.
    apply compare_step_lt_inv in Hab, Hbc.
    destruct Hab as [Hhead_ab | [Hhead_ab Hab_tail]];
      destruct Hbc as [Hhead_bc | [Hhead_bc Hbc_tail]].
    + apply Z.compare_lt_iff in Hhead_ab, Hhead_bc.
      assert (Hhead_ac : (hd 0 a ?= hd 0 c) = Lt).
      { apply Z.compare_lt_iff. eapply Z.lt_trans; eauto. }
      rewrite Hhead_ac. reflexivity.
    + apply Z.compare_lt_iff in Hhead_ab.
      apply Z.compare_eq_iff in Hhead_bc.
      assert (Hhead_ac : (hd 0 a ?= hd 0 c) = Lt).
      { apply Z.compare_lt_iff. rewrite <- Hhead_bc. exact Hhead_ab. }
      rewrite Hhead_ac. reflexivity.
    + apply Z.compare_eq_iff in Hhead_ab.
      apply Z.compare_lt_iff in Hhead_bc.
      assert (Hhead_ac : (hd 0 a ?= hd 0 c) = Lt).
      { apply Z.compare_lt_iff. rewrite Hhead_ab. exact Hhead_bc. }
      rewrite Hhead_ac. reflexivity.
    + apply Z.compare_eq_iff in Hhead_ab, Hhead_bc.
      assert (Hhead_ac : (hd 0 a ?= hd 0 c) = Eq).
      { apply Z.compare_eq_iff. lia. }
      rewrite Hhead_ac.
      exact (IH (tl a) (tl c) Hab_tail Hbc_tail).
Qed.

Lemma lex_compare_trans:
  forall b a c cmp,
    lex_compare a b = cmp ->
    lex_compare b c = cmp ->
    lex_compare a c = cmp.
Proof.
  intros b a c cmp Hab Hbc.
  destruct cmp.
  - apply is_eq_iff_cmp_eq in Hab.
    rewrite (lex_compare_left_eq a b c Hab).
    exact Hbc.
  - eapply lex_compare_lt_trans; eauto.
  - assert (Hca : lex_compare c a = Lt).
    {
      eapply lex_compare_lt_trans with (b := b).
      - rewrite lex_compare_antisym, Hbc. reflexivity.
      - rewrite lex_compare_antisym, Hab. reflexivity.
    }
    rewrite lex_compare_antisym, Hca.
    reflexivity.
Qed.

Lemma lex_compare_total: 
    forall a b, 
        lex_compare a b = Lt \/ lex_compare b a = Lt \/ lex_compare a b = Eq.
Proof. 
    intros.
    remember (lex_compare a b) as res.
    symmetry in Heqres.
    destruct res eqn:G; try firstorder.
    right; left.
    rewrite lex_compare_antisym.
    rewrite Heqres. simpls; trivial.
Qed. 

Definition lex_compare_leb (xs ys : list Z) : bool :=
  comparison_eqb (lex_compare xs ys) Lt ||
  comparison_eqb (lex_compare xs ys) Eq.

Definition lex_compare_geb (xs ys : list Z) : bool :=
  comparison_eqb (lex_compare xs ys) Gt ||
  comparison_eqb (lex_compare xs ys) Eq.

Lemma lex_compare_leb_trans :
  forall xs ys zs,
    lex_compare_leb xs ys = true ->
    lex_compare_leb ys zs = true ->
    lex_compare_leb xs zs = true.
Proof.
  intros xs ys zs Hxy Hyz.
  unfold lex_compare_leb in *.
  rewrite orb_true_iff in Hxy, Hyz |- *.
  destruct Hxy as [Hxy|Hxy]; destruct Hyz as [Hyz|Hyz].
  - left.
    apply comparison_eqb_iff_eq in Hxy.
    apply comparison_eqb_iff_eq in Hyz.
    apply comparison_eqb_iff_eq.
    eapply lex_compare_trans; eauto.
  - left.
    apply comparison_eqb_iff_eq in Hxy.
    apply comparison_eqb_iff_eq in Hyz.
    apply comparison_eqb_iff_eq.
    rewrite <- is_eq_iff_cmp_eq in Hyz.
    pose proof (lex_compare_right_eq xs ys zs Hyz) as Heq.
    rewrite <- Heq; exact Hxy.
  - left.
    apply comparison_eqb_iff_eq in Hxy.
    apply comparison_eqb_iff_eq in Hyz.
    apply comparison_eqb_iff_eq.
    rewrite <- is_eq_iff_cmp_eq in Hxy.
    pose proof (lex_compare_left_eq xs ys zs Hxy) as Heq.
    rewrite Heq; exact Hyz.
  - right.
    apply comparison_eqb_iff_eq in Hxy.
    apply comparison_eqb_iff_eq in Hyz.
    apply comparison_eqb_iff_eq.
    eapply lex_compare_trans; eauto.
Qed.

Lemma lex_compare_geb_flip :
  forall xs ys,
    lex_compare_geb xs ys = lex_compare_leb ys xs.
Proof.
  intros xs ys.
  unfold lex_compare_geb, lex_compare_leb.
  rewrite lex_compare_antisym.
  destruct (lex_compare ys xs); reflexivity.
Qed.

Lemma lex_compare_geb_trans :
  forall xs ys zs,
    lex_compare_geb xs ys = true ->
    lex_compare_geb ys zs = true ->
    lex_compare_geb xs zs = true.
Proof.
  intros xs ys zs Hxy Hyz.
  rewrite lex_compare_geb_flip in Hxy, Hyz |- *.
  eapply lex_compare_leb_trans; eauto.
Qed.
