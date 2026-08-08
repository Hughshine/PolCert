Require Import Permutation.
Require Import Sorting.Sorted.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import sflib.
Require Import LibTactics.
Require Import Base.
Require Import StablePermut.
Require Import Lia.
Require Import Bool.
Require Import Classical.

(** Note: This implementation of SelectionSort is stable. *)
(** Modified from *Verfied Functional Algorithm*'s selection sort implementation*)

(** x is nth element of list l *)
Fixpoint select_helper {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (l: list A) (x: A) (n: nat) (r: list A): A * list A := 
    match r with 
    | [] =>  (x, remove_nth n l)
    | x'::r' => 
        if orb (ltb x x') (eqb x x') 
        then select_helper ltb eqb (l++[x']) x n r' 
        else select_helper ltb eqb (l++[x']) x' (length l) r' 
    end.

Definition select {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (x: A) (l: list A) : A * list A :=
    select_helper ltb eqb [x] x 0 l.

(* Compute (select Nat.ltb 1 [3;0;4]). *)

(** n is the fuel for structurally decreasing restriction *)
Fixpoint selsort {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (l : list A) (n : nat) : list A :=
    match l, n with
    | _, O => [] (* ran out of fuel *)
    | [], _ => []
    | x :: r, S n' => let (y, r') := select ltb eqb x r
                    in y :: selsort ltb eqb r' n'
  end.

Definition SelectionSort {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (l: list A): list A := 
    selsort ltb eqb l (length l).

Example sort_pi: 
    SelectionSort Nat.ltb Nat.eqb [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  unfold SelectionSort.
  simpl. reflexivity.
Qed.

(** permutation & sorted & stable permutation *)
(** 1. Let's prove SelectionSort implies Permutation first *)
Lemma select_helper_perm: 
    forall A ltb eqb r l x n y l', 
        n < length l ->
        nth n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        @Permutation A (l ++ r) (y :: l').
Proof.
    induction r. 
    {
        intros until l'. intros LENGTH Hnth Hselect.
        unfold select_helper in Hselect.
        
        inv Hselect; eauto.
        replace (l ++ []) with l. 
            2: { rewrite app_nil_r; trivial. }
        eapply remove_nth_cons_nth_permut; eauto.
    }
    {
        intros until l'. intros LENGTH Hnth Hselect.
        unfold select_helper in Hselect.
        folds (@select_helper A).
        des_ifH Hselect.
        {
            eapply IHr in Hselect; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. lia.
            rewrite app_nth1; eauto.
        }
        {
            eapply IHr in Hselect; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. 
            unfold length.
            lia.
            rewrite app_nth2; eauto. 
            replace (length l - length l) with 0; try lia.
            simpl; trivial.    
        }
    }
Qed.

Lemma select_perm: 
    forall A ltb eqb l x y r,
        select ltb eqb x l = (y, r) -> 
        @Permutation A (x :: l) (y :: r).
Proof.
    intros.
    unfold select in H.
    eapply select_helper_perm in H; eauto.
Qed.

Lemma select_helper_length: 
    forall A ltb eqb r l x n y l', 
        n < length l ->
        @nth A n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        length (l++r) = length (y::l').
Proof.
    induction r.
    {
        intros.
        unfold select_helper in H1.
        inv H1.
        rewrite app_nil_r.
        replace (y::remove_nth n l) with ([y]++remove_nth n l).
        2: {
            simpl; eauto.
        }
        rewrite app_length.
        eapply remove_nth_length in H0; eauto.
        rewrite <- H0.
        simpl. lia.
    }
    {
        intros.
        unfold select_helper in H1.
        folds (@select_helper A).
        des_ifH H1.
        {
            eapply IHr in H1; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. lia.
            rewrite app_nth1; eauto.
        }
        {
            eapply IHr in H1; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. 
            unfold length.
            lia.
            rewrite app_nth2; eauto. 
            replace (length l - length l) with 0; try lia.
            simpl; trivial.    
        }
    }
Qed.

Lemma select_rest_length:
    forall A ltb eqb l x y r,
        @select A ltb eqb x l = (y, r) ->
        length l = length r.
Proof.
    intros.
    unfolds select.
    eapply select_helper_length in H; eauto.
Qed.

Lemma select_helper_map:
  forall A B (f : A -> B)
    (ltbA eqbA : A -> A -> bool) (ltbB eqbB : B -> B -> bool),
    (forall x y, ltbA x y = ltbB (f x) (f y)) ->
    (forall x y, eqbA x y = eqbB (f x) (f y)) ->
    forall r l x n y r',
      select_helper ltbA eqbA l x n r = (y, r') ->
      select_helper ltbB eqbB (map f l) (f x) n (map f r) =
        (f y, map f r').
Proof.
  intros A B f ltbA eqbA ltbB eqbB Hlt Heq r.
  induction r as [|a r IH]; intros l x n y r' Hselect.
  - simpl in Hselect.
    inversion Hselect; subst.
    simpl.
    rewrite remove_nth_maps_comm.
    reflexivity.
  - simpl in Hselect.
    destruct (ltbA x a || eqbA x a) eqn:Hord.
    + specialize (IH (l ++ [a]) x n y r' Hselect).
      simpl.
      rewrite <- (Hlt x a), <- (Heq x a), Hord.
      rewrite map_app in IH.
      simpl in IH.
      exact IH.
    + specialize (IH (l ++ [a]) a (length l) y r' Hselect).
      simpl.
      rewrite <- (Hlt x a), <- (Heq x a), Hord.
      rewrite map_app in IH.
      simpl in IH.
      rewrite map_length.
      exact IH.
Qed.

Lemma select_map:
  forall A B (f : A -> B)
    (ltbA eqbA : A -> A -> bool) (ltbB eqbB : B -> B -> bool),
    (forall x y, ltbA x y = ltbB (f x) (f y)) ->
    (forall x y, eqbA x y = eqbB (f x) (f y)) ->
    forall x l y r,
      select ltbA eqbA x l = (y, r) ->
      select ltbB eqbB (f x) (map f l) = (f y, map f r).
Proof.
  intros A B f ltbA eqbA ltbB eqbB Hlt Heq x l y r Hselect.
  unfold select in Hselect |- *.
  exact (select_helper_map A B f ltbA eqbA ltbB eqbB
    Hlt Heq l [x] x 0 y r Hselect).
Qed.

Lemma selsort_map:
  forall A B (f : A -> B)
    (ltbA eqbA : A -> A -> bool) (ltbB eqbB : B -> B -> bool),
    (forall x y, ltbA x y = ltbB (f x) (f y)) ->
    (forall x y, eqbA x y = eqbB (f x) (f y)) ->
    forall n l,
      selsort ltbB eqbB (map f l) n = map f (selsort ltbA eqbA l n).
Proof.
  intros A B f ltbA eqbA ltbB eqbB Hlt Heq n.
  induction n as [|n IH]; intros l; [destruct l; reflexivity|].
  destruct l as [|x l]; [reflexivity|].
  simpl.
  destruct (select ltbA eqbA x l) as [y r] eqn:Hselect.
  rewrite (select_map A B f ltbA eqbA ltbB eqbB
    Hlt Heq x l y r Hselect).
  simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma selsort_perm: 
    forall A ltb eqb n l, 
        length l = n -> 
        @Permutation A l (selsort ltb eqb l n).
Proof.
    induction n as [|n IH].
    {
        intros. eapply length_zero_iff_nil in H. subst.
        unfold selsort. 
        eauto.
    }
    {
        intros.
        remember (selsort ltb eqb l (S n)) as l'.
        unfold selsort in Heql'.
        folds (@selsort A).
        destruct l eqn:Hl; try discriminate.
        destruct (select ltb eqb a l0) eqn:Hselect; eauto.
        assert (length l0 = n). {
            unfolds length; eauto. 
        }
        eapply select_perm in Hselect.
        eapply IH in H0. subst.
        assert (Permutation l1 (selsort ltb eqb l1 n)). {
            eapply IH.
            eapply Permutation_length in Hselect.
            rewrite H in Hselect.
            symmetry in Hselect.
            unfolds length; eauto.
        }
        eapply Permutation_trans in Hselect; eauto.
        eapply (perm_skip a0) in H1.
        eapply Permutation_trans; eauto.
    }
Qed.

Lemma selection_sort_perm: 
    forall A ltb eqb l, 
        @Permutation A l (SelectionSort ltb eqb l).
Proof.
    intros.
    unfolds SelectionSort. 
    eapply selsort_perm; eauto.
Qed.


Lemma select_helper_fst_leq: 
    forall A ltb eqb r l x n y l', 
        transitive ltb ->
        reflexive eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb -> 
        n < length l ->
        @nth A n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        ltb y x = true \/ eqb y x = true.
Proof.
    induction r. 
    {
        intros until l'; intros TRANS REFLEX TOTAL LTEQL; intros. 
        unfold select_helper in H1. inv H1. right; eauto.
    }
    {
        intros until l'; intros TRANS REFLEX TOTAL LTEQL; intros. 
        unfold select_helper in H1. folds (@select_helper A).
        destruct (orb (ltb x a) (eqb x a)) eqn:Hordxa.
        {
            eapply IHr in H1; eauto.
            rewrite app_length; lia.
            rewrite app_nth1; eauto. 
        }
        {
            eapply IHr in H1; eauto.
            {
                destruct H1.
                {
                    unfold total in TOTAL.
                    pose proof (TOTAL x a).
                    assert (ltb a x = true). {
                        eapply orb_false_elim in Hordxa.
                        destruct Hordxa.
                        rewrite H3 in H2; rewrite H4 in H2.
                        firstorder.
                    } 
                    clear H2 Hordxa.
                    left.
                    unfold transitive in TRANS.
                    assert (ltb y x = true). {
                        eapply TRANS; eauto.
                    }
                    eauto.                
                }
                {
                    unfold total in TOTAL.
                    pose proof (TOTAL x a).
                    assert (ltb a x = true). {
                        eapply orb_false_elim in Hordxa.
                        destruct Hordxa.
                        rewrite H3 in H2; rewrite H4 in H2.
                        firstorder.
                    }
                    left. 
                    unfold transitive in TRANS.
                    assert (ltb y x = true). {
                        unfold ltb_eqb_implies_ltb in LTEQL.
                        eapply LTEQL; eauto.
                    }
                    subst; eauto. 
                }
            }
            {
                rewrite app_length. simpl. lia.
            }
            {
                rewrite app_nth2. 
                replace (length l - length l) with 0; try lia.
                simpl; eauto.
                lia.
            }   
        }
    }
Qed. 

Lemma select_fst_leq: 
    forall A ltb eqb al x y bl,
        transitive ltb ->
        reflexive eqb -> 
        symmetric eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb ->
        @select A ltb eqb x al = (y, bl) -> 
        ltb y x = true \/ eqb x y = true.
Proof.
    intros.
    unfold select in H4.
    eapply select_helper_fst_leq in H4; eauto. 
    unfold symmetric in H1. 
    destruct H4. tauto. 
    rewrite H1 in H4.
    right; eauto.
Qed.

Definition ord_all {A: Type} (ltb: A -> A -> bool) (x: A) (xs: list A) := Forall (fun y => if ltb x y then True else False) xs.

Lemma ord_all_ord_one: 
    forall A ltb x y xs,
        @ord_all A ltb x xs -> 
        In y xs -> 
        ltb x y = true.
Proof.
    intros.
    unfolds ord_all.
    eapply Forall_forall in H; eauto.
    destruct (ltb x y); eauto. 
Qed. 


Lemma ord_all_trans: 
    forall A ltb x xs a,
        transitive ltb ->
        @ord_all A ltb x xs -> 
        ltb a x = true -> 
        ord_all ltb a xs.
Proof.
    intros.
    unfold ord_all.
    unfold transitive in H.
    eapply Forall_forall; eauto. 
    intros.
    eapply ord_all_ord_one in H0; eauto.
    assert (ltb a x0 = true).
    {
        eapply H; eauto.
    }
    rewrite H3; eauto. 
Qed.

Lemma stable_permut_multi_skip_generic:
  forall A (ltb eqb sfunc : A -> A -> bool) l1 y l2,
    irreflexive ltb eqb ->
    antisymmetric ltb eqb ->
    symmetric eqb ->
    ord_all (fun y x => sfunc x y) y l1 ->
    ord_all ltb y l1 ->
    StablePermut ltb eqb sfunc
      (l1 ++ [y] ++ l2)
      (y :: l1 ++ l2).
Proof.
  intros A ltb eqb sfunc l1.
  induction l1 as [|a l1 IH]; intros y l2 Hirrefl Hantisym Heqb_sym
    Hstable Hlt.
  - simpl.
    apply stable_permut_refl.
  - unfold ord_all in Hstable, Hlt.
    inversion Hstable as [|? ? Hstable_head Hstable_tail]; subst.
    inversion Hlt as [|? ? Hlt_head Hlt_tail]; subst.
    destruct (sfunc a y) eqn:Hay_stable; [clear Hstable_head|contradiction].
    destruct (ltb y a) eqn:Hya; [clear Hlt_head|contradiction].

    assert (Htail :
      StablePermut ltb eqb sfunc
        (l1 ++ [y] ++ l2)
        (y :: l1 ++ l2)).
    {
      apply IH; assumption.
    }
    apply stable_permut_hd_cons with (a := a) in Htail.

    assert (Hswap :
      StablePermut ltb eqb sfunc
        (a :: y :: l1 ++ l2)
        (y :: a :: l1 ++ l2)).
    {
      apply stable_permut_step_implies_stable_permut.
      eapply stable_permut_swap with (tau1 := a) (tau2 := y)
        (l' := l1 ++ l2); try reflexivity.
      - destruct (ltb a y) eqn:Hay; [|reflexivity].
        unfold antisymmetric in Hantisym.
        pose proof (Hantisym a y Hay Hya) as Heq.
        unfold irreflexive in Hirrefl.
        rewrite (Hirrefl a y Heq) in Hay.
        discriminate.
      - destruct (eqb a y) eqn:Heq; [|reflexivity].
        unfold symmetric in Heqb_sym.
        rewrite Heqb_sym in Heq.
        unfold irreflexive in Hirrefl.
        rewrite (Hirrefl y a Heq) in Hya.
        discriminate.
      - exact Hay_stable.
    }
    eapply stable_permut_trans.
    + exact Htail.
    + exact Hswap.
Qed.

Lemma sorted_prefix_implies_ord_all_reverse:
  forall A (leb geb : A -> A -> bool) lfirst y lskip,
    transitive geb ->
    (forall x y, leb x y = true -> geb y x = true) ->
    Sorted_b leb (lfirst ++ y :: lskip) ->
    ord_all geb y lfirst.
Proof.
  intros A leb geb lfirst.
  induction lfirst as [|a lfirst IH]; intros y lskip Htrans Hflip Hsorted.
  - unfold ord_all. constructor.
  - simpl in Hsorted.
    unfold Sorted_b in Hsorted.
    inversion Hsorted as [|? ? Htail Hhead]; subst.
    specialize (IH y lskip Htrans Hflip Htail).
    unfold ord_all in IH |- *.
    constructor; [|exact IH].
    destruct lfirst as [|next lfirst].
    + inversion Hhead as [|? ? Hrel]; subst.
      rewrite (Hflip a y Hrel).
      trivial.
    + inversion Hhead as [|? ? Hrel]; subst.
      inversion IH as [|? ? Hy_next]; subst.
      destruct (geb y next) eqn:Hynext; [clear Hy_next|contradiction].
      pose proof (Hflip a next Hrel) as Hnext_a.
      unfold transitive in Htrans.
      rewrite (Htrans y next a Hynext Hnext_a).
      trivial.
Qed.

Lemma ord_all_but_nth_and_nth: 
    forall A ltb x n l a, 
        n < length l ->
        @ord_all A ltb x (remove_nth n l) -> 
        nth n l a = a -> 
        ltb x a -> 
        ord_all ltb x l.
Proof.
    intros.
    remember (remove_nth n l) as l'.
    symmetry in Heql'.
    eapply remove_nth_implies_splits with (x:=a) in Heql'; eauto.
    destruct Heql' as (Hl & Hl').
    unfold ord_all in H0.
    rewrite Hl' in H0.
    eapply Forall_app in H0; eauto.
    destruct H0 as (Hfirst & Hskip).
    rewrite Hl.
    eapply Forall_app; eauto.
    splits; eauto.
    simpl.
    eapply Forall_cons; eauto. 
    rewrite H2; eauto. 
Qed.

Lemma ord_all_remove_nth_ord_all: 
    forall A ltb x n l, 
        n < length l -> (** this is redundant*)
        @ord_all A ltb x l -> 
        ord_all ltb x (remove_nth n l).
Proof.
    intros.
    unfolds ord_all.
    remember (remove_nth n l) as l'.
    symmetry in Heql'.
    remember (nth n l x) as x'.
    symmetry in Heqx'.
    (* remember (nth n l ) *)
    eapply remove_nth_implies_splits in Heql'; eauto.
    destruct Heql' as (Hl & Hl').
    rewrite Hl'.
    rewrite Hl in H0.
    remember (firstn n l) as lf.
    remember (skipn (n+1) l) as ls. 
    eapply Forall_app in H0. 
    destruct H0.
    eapply Forall_app in H1.
    destruct H1.
    eapply Forall_app; splits; firstorder.
Qed.

Local Lemma total_not_combine_reverse_lt:
  forall A (ltb eqb : A -> A -> bool) x y,
    total ltb eqb ->
    combine_leb ltb eqb x y = false ->
    ltb y x = true.
Proof.
  intros A ltb eqb x y Htotal Hnot_le.
  unfold combine_leb in Hnot_le.
  apply orb_false_iff in Hnot_le.
  destruct Hnot_le as [Hnot_lt Hnot_eq].
  unfold total in Htotal.
  destruct (Htotal x y) as [Hlt | [Hgt | Heq]];
    congruence.
Qed.

Local Lemma ord_all_lt_from_lt_combine:
  forall A (ltb eqb : A -> A -> bool) a x xs,
    transitive ltb ->
    ltb_eqb_implies_ltb ltb eqb ->
    ltb a x = true ->
    ord_all (combine_leb ltb eqb) x xs ->
    ord_all ltb a xs.
Proof.
  intros A ltb eqb a x xs Htrans Hlt_eq Hax Hall.
  unfold ord_all in Hall |- *.
  rewrite !Forall_forall in Hall |- *.
  intros z Hin.
  specialize (Hall z Hin).
  unfold combine_leb in Hall.
  destruct (ltb x z || eqb x z) eqn:Hxz; [|contradiction].
  apply orb_true_iff in Hxz.
  destruct Hxz as [Hxz | Hxz].
  - unfold transitive in Htrans.
    rewrite (Htrans a x z Hax Hxz).
    trivial.
  - unfold ltb_eqb_implies_ltb in Hlt_eq.
    rewrite (Hlt_eq a x z Hax Hxz).
    trivial.
Qed.

Local Lemma ord_all_combine_of_lt:
  forall A (ltb eqb : A -> A -> bool) x xs,
    ord_all ltb x xs ->
    ord_all (combine_leb ltb eqb) x xs.
Proof.
  intros A ltb eqb x xs Hall.
  unfold ord_all in Hall |- *.
  rewrite !Forall_forall in Hall |- *.
  intros y Hin.
  specialize (Hall y Hin).
  destruct (ltb x y) eqn:Hxy; [|contradiction].
  unfold combine_leb.
  rewrite Hxy.
  trivial.
Qed.

Lemma select_helper_stable_permut_generic:
  forall A (ltb eqb sfunc sortb : A -> A -> bool),
    transitive ltb ->
    total ltb eqb ->
    reflexive eqb ->
    transitive eqb ->
    eqb_ltb_implies_ltb ltb eqb ->
    ltb_eqb_implies_ltb ltb eqb ->
    symmetric eqb ->
    irreflexive ltb eqb ->
    antisymmetric ltb eqb ->
    (forall lfirst y lskip,
      Sorted_b sortb (lfirst ++ y :: lskip) ->
      ord_all (fun y x => sfunc x y) y lfirst) ->
    forall r l x (n : nat) y l',
      Sorted_b sortb (l ++ r) ->
      nth n l x = x ->
      n < length l ->
      ord_all ltb x (firstn n l) ->
      ord_all (combine_leb ltb eqb) x (remove_nth n l) ->
      select_helper ltb eqb l x n r = (y, l') ->
      StablePermut ltb eqb sfunc (l ++ r) (y :: l').
Proof.
  intros A ltb eqb sfunc sortb
    Htrans Htotal Heqb_refl Heqb_trans Heqb_lt Hlt_eq Heqb_sym
    Hirrefl Hantisym Hprefix_stable r.
  induction r as [|a r IH];
    intros l x n y l' Hsorted Hnth Hbound Hprefix Hremain Hselect.
  - simpl in Hselect.
    inversion Hselect; subst.
    rewrite app_nil_r in Hsorted |- *.
    remember (remove_nth n l) as removed eqn:Hremoved.
    symmetry in Hremoved.
    apply remove_nth_implies_splits with (x := y) (x0 := y) in Hremoved;
      [|exact Hbound|exact Hnth].
    destruct Hremoved as [Hlist Hremoved].
    rewrite Hlist, Hremoved.
    eapply stable_permut_multi_skip_generic.
    + exact Hirrefl.
    + exact Hantisym.
    + exact Heqb_sym.
    + eapply Hprefix_stable with (lskip := skipn (n + 1) l).
      rewrite Hlist in Hsorted.
      simpl in Hsorted.
      exact Hsorted.
    + exact Hprefix.
  - simpl in Hselect.
    destruct (combine_leb ltb eqb x a) eqn:Hord.
    + unfold combine_leb in Hord.
      rewrite Hord in Hselect.
      assert (Hremove :
        remove_nth n (l ++ [a]) = remove_nth n l ++ [a]).
      {
        eapply remove_nth_app; eauto.
      }
      assert (Hremain_app :
        ord_all (combine_leb ltb eqb) x (remove_nth n (l ++ [a]))).
      {
        rewrite Hremove.
        unfold ord_all in Hremain |- *.
        apply Forall_app.
        split; [exact Hremain|].
        constructor; [unfold combine_leb; rewrite Hord; trivial|constructor].
      }
      assert (Hrec :
        StablePermut ltb eqb sfunc
          ((l ++ [a]) ++ r) (y :: l')).
      {
        eapply IH.
        - rewrite <- app_assoc.
          simpl.
          exact Hsorted.
        - rewrite app_nth1; [exact Hnth|lia].
        - rewrite app_length; simpl; lia.
        - rewrite firstn_app.
          replace (n - length l) with 0 by lia.
          simpl.
          rewrite app_nil_r.
          exact Hprefix.
        - exact Hremain_app.
        - exact Hselect.
      }
      rewrite <- app_assoc in Hrec.
      simpl in Hrec.
      exact Hrec.
    + pose proof Hord as Hnot_combine.
      unfold combine_leb in Hord.
      rewrite Hord in Hselect.
      pose proof
        (total_not_combine_reverse_lt A ltb eqb x a Htotal Hnot_combine)
        as Hax.
      assert (Hself : combine_leb ltb eqb x x = true).
      {
        unfold combine_leb.
        unfold reflexive in Heqb_refl.
        rewrite (Heqb_refl x), orb_true_r.
        reflexivity.
      }
      assert (Hall_x : ord_all (combine_leb ltb eqb) x l).
      {
        eapply ord_all_but_nth_and_nth; eauto.
      }
      pose proof
        (ord_all_lt_from_lt_combine A ltb eqb a x l
          Htrans Hlt_eq Hax Hall_x)
        as Hall_a_lt.
      pose proof
        (ord_all_combine_of_lt A ltb eqb a l Hall_a_lt)
        as Hall_a_le.
      assert (Hrec :
        StablePermut ltb eqb sfunc
          ((l ++ [a]) ++ r) (y :: l')).
      {
        eapply IH.
        - rewrite <- app_assoc.
          simpl.
          exact Hsorted.
        - rewrite app_nth2.
          replace (length l - length l) with 0 by lia.
          reflexivity.
          lia.
        - rewrite app_length; simpl; lia.
        - rewrite firstn_app, firstn_all, Nat.sub_diag.
          simpl.
          rewrite app_nil_r.
          exact Hall_a_lt.
        - rewrite remove_nth_length_append_one.
          exact Hall_a_le.
        - exact Hselect.
      }
      rewrite <- app_assoc in Hrec.
      simpl in Hrec.
      exact Hrec.
Qed.

Lemma select_helper_preserve_remain_sorted_generic:
  forall A (ltb eqb sortb : A -> A -> bool),
    transitive sortb ->
    forall r x l y n r',
      Sorted_b sortb (l ++ r) ->
      select_helper ltb eqb l x n r = (y, r') ->
      Sorted_b sortb r'.
Proof.
  intros A ltb eqb sortb Htrans r.
  induction r as [|a r IH]; intros x l y n r' Hsorted Hselect.
  - simpl in Hselect.
    inversion Hselect; subst.
    rewrite app_nil_r in Hsorted.
    eapply remove_nth_preserve_sorted; eauto.
  - simpl in Hselect.
    destruct (ltb x a || eqb x a) eqn:Hord.
    + eapply IH; [|exact Hselect].
      rewrite <- app_assoc.
      simpl.
      exact Hsorted.
    + eapply IH; [|exact Hselect].
      rewrite <- app_assoc.
      simpl.
      exact Hsorted.
Qed.

Lemma selsort_stable_permut_generic:
  forall A (ltb eqb sfunc sortb : A -> A -> bool),
    (forall x l y r,
      Sorted_b sortb (x :: l) ->
      select ltb eqb x l = (y, r) ->
      StablePermut ltb eqb sfunc (x :: l) (y :: r)) ->
    (forall x l y r,
      Sorted_b sortb (x :: l) ->
      select ltb eqb x l = (y, r) ->
      Sorted_b sortb r) ->
    forall n l,
      Sorted_b sortb l ->
      length l = n ->
      StablePermut ltb eqb sfunc l (selsort ltb eqb l n).
Proof.
  intros A ltb eqb sfunc sortb Hselect_stable Hselect_sorted n.
  induction n as [|n IH]; intros l Hsorted Hlength.
  - apply length_zero_iff_nil in Hlength.
    subst l.
    simpl.
    apply stable_permut_refl.
  - destruct l as [|x l]; [discriminate|].
    simpl.
    destruct (select ltb eqb x l) as [y r] eqn:Hselect.
    pose proof (Hselect_stable x l y r Hsorted Hselect) as Hstep.
    assert (Hrest_length : length r = n).
    {
      apply select_rest_length in Hselect.
      simpl in Hlength.
      lia.
    }
    assert (Hrest_sorted : Sorted_b sortb r).
    {
      exact (Hselect_sorted x l y r Hsorted Hselect).
    }
    pose proof (IH r Hrest_sorted Hrest_length) as Htail.
    apply stable_permut_hd_cons with (a := y) in Htail.
    eapply stable_permut_trans; eauto.
Qed.

Lemma select_helper_smallest: 
    forall A ltb eqb r l n x y l', 
        transitive ltb ->
        transitive eqb ->
        reflexive eqb -> 
        symmetric eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb -> 
        ltb_eqb_implies_ltb ltb eqb ->
        n < length l ->
        ord_all (combine_leb ltb eqb) x (remove_nth n l) -> 
        nth n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        ord_all (combine_leb ltb eqb) y l'.
Proof.
    induction r.
    {
        intros until l'; intros TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR; intros.
        unfold select_helper in H2. 
        inversion H2.
        subst; eauto.
    }
    {
        intros until l'; intros TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR; intros.
        unfold select_helper in H2. folds (@select_helper A).
        destruct ((ltb x a)||(eqb x a)) eqn:Hord; eauto.
        {
            {
                pose proof (IHr (l++[a]) n x y l' TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR).
                eapply H3; eauto.
                rewrite app_length; lia.
                {
                    remember (remove_nth n l) as ll.
                    symmetry in Heqll. 
                    pose proof (remove_nth_app A n l ll [a]).
                    rewrite H4; eauto. subst; eauto.
                    unfold ord_all. 
                    eapply Forall_app. 
                    splits.
                    {       
                        unfolds ord_all; eauto. 
                    }
                    {
                        eapply Forall_cons; eauto.
                        unfold combine_leb.
                        rewrite Hord; simpl; eauto.
                    }
                }
                rewrite app_nth1; eauto.   
            }
        }
        {
            {
                simpl in H2; eauto.

                pose proof (IHr (l++[a]) (length l) a y l' TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR).
                eapply H3; eauto.
                rewrite app_length; simpl; lia.
                {
                    (** transitivity *)
                    pose proof (TOTAL x a).
                    assert (ltb a x = true \/ eqb x a = true). {
                        clear - Hord H4.
                        eapply orb_false_iff in Hord.
                        destruct Hord.
                        rewrite H in H4; rewrite H0 in H4. 
                        firstorder.
                    }
                    clear H4 Hord.
                    rewrite remove_nth_length_append_one.
                    destruct H5.
                    {
                        (** transitivity *)
                        assert ((combine_leb ltb eqb) a x = true). {
                            unfold combine_leb.
                            rewrite H4. simpl; eauto.
                        }
                        eapply ord_all_trans with (a:=a) in H0; eauto.
                        eapply ord_all_but_nth_and_nth; eauto.
                        eapply transitive_combine_implies_transitive; eauto.
                    }
                    {
                        subst; eauto.
                        assert ((combine_leb ltb eqb) x a = true). {
                            unfold combine_leb.
                            eapply orb_true_iff.
                            right; eauto.
                        }
                        eapply ord_all_but_nth_and_nth in H0; eauto.
                        {
                            clear - H0 H4 H5 TRANS TRANS_EQ TRANSL TRANSR SYMM.
                            unfold ord_all.
                            eapply Forall_forall; intros.
                            unfold ord_all in H0.
                            eapply Forall_forall with (x:=x0) in H0; eauto.
                            destruct (combine_leb ltb eqb x x0) eqn:Hle.
                            {
                                assert (combine_leb ltb eqb a x0 = true).
                                {
                                    unfolds combine_leb.
                                    (* clear - Hle H4. *)
                                    eapply orb_true_iff in Hle.
                                    eapply orb_true_iff.
                                    destruct Hle.
                                    {
                                        left.
                                        unfold eqb_ltb_implies_ltb in TRANSL.
                                        unfold symmetric in SYMM.
                                        rewrite SYMM in H4.
                                        eapply TRANSL; eauto.
                                    }
                                    {
                                        right.
                                        unfold symmetric in SYMM.
                                        rewrite SYMM in H4.
                                        unfold transitive in TRANS_EQ.
                                        eapply TRANS_EQ; eauto.
                                    }    
                                }
                                rewrite H1; eauto.
                            }
                            {
                                contradiction.
                            }
                        }
                        {
                            clear - REFLEX.
                            unfold combine_leb.
                            eapply orb_true_iff.
                            right.
                            unfolds reflexive; eapply REFLEX.
                        }
                    }
                }
                rewrite app_nth2; eauto.
                replace (length l - length l) with 0; simpl; try lia; trivial.
            }        
        }
    }
Qed.

Lemma select_smallest: 
    forall A ltb eqb al x y bl, 
        transitive ltb ->
        transitive eqb ->
        reflexive eqb -> 
        symmetric eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb -> 
        ltb_eqb_implies_ltb ltb eqb ->
        @select A ltb eqb x al = (y, bl) -> 
        ord_all (combine_leb ltb eqb) y bl.
Proof. 
    intros.
    unfold select in H6.
    eapply select_helper_smallest in H6; eauto.
    {
        unfold ord_all; simpls; eauto. 
    }
Qed.

Lemma select_helper_in: 
    forall A ltb eqb r l x n y l', 
        n < length l ->
        @nth A n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        In y (l++r).
Proof.
    induction r.
    {
        intros.
        simpls; eauto.
        inv H1.
        rewrite app_nil_r.
        pose proof (@nth_In A n l y).
        eapply H1 in H; eauto.
        rewrite H0 in H; eauto.
    }
    {
        intros.
        simpls; eauto.
        des_ifH H1.
        {
            eapply IHr in H1; simpls; eauto.
            assert ((l++[a])++r = l++a::r). 
            {
                rewrite <- app_assoc.   
                simpl; eauto.
            }
            rewrite <- H2; eauto.
            rewrite app_length; try lia.
            rewrite app_nth1; eauto.
        }
        {
            eapply IHr in H1; simpls; eauto.
            assert ((l++[a])++r = l++a::r). 
            {
                rewrite <- app_assoc.   
                simpl; eauto.
            }
            rewrite <- H2; eauto.
            rewrite app_length; simpls; try lia. 
            rewrite app_nth2; eauto.
            replace (length l - length l) with 0; try lia. 
            simpls; eauto.
        }
    }
Qed.

Lemma select_in: 
    forall A ltb eqb al x y bl,
        @select A ltb eqb x al = (y, bl) -> 
        In y (x :: al).
Proof.
    intros.
    unfolds select.    
    eapply select_helper_in in H; eauto.
Qed.

Lemma cons_of_small_maintains_sort: 
    forall A ltb eqb x bl n, 
    n = length bl -> 
    @ord_all A (combine_leb ltb eqb) x bl -> 
    Sorted_b (combine_leb ltb eqb) (selsort ltb eqb bl n) -> 
    Sorted_b (combine_leb ltb eqb) (x :: selsort ltb eqb bl n).
Proof.
    intros.
    unfolds Sorted_b.
    eapply Sorted_cons; eauto.
    destruct (selsort ltb eqb bl n) eqn:Hselsort; eauto.

    eapply ord_all_ord_one in H0; eauto.
    unfolds selsort.
    destruct n eqn:Hn; eauto.
    {
        symmetry in H.
        eapply length_zero_iff_nil in H.
        rewrite H in Hselsort. 
        discriminate.
    }
    {
        destruct bl eqn:Hbl; simpls; try discriminate.
        destruct (select ltb eqb a0 l0) as (y, r') eqn:Hselect.
        folds (@selsort A).
        eapply select_in in Hselect.
        inv Hselsort.
        eauto.
    }
Qed.

Lemma selsort_sorted: 
    forall A ltb eqb n al,
    transitive ltb ->
    transitive eqb ->
    reflexive eqb -> 
    symmetric eqb -> 
    @total A ltb eqb ->
    eqb_ltb_implies_ltb ltb eqb -> 
    ltb_eqb_implies_ltb ltb eqb ->
    n = length al -> 
    Sorted_b (combine_leb ltb eqb) (@selsort A ltb eqb al n).
Proof. 
    intros until ltb.
    induction n.
    { (** n = 0*)
        intro; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR; intros.
        symmetry in H.
        rewrite length_zero_iff_nil in H.
        subst.
        unfolds selsort. 
        unfolds Sorted_b.
        eapply Sorted_nil; eauto.
    }
    { (** n = S O *)
        intro; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR; intros.
        remember (selsort ltb eqb al (S n)) as bl.
        assert (al <> []). {
            intro.
            symmetry in H.
            eapply length_zero_iff_nil in H0.
            rewrite H in H0.
            discriminate.
        }
        assert (exists hd tl, al = hd :: tl). 
        {
            destruct al; eauto; try discriminate.
        }
        destruct H1 as (hd & tl & Hal); eauto.
        unfold selsort in Heqbl.
        rewrite Hal in Heqbl. folds (@selsort A). 
        destruct (select ltb eqb hd tl) as (y, r') eqn:Hal'.
        remember (selsort ltb eqb r' n) as bl'.
        assert (n = length r'). {
            pose proof Hal'.
            eapply select_rest_length in Hal'.
            rewrite <- Hal'.
            rewrite Hal in H. unfold length in H. inversion H. subst; eauto.
        }
        pose proof (IHn r' TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR H1).
        rewrite <- Heqbl' in H2.
        eapply select_smallest in Hal'; eauto.
        eapply cons_of_small_maintains_sort in Hal'; eauto. 
        subst; eauto.
    }
Qed.

Lemma selection_sort_sorted: 
    forall A ltb eqb al, 
    transitive ltb ->
    transitive eqb ->
    reflexive eqb -> 
    symmetric eqb -> 
    @total A ltb eqb ->
    eqb_ltb_implies_ltb ltb eqb -> 
    ltb_eqb_implies_ltb ltb eqb ->
    Sorted_b (combine_leb ltb eqb) (@SelectionSort A ltb eqb al).
Proof. 
    intros until al; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR.
    remember (SelectionSort ltb eqb al) as bl.
    unfolds SelectionSort.
    pose proof (selsort_sorted A ltb eqb (length al) al).
    rewrite <- Heqbl in H.
    eauto.
Qed.

Theorem selection_sort_is_correct: 
    forall A ltb eqb al bl, 
    transitive ltb ->
    transitive eqb ->
    reflexive eqb -> 
    symmetric eqb -> 
    @total A ltb eqb ->
    eqb_ltb_implies_ltb ltb eqb -> 
    ltb_eqb_implies_ltb ltb eqb ->
    @SelectionSort A ltb eqb al = bl -> 
    (
        Permutation al bl /\
        Sorted_b (combine_leb ltb eqb) bl
    ).
Proof.
    intros until bl; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR; intros. splits.
    pose proof (selection_sort_perm A ltb eqb al).
    subst; eauto.
    pose proof (selection_sort_sorted A ltb eqb al).
    subst; eauto.
Qed.
