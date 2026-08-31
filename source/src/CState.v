Require Import Bool.
Require Import List.
Require Import Coqlib.
Require Import Csem.
Require Import Memory.
Require Import StateTy.
Require Import PolyBase.
Require Import Values.
Require Import Maps.
Require Import AST.
Require Import Globalenvs.
Require Import Ctypes.
Require Import ZArith.
Require Import LibTactics.
Require Import TyTy.
Require Import CTy.
Require Import Cop.
Require Import Linalg.
Require Import Lia.
Require Import sflib.

Module CState <: STATE.

    Module Ty := CTy.
    Definition state: Type := (genv * env * mem)%type.
    Definition mkState (ge: genv) (e: env) (m: mem) := (ge,e,m). 
    Definition t := state.

    Definition dummy_state:t := 
        mkState 
          {| genv_genv := (Genv.empty_genv Csyntax.fundef Ctypes.type []);
             genv_cenv := (PTree.empty composite) |}
          (Csem.empty_env) 
          (Mem.empty).

    Definition get_var_loc_type (st: t) (id: ident): option (block * Ctypes.type) :=
        let '(ge, e, m) := st in
        match e!id with
        | Some (b, ty) => Some (b, ty)
        | None => match Genv.find_var_info ge.(genv_genv) id, Genv.find_symbol ge.(genv_genv) id with 
                | Some def, Some b => Some (b, def.(gvar_info))
                | _, _ => None
                end
        end.

      Lemma get_var_loc_type_disregard_mem:
        forall ge e m m' id b ty,
          get_var_loc_type (ge, e, m) id = Some (b, ty) ->
          get_var_loc_type (ge, e, m') id = Some (b, ty).
      Proof. 
        intros. simpls.
        destruct (e!id); tryfalse; trivial. 
      Qed.
  
  
    (* State records values of *)
    (* 1. symbolic constants, like M/N, those invariants (not being written) inside loop nests *)
    (* 2. arrays, like alpha, beta, arr[][], they are written inside loop nests *)
    (* Note that state do not record values for "iterators". iterators are nameless at instruction level *)
    (* and should be allocated with fresh ident after codegen back to structural representation like Csyntax. *)
    (* Even though the state still records values for "ident" that was iterator. They are no longer iterator now. We could just regard them as symbolic constants. *)
    Definition mem_eq (m m': mem): Prop := 
        Mem.extends m m' /\ Mem.extends m' m.

    Lemma mem_eq_sym:
        forall m m', mem_eq m m' -> mem_eq m' m.
    Proof. intros. unfolds mem_eq. tauto. Qed.

    Lemma mem_eq_trans:
        forall m1 m2 m3, mem_eq m1 m2 -> mem_eq m2 m3 -> mem_eq m1 m3.
    Proof.
      intros. unfolds mem_eq. destruct H as (H1 & H2). destruct H0 as (H3 & H4). split.
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
    Qed.

    Lemma mem_eq_refl:
        forall m, mem_eq m m.
    Proof. intros. split. all: eapply Mem.extends_refl. Qed.

    Lemma mem_eq_prsv_valid_access:
      forall m m' chunk b ofs p,
        mem_eq m m' ->
          Mem.valid_access m chunk b ofs p ->
          Mem.valid_access m' chunk b ofs p.
    Proof. intros. destruct H. eapply Mem.valid_access_extends; eauto. Qed.


    Lemma mem_eq_prsv_next_block:
      forall m m',
        mem_eq m m' ->
        Mem.nextblock m = Mem.nextblock m'.
    Proof.
      intros. destruct H. inv H; trivial.
    Qed.

    Lemma mem_eq_prsv_perm:
      forall m m' b ofs k p,
        mem_eq m m' ->
        Mem.perm m b ofs k p ->
        Mem.perm m' b ofs k p.
    Proof. 
      intros. destruct H. 
      eapply Mem.perm_extends; eauto.
    Qed.

    Lemma mem_eq_prsv_contents:
      forall m m',
        mem_eq m m' ->
        forall b ofs, 
          Mem.perm m b ofs Cur Readable ->
          ZMap.get ofs ((Mem.mem_contents m)!!b) = ZMap.get ofs ((Mem.mem_contents m')!!b).
    Proof. 
      intros. rename H0 into Hread. destruct H.
      inv H. inv H0. clear - Hread mext_inj mext_inj0.
      unfolds inject_id.
      inv mext_inj. inv mext_inj0.
      assert (Mem.perm m' b ofs Cur Readable). {
        pose proof (mi_perm b b 0 ofs Cur Readable). 
        replace (ofs + 0) with ofs in H; try lia.
        eapply H; trivial.
      }
      eapply mi_memval in Hread; eauto.
      eapply mi_memval0 in H; eauto.
      replace (ofs + 0) with ofs in Hread; try lia.
      replace (ofs + 0) with ofs in H; try lia.
      inv Hread; inv H; tryfalse; eauto.
      {
        inv H2; inv H5; tryfalse; eauto.
        - inv H; inv H2; simpls.
          rewrite Integers.Ptrofs.add_zero; trivial.
        - rewrite <- H1 in H3. inv H3. trivial. 
      }
    Qed. 

    Lemma setN_inside_nth:
      forall vl ofs ofs' c,
        ofs' <= ofs < ofs' + Z.of_nat (length vl) ->
        ZMap.get ofs (Mem.setN vl ofs' c) = 
        nth (Z.to_nat (ofs - ofs')) vl (fst c).
    Proof.
      induction vl.
      - intros. simpls. lia.
      - intros. simpls.
      destruct (ofs - ofs') eqn:Hdelter; simpls; tryfalse; try lia.
      {
        assert (ofs = ofs'). lia. subst.
        rewrite Mem.setN_outside; try lia.
        eapply ZMap.gss.
      }
      {
        rewrite IHvl; simpls; try lia.
        remember (ofs - ofs') as delta.
        replace (ofs - (ofs' + 1)) with (delta - 1); try lia.
        assert (delta > 0). lia. 
        destruct (Z.to_nat (delta-1)) eqn:Hn; simpls; 
        destruct (Pos.to_nat p) eqn:Hp; simpls; try lia.
        - 
        assert (delta = 1). lia. subst. rewrite H1 in Hdelter.
        inv Hdelter. inv Hp. trivial.
        - 
        assert (n0 = S n). lia. subst; trivial.
      }  
    Qed.

    Local Lemma pmap_set_commute :
      forall (A : Type) (i j : positive) (x y : A) (m : PMap.t A),
        i <> j ->
        PMap.set i x (PMap.set j y m) =
        PMap.set j y (PMap.set i x m).
    Proof.
      intros A i j x y [default tree] Hneq.
      unfold PMap.set; simpl.
      f_equal.
      apply PTree.extensionality.
      intros key.
      rewrite !PTree.gsspec.
      destruct (peq key i), (peq key j); subst; try congruence; reflexivity.
    Qed.

    Local Lemma zmap_set_commute :
      forall (A : Type) (i j : Z) (x y : A) (m : ZMap.t A),
        i <> j ->
        ZMap.set i x (ZMap.set j y m) =
        ZMap.set j y (ZMap.set i x m).
    Proof.
      intros A i j x y m Hneq.
      unfold ZMap.set.
      apply pmap_set_commute.
      intro Hindices.
      apply Hneq.
      apply ZIndexed.index_inj.
      exact Hindices.
    Qed.

    Local Lemma setN_set_outside :
      forall (values : list memval) start point value
             (contents : ZMap.t memval),
        (point < start \/
         point >= start + Z.of_nat (length values)) ->
        Mem.setN values start (ZMap.set point value contents) =
        ZMap.set point value (Mem.setN values start contents).
    Proof.
      induction values as [|head values IH];
        intros start point value contents Houtside.
      - reflexivity.
      - simpl in *.
        rewrite zmap_set_commute by lia.
        rewrite IH by lia.
        reflexivity.
    Qed.

    Local Lemma setN_disjoint_commute :
      forall values1 values2 start1 start2 (contents : ZMap.t memval),
        (start1 + Z.of_nat (length values1) <= start2 \/
         start2 + Z.of_nat (length values2) <= start1) ->
        Mem.setN values2 start2 (Mem.setN values1 start1 contents) =
        Mem.setN values1 start1 (Mem.setN values2 start2 contents).
    Proof.
      induction values2 as [|head values2 IH];
        intros start1 start2 contents Hdisjoint.
      - reflexivity.
      - simpl in *.
        rewrite <- setN_set_outside by lia.
        rewrite IH by lia.
        reflexivity.
    Qed.

    Local Lemma store_preserves_mem_eq :
      forall chunk m1 m2 b ofs value m1',
        mem_eq m1 m2 ->
        Mem.store chunk m1 b ofs value = Some m1' ->
        exists m2',
          Mem.store chunk m2 b ofs value = Some m2' /\
          mem_eq m1' m2'.
    Proof.
      intros chunk m1 m2 b ofs value m1'
             [Hforward Hbackward] Hstore1.
      destruct
        (Mem.store_within_extends
           chunk m1 m2 b ofs value m1' value
           Hforward Hstore1 (Val.lessdef_refl value))
        as [m2' [Hstore2 Hresult_forward]].
      destruct
        (Mem.store_within_extends
           chunk m2 m1 b ofs value m2' value
           Hbackward Hstore2 (Val.lessdef_refl value))
        as [m1'' [Hstore1' Hresult_backward]].
      rewrite Hstore1 in Hstore1'.
      inversion Hstore1'; subst m1''.
      exists m2'.
      split; [exact Hstore2|].
      split; assumption.
    Qed.

    Local Lemma disjoint_store_commute :
      forall chunk m b1 ofs1 v1 m1 b2 ofs2 v2 m12 m2 m21,
        Mem.store chunk m b1 ofs1 v1 = Some m1 ->
        Mem.store chunk m1 b2 ofs2 v2 = Some m12 ->
        Mem.store chunk m b2 ofs2 v2 = Some m2 ->
        Mem.store chunk m2 b1 ofs1 v1 = Some m21 ->
        (b1 <> b2 \/
         ofs1 + size_chunk chunk <= ofs2 \/
         ofs2 + size_chunk chunk <= ofs1) ->
        m12 = m21.
    Proof.
      intros chunk m b1 ofs1 v1 m1 b2 ofs2 v2 m12 m2 m21
             Hstore1 Hstore12 Hstore2 Hstore21 Hdisjoint.
      assert (Hcontents : Mem.mem_contents m12 = Mem.mem_contents m21).
      {
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore12).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore1).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore21).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore2).
        destruct (peq b1 b2) as [Heq|Hneq].
        - subst b2.
          rewrite !PMap.gss, !PMap.set2.
          f_equal.
          apply setN_disjoint_commute.
          destruct Hdisjoint as [Hneq|Hoffsets]; [contradiction|].
          rewrite !encode_val_length, <- !size_chunk_conv.
          exact Hoffsets.
        - rewrite !PMap.gso by congruence.
          apply pmap_set_commute.
          congruence.
      }
      assert (Haccess : Mem.mem_access m12 = Mem.mem_access m21).
      {
        rewrite (Mem.store_access _ _ _ _ _ _ Hstore12).
        rewrite (Mem.store_access _ _ _ _ _ _ Hstore1).
        rewrite (Mem.store_access _ _ _ _ _ _ Hstore21).
        rewrite (Mem.store_access _ _ _ _ _ _ Hstore2).
        reflexivity.
      }
      assert (Hnext : Mem.nextblock m12 = Mem.nextblock m21).
      {
        rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore12).
        rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore1).
        rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore21).
        rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore2).
        reflexivity.
      }
      destruct m12 as
          [contents12 access12 next12 max12 noaccess12 default12].
      destruct m21 as
          [contents21 access21 next21 max21 noaccess21 default21].
      simpl in Hcontents, Haccess, Hnext.
      apply Mem.mkmem_ext; assumption.
    Qed.


    Lemma swap_store_cell_neq_prsv_mem_eq:
      forall m0 b1 ofs1 v1 m1' m1 b2 ofs2 v2 m2' m0' m1x' m1x m2x' chunk,
        Mem.store chunk m0 b1 ofs1 v1 = Some m1' ->
        Mem.store chunk m1 b2 ofs2 v2 = Some m2' ->
        Mem.store chunk m0' b2 ofs2 v2 = Some m1x' ->
        Mem.store chunk m1x b1 ofs1 v1 = Some m2x' ->
        mem_eq m0 m0' ->
        mem_eq m1 m1' ->
        mem_eq m1x m1x' ->
        (b1 <> b2 \/ ofs1 + (size_chunk chunk) <= ofs2 \/ ofs2 + (size_chunk chunk) <= ofs1 ) ->
        mem_eq m2' m2x'.
    Proof.
      intros m0 b1 ofs1 v1 m1' m1 b2 ofs2 v2 m2'
             m0' m1x' m1x m2x' chunk
             Hstore1 Hstore2 Hstore2x Hstore1x
             Hbase_eq Hafter1_eq Hafter2_eq Hdisjoint.
      destruct
        (store_preserves_mem_eq
           chunk m1 m1' b2 ofs2 v2 m2' Hafter1_eq Hstore2)
        as [m12 [Hstore12 Hresult12_eq]].
      destruct
        (store_preserves_mem_eq
           chunk m1x m1x' b1 ofs1 v1 m2x' Hafter2_eq Hstore1x)
        as [m21 [Hstore21 Hresult21_eq]].
      destruct
        (store_preserves_mem_eq
           chunk m0 m0' b1 ofs1 v1 m1' Hbase_eq Hstore1)
        as [m1_on_right [Hstore1_right Hafter1_right_eq]].
      destruct
        (store_preserves_mem_eq
           chunk m1' m1_on_right b2 ofs2 v2 m12
           Hafter1_right_eq Hstore12)
        as [m12_on_right [Hstore12_right Hresult12_right_eq]].
      pose proof
        (disjoint_store_commute
           chunk m0' b1 ofs1 v1 m1_on_right b2 ofs2 v2
           m12_on_right m1x' m21
           Hstore1_right Hstore12_right Hstore2x Hstore21 Hdisjoint)
        as Hcommute.
      eapply mem_eq_trans; [exact Hresult12_eq|].
      eapply mem_eq_trans; [exact Hresult12_right_eq|].
      rewrite Hcommute.
      apply mem_eq_sym.
      exact Hresult21_eq.
    Qed.

    Definition eq (st st': t): Prop := 
        let '(ge, env, m) := st in
        let '(ge', env', m') := st' in
        ge = ge' /\ env = env' /\ mem_eq m m'.

    Lemma eq_sym:
        forall st st', eq st st' -> eq st' st.
    Proof. intros. unfolds eq. 
      destruct st as [[ge e] m]. destruct st' as [[ge' e'] m'].
      destruct H as (Hge & He & Hmf & Hmb).
      splits; subst; trivial. 
      unfold mem_eq; split; trivial.
    Qed.

    Lemma eq_refl:
        forall st, eq st st.
    Proof.
        intros. unfold eq. destruct st eqn:Hst; destruct p eqn:Hp; splits; trivial.
        unfold mem_eq. split.
        all: eapply Mem.extends_refl.
    Qed.

    Lemma eq_trans:
        forall st1 st2 st3, eq st1 st2 -> eq st2 st3 -> eq st1 st3.
    Proof. 
      intros. 
      destruct st1 as [[ge1 e1] m1]. 
      destruct st2 as [[ge2 e2] m2]. 
      destruct st3 as [[ge3 e3] m3].
      unfolds eq. 
      destruct H as (Hge1 & He1 & Hmf & Hmb).
      destruct H0 as (Hge2 & He2 & Hmf' & Hmb').
      splits; subst; eauto. unfold mem_eq. split.
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
    Qed.      

    Lemma advance_store_valid:
      forall chunk1 m1 b1 ofs1 v1 chunk2 m2 b2 ofs2 v2 m3 m2',
        Mem.store chunk1 m1 b1 ofs1 v1 = Some m2 ->
        mem_eq m2 m2' ->
        Mem.store chunk2 m2' b2 ofs2 v2 = Some m3 ->
        exists m2'',
          Mem.store chunk2 m1 b2 ofs2 v2 = Some m2''.
    Proof.
      intros.
      eapply Mem.store_valid_access_2 
        with (chunk':=chunk2) (b':=b2) (ofs':=ofs2) (p:=Writable) in H.
      eapply Mem.valid_access_store with (v:=v2) in H. destruct H. 
      exists x; trivial.
      eapply Mem.store_valid_access_3 in H1.
      destruct H0 as (_ & B).
      eapply Mem.valid_access_extends; eauto.
    Qed.

    Fixpoint calc_offset_helper (bounds subs: list Z) (sz: Z): option Z :=
        match bounds, subs with
        | [], [] => Some 0%Z
        | b::bounds', s::subs' => 
            if (b <=? s)%Z then None else
            match calc_offset_helper bounds' subs' (sz * b) with
            | None => None
            | Some ofs => Some (ofs + sz * s)%Z
            end
        | _, _ => None
        end
    .

    Definition calc_offset (ty: CTy.arrtype) (sub: list Z): option Z := 
      match ty with
      | CTy.arr_type_intro ty bounds =>
        if Nat.eqb (length bounds) (length sub) 
          && forallb (fun bd => (bd >? 0)%Z) bounds
          && forallb (fun s => (s >=? 0)%Z) sub
        then
          calc_offset_helper (List.rev bounds) (List.rev sub) (CTy.basetype_size ty)
        else None
      end
    .

    Local Lemma calc_offset_success_facts :
      forall basety bounds sub ofs,
        calc_offset (CTy.arr_type_intro basety bounds) sub = Some ofs ->
        length bounds = length sub /\
        Forall (fun bound => (bound > 0)%Z) (rev bounds) /\
        Forall (fun index => (index >= 0)%Z) (rev sub) /\
        calc_offset_helper
          (rev bounds) (rev sub) (CTy.basetype_size basety) = Some ofs.
    Proof.
      intros basety bounds sub ofs Hcalc.
      unfold calc_offset in Hcalc; simpl in Hcalc.
      destruct
        (Nat.eqb (length bounds) (length sub) &&
         forallb (fun bound => (bound >? 0)%Z) bounds &&
         forallb (fun index => (index >=? 0)%Z) sub)
        eqn:Hchecks; try discriminate.
      do 2 rewrite andb_true_iff in Hchecks.
      destruct Hchecks as [[Hlength Hbounds] Hindices].
      apply Nat.eqb_eq in Hlength.
      repeat split.
      - exact Hlength.
      - apply Forall_forall.
        intros bound Hin.
        apply forallb_forall with (x := bound) in Hbounds.
        + lia.
        + apply in_rev. exact Hin.
      - apply Forall_forall.
        intros index Hin.
        apply forallb_forall with (x := index) in Hindices.
        + lia.
        + apply in_rev. exact Hin.
      - exact Hcalc.
    Qed.

    Example calc_offset_example:
        calc_offset (CTy.arr_type_intro (CTy.int32s) [10;10;10]%Z) [1;2;3]%Z = Some 492%Z.
        (* 3*4 + 2*(10*4) + (1*(10*10*4))*)
    Proof. simpl. reflexivity. Qed.

    
    Lemma calc_offset_helper_same_bounds_same_length:
      forall bounds sub1 sub2 sz ofs1 ofs2,
        calc_offset_helper bounds sub1 sz = Some ofs1 ->
        calc_offset_helper bounds sub2 sz = Some ofs2 ->
        length sub1 = length sub2.
    Proof. 
      induction bounds.
      - intros. simpls. destruct sub1; destruct sub2; tryfalse. trivial.
      - intros. simpls.
        destruct sub1 eqn:Hsub1; tryfalse. 
        destruct sub2 eqn:Hsub2; tryfalse.
        destruct (a <=? z); destruct (a <=? z0); tryfalse.
        destruct (calc_offset_helper bounds l (sz * a)) eqn:Hofs1; tryfalse.
        destruct (calc_offset_helper bounds l0 (sz * a)) eqn:Hofs2; tryfalse.
        simpls. f_equal. 
        eapply IHbounds; eauto.
    Qed. 


    Lemma calc_offset_helper_correct:
      forall bounds sub1 sub2 sz ofs1 ofs2,
        calc_offset_helper bounds sub1 sz = Some ofs1 ->
        calc_offset_helper bounds sub2 sz = Some ofs2 ->
        ~ sub1 =v= sub2 ->
        Forall (fun bd => (bd > 0)%Z) bounds ->
        Forall (fun s1 => (s1 >= 0)%Z) sub1 ->
        Forall (fun s2 => (s2 >= 0)%Z) sub2 ->
        sz > 0 ->
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1.
    Proof.
      induction bounds as [|bound bounds IH];
        intros sub1 sub2 sz ofs1 ofs2
               Hcalc1 Hcalc2 Hneq Hbounds Hsub1 Hsub2 Hsz.
      - simpl in Hcalc1, Hcalc2.
        destruct sub1, sub2; try discriminate.
        exfalso. apply Hneq. apply veq_refl.
      - destruct sub1 as [|index1 tail1], sub2 as [|index2 tail2];
          simpl in Hcalc1, Hcalc2; try discriminate.
        destruct (bound <=? index1)%Z eqn:Hindex1; try discriminate.
        destruct (bound <=? index2)%Z eqn:Hindex2; try discriminate.
        destruct (calc_offset_helper bounds tail1 (sz * bound))
          as [tail_offset1|] eqn:Htail1; try discriminate.
        destruct (calc_offset_helper bounds tail2 (sz * bound))
          as [tail_offset2|] eqn:Htail2; try discriminate.
        inversion Hcalc1; inversion Hcalc2; subst ofs1 ofs2.
        inversion Hbounds as [|? ? Hbound Hbounds_tail]; subst.
        inversion Hsub1 as [|? ? Hnonneg1 Hsub1_tail]; subst.
        inversion Hsub2 as [|? ? Hnonneg2 Hsub2_tail]; subst.
        apply Z.leb_gt in Hindex1, Hindex2.
        destruct (is_eq tail1 tail2) eqn:Htails.
        + assert (Htails_eq : tail1 =v= tail2).
          { unfold veq. exact Htails. }
          assert (Htail_lists : tail1 = tail2).
          {
            apply same_length_eq.
            - eapply calc_offset_helper_same_bounds_same_length; eauto.
            - exact Htails_eq.
          }
          subst tail2.
          rewrite Htail1 in Htail2.
          inversion Htail2; subst tail_offset2.
          assert (Hindices_neq : index1 <> index2).
          {
            intro Heq. subst index2.
            apply Hneq.
            unfold veq; simpl.
            rewrite Z.eqb_refl.
            exact Htails_eq.
          }
          destruct (Z.lt_trichotomy index1 index2) as [Hlt|[Heq|Hgt]];
            [left|contradiction|right]; nia.
        + assert (Htails_neq : ~ tail1 =v= tail2).
          {
            unfold veq. intro Htails_eq.
            rewrite Htails_eq in Htails. discriminate.
          }
          specialize
            (IH tail1 tail2 (sz * bound) tail_offset1 tail_offset2
                Htail1 Htail2 Htails_neq Hbounds_tail
                Hsub1_tail Hsub2_tail ltac:(nia)).
          destruct IH as [Htail_order|Htail_order];
            [left|right]; nia.
    Qed.

    

    Lemma calc_offset_different_sub_implies_disjoint:
      forall aty chunk sub1 sub2 ofs1 ofs2,
        calc_offset aty sub1 = Some ofs1 ->
        calc_offset aty sub2 = Some ofs2 ->
        ~ veq sub1 sub2 ->
        CTy.basetype_access_mode (CTy.basetype_of_arrtype aty) = By_value chunk ->
        (ofs1 + size_chunk chunk <= ofs2)%Z \/ (ofs2 + size_chunk chunk <= ofs1)%Z.
    Proof.
      intros [basety bounds] chunk sub1 sub2 ofs1 ofs2
             Hcalc1 Hcalc2 Hsubscripts_neq Hmode.
      pose proof
        (calc_offset_success_facts
           basety bounds sub1 ofs1 Hcalc1)
        as [Hlength1 [Hbounds [Hindices1 Hhelper1]]].
      pose proof
        (calc_offset_success_facts
           basety bounds sub2 ofs2 Hcalc2)
        as [Hlength2 [_ [Hindices2 Hhelper2]]].
      simpl in Hmode.
      apply CTy.basety_size_eq_size_chunk in Hmode.
      rewrite Hmode in Hhelper1, Hhelper2.
      eapply calc_offset_helper_correct; eauto.
      - intro Hreversed_eq.
        apply Hsubscripts_neq.
        apply veq_implies_rev_veq in Hreversed_eq.
        rewrite !rev_involutive in Hreversed_eq.
        exact Hreversed_eq.
        rewrite !rev_length, <- Hlength1, <- Hlength2.
        reflexivity.
      - unfold CTy.basetype_size in Hmode.
        destruct basety; simpl in Hmode; lia.
    Qed.

    Definition valid (id: ident) (ty: Ty.t) (st: t): Prop := 
      let '(ge, e, m) := st in
      forall b ty', 
        get_var_loc_type st id = Some (b, ty') /\
        Ty.of_compcert_arrtype ty' = Some ty /\
        Mem.range_perm m b 0 (sizeof ge ty') Cur Writable. 


    Inductive read_cell: MemCell -> Ty.basetype -> val -> t -> Prop :=
    | read_cell_intro: 
        forall cell v st id sub ge e m b ty ofs ty' basety chunk,
            cell = {| arr_id := id; arr_index := sub |} ->
            get_var_loc_type st id = Some (b, ty) ->
            st = (ge, e, m) ->
            CTy.of_compcert_arrtype ty = Some ty' ->
            CTy.basetype_of_arrtype ty' = basety -> 
            (* no semantics cast at this level *)
            calc_offset ty' sub = Some ofs ->
            CTy.basetype_access_mode basety = By_value chunk -> 
            Mem.load chunk m b ofs = Some v ->
            read_cell cell basety v st
    .

    Definition write_cell_dec (cell: MemCell) (basety: Ty.basetype) (v: val) (st: t): option t := 
        let '(ge, e, m) := st in
        let arr_id := cell.(arr_id) in
        let sub := cell.(arr_index) in
        let blk_ty := get_var_loc_type st arr_id
        in
        match blk_ty with
        | None => None
        | Some (b, ty) =>
            match CTy.of_compcert_arrtype ty with
            | Some ty' => 
                if CTy.basetype_eqb (CTy.basetype_of_arrtype ty') basety
                then 
                    match calc_offset ty' sub with
                    | None => None
                    | Some ofs => 
                        match CTy.basetype_access_mode basety with
                        | By_value chunk => 
                            match Mem.store chunk m b ofs v with
                            | None => None
                            | Some m' => Some (ge, e, m')
                            end
                        | _ => None
                        end
                    end
                else None
            | None => None
            end
        end
    .

    Inductive write_cell: MemCell -> Ty.basetype -> val -> t -> t -> Prop :=
    | write_cell_intro: 
        forall cell v st st' st0 st0' id sub ge e m m' b ty ofs ty' basety chunk,
            cell = {| arr_id := id; arr_index := sub |} ->
            st = (ge, e, m) ->
            get_var_loc_type st id = Some (b, ty) ->
            CTy.of_compcert_arrtype ty = Some ty' ->
            CTy.basetype_of_arrtype ty' = basety -> 
            (* no semantics cast at this level *)
            calc_offset ty' sub = Some ofs ->
            CTy.basetype_access_mode basety = By_value chunk -> 
            Mem.store chunk m b ofs v = Some m' ->
            st' = (ge, e, m') ->
            eq st st0 ->
            eq st' st0' ->
            write_cell cell basety v st0 st0'
    .

    Lemma write_cell_dec_correct:
        forall cell v st st' bty,
            write_cell_dec cell bty v st = Some st' -> write_cell cell bty v st st'.
    Proof.
      intros.
      unfold write_cell_dec in H.
      destruct st as [[ge e] m].
      destruct (get_var_loc_type (ge, e, m) (arr_id cell)) eqn:Heid; tryfalse.
      destruct p as (b, ty).
      destruct (CTy.of_compcert_arrtype ty) eqn:Hty; simpls; tryfalse.
      rename a into ty'.
      destruct (CTy.basetype_eqb (CTy.basetype_of_arrtype ty') bty) eqn:Hbty; simpls; tryfalse.
      destruct (calc_offset ty' (arr_index cell)) eqn:Hofs; simpls; tryfalse.
      destruct (CTy.basetype_access_mode bty) eqn:Hchunk; simpls; tryfalse.
      rename m0 into chunk.
      destruct (Mem.store chunk m b z v) eqn:Hm'; simpls; tryfalse.
      inv H.
      destruct cell eqn:Hcell; simpls.
      econs; eauto.
      eapply CTy.basetype_eqb_eq in Hbty; trivial.
      eapply eq_refl.
      eapply eq_refl.
    Qed.


        (* It would be easy to further weaken this condition retricting only on free vars of the fragment, no imposing non-aliasing on invisible programs. *)
    (* Of little significance, so we currently omit. *)
    Definition non_alias  (st: t): Prop :=
        forall id1 id2 b1 b2 (ty1 ty2: Ctypes.type),
          (* List.In id1 vars -> List.In id2 vars -> *)
          get_var_loc_type st id1 = Some (b1, ty1) ->
          get_var_loc_type st id2 = Some (b2, ty2) ->
          id1 <> id2 -> 
          b1 <> b2.

    Local Lemma cell_neq_implies_disjoint_access :
      forall st id1 id2 sub1 sub2 b1 b2 ty1 ty2 aty1 aty2
             ofs1 ofs2 chunk1 chunk2,
        get_var_loc_type st id1 = Some (b1, ty1) ->
        get_var_loc_type st id2 = Some (b2, ty2) ->
        CTy.of_compcert_arrtype ty1 = Some aty1 ->
        CTy.of_compcert_arrtype ty2 = Some aty2 ->
        calc_offset aty1 sub1 = Some ofs1 ->
        calc_offset aty2 sub2 = Some ofs2 ->
        CTy.basetype_access_mode (CTy.basetype_of_arrtype aty1) =
          By_value chunk1 ->
        CTy.basetype_access_mode (CTy.basetype_of_arrtype aty2) =
          By_value chunk2 ->
        cell_neq
          {| arr_id := id1; arr_index := sub1 |}
          {| arr_id := id2; arr_index := sub2 |} ->
        non_alias st ->
        b1 <> b2 \/
        ofs1 + size_chunk chunk1 <= ofs2 \/
        ofs2 + size_chunk chunk2 <= ofs1.
    Proof.
      intros st id1 id2 sub1 sub2 b1 b2 ty1 ty2 aty1 aty2
             ofs1 ofs2 chunk1 chunk2
             Hloc1 Hloc2 Haty1 Haty2 Hoff1 Hoff2
             Hmode1 Hmode2 Hcells_neq Hnonalias.
      unfold cell_neq in Hcells_neq; simpl in Hcells_neq.
      destruct Hcells_neq as [Hids_neq|Hsubscripts_neq].
      - left. eapply Hnonalias; eauto.
      - destruct (peq id1 id2) as [Hids_eq|Hids_neq].
        + subst id2.
          rewrite Hloc1 in Hloc2.
          inversion Hloc2; subst b2 ty2.
          rewrite Haty1 in Haty2.
          inversion Haty2; subst aty2.
          rewrite Hmode1 in Hmode2.
          inversion Hmode2; subst chunk2.
          right.
          eapply calc_offset_different_sub_implies_disjoint; eauto.
        + left. eapply Hnonalias; eauto.
    Qed.
    

  Lemma write_cell_prsv_env:
  forall cell bty v st st' ge e m ge' e' m',
      write_cell cell bty v st st' ->
      st = (ge, e, m) ->
      st' = (ge', e', m') ->
      ge = ge' /\ e = e'.
  Proof.
    intros.
    inv H0. 
    inv H. inv H10. 
    inv H9. splits; trivial. destruct H0; destruct H1; subst; trivial.
  Qed.

    Lemma write_cell_prsv_nonalias:
      forall cell bty v st st',
        write_cell cell bty v st st' ->
        non_alias st ->
        non_alias st'.
    Proof. 
      intros. unfolds non_alias.
      intros.
      destruct st as [[ge e] m].
      destruct st' as [[ge' e'] m'].
      eapply write_cell_prsv_env in H; eauto.
      destruct H; subst.
      eapply H0; eauto.
    Qed.

    Lemma eq_prsv_nonalias:
      forall st st',
        eq st st' ->
        non_alias st ->
        non_alias st'.
    Proof. 
      intros. unfolds non_alias. unfolds eq.
      destruct st as [[ge e] m].
      destruct st' as [[ge' e'] m'].
      intros. 
      destruct H as (Hge & He & Hmf & Hmb). subst. 
      eapply H0; eauto.
    Qed.

    Lemma read_cell_stable_under_eq:
      forall rc ty v st1 st1',
        eq st1 st1' ->
        read_cell rc ty v st1 ->
        read_cell rc ty v st1'.
    Proof.
      intros. 
      destruct st1 as [[ge1 e1] m1].
      destruct st1' as [[ge1' e1'] m1'].
      unfolds eq. destruct H as (Hge & He & Hmf & Hmb). subst.
      inv H0.
      econs; eauto. inv H2.
      eapply Mem.load_extends with (m2:=m1') in Hmf; eauto.
      destruct Hmf as (v' & Hload & Hext).
      eapply Mem.load_extends with (m2:=m) in Hmb; eauto.
      destruct Hmb as (v'' & Hload' & Hext').
      rewrite Hload. f_equal.
      rewrite H7 in Hload'. inv Hload'.
      clear - Hext Hext'.
      inv Hext. inv Hext'; eauto.
      inv Hext'; trivial.
    Qed.

    Lemma write_cell_stable_under_eq:
      forall wc ty v st1 st1' st2 st2',
        eq st1 st1' ->
        eq st2 st2' ->
        write_cell wc ty v st1 st2 ->
        write_cell wc ty v st1' st2'.
    Proof. 
      intros.
      destruct st1 as [[ge1 e1] m1].
      destruct st1' as [[ge1' e1'] m1'].
      destruct st2 as [[ge2 e2] m2].
      destruct st2' as [[ge2' e2'] m2'].
      unfolds eq. 
      destruct H as (Hge1 & He1 & Hmf1 & Hmb1). subst.
      destruct H0 as (Hge2 & He2 & Hmf2 & Hmb2). subst.
      inv H1. 
      eapply write_cell_intro; eauto. 
      clear - Hmf1 Hmb1 H9 H10.
      unfolds eq.
      destruct H9 as (Hge & He & Hmf & Hmb). subst.
      destruct H10 as (Hge' & He' & Hmf' & Hmb'). subst.
      splits; trivial. 
      unfold mem_eq. split.
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
      unfolds eq.
      destruct H9 as (Hge & He & Hmf & Hmb). subst.
      destruct H10 as (Hge' & He' & Hmf' & Hmb'). subst.
      splits; trivial. unfold mem_eq; split. 
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
    Qed.

    (* currently, we only suppose single basetype int32s here, so no compatibility problem for access "size"*)
    Lemma write_after_write_cell_neq:
        forall cell1 cell2 v1 v2 st1 st2 st3 st2' bty bty',
            write_cell cell1 bty v1 st1 st2 -> 
            write_cell cell2 bty' v2 st2 st3 ->
            cell_neq cell1 cell2 ->
            write_cell cell2 bty' v2 st1 st2' ->
            non_alias st1 ->
            exists st3',
            write_cell cell1 bty v1 st2' st3' /\ eq st3 st3'.
    Proof.
      intros until bty'. intros Hw1 Hw2 Hneq Hw2' Halias.
      destruct st1 as [[ge1 e1] m1].
      destruct st2 as [[ge2 e2] m2].
      destruct st2' as [[ge2' e2'] m2'].
      destruct st3 as [[ge3 e3] m3].
      inv Hw1. inv Hw2. inv Hw2'.
      inv H.

      destruct H15 as (Hge1 & He1 & Hm1 ); subst.
      destruct H16 as (Hge2 & He2 & Hm2); subst.
      destruct H22 as (Hge2' & He2' & Hm2'); subst.
      destruct H23 as (Hge3 & He3 & Hm3); subst.
      destruct H8 as (Hge & He & Hm);
      destruct H9 as (Hge' & He' & Hm'); subst.

      rename ge3 into ge. rename e3 into e. 
      rename b1 into b2; rename ofs1 into ofs2. 
      rename b into b1; rename ofs into ofs1.
      rename m1 into m0'. rename m0 into m1''.
      rename m into m0. rename m' into m1.
      rename m2 into m1'.
      rename m'0 into m2. 
      rename m4 into m0''. rename m'1 into m1x. rename m2' into m1x'.
      rename m3 into m2'.
      rename id1 into id2. rename id into id1. 
      rename sub1 into sub2. rename sub into sub1.
      rename ty1 into ty2. 
      assert (b0 = b2 /\ ty0 = ty2). {
        clear - H3 H10. simpls.
        rewrite H3 in H10. inv H10; split; trivial.
      }
      destruct H; subst. 
      rewrite H7 in H14. inv H14. rename ty'1 into ty2'.
      clear H17 H3. 
      rewrite H11 in H18. inv H18.
      rewrite H12 in H19. inv H19. rename chunk1 into chunk2. rename chunk into chunk1.
      rename ty into ty1. rename ty' into ty1'.
      assert (chunk1 = chunk2). {
        clear - H5 H12.
        destruct ty1'; destruct ty2'; simpls.
        destruct b; destruct b0; simpls. rewrite H5 in H12. inv H12; trivial.
      }
      subst. rename chunk2 into chunk.
      rename H6 into Hw1. rename H13 into Hw2.
      rename H20 into Hw2'.
      (**
      write 1 then write 2:
      (<m0>, m0', m0'') --- b1,ofs1,v1 --> (<m1>, m1', m1'') --- b2,ofs2,v2 --> (<m2>, m2')

      write 2 then write 1:
      (m0, m0', <m0''>) --- b2,ofs2,v2 --> (<m1x>, m1x') --- b1,ofs1,v1 --> [<m2x>]
      
      The m2x is what we need.
      **)

      assert (exists m2x, 
        Mem.store chunk m1x' b1 ofs1 v1 = Some m2x /\ mem_eq m2x m2'). {
        (* first we try to prove there is m2x after storation in m1x', because of valid_access *)
        assert (Mem.valid_access m1x' chunk b1 ofs1 Writable). {
          eapply Mem.store_valid_access_3 in Hw2.
          eapply mem_eq_prsv_valid_access with (m':=m1) in Hw2.
          2: {
            clear - Hm' Hm1. eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          }
          eapply Mem.store_valid_access_3 in Hw1.
          eapply mem_eq_prsv_valid_access with (m':=m0'') in Hw1.
          2: {
            clear - Hm Hm2'. eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          } 
          eapply Mem.store_valid_access_1  in Hw2'; eauto.
          eapply mem_eq_prsv_valid_access; eauto.
        }
        eapply Mem.valid_access_store with (v:=v1) in H.
        destruct H as (m2x & Hw2x).
        exists m2x. split; trivial.
        (* then we prove the constructed m2x mem_eq to m2', as they just swap the last two disjoint writes. *)
        assert (mem_eq m2 m2x). {
          eapply swap_store_cell_neq_prsv_mem_eq
            with (chunk:=chunk) (m1:=m1'') (b2:=b2) (ofs2:=ofs2) (v2:=v2)
            (m1x':=m1x) (m0':=m0'') (m1x:=m1x') (m0:=m0) (m1':=m1)
            ; eauto.
          - eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          - eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          - eapply mem_eq_sym; trivial.
          - eapply cell_neq_implies_disjoint_access; eauto.
        }
        eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
      }

      destruct H as (m2x & Hm2x & Hmeq).
      exists (ge, e, m2x). split.
      2: { splits; simpl; trivial. eapply mem_eq_sym; trivial. }
      eapply write_cell_intro with 
        (st:=(ge, e, m1x')) (st0':=(ge, e, m2x)) ; eauto.
      all: try eapply eq_refl.
    Qed.



    Lemma read_after_write_cell_neq:
      forall wc rc v1 v2 st st' bty bty',
          write_cell wc bty v1 st st' -> 
          cell_neq wc rc ->
          non_alias st ->
          read_cell rc bty' v2 st <->
          read_cell rc bty' v2 st'.
    Proof.
      intros. split; intro.
      - 
        destruct st as [[ge e] m].
        destruct st' as ((ge', e'), m').
        inv H.

        eapply read_cell_stable_under_eq with (st1':=(ge,e,m0)) in H2.
        2: { clear - H12. simpls. splits; trivial.  
          destruct H12 as (Hge & He & Hm). destruct Hm. split; trivial.
        }

        inversion_clear H2.
        inv H4.

        unfold cell_neq in H0. simpl in H0.
        unfolds eq. 
        destruct H12 as (Hge & He & Hm); subst.
        destruct H13 as (Hge' & He' & Hm'); subst. 
        
        eapply read_cell_stable_under_eq with (st1:=(ge', e', m'0)).
        { simpls. splits; trivial. }
        
        rename H10 into Hstore.
        eapply Mem.store_storebytes in Hstore.
        destruct H0.
        
        -- (* id neq *) 
          eapply read_cell_intro; eauto.
          rewrite <- H16.
          eapply Mem.load_storebytes_other
          with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto. 
        -- (* subscript neq *)
          econs; eauto. rewrite <- H16.
          eapply Mem.load_storebytes_other
          with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto; trivial.
          assert (id = id0 \/ id <> id0). {
            clear. destruct id; destruct id0; simpls; try lia.
          }
          destruct H0. 2: {  
            unfold non_alias in H1.
            eapply H1 with (id1:=id) (b1:=b) (id2:=id0) (b2:=b0) in H0; eauto. 
          }
          right. subst. rewrite H5 in H3. inv H3. 
          rewrite H6 in H7. inv H7. rename ty'0 into aty.
          rewrite H9 in H15. inv H15.
          rewrite encode_val_length.
          rewrite <- size_chunk_conv.
          eapply calc_offset_different_sub_implies_disjoint; eauto.
          intro. eapply H. 
          eapply veq_sym; trivial.
      - 
          destruct st as [[ge e] m].
          destruct st' as ((ge', e'), m').
          inv H.
  
          eapply read_cell_stable_under_eq with (st1':=(ge,e,m'0)) in H2.
          2: { 
            clear - H12 H13. simpls.
            destruct H13 as (Hge & He & Hm); subst.
            destruct H12 as (Hge' & He' & Hm'); subst. 
            splits; trivial.  
            destruct Hm. destruct Hm'. split.
            eapply Mem.extends_extends_compose; eauto. eapply Mem.extends_refl.
            eapply Mem.extends_extends_compose; eauto. eapply Mem.extends_refl.
          }
  
          inversion_clear H2.
          inv H4.
  
          unfold cell_neq in H0. simpl in H0.
          unfolds eq. 
          destruct H12 as (Hge & He & Hm); subst.
          destruct H13 as (Hge' & He' & Hm'); subst. 
          
          eapply read_cell_stable_under_eq with (st1:=(ge', e', m0)).
          { simpls. splits; trivial. }
          
          rename H10 into Hstore.
          eapply Mem.store_storebytes in Hstore.
          destruct H0.
          
          -- (* id neq *) 
            eapply read_cell_intro; eauto.
            rewrite <- H16.
            symmetry.
            eapply Mem.load_storebytes_other
            with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto. 
          -- (* subscript neq *)
            econs; eauto. rewrite <- H16.
            symmetry.
            eapply Mem.load_storebytes_other
            with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto; trivial.
            assert (id = id0 \/ id <> id0). {
              clear. destruct id; destruct id0; simpls; try lia.
            }
            destruct H0. 2: {  
              unfold non_alias in H1.
              eapply H1 with (id1:=id) (b1:=b) (id2:=id0) (b2:=b0) in H0; eauto. 
            }
            right. subst. 
            assert (b = b0 /\ ty = ty0). {
              clear - H3 H5.
              simpls. rewrite H5 in H3. inv H3; trivial. split; trivial.
            }
            destruct H0; subst.
            rewrite H6 in H7. inv H7. rename ty'0 into aty.
            rewrite H9 in H15. inv H15.
            rewrite encode_val_length.
            rewrite <- size_chunk_conv.
            eapply calc_offset_different_sub_implies_disjoint; eauto.
            intro. eapply H. 
            eapply veq_sym; trivial.
  Qed.
    
  Lemma sem_unary_operation_eq_invariant:
    forall ge e m ge' e' m' op v ty' v',
      eq (ge, e, m) (ge', e', m') ->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m = Some v' ->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m' = Some v'.
  Proof. 
    intros. unfolds eq. destruct H as (Hge & He & Hmf & Hmb). subst.
    destruct ty'; destruct op; destruct v; simpls; eauto.
  Qed.

  Lemma sem_binary_operation_eq_invariant:
    forall ge e m ge' e' m' op v1 ty1 v2 ty2 v',
      eq (ge, e, m) (ge', e', m') ->
      sem_binary_operation ge op v1 (CTy.basetype_to_compcert_type ty1) v2 (CTy.basetype_to_compcert_type ty2) m = Some v' ->
      sem_binary_operation ge' op v1 (CTy.basetype_to_compcert_type ty1) 
      v2 (CTy.basetype_to_compcert_type ty2) m' = Some v'.
  Proof. 
    intros. destruct H as (Hge & He & Hmf & Hmb). subst.
    destruct ty1; destruct ty2; destruct op; destruct v1; destruct v2; simpls; trivial.
  Qed.

  Lemma sem_unary_operation_write_cell_invariant:
    forall op v v' v0 wc ty ty' (m1 m2:mem) ge env m1 ge' env' m2,
      write_cell wc ty v0 (ge, env, m1) (ge', env', m2) ->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m1 = Some v' <->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m2 = Some v'.
  Proof.
    intros.
    split; intro.
    - 
      unfolds sem_unary_operation. destruct op; simpl in H0; try discriminate; eauto.
      unfolds CTy.basetype_to_compcert_type. destruct ty'; simpls.
      unfolds sem_notbool. unfolds bool_val; simpls. destruct v; simpls; try discriminate.
      trivial.
    - 
      unfolds sem_unary_operation. destruct op; simpl in H0; try discriminate; eauto.
      unfolds CTy.basetype_to_compcert_type. destruct ty'; simpls.
      unfolds sem_notbool. unfolds bool_val; simpls. destruct v; simpls; try discriminate.
      trivial.
  Qed.

  Lemma sem_binary_operation_write_cell_invariant:
    forall op v1 v2 v' v0 wc ty ty1 ty2 (m1 m2:mem) ge env m1 ge' env' m2,
      write_cell wc ty v0 (ge, env, m1) (ge', env', m2) ->
      sem_binary_operation ge op v1 (CTy.basetype_to_compcert_type ty1) 
      v2 (CTy.basetype_to_compcert_type ty2) m1 = Some v' <->
      sem_binary_operation ge op v1 (CTy.basetype_to_compcert_type ty1) 
      v2 (CTy.basetype_to_compcert_type ty2) m2 = Some v'.
  Proof.
    intros. split; intro.
    - unfolds CTy.basetype_to_compcert_type. destruct ty1; destruct ty2; simpls.
      unfolds sem_binary_operation. destruct op; simpls; trivial.
    - unfolds CTy.basetype_to_compcert_type. destruct ty1; destruct ty2; simpls.
      unfolds sem_binary_operation. destruct op; simpls; trivial.
  Qed.

End CState.
