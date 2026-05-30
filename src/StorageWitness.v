Require Import List.

Require Import Linalg.
Require Import PolyBase.
Require Import PolIRs.
Require Import PointWitness.

Import ListNotations.

(** Storage-side witness vocabulary shared by layout remapping, private
    expansion, copy protocols, and storage reuse.

    The relation direction is target-to-source: [rel target_cell source_cell]
    means that the target cell represents the source logical cell for the
    observation being proved. *)

Definition cell_relation := MemCell -> MemCell -> Prop.

Definition identity_cell_relation : cell_relation := cell_eq.

Definition compose_cell_relation
    (target_mid mid_source: cell_relation) : cell_relation :=
  fun target_cell source_cell =>
    exists mid_cell,
      target_mid target_cell mid_cell /\
      mid_source mid_cell source_cell.

Definition cell_relation_reflexive (rel: cell_relation) : Prop :=
  forall cell, rel cell cell.

Definition cell_relation_target_functional (rel: cell_relation) : Prop :=
  forall target_cell source_cell1 source_cell2,
    rel target_cell source_cell1 ->
    rel target_cell source_cell2 ->
    cell_eq source_cell1 source_cell2.

Definition cell_relation_source_functional (rel: cell_relation) : Prop :=
  forall target_cell1 target_cell2 source_cell,
    rel target_cell1 source_cell ->
    rel target_cell2 source_cell ->
    cell_eq target_cell1 target_cell2.

Definition cell_relation_respects_cell_eq (rel: cell_relation) : Prop :=
  forall target_cell1 target_cell2 source_cell1 source_cell2,
    cell_eq target_cell1 target_cell2 ->
    cell_eq source_cell1 source_cell2 ->
    rel target_cell1 source_cell1 ->
    rel target_cell2 source_cell2.

Lemma identity_cell_relation_reflexive :
  cell_relation_reflexive identity_cell_relation.
Proof.
  unfold cell_relation_reflexive, identity_cell_relation.
  intros cell.
  unfold cell_eq.
  split; simpl; auto.
  apply veq_refl.
Qed.

Definition same_point_access_relation
    (rel: cell_relation)
    (target_access source_access: AccessFunction) : Prop :=
  forall p,
    rel (exact_cell target_access p) (exact_cell source_access p).

Definition access_list_relation
    (rel: cell_relation)
    (target_accesses source_accesses: list AccessFunction) : Prop :=
  Forall2 (same_point_access_relation rel) target_accesses source_accesses.

Lemma same_point_access_relation_identity_refl :
  forall access,
    same_point_access_relation identity_cell_relation access access.
Proof.
  unfold same_point_access_relation.
  intros access p.
  apply identity_cell_relation_reflexive.
Qed.

Lemma same_point_access_relation_refl :
  forall rel access,
    cell_relation_reflexive rel ->
    same_point_access_relation rel access access.
Proof.
  unfold same_point_access_relation, cell_relation_reflexive.
  intros rel access Hrel p.
  apply Hrel.
Qed.

Lemma access_list_relation_identity_refl :
  forall accesses,
    access_list_relation identity_cell_relation accesses accesses.
Proof.
  induction accesses as [|access accesses IH]; simpl.
  - constructor.
  - constructor.
    + apply same_point_access_relation_identity_refl.
    + exact IH.
Qed.

Lemma access_list_relation_refl :
  forall rel accesses,
    cell_relation_reflexive rel ->
    access_list_relation rel accesses accesses.
Proof.
  intros rel accesses Hrel.
  induction accesses as [|access accesses IH]; simpl.
  - constructor.
  - constructor.
    + apply same_point_access_relation_refl.
      exact Hrel.
    + exact IH.
Qed.

Lemma same_point_access_relation_compose :
  forall target_mid mid_source target_access mid_access source_access,
    same_point_access_relation target_mid target_access mid_access ->
    same_point_access_relation mid_source mid_access source_access ->
    same_point_access_relation
      (compose_cell_relation target_mid mid_source)
      target_access source_access.
Proof.
  unfold same_point_access_relation, compose_cell_relation.
  intros target_mid mid_source target_access mid_access source_access
         Htarget_mid Hmid_source p.
  exists (exact_cell mid_access p).
  split.
  - apply Htarget_mid.
  - apply Hmid_source.
Qed.

Lemma access_list_relation_compose :
  forall target_mid mid_source
         target_accesses mid_accesses source_accesses,
    access_list_relation target_mid target_accesses mid_accesses ->
    access_list_relation mid_source mid_accesses source_accesses ->
    access_list_relation
      (compose_cell_relation target_mid mid_source)
      target_accesses source_accesses.
Proof.
  intros target_mid mid_source target_accesses mid_accesses source_accesses
         Htarget_mid Hmid_source.
  revert source_accesses Hmid_source.
  induction Htarget_mid as
    [|target_access mid_access target_tail mid_tail
       Hhead_target_mid Htail_target_mid IH];
    intros source_accesses Hmid_source.
  - inversion Hmid_source. constructor.
  - inversion Hmid_source as
      [|mid_access' source_access mid_tail' source_tail
         Hhead_mid_source Htail_mid_source Hmid_eq Hsource_eq].
    subst.
    constructor.
    + eapply same_point_access_relation_compose; eauto.
    + eapply IH; eauto.
Qed.

Module StorageWitness (PolIRs: POLIRS).

Module PL := PolIRs.PolyLang.

(** Same logical statement instances, but access cells may be related by a
    storage relation.  This is the first non-[EqDom] shape needed for layout
    remapping and scalar/private expansion.  Scheduling can still be validated
    separately; this record only states the storage side of the relation. *)
Record same_instance_access_remap
    (rel: cell_relation)
    (before after: PL.PolyInstr) : Prop := {
  siar_same_depth :
    PL.pi_depth after = PL.pi_depth before;
  siar_same_instr :
    PL.pi_instr after = PL.pi_instr before;
  siar_same_domain :
    PL.pi_poly after = PL.pi_poly before;
  siar_same_point_witness :
    PL.pi_point_witness after = PL.pi_point_witness before;
  siar_same_source_transformation :
    PL.pi_transformation after = PL.pi_transformation before;
  siar_write_accesses :
    access_list_relation rel
      (PL.pi_waccess after) (PL.pi_waccess before);
  siar_read_accesses :
    access_list_relation rel
      (PL.pi_raccess after) (PL.pi_raccess before);
}.

Definition same_instance_identity_remap
    (before after: PL.PolyInstr) : Prop :=
  same_instance_access_remap identity_cell_relation before after.

Lemma same_instance_identity_remap_refl :
  forall pi,
    same_instance_identity_remap pi pi.
Proof.
  intros pi.
  unfold same_instance_identity_remap.
  constructor; try reflexivity.
  - apply access_list_relation_identity_refl.
  - apply access_list_relation_identity_refl.
Qed.

Lemma same_instance_access_remap_refl :
  forall rel pi,
    cell_relation_reflexive rel ->
    same_instance_access_remap rel pi pi.
Proof.
  intros rel pi Hrel.
  constructor; try reflexivity.
  - apply access_list_relation_refl.
    exact Hrel.
  - apply access_list_relation_refl.
    exact Hrel.
Qed.

Lemma same_instance_access_remap_compose :
  forall target_mid mid_source before mid after,
    same_instance_access_remap target_mid mid after ->
    same_instance_access_remap mid_source before mid ->
    same_instance_access_remap
      (compose_cell_relation target_mid mid_source)
      before after.
Proof.
  intros target_mid mid_source before mid after Htarget_mid Hmid_source.
  constructor.
  - transitivity (PL.pi_depth mid).
    + apply Htarget_mid.
    + apply Hmid_source.
  - transitivity (PL.pi_instr mid).
    + apply Htarget_mid.
    + apply Hmid_source.
  - transitivity (PL.pi_poly mid).
    + apply Htarget_mid.
    + apply Hmid_source.
  - transitivity (PL.pi_point_witness mid).
    + apply Htarget_mid.
    + apply Hmid_source.
  - transitivity (PL.pi_transformation mid).
    + apply Htarget_mid.
    + apply Hmid_source.
  - eapply access_list_relation_compose.
    + apply Htarget_mid.
    + apply Hmid_source.
  - eapply access_list_relation_compose.
    + apply Htarget_mid.
    + apply Hmid_source.
Qed.

Lemma same_instance_access_remap_list_compose :
  forall target_mid mid_source before mid after,
    Forall2
      (same_instance_access_remap target_mid)
      mid after ->
    Forall2
      (same_instance_access_remap mid_source)
      before mid ->
    Forall2
      (same_instance_access_remap
         (compose_cell_relation target_mid mid_source))
      before after.
Proof.
  intros target_mid mid_source before mid after Htarget_mid Hmid_source.
  revert before Hmid_source.
  induction Htarget_mid as
    [|mid_instr after_instr mid_tail after_tail
       Hhead_target_mid Htail_target_mid IH];
    intros before Hmid_source.
  - inversion Hmid_source. constructor.
  - inversion Hmid_source as
      [|before_instr mid_instr' before_tail mid_tail'
         Hhead_mid_source Htail_mid_source Hbefore_eq Hmid_eq].
    subst.
    constructor.
    + eapply same_instance_access_remap_compose; eauto.
    + eapply IH; eauto.
Qed.

Definition pprog_same_instance_access_remap
    (rel: cell_relation)
    (before after: PL.t) : Prop :=
  let '(pis_before, varctxt_before, vars_before) := before in
  let '(pis_after, varctxt_after, vars_after) := after in
  varctxt_after = varctxt_before /\
  vars_after = vars_before /\
  Forall2 (same_instance_access_remap rel) pis_before pis_after.

Theorem pprog_same_instance_access_remap_varctxt_equal :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    varctxt_after = varctxt_before.
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after Hremap.
  destruct Hremap as [Hvarctxt _].
  exact Hvarctxt.
Qed.

Theorem pprog_same_instance_access_remap_vars_equal :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    vars_after = vars_before.
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after Hremap.
  destruct Hremap as [_ [Hvars _]].
  exact Hvars.
Qed.

Theorem pprog_same_instance_access_remap_instrs_length :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    length pis_before = length pis_after.
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after Hremap.
  destruct Hremap as [_ [_ Hpis]].
  induction Hpis as [|before_pi after_pi before_tail after_tail Hhead Htail IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma Forall2_nth_error_left :
  forall (A B: Type) (R: A -> B -> Prop) xs ys n x,
    Forall2 R xs ys ->
    nth_error xs n = Some x ->
    exists y,
      nth_error ys n = Some y /\
      R x y.
Proof.
  intros A B R xs ys n x Hforall.
  revert n x.
  induction Hforall as [|x_head y_head xs_tail ys_tail Hhead Htail IH];
    intros n x Hnth;
    destruct n as [|n]; simpl in Hnth; try discriminate.
  - inversion Hnth. subst.
    exists y_head.
    split; [reflexivity|exact Hhead].
  - eapply IH; eauto.
Qed.

Lemma Forall2_nth_error_right :
  forall (A B: Type) (R: A -> B -> Prop) xs ys n y,
    Forall2 R xs ys ->
    nth_error ys n = Some y ->
    exists x,
      nth_error xs n = Some x /\
      R x y.
Proof.
  intros A B R xs ys n y Hforall.
  revert n y.
  induction Hforall as [|x_head y_head xs_tail ys_tail Hhead Htail IH];
    intros n y Hnth;
    destruct n as [|n]; simpl in Hnth; try discriminate.
  - inversion Hnth. subst.
    exists x_head.
    split; [reflexivity|exact Hhead].
  - eapply IH; eauto.
Qed.

Theorem pprog_same_instance_access_remap_source_instr :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    nth_error pis_before n = Some before_pi ->
    exists after_pi,
      nth_error pis_after n = Some after_pi /\
      same_instance_access_remap rel before_pi after_pi.
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi Hremap Hnth.
  destruct Hremap as [_ [_ Hpis]].
  eapply Forall2_nth_error_left; eauto.
Qed.

Theorem pprog_same_instance_access_remap_target_instr :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n after_pi,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    nth_error pis_after n = Some after_pi ->
    exists before_pi,
      nth_error pis_before n = Some before_pi /\
      same_instance_access_remap rel before_pi after_pi.
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n after_pi Hremap Hnth.
  destruct Hremap as [_ [_ Hpis]].
  eapply Forall2_nth_error_right; eauto.
Qed.

Theorem pprog_same_instance_access_remap_instr_nth :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi after_pi,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    nth_error pis_before n = Some before_pi ->
    nth_error pis_after n = Some after_pi ->
    same_instance_access_remap rel before_pi after_pi.
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi after_pi
         Hremap Hbefore Hafter.
  destruct
    (pprog_same_instance_access_remap_source_instr
       rel pis_before varctxt_before vars_before
       pis_after varctxt_after vars_after n before_pi Hremap Hbefore)
    as (after_pi' & Hafter' & Hsiar).
  rewrite Hafter in Hafter'.
  inversion Hafter'. subst.
  exact Hsiar.
Qed.

Theorem pprog_same_instance_access_remap_write_accesses_nth :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi after_pi,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    nth_error pis_before n = Some before_pi ->
    nth_error pis_after n = Some after_pi ->
    access_list_relation rel
      (PL.pi_waccess after_pi) (PL.pi_waccess before_pi).
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi after_pi
         Hremap Hbefore Hafter.
  pose proof
    (pprog_same_instance_access_remap_instr_nth
       rel pis_before varctxt_before vars_before
       pis_after varctxt_after vars_after n before_pi after_pi
       Hremap Hbefore Hafter)
    as Hsiar.
  exact (siar_write_accesses _ _ _ Hsiar).
Qed.

Theorem pprog_same_instance_access_remap_read_accesses_nth :
  forall rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi after_pi,
    pprog_same_instance_access_remap
      rel
      ((pis_before, varctxt_before), vars_before)
      ((pis_after, varctxt_after), vars_after) ->
    nth_error pis_before n = Some before_pi ->
    nth_error pis_after n = Some after_pi ->
    access_list_relation rel
      (PL.pi_raccess after_pi) (PL.pi_raccess before_pi).
Proof.
  intros rel pis_before varctxt_before vars_before
         pis_after varctxt_after vars_after n before_pi after_pi
         Hremap Hbefore Hafter.
  pose proof
    (pprog_same_instance_access_remap_instr_nth
       rel pis_before varctxt_before vars_before
       pis_after varctxt_after vars_after n before_pi after_pi
       Hremap Hbefore Hafter)
    as Hsiar.
  exact (siar_read_accesses _ _ _ Hsiar).
Qed.

Definition pprog_same_instance_identity_remap
    (before after: PL.t) : Prop :=
  pprog_same_instance_access_remap identity_cell_relation before after.

Lemma pprog_same_instance_identity_remap_refl :
  forall pp,
    pprog_same_instance_identity_remap pp pp.
Proof.
  intros ((pis, varctxt), vars).
  unfold pprog_same_instance_identity_remap.
  unfold pprog_same_instance_access_remap.
  simpl.
  split; [reflexivity|].
  split; [reflexivity|].
  induction pis as [|pi pis IH].
  - constructor.
  - constructor.
    + apply same_instance_identity_remap_refl.
    + exact IH.
Qed.

Lemma pprog_same_instance_access_remap_refl :
  forall rel pp,
    cell_relation_reflexive rel ->
    pprog_same_instance_access_remap rel pp pp.
Proof.
  intros rel ((pis, varctxt), vars) Hrel.
  unfold pprog_same_instance_access_remap.
  simpl.
  split; [reflexivity|].
  split; [reflexivity|].
  induction pis as [|pi pis IH].
  - constructor.
  - constructor.
    + apply same_instance_access_remap_refl.
      exact Hrel.
    + exact IH.
Qed.

Lemma pprog_same_instance_access_remap_compose :
  forall target_mid mid_source before mid after,
    pprog_same_instance_access_remap target_mid mid after ->
    pprog_same_instance_access_remap mid_source before mid ->
    pprog_same_instance_access_remap
      (compose_cell_relation target_mid mid_source)
      before after.
Proof.
  intros target_mid mid_source
         ((before_pis, before_varctxt), before_vars)
         ((mid_pis, mid_varctxt), mid_vars)
         ((after_pis, after_varctxt), after_vars)
         Htarget_mid Hmid_source.
  unfold pprog_same_instance_access_remap in *.
  simpl in *.
  destruct Htarget_mid as (Hvarctxt_target_mid & Hvars_target_mid & Hpis_target_mid).
  destruct Hmid_source as (Hvarctxt_mid_source & Hvars_mid_source & Hpis_mid_source).
  split.
  - transitivity mid_varctxt.
    + exact Hvarctxt_target_mid.
    + exact Hvarctxt_mid_source.
  - split.
    + transitivity mid_vars.
      * exact Hvars_target_mid.
      * exact Hvars_mid_source.
    + eapply same_instance_access_remap_list_compose; eauto.
Qed.

End StorageWitness.
