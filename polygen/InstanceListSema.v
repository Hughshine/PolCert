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

Definition eq_except_sched (ip1 ip2: InstrPoint): Prop := 
  ip1.(ip_nth) = ip2.(ip_nth) /\ 
  ip1.(ip_index) = ip2.(ip_index) /\ 
  ip1.(ip_transformation) = ip2.(ip_transformation) /\
  ip1.(ip_instruction) = ip2.(ip_instruction) /\ 
  ip1.(ip_depth) = ip2.(ip_depth).

Inductive instr_point_sema (ip: InstrPoint) 
  (st1 st2: State.t): Prop :=
  | ip_sema_intro: forall wcs rcs,
    Instr.instr_semantics ip.(ip_instruction) 
      (affine_product ip.(ip_transformation) ip.(ip_index)) wcs rcs st1 st2 -> 
    instr_point_sema ip st1 st2.

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


End ILSema.