Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.

Import ListNotations.

(** A first-class endpoint relation for storage-aware validation.

    [TransformContract] exposes the semantic shape:

      relational_refinement R_in R_out before after

    This module packages those relations as named state views.  The current
    affine validators use two standard views:

      - [same_state_view] for the input side, because the existing theorem
        starts source and target from the same Coq state object;
      - [identity_view] for the output side, because the final observation is
        [State.eq].

    Future storage transformations should add concrete view constructors for
    layout projection, private erasure, commit selection, merge, reuse, and
    phase selection.  They should prove [view_refinement] theorems rather than
    inventing feature-specific final-state relations. *)

(** The view carrier is intentionally defined outside the [StateView] functor.
    Otherwise each functor application creates a fresh record type, and
    validators that instantiate [StateView PolIRs] independently cannot share
    endpoint views through a common facade. *)
Record generic_state_view (state: Type) := {
  generic_state_view_rel : state -> state -> Prop;
}.

Arguments generic_state_view_rel {state} _ _ _.

Record generic_checked_parameterized_view_transform_family
    (state program params: Type)
    (view_refinement:
      generic_state_view state -> generic_state_view state ->
      program -> program -> Prop) := {
  generic_cpvtf_input_view : params -> generic_state_view state;
  generic_cpvtf_output_view : params -> generic_state_view state;
  generic_cpvtf_check : params -> program -> program -> imp bool;
  generic_cpvtf_side_condition : params -> program -> program -> Prop;
  generic_cpvtf_check_sound :
    forall transform_params before after ok,
      mayReturn
        (generic_cpvtf_check transform_params before after) ok ->
      ok = true ->
      generic_cpvtf_side_condition transform_params before after ->
      view_refinement
        (generic_cpvtf_input_view transform_params)
        (generic_cpvtf_output_view transform_params)
        before after;
}.

Arguments generic_cpvtf_input_view
  {state program params view_refinement} _ _.
Arguments generic_cpvtf_output_view
  {state program params view_refinement} _ _.
Arguments generic_cpvtf_check
  {state program params view_refinement} _ _ _ _.
Arguments generic_cpvtf_side_condition
  {state program params view_refinement} _ _ _ _.
Arguments generic_cpvtf_check_sound
  {state program params view_refinement} _ _ _ _ _ _ _ _.

Module StateView (PolIRs: POLIRS).

Module State := PolIRs.State.
Module PolyLang := PolIRs.PolyLang.
Module AffineCore := AffineValidator PolIRs.
Module Transform := TransformContract PolIRs.

Definition view := generic_state_view State.t.

Definition state_view_rel (state_view: view) : Transform.state_relation :=
  generic_state_view_rel state_view.

Definition states_match (state_view: view) : Transform.state_relation :=
  state_view_rel state_view.

Definition mk_view (rel: Transform.state_relation) : view := {|
  generic_state_view_rel := rel;
|}.

Definition identity_view : view :=
  mk_view Transform.identity_observation.

Definition same_state_view : view :=
  mk_view Transform.same_state_relation.

Definition compose_view (target_mid mid_source: view) : view :=
  mk_view
    (Transform.compose_state_relation
      (state_view_rel target_mid)
      (state_view_rel mid_source)).

Definition view_included (smaller larger: view) : Prop :=
  Transform.relation_included
    (state_view_rel smaller)
    (state_view_rel larger).

Theorem view_included_refl :
  forall state_view,
    view_included state_view state_view.
Proof.
  unfold view_included.
  intros state_view.
  apply Transform.relation_included_refl.
Qed.

Theorem view_included_trans :
  forall first second third,
    view_included first second ->
    view_included second third ->
    view_included first third.
Proof.
  unfold view_included.
  intros first second third Hfirst_second Hsecond_third.
  eapply Transform.relation_included_trans; eauto.
Qed.

Theorem compose_view_monotone :
  forall target_mid target_mid'
         mid_source mid_source',
    view_included target_mid target_mid' ->
    view_included mid_source mid_source' ->
    view_included
      (compose_view target_mid mid_source)
      (compose_view target_mid' mid_source').
Proof.
  unfold view_included, compose_view.
  simpl.
  intros target_mid target_mid' mid_source mid_source'
         Htarget Hsource.
  apply Transform.compose_state_relation_monotone; assumption.
Qed.

Definition view_refinement
    (input_view output_view: view)
    (before after: PolyLang.t) : Prop :=
  Transform.relational_refinement
    (state_view_rel input_view)
    (state_view_rel output_view)
    before after.

(** A paper-facing spelling of [view_refinement].

    The executable validators and composition lemmas use [view_refinement] as the
    compact connective.  The theorem exposed at the top of a storage-aware
    pipeline should read like the old semantic refinement theorem, with
    [State.eq] replaced by explicit public views. *)
Definition public_semantic_refinement
    (input_view output_view: view)
    (before after: PolyLang.t) : Prop :=
  forall st_target0 st_source0 st_target_after,
    states_match input_view st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      states_match output_view st_target_after st_source_after.

Theorem public_semantic_refinement_iff :
  forall input_view output_view before after,
    public_semantic_refinement input_view output_view before after <->
    view_refinement input_view output_view before after.
Proof.
  unfold public_semantic_refinement, view_refinement.
  unfold Transform.relational_refinement.
  tauto.
Qed.

Theorem view_refinement_to_public_semantic_refinement :
  forall input_view output_view before after,
    view_refinement input_view output_view before after ->
    public_semantic_refinement input_view output_view before after.
Proof.
  intros input_view output_view before after Href.
  apply public_semantic_refinement_iff.
  exact Href.
Qed.

Theorem public_semantic_refinement_to_view_refinement :
  forall input_view output_view before after,
    public_semantic_refinement input_view output_view before after ->
    view_refinement input_view output_view before after.
Proof.
  intros input_view output_view before after Href.
  apply public_semantic_refinement_iff.
  exact Href.
Qed.

Theorem identity_view_contains_state_eq :
  Transform.observation_contains_state_eq
    (state_view_rel identity_view).
Proof.
  unfold Transform.observation_contains_state_eq.
  intros st_target st_source Heq.
  exact Heq.
Qed.

Theorem same_state_view_included_identity_view :
  view_included same_state_view identity_view.
Proof.
  unfold view_included, Transform.relation_included.
  unfold same_state_view, identity_view.
  simpl.
  unfold Transform.same_state_relation.
  intros st_target st_source Heq.
  subst st_source.
  apply State.eq_refl.
Qed.

Theorem view_included_compose_right_same_intro :
  forall input_view,
    view_included
      input_view
      (compose_view input_view same_state_view).
Proof.
  unfold view_included, compose_view, same_state_view.
  simpl.
  intros input_view.
  apply Transform.relation_included_compose_right_same_intro.
Qed.

Theorem view_included_compose_right_same_elim :
  forall input_view,
    view_included
      (compose_view input_view same_state_view)
      input_view.
Proof.
  unfold view_included, compose_view, same_state_view.
  simpl.
  intros input_view.
  apply Transform.relation_included_compose_right_same_elim.
Qed.

Theorem refinement_under_to_view_refinement :
  forall output_view before after,
    Transform.refinement_under
      (state_view_rel output_view) before after ->
    view_refinement same_state_view output_view before after.
Proof.
  unfold view_refinement.
  intros output_view before after Href.
  apply Transform.refinement_under_to_relational.
  exact Href.
Qed.

Theorem view_refinement_compose :
  forall target_mid_in target_mid_out
         mid_source_in mid_source_out
         before mid after,
    view_refinement target_mid_in target_mid_out mid after ->
    view_refinement mid_source_in mid_source_out before mid ->
    view_refinement
      (compose_view target_mid_in mid_source_in)
      (compose_view target_mid_out mid_source_out)
      before after.
Proof.
  unfold view_refinement, compose_view.
  simpl.
  intros target_mid_in target_mid_out mid_source_in mid_source_out
         before mid after Htarget_mid Hmid_source.
  eapply Transform.relational_refinement_compose; eauto.
Qed.

Theorem view_refinement_monotone :
  forall input_view output_view
         input_view' output_view'
         before after,
    view_included input_view' input_view ->
    view_included output_view output_view' ->
    view_refinement input_view output_view before after ->
    view_refinement input_view' output_view' before after.
Proof.
  unfold view_refinement, view_included.
  intros input_view output_view input_view' output_view'
         before after Hinput Houtput Href.
  eapply Transform.relational_refinement_monotone; eauto.
Qed.

Record checked_view_transform_family := {
  cvtf_input_view : view;
  cvtf_output_view : view;
  cvtf_check : PolyLang.t -> PolyLang.t -> imp bool;
  cvtf_check_sound :
    forall before after ok,
      mayReturn (cvtf_check before after) ok ->
      ok = true ->
      view_refinement cvtf_input_view cvtf_output_view before after;
}.

Theorem checked_view_transform_family_pair_compose :
  forall first second before mid after first_ok second_ok,
    mayReturn (cvtf_check first before mid) first_ok ->
    first_ok = true ->
    mayReturn (cvtf_check second mid after) second_ok ->
    second_ok = true ->
    view_refinement
      (compose_view (cvtf_input_view second) (cvtf_input_view first))
      (compose_view (cvtf_output_view second) (cvtf_output_view first))
      before after.
Proof.
  intros first second before mid after first_ok second_ok
         Hfirst_ret Hfirst_ok Hsecond_ret Hsecond_ok.
  eapply view_refinement_compose.
  - eapply cvtf_check_sound; eauto.
  - eapply cvtf_check_sound; eauto.
Qed.

Definition checked_view_transform_certificate
    (family: checked_view_transform_family) : Type :=
  unit.

Definition checked_view_transform_certificate_input_view
    (family: checked_view_transform_family)
    (_certificate: checked_view_transform_certificate family) : view :=
  cvtf_input_view family.

Definition checked_view_transform_certificate_output_view
    (family: checked_view_transform_family)
    (_certificate: checked_view_transform_certificate family) : view :=
  cvtf_output_view family.

Definition checked_view_transform_certificate_input_states_match
    (family: checked_view_transform_family)
    (certificate: checked_view_transform_certificate family) :=
  states_match
    (checked_view_transform_certificate_input_view family certificate).

Definition checked_view_transform_certificate_output_states_match
    (family: checked_view_transform_family)
    (certificate: checked_view_transform_certificate family) :=
  states_match
    (checked_view_transform_certificate_output_view family certificate).

Definition checked_view_transform_certificate_refinement
    (family: checked_view_transform_family)
    (certificate: checked_view_transform_certificate family)
    (source target: PolyLang.t) : Prop :=
  forall st_target0 st_source0 st_target_after,
    checked_view_transform_certificate_input_states_match
      family certificate st_target0 st_source0 ->
    PolyLang.instance_list_semantics target st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics source st_source0 st_source_after /\
      checked_view_transform_certificate_output_states_match
        family certificate st_target_after st_source_after.

Definition checked_view_transform_certificate_accepted
    (family: checked_view_transform_family)
    (_certificate: checked_view_transform_certificate family)
    (before after: PolyLang.t) : Prop :=
  exists ok,
    mayReturn (cvtf_check family before after) ok /\
    ok = true.

Theorem checked_view_transform_certificate_public_semantic_sound :
  forall family certificate before after,
    checked_view_transform_certificate_accepted
      family certificate before after ->
    public_semantic_refinement
      (checked_view_transform_certificate_input_view family certificate)
      (checked_view_transform_certificate_output_view family certificate)
      before after.
Proof.
  intros family certificate before after Haccepted.
  destruct Haccepted as [ok [Hret Hok]].
  apply view_refinement_to_public_semantic_refinement.
  eapply cvtf_check_sound; eauto.
Qed.

Theorem checked_view_transform_certificate_state_sound :
  forall family certificate before after
         st_target0 st_source0 st_target_after,
    checked_view_transform_certificate_accepted
      family certificate before after ->
    state_view_rel
      (checked_view_transform_certificate_input_view family certificate)
      st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      state_view_rel
        (checked_view_transform_certificate_output_view family certificate)
        st_target_after st_source_after.
Proof.
  intros family certificate before after
         st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  eapply
    (checked_view_transform_certificate_public_semantic_sound
       family certificate before after Haccepted);
    eauto.
Qed.

Theorem checked_view_transform_certificate_refines :
  forall family certificate source target,
    checked_view_transform_certificate_accepted
      family certificate source target ->
    checked_view_transform_certificate_refinement
      family certificate source target.
Proof.
  unfold checked_view_transform_certificate_refinement.
  intros family certificate source target Haccepted
         st_target0 st_source0 st_target_after Hinput Htarget.
  eapply checked_view_transform_certificate_state_sound; eauto.
Qed.

Theorem checked_view_transform_certificate_semantic_refinement :
  forall family certificate source target
         st_target0 st_source0 st_target_after,
    checked_view_transform_certificate_accepted
      family certificate source target ->
    checked_view_transform_certificate_input_states_match
      family certificate st_target0 st_source0 ->
    PolyLang.instance_list_semantics target st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics source st_source0 st_source_after /\
      checked_view_transform_certificate_output_states_match
        family certificate st_target_after st_source_after.
Proof.
  intros family certificate source target
         st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  eapply checked_view_transform_certificate_state_sound; eauto.
Qed.

Definition checked_parameterized_view_transform_family (params: Type) :=
  generic_checked_parameterized_view_transform_family
    State.t PolyLang.t params view_refinement.

Definition cpvtf_input_view {params}
    (family: checked_parameterized_view_transform_family params)
    (transform_params: params) : view :=
  generic_cpvtf_input_view family transform_params.

Definition cpvtf_output_view {params}
    (family: checked_parameterized_view_transform_family params)
    (transform_params: params) : view :=
  generic_cpvtf_output_view family transform_params.

Definition cpvtf_check {params}
    (family: checked_parameterized_view_transform_family params)
    (transform_params: params) (before after: PolyLang.t) : imp bool :=
  generic_cpvtf_check family transform_params before after.

Definition cpvtf_side_condition {params}
    (family: checked_parameterized_view_transform_family params)
    (transform_params: params) (before after: PolyLang.t) : Prop :=
  generic_cpvtf_side_condition family transform_params before after.

Theorem cpvtf_check_sound :
  forall params
         (family: checked_parameterized_view_transform_family params)
         transform_params before after ok,
    mayReturn (cpvtf_check family transform_params before after) ok ->
    ok = true ->
    cpvtf_side_condition family transform_params before after ->
    view_refinement
      (cpvtf_input_view family transform_params)
      (cpvtf_output_view family transform_params)
      before after.
Proof.
  intros params family transform_params before after ok Hret Hok Hside.
  exact
    (generic_cpvtf_check_sound
       family transform_params before after ok Hret Hok Hside).
Qed.

Theorem cpvtf_check_public_semantic_sound :
  forall params
         (family: checked_parameterized_view_transform_family params)
         transform_params before after ok,
    mayReturn (cpvtf_check family transform_params before after) ok ->
    ok = true ->
    cpvtf_side_condition family transform_params before after ->
    public_semantic_refinement
      (cpvtf_input_view family transform_params)
      (cpvtf_output_view family transform_params)
      before after.
Proof.
  intros params family transform_params before after ok Hret Hok Hside.
  apply view_refinement_to_public_semantic_refinement.
  eapply cpvtf_check_sound; eauto.
Qed.

Theorem cpvtf_check_public_semantic_state_sound :
  forall params
         (family: checked_parameterized_view_transform_family params)
         transform_params before after ok
         st_target0 st_source0 st_target_after,
    mayReturn (cpvtf_check family transform_params before after) ok ->
    ok = true ->
    cpvtf_side_condition family transform_params before after ->
    state_view_rel
      (cpvtf_input_view family transform_params)
      st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      state_view_rel
        (cpvtf_output_view family transform_params)
        st_target_after st_source_after.
Proof.
  intros params family transform_params before after ok
         st_target0 st_source0 st_target_after
         Hret Hok Hside Hinput Hsem.
  eapply cpvtf_check_public_semantic_sound; eauto.
Qed.

Record checked_parameterized_transform_certificate
    {params: Type}
    (family: checked_parameterized_view_transform_family params) := {
  cptc_params : params;
}.

Arguments cptc_params {params family} _.

Definition checked_parameterized_transform_certificate_input_view
    {params}
    {family: checked_parameterized_view_transform_family params}
    (certificate:
      checked_parameterized_transform_certificate family) : view :=
  cpvtf_input_view family (cptc_params certificate).

Definition checked_parameterized_transform_certificate_output_view
    {params}
    {family: checked_parameterized_view_transform_family params}
    (certificate:
      checked_parameterized_transform_certificate family) : view :=
  cpvtf_output_view family (cptc_params certificate).

Definition checked_parameterized_transform_certificate_input_states_match
    {params}
    {family: checked_parameterized_view_transform_family params}
    (certificate:
      checked_parameterized_transform_certificate family) :=
  states_match
    (checked_parameterized_transform_certificate_input_view certificate).

Definition checked_parameterized_transform_certificate_output_states_match
    {params}
    {family: checked_parameterized_view_transform_family params}
    (certificate:
      checked_parameterized_transform_certificate family) :=
  states_match
    (checked_parameterized_transform_certificate_output_view certificate).

Definition checked_parameterized_transform_certificate_refinement
    {params}
    {family: checked_parameterized_view_transform_family params}
    (certificate:
      checked_parameterized_transform_certificate family)
    (source target: PolyLang.t) : Prop :=
  forall st_target0 st_source0 st_target_after,
    checked_parameterized_transform_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolyLang.instance_list_semantics target st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics source st_source0 st_source_after /\
      checked_parameterized_transform_certificate_output_states_match
        certificate st_target_after st_source_after.

Definition checked_parameterized_transform_certificate_accepted
    {params}
    {family: checked_parameterized_view_transform_family params}
    (certificate:
      checked_parameterized_transform_certificate family)
    (before after: PolyLang.t) : Prop :=
  exists ok,
    mayReturn
      (cpvtf_check family (cptc_params certificate) before after)
      ok /\
    ok = true /\
    cpvtf_side_condition family (cptc_params certificate) before after.

Theorem checked_parameterized_transform_certificate_public_semantic_sound :
  forall params
         (family: checked_parameterized_view_transform_family params)
         (certificate:
           checked_parameterized_transform_certificate family)
         before after,
    checked_parameterized_transform_certificate_accepted
      certificate before after ->
    public_semantic_refinement
      (checked_parameterized_transform_certificate_input_view certificate)
      (checked_parameterized_transform_certificate_output_view certificate)
      before after.
Proof.
  intros params family certificate before after Haccepted.
  destruct Haccepted as [ok [Hret [Hok Hside]]].
  exact
    (cpvtf_check_public_semantic_sound
       params family (cptc_params certificate)
       before after ok Hret Hok Hside).
Qed.

Theorem checked_parameterized_transform_certificate_state_sound :
  forall params
         (family: checked_parameterized_view_transform_family params)
         (certificate:
           checked_parameterized_transform_certificate family)
         before after st_target0 st_source0 st_target_after,
    checked_parameterized_transform_certificate_accepted
      certificate before after ->
    state_view_rel
      (checked_parameterized_transform_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      state_view_rel
        (checked_parameterized_transform_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros params family certificate before after
         st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  eapply
    (checked_parameterized_transform_certificate_public_semantic_sound
       params family certificate before after Haccepted);
    eauto.
Qed.

Theorem checked_parameterized_transform_certificate_refines :
  forall params
         (family: checked_parameterized_view_transform_family params)
         (certificate:
           checked_parameterized_transform_certificate family)
         source target,
    checked_parameterized_transform_certificate_accepted
      certificate source target ->
    checked_parameterized_transform_certificate_refinement
      certificate source target.
Proof.
  unfold checked_parameterized_transform_certificate_refinement.
  intros params family certificate source target Haccepted
         st_target0 st_source0 st_target_after Hinput Htarget.
  eapply checked_parameterized_transform_certificate_state_sound; eauto.
Qed.

Theorem checked_parameterized_transform_certificate_semantic_refinement :
  forall params
         (family: checked_parameterized_view_transform_family params)
         (certificate:
           checked_parameterized_transform_certificate family)
         source target st_target0 st_source0 st_target_after,
    checked_parameterized_transform_certificate_accepted
      certificate source target ->
    checked_parameterized_transform_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolyLang.instance_list_semantics target st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics source st_source0 st_source_after /\
      checked_parameterized_transform_certificate_output_states_match
        certificate st_target_after st_source_after.
Proof.
  intros params family certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  eapply checked_parameterized_transform_certificate_state_sound;
    eauto.
Qed.

Theorem checked_parameterized_view_transform_family_pair_compose :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         first_params second_params before mid after first_ok second_ok,
    mayReturn
      (@cpvtf_check params_first first first_params before mid) first_ok ->
    first_ok = true ->
    @cpvtf_side_condition params_first first first_params before mid ->
    mayReturn
      (@cpvtf_check params_second second second_params mid after) second_ok ->
    second_ok = true ->
    @cpvtf_side_condition params_second second second_params mid after ->
    view_refinement
      (compose_view
        (@cpvtf_input_view params_second second second_params)
        (@cpvtf_input_view params_first first first_params))
      (compose_view
        (@cpvtf_output_view params_second second second_params)
        (@cpvtf_output_view params_first first first_params))
      before after.
Proof.
  intros params_first params_second first second first_params second_params
         before mid after first_ok second_ok
         Hfirst_ret Hfirst_ok Hfirst_side
         Hsecond_ret Hsecond_ok Hsecond_side.
  eapply view_refinement_compose.
  - eapply (@cpvtf_check_sound params_second second); eauto.
  - eapply (@cpvtf_check_sound params_first first); eauto.
Qed.

Theorem checked_parameterized_public_semantic_family_pair_compose :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         first_params second_params before mid after first_ok second_ok,
    mayReturn
      (@cpvtf_check params_first first first_params before mid) first_ok ->
    first_ok = true ->
    @cpvtf_side_condition params_first first first_params before mid ->
    mayReturn
      (@cpvtf_check params_second second second_params mid after) second_ok ->
    second_ok = true ->
    @cpvtf_side_condition params_second second second_params mid after ->
    public_semantic_refinement
      (compose_view
        (@cpvtf_input_view params_second second second_params)
        (@cpvtf_input_view params_first first first_params))
      (compose_view
        (@cpvtf_output_view params_second second second_params)
        (@cpvtf_output_view params_first first first_params))
      before after.
Proof.
  intros params_first params_second first second first_params second_params
         before mid after first_ok second_ok
         Hfirst_ret Hfirst_ok Hfirst_side
         Hsecond_ret Hsecond_ok Hsecond_side.
  apply view_refinement_to_public_semantic_refinement.
  eapply checked_parameterized_view_transform_family_pair_compose; eauto.
Qed.

Theorem checked_parameterized_public_semantic_family_pair_state_sound :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         first_params second_params before mid after first_ok second_ok
         st_target0 st_source0 st_target_after,
    mayReturn
      (@cpvtf_check params_first first first_params before mid) first_ok ->
    first_ok = true ->
    @cpvtf_side_condition params_first first first_params before mid ->
    mayReturn
      (@cpvtf_check params_second second second_params mid after) second_ok ->
    second_ok = true ->
    @cpvtf_side_condition params_second second second_params mid after ->
    state_view_rel
      (compose_view
        (@cpvtf_input_view params_second second second_params)
        (@cpvtf_input_view params_first first first_params))
      st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      state_view_rel
        (compose_view
          (@cpvtf_output_view params_second second second_params)
          (@cpvtf_output_view params_first first first_params))
        st_target_after st_source_after.
Proof.
  intros params_first params_second first second first_params second_params
         before mid after first_ok second_ok
         st_target0 st_source0 st_target_after
         Hfirst_ret Hfirst_ok Hfirst_side
         Hsecond_ret Hsecond_ok Hsecond_side Hinput Hsem.
  eapply checked_parameterized_public_semantic_family_pair_compose; eauto.
Qed.

Record checked_parameterized_family_pair_certificate
    {params_first params_second: Type}
    (first: checked_parameterized_view_transform_family params_first)
    (second: checked_parameterized_view_transform_family params_second) := {
  cpfpc_first_params : params_first;
  cpfpc_second_params : params_second;
  cpfpc_mid_program : PolyLang.t;
}.

Arguments cpfpc_first_params
  {params_first params_second first second} _.
Arguments cpfpc_second_params
  {params_first params_second first second} _.
Arguments cpfpc_mid_program
  {params_first params_second first second} _.

Definition checked_parameterized_family_pair_certificate_input_view
    {params_first params_second}
    {first: checked_parameterized_view_transform_family params_first}
    {second: checked_parameterized_view_transform_family params_second}
    (certificate:
      checked_parameterized_family_pair_certificate first second) : view :=
  compose_view
    (cpvtf_input_view second (cpfpc_second_params certificate))
    (cpvtf_input_view first (cpfpc_first_params certificate)).

Definition checked_parameterized_family_pair_certificate_output_view
    {params_first params_second}
    {first: checked_parameterized_view_transform_family params_first}
    {second: checked_parameterized_view_transform_family params_second}
    (certificate:
      checked_parameterized_family_pair_certificate first second) : view :=
  compose_view
    (cpvtf_output_view second (cpfpc_second_params certificate))
    (cpvtf_output_view first (cpfpc_first_params certificate)).

Definition checked_parameterized_family_pair_certificate_input_states_match
    {params_first params_second}
    {first: checked_parameterized_view_transform_family params_first}
    {second: checked_parameterized_view_transform_family params_second}
    (certificate:
      checked_parameterized_family_pair_certificate first second) :=
  states_match
    (checked_parameterized_family_pair_certificate_input_view certificate).

Definition checked_parameterized_family_pair_certificate_output_states_match
    {params_first params_second}
    {first: checked_parameterized_view_transform_family params_first}
    {second: checked_parameterized_view_transform_family params_second}
    (certificate:
      checked_parameterized_family_pair_certificate first second) :=
  states_match
    (checked_parameterized_family_pair_certificate_output_view certificate).

Definition checked_parameterized_family_pair_certificate_refinement
    {params_first params_second}
    {first: checked_parameterized_view_transform_family params_first}
    {second: checked_parameterized_view_transform_family params_second}
    (certificate:
      checked_parameterized_family_pair_certificate first second)
    (source target: PolyLang.t) : Prop :=
  forall st_target0 st_source0 st_target_after,
    checked_parameterized_family_pair_certificate_input_states_match
      certificate st_target0 st_source0 ->
    PolyLang.instance_list_semantics target st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics source st_source0 st_source_after /\
      checked_parameterized_family_pair_certificate_output_states_match
        certificate st_target_after st_source_after.

Definition checked_parameterized_family_pair_certificate_accepted
    {params_first params_second}
    {first: checked_parameterized_view_transform_family params_first}
    {second: checked_parameterized_view_transform_family params_second}
    (certificate:
      checked_parameterized_family_pair_certificate first second)
    (before after: PolyLang.t) : Prop :=
  exists first_ok second_ok,
    mayReturn
      (cpvtf_check first (cpfpc_first_params certificate)
        before (cpfpc_mid_program certificate))
      first_ok /\
    first_ok = true /\
    cpvtf_side_condition first (cpfpc_first_params certificate)
      before (cpfpc_mid_program certificate) /\
    mayReturn
      (cpvtf_check second (cpfpc_second_params certificate)
        (cpfpc_mid_program certificate) after)
      second_ok /\
    second_ok = true /\
    cpvtf_side_condition second (cpfpc_second_params certificate)
      (cpfpc_mid_program certificate) after.

Theorem checked_parameterized_family_pair_certificate_public_semantic_sound :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         (certificate:
           checked_parameterized_family_pair_certificate first second)
         before after,
    checked_parameterized_family_pair_certificate_accepted
      certificate before after ->
    public_semantic_refinement
      (checked_parameterized_family_pair_certificate_input_view certificate)
      (checked_parameterized_family_pair_certificate_output_view certificate)
      before after.
Proof.
  intros params_first params_second first second certificate before after
         Haccepted.
  destruct Haccepted as [first_ok [second_ok Haccepted]].
  destruct Haccepted as
    [Hfirst_ret [Hfirst_ok [Hfirst_side
     [Hsecond_ret [Hsecond_ok Hsecond_side]]]]].
  destruct certificate as [first_params second_params mid].
  simpl in *.
  exact
    (checked_parameterized_public_semantic_family_pair_compose
       params_first params_second first second
       first_params second_params
       before mid after first_ok second_ok
       Hfirst_ret Hfirst_ok Hfirst_side
       Hsecond_ret Hsecond_ok Hsecond_side).
Qed.

Theorem checked_parameterized_family_pair_certificate_state_sound :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         (certificate:
           checked_parameterized_family_pair_certificate first second)
         before after st_target0 st_source0 st_target_after,
    checked_parameterized_family_pair_certificate_accepted
      certificate before after ->
    state_view_rel
      (checked_parameterized_family_pair_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      state_view_rel
        (checked_parameterized_family_pair_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros params_first params_second first second certificate
         before after st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  eapply
    (checked_parameterized_family_pair_certificate_public_semantic_sound
       params_first params_second first second
       certificate before after Haccepted);
    eauto.
Qed.

Theorem checked_parameterized_family_pair_certificate_refines :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         (certificate:
           checked_parameterized_family_pair_certificate first second)
         source target,
    checked_parameterized_family_pair_certificate_accepted
      certificate source target ->
    checked_parameterized_family_pair_certificate_refinement
      certificate source target.
Proof.
  unfold checked_parameterized_family_pair_certificate_refinement.
  intros params_first params_second first second certificate
         source target Haccepted
         st_target0 st_source0 st_target_after Hinput Htarget.
  eapply checked_parameterized_family_pair_certificate_state_sound;
    eauto.
Qed.

Theorem checked_parameterized_family_pair_certificate_semantic_refinement :
  forall params_first params_second
         (first: checked_parameterized_view_transform_family params_first)
         (second: checked_parameterized_view_transform_family params_second)
         (certificate:
           checked_parameterized_family_pair_certificate first second)
         source target st_target0 st_source0 st_target_after,
    checked_parameterized_family_pair_certificate_accepted
      certificate source target ->
    states_match
      (checked_parameterized_family_pair_certificate_input_view certificate)
      st_target0 st_source0 ->
    PolyLang.instance_list_semantics target st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics source st_source0 st_source_after /\
      states_match
        (checked_parameterized_family_pair_certificate_output_view certificate)
        st_target_after st_source_after.
Proof.
  intros params_first params_second first second certificate
         source target st_target0 st_source0 st_target_after
         Haccepted Hinput Htarget.
  eapply checked_parameterized_family_pair_certificate_state_sound;
    eauto.
Qed.

Theorem affine_validate_identity_view_sound :
  forall before after ok,
    mayReturn (AffineCore.validate before after) ok ->
    ok = true ->
    view_refinement same_state_view identity_view before after.
Proof.
  unfold view_refinement, same_state_view, identity_view.
  simpl.
  intros before after ok Hret Hok.
  eapply Transform.affine_validate_identity_relational_sound; eauto.
Qed.

Definition affine_identity_view_family
    : checked_view_transform_family := {|
  cvtf_input_view := same_state_view;
  cvtf_output_view := identity_view;
  cvtf_check := AffineCore.validate;
  cvtf_check_sound := affine_validate_identity_view_sound;
|}.

Definition affine_identity_view_certificate
    : checked_view_transform_certificate affine_identity_view_family :=
  tt.

Theorem general_validate_identity_view_sound :
  forall before after ok,
    mayReturn (AffineCore.validate_general before after) ok ->
    ok = true ->
    view_refinement same_state_view identity_view before after.
Proof.
  unfold view_refinement, same_state_view, identity_view.
  simpl.
  intros before after ok Hret Hok.
  eapply Transform.general_validate_identity_relational_sound; eauto.
Qed.

Definition general_identity_view_family
    : checked_view_transform_family := {|
  cvtf_input_view := same_state_view;
  cvtf_output_view := identity_view;
  cvtf_check := AffineCore.validate_general;
  cvtf_check_sound := general_validate_identity_view_sound;
|}.

Definition general_identity_view_certificate
    : checked_view_transform_certificate general_identity_view_family :=
  tt.

End StateView.
