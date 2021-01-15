Require Import Base.
Require Import Circuit.
Require Import Monad.
Require Import Setoid.

Require Import StateSpace.Definitions.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Import EnsembleNotation.
Open Scope ensemble_scope.


Section RelateTrace.

  Context (name : Set) `{name_dec : eq_dec name}.

  Variable S1 S2 : StateSpace name.
  Variable σ1_0 σ2_0 : state name.
  Hypothesis init_domain_consistent :
    forall x, x ∈ space_domain S1 ->
              x ∈ space_domain S2 ->
              σ1_0 x = σ2_0 x.

  (* input(SS1)=input(SS2)
     output(SS1)=output(SS2) *)
  Inductive relate_trace : state name -> trace name value -> state name -> Prop :=
  | relate_trace_nil :
    relate_trace σ1_0 t_empty σ2_0

  | relate_trace_left σ1 σ1' σ2 t :
    relate_trace σ1 t σ2 ->
    S1 ⊢ σ1 →{None} Some σ1' ->
    relate_trace σ1' t σ2

  | relate_trace_right σ1 σ2 σ2' t :
    relate_trace σ1 t σ2 ->
    S2 ⊢ σ2 →{None} Some σ2' ->
    relate_trace σ1 t σ2'

  | relate_trace_sync σ1 σ1' σ2 σ2' t e :
    relate_trace σ1 t σ2 ->
    S1 ⊢ σ1 →{Some e} Some σ1' ->
    S2 ⊢ σ2 →{Some e} Some σ2' ->
    relate_trace σ1' (t ▶ e) σ2'.

  Hypothesis internal_disjoint_1 : space_internal S1 ⊥ space_domain S2.
  Hypothesis internal_disjoint_2 : space_internal S2 ⊥ space_domain S1.

  Lemma relate_trace_domain : forall σ1 σ2 t,
    well_formed S1 ->
    well_formed S2 ->
    relate_trace σ1 t σ2 ->
    forall x, x ∈ space_domain S1 ->
              x ∈ space_domain S2 ->
              σ1 x = σ2 x.
  Proof.
    intros σ1 σ2 t Hwf1 Hwf2 Hrelate x Hx1 Hx2.
    assert (x ∉ space_internal S1).
    { (* if it were, it would be disjoint from dom(S2) *)
      intro Hx.
      find_contradiction.
    }
    assert (x ∉ space_internal S2).
    { (* if it were, it would be disjoint from dom(S1) *)
      intros Hx.
      find_contradiction.
    }

    induction Hrelate.
    * apply init_domain_consistent; auto.
    * assert (Hσ1' : σ1' x = σ1 x).
      { (* Since σ1 →{None} Some σ1', it must be the case that σ1 and σ1' only
        differ on internal wires *)
        eapply (wf_scoped _ Hwf1); eauto.
        { intros v; inversion 1. }
        { unfold space_domain in *. decompose_set_structure; solve_set. }
      }
      congruence.
    * assert (Hσ2' : σ2' x = σ2 x).
      { (* Since σ2 →{None} Some σ2', it must be the case that σ2 and σ2' only
        differ on internal wires *)
        eapply (wf_scoped _ Hwf2); eauto.
        { intros v; inversion 1. }
        { unfold space_domain in *. decompose_set_structure; solve_set. }
      }
      congruence.
    * destruct e as [y v].
      compare x y.
      + (* x = y *)
        assert (σ1' y = v).
        { (* another feature of well-formed step relations *) 
          eapply (wf_update _ Hwf1); eauto. 
        }
        assert (σ2' y = v).
        { (* another feature of well-formed step relations *)
          eapply (wf_update _ Hwf2); eauto.
        }
        congruence.
      + (* x <> y *)
        assert (σ1' x = σ1 x).
        { (* σ1 and σ1' must only vary on interal wires and y *) 
          eapply (wf_scoped _ Hwf1); eauto.
          { intros v'; inversion 1; subst; find_contradiction. }
          { unfold space_domain in *. decompose_set_structure; solve_set. }
        }
        assert (σ2' x = σ2 x).
        { (* σ2 and σ2' must only vary on interal wires and y *)
          eapply (wf_scoped _ Hwf2); eauto.
          { intros v'; inversion 1; subst; find_contradiction. }
          { unfold space_domain in *. decompose_set_structure; solve_set. }
        }
        congruence.
  Qed.

  Definition relate_trace_step_lemma := forall σ1 σ1' σ2 e t,
    S1 ⊢ σ1 →{Some e} Some σ1' ->
    relate_trace σ1 t σ2 ->
    exists σ2', S2 ⊢ σ2 →{Some e} Some σ2'.


  Theorem relate_trace_subset_lemma :
    relate_trace_step_lemma ->
    forall (σ1 : state name) t,
      S1 ⊢ σ1_0 →*{t} Some σ1 ->
      exists σ2, relate_trace σ1 t σ2.
  Proof.
    intros Hlemma σ1 t Hstep.
    remember (Some σ1) as τ1 eqn:Heqτ.
      generalize dependent σ1.
    induction Hstep as [ | | ]; intros σ1 Heqτ; subst.
    * inversion Heqτ; subst. rewrite <- H0.
      exists σ2_0. constructor.
    * unfold relate_trace_step_lemma in Hlemma.
      rename σ' into σ1'.
      destruct (IHHstep σ1' eq_refl) as [σ2' IH].
      specialize (Hlemma _ _ _ _ _ H IH).
      destruct Hlemma as [σ2 Hstep2].
      exists σ2.
      eapply relate_trace_sync; eauto.
    * rename σ' into σ1'.
      destruct (IHHstep σ1' eq_refl) as [σ2' IH].
      exists σ2'.
      eapply relate_trace_left; eauto.
  Qed.

  Lemma relate_trace_project_left : forall σ1 t σ2,
      relate_trace σ1 t σ2 ->
      S1 ⊢ σ1_0 →*{t} Some σ1.
  Proof.
    intros σ1 t σ2 Hrelate.
    induction Hrelate.
    * constructor.
    * eapply stepsEps; eauto.
    * apply IHHrelate.
    * eapply steps1; eauto.
  Qed.

  Lemma relate_trace_project_right : forall σ1 t σ2,
      relate_trace σ1 t σ2 ->
      S2 ⊢ σ2_0 →*{t} Some σ2.
  Proof.
    intros σ1 t σ2 Hrelate.
    induction Hrelate.
    * constructor.
    * apply IHHrelate.
    * eapply stepsEps; eauto.
    * eapply steps1; eauto.
  Qed.


  Theorem relate_trace_step_subset :
    relate_trace_step_lemma ->
    traces_of S1 σ1_0 ⊆ traces_of S2 σ2_0.
  Proof.
    intros Hlemma t H1.
    destruct H1 as [σ1 H1].
    destruct (relate_trace_subset_lemma Hlemma _ _ H1) as [σ2 Hrelate].
    exists σ2.
    eapply relate_trace_project_right; eauto.
  Qed.

End RelateTrace.


Section UnionStateSpaceRefinement.

  Context {name : Set} `{name_dec : eq_dec name}.
  Variable S1 S2 S1' S2' : StateSpace name.
  Variable σ0 σ0' : state name.

  Theorem union_refinement : 
    state_equiv_on (space_domain (S1 ∥ S2) ∩ space_domain (S1' ∥ S2'))
                   (Some σ0) (Some σ0') ->
    traces_of S1 σ0 ⊆ traces_of S1' σ0' ->
    traces_of S2 σ0 ⊆ traces_of S2' σ0' ->
    traces_of (S1 ∥ S2) σ0 ⊆ traces_of (S1' ∥ S2') σ0'.
  Proof.
    intros Hequiv H1 H2.
    apply relate_trace_step_subset.
    { intros x Hx Hx'.
      apply Hequiv.
      solve_set.
    }
    unfold relate_trace_step_lemma.
    intros σ σ' σT e t Hstep1 Hrelate.

    inversion Hrelate; subst.
    * inversion Hstep1; subst.
      + (* e ∉ domain S2 *)
        assert (H1' : t_empty ▶ e ∈ traces_of S1' σT).
        { apply H1.
          exists σ'. econstructor; eauto. constructor.
        }
        destruct H1' as [σT' H1'].
        assert (Hstep' : exists σT'', S1' ⊢ σT →{Some e} Some σT'') by admit (* lemma *).
        destruct Hstep' as [σT'' Hstep'].
        exists σT''.
        apply union_step_1; auto.
        (* These  two rely on the relation between the domain of Si and the domain of Si'. *)
        admit (* why? *).
        admit (* why? *).
      + (* e ∉ domain S1 *)
        admit (* same as above *).
      + admit.

  Abort.


      
End UnionStateSpaceRefinement.

