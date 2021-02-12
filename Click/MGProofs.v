
Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import StateSpace.MarkedGraphs.
Require Import StateSpace.RelateTrace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import MarkedGraph.
Require Import Click.Definitions.
Require Import Click.Invariants.
Require Import Click.MG.

Require Import Click.PropMarked.PropMarked.
Require Import Click.PropMarked.Step.
Require Import Click.PropMarked.Outgoing.
Require Import Click.PropMarked.StepPreserved.

Require Import Omega.


Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.


Module ClickMGProofs (Export PropMarked : PropMarkedType).

  Export PropMarked.ClickMG.
  Export ClickTactics.

  Module Import PropMarkedTactics := PropMarkedTactics PropMarked.
  Module Import StepImpliesPropMarked := StepImpliesPropMarked PropMarked.
  Module Import OutgoingPlaceNotMarked := OutgoingPlaceNotMarked PropMarked.
  Module Import StepPreservation := StepPreservation PropMarked.


  (* The theorem *)
  Theorem MG_refines_stage : forall l,
      traces_of (latch_stage_with_env l) (σR l)
    ⊆ traces_of (latch_stage_MG_SS l) (init_stage_MG_state l).
  Proof.
    unfold traces_of.
    intros l t Hstage.
    destruct Hstage as [τ Hstage].
    (* Need to define a relation between <t,τ> acceepted by (latch_stage l) and
    <t,τ'> accepted by (stage_MG_SS l in_flag), and then prove that whenever
    latch_stage l ⊢ σR l →*{t} τ, there exists a τ' such that
    latch_stage l ⊢ init_stage_MG_state →*{t} τ'. *)
  Abort.


  (** When are a state and a marking related? *)

  Inductive state_relate_marking (l : latch even odd) : state name -> marking (latch_stage_MG l) -> Prop :=
  | R_init : state_relate_marking l (σR l) (init_marking (latch_stage_MG l))
  | R_step σ σ' t m m' : 
    state_relate_marking l σ m ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    is_enabled _ t m ->
    (forall {t1 t2} (p : stage_place t1 t2), m' _ _ p = fire t _ m _ _ p) ->
    state_relate_marking l σ' m'
  | R_Eps σ σ' m:
    state_relate_marking l σ m ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    state_relate_marking l σ' m
  .


  (** If σ1 is related to σ2 via t, then σ1 and σ2 are equal on all transition names.
  *)
  Lemma stage_relate_trace_domain : forall l σ1 t σ2,
    relate_trace name (latch_stage_with_env l) (latch_stage_MG_SS l) 
                      (σR l) (init_stage_MG_state l)
                      σ1 t σ2 ->
    forall x tr,
      x = @transition_name name _ (latch_stage_MG l) _ tr ->
      σ1 x = σ2 x.
  Proof.
    intros l σ1 t σ2 Hrelate x tr Hx.
    subst.
    eapply (relate_trace_domain _ (latch_stage_with_env l)
                                  (latch_stage_MG_SS l)
            (σR l) (init_stage_MG_state l)); eauto with click.
    2:{ apply stage_internal_disjoint. }
    2:{ apply stage_MG_internal_disjoint. }
    2:{ apply wf_MG_SS. }
    2:{ rewrite dom_latch_stage_with_env.
        to_in_list_dec. simpl.
        destruct tr; simpl; reduce_eqb; auto.
      }
    2:{ unfold latch_stage_MG_SS. rewrite dom_MG_SS.
        destruct tr; solve_space_set.
    }
    intros x Hx1 Hx2.
    unfold latch_stage_MG_SS in Hx2; rewrite dom_MG_SS in Hx2.
    rewrite dom_latch_stage_with_env in Hx1.

    unfold init_stage_MG_state, σR. simpl.

    to_in_list_dec.
    simpl in Hx1, Hx2.
    repeat (compare_next; auto).
  Qed.

  Lemma state_relate_marking_equiv : forall l σ m1 m2,
    state_relate_marking l σ m1 ->
    (forall t1 t2 (p : stage_place t1 t2), m1 _ _ p = m2 _ _ p) ->
    state_relate_marking l σ m2.
  Proof.
    intros l σ m1 m2 Hrelate Hm12.
    replace m2 with m1; auto.
    (* functional extensionality *)

    apply functional_extensionality_dep_good.
    intros t1.
    apply functional_extensionality_dep_good.
    intros t2.
    apply functional_extensionality.
    intros p.
    apply Hm12.
  Qed.




  Arguments fire_in_state {name transition transition_dec} MG {MG_scheme}.
  (** Unfolding the definition of fire_in_state *)
  Lemma fire_in_state_place : forall l t σ t1 t2 (p : stage_place t1 t2),
    fire_in_state (latch_stage_MG l) t σ (place_name (latch_stage_MG l) p)
    = if t =? t2 then dec_value (σ (stage_place_name l p))
      else if t =? t1 then inc_value (σ (stage_place_name l p))
      else σ (stage_place_name l p).
  Proof.
    intros l t σ t1 t2 p.
    unfold fire_in_state.
    rewrite name_to_place_eq.
    compare_next; auto.
    { (* contradiction *) inversion p; subst; find_contradiction. }
  Qed.


  Lemma state_relate_marking_implies : forall l σ t σ',
    relate_trace name (latch_stage_with_env l) (latch_stage_MG_SS l)
                      (σR l) (init_stage_MG_state l)
                      σ t σ' ->
    state_relate_marking l σ (state_to_marking σ').
  Proof.
    intros l σ t σ' Hrelate.
    induction Hrelate as [ | ? ? ? ? Hrelate IH Hstep
                           | ? ? ? ? Hrelate IH Hstep
                           | ? ? ? ? ? ? Hrelate IH Hstep1 Hstep2].
    * eapply state_relate_marking_equiv; [apply R_init | ].
      intros t1 t2 p. simpl.
      destruct l; destruct p; simpl;
          unfold init_marking_flag, state_to_marking, init_stage_MG_state;
          simpl; try reduce_eqb; auto.

    * eapply R_Eps; eauto.
    * inversion Hstep. (* contradiction *)
    * inversion Hstep2 as [ ? ? ? ? t' ? Henabled | ]; subst.
      eapply R_step; eauto.
      { unfold latch_transition_event, transition_event.
        replace (σ1 (transition_name t')) with (σ2 (transition_name t')).
        2:{ symmetry; eapply stage_relate_trace_domain; eauto. }
        exact Hstep1.
      }
      { intros t1 t2 p.
        unfold fire.
        assert (t1 <> t2).
        { intro; subst. inversion p. }
        reduce_eqb.
        unfold state_to_marking.
        rewrite_state_equiv.
        2:{ right. do 3 eexists. reflexivity. }

        assert (@transition_name name _ (latch_stage_MG l) _ t'
             <> @place_name _ _ (latch_stage_MG l) _ t1 t2 p).
        { apply transition_place_name_disjoint. }
        reduce_eqb.

        replace (fire_in_state (stage_MG (latch_in_flag l) (latch_to_token_flag l))
                               t' σ2 (place_name (latch_stage_MG l) p))
          with  (fire_in_state (latch_stage_MG l)
                               t' σ2 (place_name (latch_stage_MG l) p))
          by reflexivity.
        rewrite fire_in_state_place.
        repeat compare_next; auto.
        + rewrite val_to_nat_dec; auto.
        + rewrite val_to_nat_inc; auto.

          replace (stage_place_name l p)
            with (place_name (latch_stage_MG l) p)
            by reflexivity.
          eapply places_all_numbers.
          2:{ eapply relate_trace_project_right; eauto. }
          { unfold init_stage_MG_state. simpl.
            destruct p; simpl; reduce_eqb.
          }
        }
  Qed.



Lemma eps_from_σR : forall l σ,
      latch_stage_with_env l ⊢ σR l →*{t_empty} Some σ ->
      forall x, x ∈ space_output (latch_stage_with_env l) ->
      σ x = σR l x.
Proof.
  intros l σ Hstep x Hx.
  dependent induction Hstep; subst; auto.
  erewrite wf_scoped; [ | | eauto | intro; inversion 1 |]; auto.
  { solve_set. }
Qed.




Lemma latch_clk_function_is_bit : forall l σ,
    wf_stage_state l σ ->
    val_is_bit (latch_clk_function l σ).
Proof.
  intros l σ Hwf.
  assert (Hlreq : val_is_bit (σ (req (latch_input l)))) by solve_val_is_bit.
  assert (Hstate0 : val_is_bit (σ (latch_state0 l))) by solve_val_is_bit.
  assert (Hrack :  val_is_bit (σ (ack (latch_output l)))) by solve_val_is_bit.
  destruct Hwf as [Hbits Hctrl Hdp Hhidden].
  unfold latch_clk_function.
  destruct l; simpl in *.
  * unfold clk_defn.
    rewrite Hctrl. simpl.
    inversion Hlreq; auto;
    inversion Hstate0; auto;
    inversion Hrack; auto;
    simpl; solve_val_is_bit.

  * unfold tok_clk_defn.
    rewrite Hctrl. simpl.
    inversion Hlreq; auto;
    inversion Hstate0; auto;
    inversion Hrack; auto;
    simpl; solve_val_is_bit.
Qed.
Hint Resolve latch_clk_function_is_bit : wf.


  Lemma state_relate_marking_steps : forall l σ m,
    state_relate_marking l σ m ->
    exists tr, latch_stage_with_env l ⊢ σR l →*{tr} Some σ.
  Proof.
    intros l σ m Hrelate.
    induction Hrelate.
    * exists t_empty. constructor.
    * destruct IHHrelate as [tr IH].
      exists (tr ▶ latch_transition_event l t σ).
      econstructor; eauto.
    * destruct IHHrelate as [tr IH].
      exists tr.
      econstructor; eauto.
  Qed.


  Lemma relate_implies_marked : forall l σ m,
    state_relate_marking l σ m ->
    forall {t1 t2} (p : stage_place t1 t2),
      prop_marked l p σ ->
      0 < m _ _ p.
  Proof.   (* by induction on state_relate_marking *)
    intros l σ m Hrelate.
    induction Hrelate as [ | ? ? ? ? ? Hrelate IH Hstep Henabled Hm'
                           | ? ? ? Hrelate IH Hstep]; intros t1 t2 p Hp.
    * apply init_relate_implies_marked; auto.
    * assert (Hwf : wf_stage_state l σ).
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state; eauto.
      }
      assert (Hwf' : Invariants.wf_lack_clk_Bit0 l σ).
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        unfold Invariants.wf_lack_clk_Bit0.
        eapply Invariants.wf_lack_clk_Bit0_steps; eauto.
      }

      unfold is_enabled in Henabled.
      rewrite Hm'.
      unfold fire.
      compare_next.
      { inversion p; subst; find_contradiction. }
      compare_next.
      { (* t = t2 *) contradict Hp.
        eapply outgoing_place_not_marked; eauto.
      }
      compare_next.
      { omega. }
      { apply IH.
        eapply disjoint_place_marked; eauto.
      }
    * apply IH.
      eapply relate_implies_marked_eps; eauto.
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state; eauto.
      }
  Qed.

  Theorem state_related_enabled : forall l σ σ' t m,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    state_relate_marking l σ m ->
    is_enabled _ t m.
  Proof.
    intros.
    intros t0 p.
    assert (prop_marked l p σ).
    { eapply step_implies_prop_marked; eauto. }
    eapply relate_implies_marked; eauto.
  Qed.


  Lemma step_implies_bit : forall l σ x v σ',
    wf_stage_state l σ ->

    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    val_is_bit v.
  Proof.
    intros ? ? ? ? ? Hwf Hstep.
    assert (v = σ' x).
    { apply wf_update in Hstep; auto. }
    subst.
    assert (x ∈ space_domain (latch_stage_with_env l)).
    { apply wf_space in Hstep; auto.
      unfold space_domain. solve_set.
    }
    apply step_wf_state_lemma in Hstep; auto.
    clear Hwf.
    eapply wf_all_bits; eauto.
  Qed.

Ltac destruct_bit v :=
  match goal with
  | [ H : val_is_bit v |- _ ] => inversion H; subst
  | [ H : wf_stage_state ?l ?σ |- _ ] =>
    match v with
    | (σ ?x) => let H' := fresh "H" in
                assert (H' : val_is_bit (σ x))
                  by (apply (@wf_all_bits l); auto; unfold space_domain; simpl; solve_set);
                inversion H'; my_subst
   end
  end.

Ltac solve_bit_neq_neg :=
  match goal with
  | [ H : ?v <> ?v' |- _ ] => destruct_bit v;
                              destruct_bit v';
                              auto; find_contradiction
  end.


  Lemma MG_relate_trace_step_lemma : forall l,
    relate_trace_step_lemma _ (latch_stage_with_env l)
                              (latch_stage_MG_SS l)
        (σR l) (init_stage_MG_state l).
  Proof.
    intros l.
    unfold relate_trace_step_lemma.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ1 σ1' σ2 [x v] t Hstep Hrelate.
    assert (Hwfσ1 : wf_stage_state l σ1).
    { eapply step_wf_state.
      eapply relate_trace_project_left.
      eauto.
    }
    assert (Hv : val_is_bit v).
    { eapply step_implies_bit; eauto. }

    assert (Hwf : well_formed (latch_stage_with_env l)) by (apply latch_stage_well_formed).
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { destruct Hwf. eapply wf_space; eauto. }
    assert (Ht : exists t, x = @transition_name _ _ (latch_stage_MG l) _ t
                      /\   v = @transition_update_value _ _ (latch_stage_MG l) _ t (σ1 x)).
    {
      rewrite latch_stage_with_env_input in Hx.
      rewrite latch_stage_with_env_output in Hx.
      decompose_set_structure.
      + exists left_req; split; [ reflexivity | ].
        simpl.
        step_inversion_clean.
        clear Hin.
        apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
        rewrite val_is_bit_neg_neg in Hunstable; try solve_val_is_bit.
        rewrite <- Hunstable; auto.

      + exists left_ack; split; [ reflexivity | ].
        simpl.
        step_inversion_clean.
        clear Hin0.
        combine_state_equiv_on_complex; try (simpl; solve_space_set).

        subst.
        symmetry; apply val_is_bit_neq; try solve_val_is_bit.

      + exists right_req; split; [ reflexivity | ].
        step_inversion_clean.

        subst; simpl.
        symmetry; apply val_is_bit_neq; try solve_val_is_bit.

      + exists right_ack; split; [ reflexivity | ].
        step_inversion_clean.

        subst; simpl.
        symmetry; apply val_is_bit_neq; try solve_val_is_bit.

      + inversion Hv; subst.
        ++ (* Bit0 *) exists clk_fall; split; [reflexivity | reflexivity ].
        ++ (* Bit1 *) exists clk_rise; split; [reflexivity | reflexivity ].
    }
    destruct Ht as [t' [Hx' Hv']]; subst.
    eexists. econstructor; eauto.
    { eapply state_related_enabled; eauto.
      { eapply state_relate_marking_implies; eauto. }
    }
    { f_equal.
      eapply stage_relate_trace_domain; eauto.
    }
    { intros y Hy. reflexivity. }
  Unshelve.
    all: exact (fun _ => true).
  Qed.

  Lemma place_name_disjoint_SS : forall l t1 t2 (p : place (latch_stage_MG l) t1 t2),
    place_name (latch_stage_MG l) p ∉ space_domain (latch_stage_with_env l).
  Proof.
    intros.
    rewrite dom_latch_stage_with_env.
    destruct p; solve_space_set.
  Qed.

  Theorem MG_refines_stage : forall l,
    traces_of (latch_stage_with_env l) (σR l) ⊆ traces_of (latch_stage_MG_SS l) (init_stage_MG_state l).
  Proof.
    intros l.
    apply relate_trace_step_subset.
    { intros x Hdom1 Hdom2.
      unfold init_stage_MG_state.

      rewrite dom_latch_stage_with_env in Hdom1.
      simpl in Hdom1.
      decompose_set_structure; auto.
    }
    { apply MG_relate_trace_step_lemma. }
  Qed.


End ClickMGProofs.
