
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


Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.


Module StepImpliesPropMarked (Import PropMarked : PropMarkedType).
  Module PropMarkedTactics := PropMarkedTactics PropMarked.
  Import PropMarkedTactics.

  Section step_implies_prop_marked.

    Variable l : latch even odd.
    Variable σ σ' : state name.
    Hypothesis Hwf : wf_stage_state l σ.
(*    Hypothesis Hwf_stable : wf_stage_state_stable l σ. *)



  Definition step_implies_prop_marked_spec {t t0} (p : stage_place t0 t) :=
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    prop_marked l p σ.

  Lemma step_implies_prop_marked_left_ack_left_req :
    step_implies_prop_marked_spec left_ack_left_req.
  Proof.
    intros Hstep.
      constructor.
      unfold latch_transition_event, transition_event in Hstep.
      step_inversion_clean.

      apply val_is_bit_neg_inversion in Heq.
      2:{ solve_val_is_bit. }
      simpl.
      rewrite <- Heq.
      apply val_is_bit_neg_inversion.
      { solve_val_is_bit. }
      reflexivity.
  Unshelve. exact (fun _ => true).
  Qed.

  Lemma step_implies_prop_marked_clk_fall_left_ack :
    step_implies_prop_marked_spec clk_fall_left_ack.
  Proof.
    intros Hstep. 
      unfold latch_transition_event, transition_event in Hstep.

      step_inversion_clean.
      clear Hin0.
      combine_state_equiv_on_complex.
      { simpl. solve_space_set. }

      simpl in Hguard. destruct Hguard as [Hclk Hstate0].

      apply clk_fall_left_ack_marked; auto.
        apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
        simpl. rewrite <- Hunstable.
        destruct l; simpl; auto.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit; auto.
  Unshelve. exact (fun _ => true).
  Qed.

  Lemma step_implies_prop_marked_clk_rise_right_req :
    step_implies_prop_marked_spec clk_rise_right_req.
  Proof.
    intros Hstep.
      replace (latch_transition_event l right_req σ)
        with  (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
        in    Hstep
        by    auto.
      step_inversion_clean.
      clear Hin0.

      destruct Hin as [Hin | Hin].
      2:{ contradict Hin. unfold update. reduce_eqb.
          apply bit_neq_neg_r; try solve_val_is_bit.
      }
      apply clk_rise_right_req_marked_state0.
      { apply val_is_bit_neq_neg; auto.
        { right; solve_val_is_bit. }
      }
    Unshelve. exact (fun _ => true).
  Qed. 

  Lemma step_implies_prop_marked_right_req_right_ack :
    step_implies_prop_marked_spec right_req_right_ack.
  Proof.
    intros Hstep.
      constructor.
      unfold latch_transition_event, transition_event in Hstep.
      step_inversion_clean.
  Unshelve. exact (fun _ => true).
  Qed.


  Lemma step_implies_prop_marked_clock_fall :
    step_implies_prop_marked_spec clock_fall.
  Proof.
    intros Hstep.
    replace (latch_transition_event l clk_fall σ)
      with  (Event (latch_clk l) Bit0)
      in    Hstep
      by    auto.
    step_inversion_clean.
    clear Hdec.
    combine_state_equiv_on_complex. { simpl; solve_space_set. }
    

    assert (Hclk : σ (latch_clk l) = Bit1).
    { rewrite <- Heq in *.
      apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
    }

    { apply clock_fall_state0_marked; auto.
      { (* old_clk *) rewrite <- Hold_clk; auto. }
      intros Hstable; apply func_stable_equiv in Hstable.
      2:{ solve_space_set. }
      contradict Hstable; auto.
    }

  Unshelve.
    exact (fun _ => true).
  Qed.

  Lemma step_implies_prop_marked_left_req_clk_rise :
    step_implies_prop_marked_spec left_req_clk_rise.
  Proof.
    intros Hstep.
    replace (latch_transition_event l clk_rise σ)
      with  (Event (latch_clk l) Bit1)
      in    Hstep
      by    auto.

    step_inversion_clean.
    clear Hdec.
    combine_state_equiv_on_complex. { simpl; solve_space_set. }

    assert (Hclk : σ (latch_clk l) = Bit0).
    { apply val_is_bit_neq in Hunstable;
        try solve_val_is_bit.
      simpl. rewrite <- Hunstable.
      rewrite <- Heq. auto.
    }
    assert (Hlreq : σ (req (latch_input l)) = if_token l (σ (latch_state0 l))).
    { apply latch_clk_function_Bit1_l_req; auto. }

    apply left_req_clk_rise_marked; auto.
    { (* Uses latch_clk_function_Bit1_l_req and wf_left_env *)
      compare (σ (req (latch_input l)))
              (σ (ack (latch_input l))).
      2:{ symmetry. apply val_is_bit_neq; try solve_val_is_bit. }
      symmetry in Heq0.
      assert (Hreq : σ (req (latch_input l)) <> if_token l (σ (latch_state0 l))).
      { rewrite <- Heq0. 
        apply wf_left_env in Heq0; auto.
        rewrite Heq0.
        apply not_eq_sym.
        destruct l; apply bit_neq_neg_r; simpl; solve_val_is_bit.
      }
      contradict Hreq; auto.
    }
    { rewrite <- Hold_clk; auto. }

    Unshelve. exact (fun _ => true).

  Qed.

  Lemma step_implies_prop_marked_right_ack_clk_rise :
    step_implies_prop_marked_spec right_ack_clk_rise.
  Proof.
    intros Hstep.
    replace (latch_transition_event l clk_rise σ)
      with  (Event (latch_clk l) Bit1)
      in    Hstep
      by    auto.
    step_inversion_clean.
    clear Hdec.
    combine_state_equiv_on_complex.
    { simpl; solve_space_set. }


    assert (Hclk : σ (latch_clk l) = Bit0).
    { apply val_is_bit_neq in Hunstable;
        try solve_val_is_bit.
      simpl. rewrite <- Hunstable.
      rewrite <- Heq. auto.
    }
    assert (Hrack : σ (ack (latch_output l)) = σ (latch_state0 l)).
    { apply latch_clk_function_Bit1_r_ack; auto. }

    apply right_ack_clk_rise_marked; auto.
    { (* Uses latch_clk_function_Bit1_r_ack and wf_right_env *)
      compare (σ (req (latch_output l)))
              (σ (ack (latch_output l))); auto.
      assert (Hneq1 : σ (req (latch_output l)) = neg_value (σ (ack (latch_output l)))).
      { symmetry; apply  val_is_bit_neq; try solve_val_is_bit. }
      assert (Hneq2 : σ (ack (latch_output l)) = neg_value (σ (req (latch_output l)))).
      { symmetry; apply  val_is_bit_neq; try solve_val_is_bit. }
      clear Hneq.
      assert (Hack : σ (ack (latch_output l)) = σ (latch_state0 l)).
      { apply latch_clk_function_Bit1_r_ack; auto. }
      apply wf_right_env in Hneq2; auto.
      contradict Hneq1.
      { rewrite Hneq2. rewrite Hack.
        apply bit_neq_neg_r; solve_val_is_bit.
      }
    }
    { rewrite <- Hold_clk. auto. }

    Unshelve. exact (fun _ => true).
  Qed.


  End step_implies_prop_marked.

  Lemma step_implies_prop_marked : forall l σ t σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t), prop_marked l p σ.
  Proof.
    intros l σ t σ' Hwf Hstep t0 p.
    dependent destruction p.
    { eapply step_implies_prop_marked_left_ack_left_req; eauto. }
    { eapply step_implies_prop_marked_clk_fall_left_ack; eauto. }
    { eapply step_implies_prop_marked_clk_rise_right_req; eauto. }
    { eapply step_implies_prop_marked_right_req_right_ack; eauto. }
    { eapply step_implies_prop_marked_clock_fall; eauto. }
    { eapply step_implies_prop_marked_left_req_clk_rise; eauto. }
    { eapply step_implies_prop_marked_right_ack_clk_rise; eauto. }
  Qed.


End StepImpliesPropMarked.
