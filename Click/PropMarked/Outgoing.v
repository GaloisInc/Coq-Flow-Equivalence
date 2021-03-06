
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


Module OutgoingPlaceNotMarked (Import PropMarked : PropMarkedType).
  Module PropMarkedTactics := PropMarkedTactics PropMarked.
  Import PropMarkedTactics.
  Import PropMarked.ClickMG. (* for stage_place *)

  Lemma outgoing_place_not_marked : forall l σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t),
        ~ prop_marked l p σ'.
  Proof.
    intros l σ σ' t Hwf Hstep t0 p Hprop.

    dependent destruction Hprop.
    * (* t = left_req *)
      unfold latch_transition_event, transition_event in Hstep.

      step_inversion_clean.

      apply neg_value_inj in Heq; try solve_val_is_bit.
      (* Know:

         H : σ left_ack = σ0 left_ack = σ0 left_req = neg_value (σ left_req)
         Heq : σ left_req = σ left_ack
      *)
      contradict H.
      repeat (rewrite_state_equiv; try solve_in_dom).
      simpl. reduce_eqb.
      rewrite Heq.
      apply bit_neq_neg_r; try solve_val_is_bit.

    * (* t = right_ack *)
      unfold latch_transition_event, transition_event in Hstep.
      step_inversion_clean.

      (* Know:
         H : σ right_req = σ0 right_req 
                         = neg_value (σ0 right_ack)
                         = neg_value (neg_value (σ right_ack))
         Heq : neg_value (σ right_ack) = σ right_req
      *)
      contradict H.
      repeat (rewrite_state_equiv; try solve_in_dom).
      simpl. reduce_eqb.
      rewrite <- Heq.
      apply bit_neq_neg_r; solve_val_is_bit.

    * (* t = left_ack (1) *)
      replace (latch_transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.
      step_inversion_clean.
      clear Hin0.
      destruct Hguard as [Hclk Hstate0].
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      (* Know:
         H : σ clk = σ0 clk = Bit0
         H0 : neg_value (σ l_ack) = σ0 l_ack = if_token l (σ0 state0) = if_token l (σ state0)
         Heq : neg_value (σ l_ack) = if_token l (neg_value (σ state0))
         Hunstable : if_token l (neg_value (σ state0)) <> σ l_ack
         Hclk : σ clk = Bit0
         Hstate0 : σ not_state0 = neg_value (σ state0)
      *)
      contradict H0.
      repeat (rewrite_state_equiv; try solve_in_dom).
      simpl. reduce_eqb.
      rewrite Heq.
      destruct l; simpl; [ | apply not_eq_sym ]; apply bit_neq_neg_r; simpl;
        try solve_val_is_bit.


    * (* t = right_req (1) *)
      replace (latch_transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.
      step_inversion_clean.
      clear Hin0.
      (* Know:
         H : σ clk = σ0 clk = Bit1
         H0 : σ old_clk = σ0 old_clk = Bit0
         Heq : neg_value (σ r_req) = σ state0
         Hunstable : σ state0 <> σ r_req
      *)
      (* Since the flop is unstable on clk+, it must be the case that
         latch_clk_function σ = Bit1 [ because of invariant ]
       Therefore, it must be the case that 
         σ (ack (latch_output l)) = σ (latch_state0 l)
       from latch_clk_function_Bit1_r_ack.
       But this means that
         σ r_ack = neg_value (σ r_req)
       By wf_right_env, this implies that
         σ r_req = σ state0
       which is a contradiction.
      *)


      assert (Hfun : latch_clk_function l σ = Bit1).
      { apply wf_clk_1; auto.
        { rewrite <- H (* σ0 clk *).
          rewrite_state_equiv; try solve_in_dom.
          simpl. auto.
        }
        { rewrite <- H0 (* σ0 old_clk *).
          rewrite_state_equiv; try solve_in_dom.
          simpl. auto.
        }
      }
      assert (Hin' : σ (req (latch_output l)) = σ (ack (latch_output l))).
      { destruct Hin as [Hin | Hin]; auto.
        unfold update in Hin. reduce_eqb.
        contradict Hin.
        apply bit_neq_neg_r; try solve_val_is_bit.
      }
      clear Hin.

      apply latch_clk_function_Bit1_iff in Hfun; auto.
      destruct Hfun as [Hreq Hack].
      contradict Hunstable.
      simpl in *.
      rewrite Hin'.
      rewrite Hack.
      reflexivity.

    * (* t = right_req (2) *)
      replace (latch_transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.
      step_inversion_clean.
      clear Hin0.
      (* Know:
         H : neg_value (σ r_req) = σ0 r_req <> σ0 state0 = σ state0
         aka    σ r_req = neg_value (σ state0)
         Heq : neg_value (σ r_req) = σ state0
         Hunstable : σ state0 <> σ r_req
      *)
      contradict H.
      repeat (rewrite_state_equiv; try solve_in_dom).
      simpl. reduce_eqb.
      rewrite <- Heq; auto.

    * (* t = clk_fall_flop_marked *)
      replace (latch_transition_event l clk_fall σ)
          with (Event (latch_clk l) Bit0)
          in Hstep
          by auto.
      step_inversion_clean.
      clear Hdec.

      (* Know: H : Bit0 = σ0 clk = Bit1 *)
      contradict H. rewrite_state_equiv; try solve_in_dom.
      reduce_eqb; inversion 1.

    * (* t = clk_fall_state0_marked *)
      replace (latch_transition_event l clk_fall σ)
          with (Event (latch_clk l) Bit0)
          in Hstep
          by auto.
      step_inversion_clean.
      clear Hdec. 
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      contradict H. rewrite_state_equiv; try solve_in_dom.
      reduce_eqb; inversion 1.

    * (* t = left_req_clk_rise_marked *)
      replace (latch_transition_event l clk_rise σ)
          with (Event (latch_clk l) Bit1)
          in Hstep
          by auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      clear Hdec. 

      contradict H1.
      rewrite_state_equiv; try solve_in_dom.
      reduce_eqb; inversion 1.

    * (* t = right_ack_clk_rise_marked *)
      replace (latch_transition_event l clk_rise σ)
          with (Event (latch_clk l) Bit1)
          in Hstep
          by auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      clear Hdec. 

      absurd (σ0 (latch_clk l) = Bit0).
      { rewrite_state_equiv; try solve_in_dom.
        simpl. reduce_eqb.
      }
      { apply H1. (* latch_clk_function σ0 = Bit1 -> σ0 clk = Bit0 *)
        rewrite (latch_clk_function_equiv σ); auto.
        intros x Hx.
        rewrite_state_equiv; try (simpl; solve_space_set); auto.
      }

  Unshelve. all: exact (fun _ => true).

  Qed.

End OutgoingPlaceNotMarked.
