
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


Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.



Module StepPreservation (Import PropMarked : PropMarkedType).
  Module PropMarkedTactics := PropMarkedTactics PropMarked.
  Import PropMarkedTactics.
  Import PropMarked.ClickMG. (* for stage_place *)
  Module Step := StepImpliesPropMarked PropMarked.
  Import Step.


  (** Lemmas **)

Lemma INVARIANT : forall σ l,
            wf_stage_state l σ ->
            σ (ack (latch_input l)) = if_token l (neg_value (σ (latch_state0 l))) ->
            latch_clk_function l σ = Bit0 ->
            σ (latch_clk l) = Bit0.
Admitted.


  Lemma transition_preserves_state0_old_clk : forall l σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
       σ' (latch_state0 l) = σ (latch_state0 l)
    /\ (σ' (latch_old_clk l) = if t =? clk_fall then Bit0 else σ (latch_old_clk l)).
  Proof.
    intros l σ σ' t Hwf Hstep.
    destruct t; try find_contradiction;
        unfold latch_transition_event, transition_event in Hstep.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      repeat (rewrite_state_equiv; try solve_in_dom).
      auto.
    + step_inversion_clean.
      repeat (rewrite_state_equiv; try solve_in_dom).
      auto.
    + step_inversion_clean.
      repeat (rewrite_state_equiv; try solve_in_dom).
      auto.
    + step_inversion_clean.
      repeat (rewrite_state_equiv; try solve_in_dom).
      auto.
    + replace (transition_name clk_rise)
        with  (latch_clk l)
        in    Hstep
        by    auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      rewrite_state_equiv; try (simpl; solve_in_dom).
      rewrite_state_equiv; try (simpl; solve_in_dom).
      simpl.
      reduce_eqb.
      auto.
    + replace (transition_name clk_fall)
        with  (latch_clk l)
        in    Hstep
        by    auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      repeat (rewrite_state_equiv; try solve_in_dom).
      simpl. reduce_eqb.
      split; auto.

  Unshelve. all:exact (fun _ => true).
  Qed.


  Lemma transition_preserves_state0  : forall l σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    σ' (latch_state0 l) = σ (latch_state0 l).
  Proof.
    intros ? ? ? ? Hwf Hstep.
    apply transition_preserves_state0_old_clk in Hstep; auto.
    destruct Hstep; auto.
  Qed.
  Lemma transition_preserves_old_clk : forall l σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    t <> clk_fall ->
    σ' (latch_old_clk l) = σ (latch_old_clk l).
  Proof.
    intros ? ? ? ? Hwf Hstep Ht.
    apply transition_preserves_state0_old_clk in Hstep; auto.
    destruct Hstep as [ ? Hstep]; auto.
    rewrite Hstep.
    compare_next; auto.
  Qed.
  Lemma transition_preserves_old_clk_fall : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l clk_fall σ)} Some σ' ->
    σ' (latch_old_clk l) = Bit0.
  Proof.
    intros ? ? ? Hwf Hstep.
    apply transition_preserves_state0_old_clk in Hstep; auto.
    destruct Hstep as [ ? Hstep]; auto.
  Qed.


  Lemma latch_clk_function_l_ack_fall : forall l σ σ',
    wf_stage_state l σ ->
    wf_stage_state l σ' ->
    σ (latch_state0 l) = σ' (latch_state0 l) ->
       σ (ack (latch_output l)) <> σ' (ack (latch_output l))
    \/ σ (req (latch_input l)) <> σ' (req (latch_input l)) ->
    latch_clk_function l σ = Bit1 ->
    latch_clk_function l σ' = Bit0.
  Proof.
    intros ? ? ? Hwf Hwf' Hstate0 Hneq Hfun.
    unfold latch_clk_function, clk_defn, tok_clk_defn in *.
    erewrite wf_ctrl_reset_n in *; eauto.
    transitivity (neg_value Bit1); auto.
    rewrite <- Hstate0; clear Hstate0.

    assert (Hstate0_bit : val_is_bit (σ (latch_state0 l))) by solve_val_is_bit.
    assert (Hrack_bit : val_is_bit (σ (ack (latch_output l)))) by solve_val_is_bit.
    assert (Hlreq_bit : val_is_bit (σ (req (latch_input l)))) by solve_val_is_bit.
    assert (Hrack_bit' : val_is_bit (σ' (ack (latch_output l)))) by solve_val_is_bit.
    assert (Hlreq_bit' : val_is_bit (σ' (req (latch_input l)))) by solve_val_is_bit.
    remember (σ (latch_state0 l)) as xstate0.
    remember (σ (ack (latch_output l))) as xrack.
    remember (σ (req (latch_input l))) as xlreq.
    remember (σ' (ack (latch_output l))) as xrack'.
    remember (σ' (req (latch_input l))) as xlreq'.

        inversion Hstate0_bit as [Hbit | Hbit];
          rewrite <- Hbit in *; clear xstate0 Hbit Hstate0_bit;
        inversion Hrack_bit as [Hbit | Hbit];
          rewrite <- Hbit in *; clear xrack Hbit Hrack_bit;
        inversion Hlreq_bit as [Hbit | Hbit];
          rewrite <- Hbit in *; clear xlreq Hbit Hlreq_bit;
        inversion Hrack_bit' as [Hbit | Hbit];
          rewrite <- Hbit in *; clear xrack' Hbit Hrack_bit';
        inversion Hlreq_bit' as [Hbit | Hbit];
          rewrite <- Hbit in *; clear xlreq' Hbit Hlreq_bit';
        simpl; simpl in Hfun;
        try match goal with
        | [ Hneq : ?x <> ?x \/ ?y <> ?y |- _ ] => destruct Hneq; find_contradiction; fail
        | [ |- _ ] => destruct l; inversion Hfun; auto; fail
        end.
  Qed.

  (********************)
  (* Non-epsilon step *)
  (********************)



Section disjoint_place_marked.
  Import PropMarkedTactics.

  Variable l : latch even odd.
  Variable σ σ' : state name.
  Variable t : token_transition.
  Hypothesis Hstep : latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ'.
  Hypothesis Hwf : wf_stage_state l σ. 

  Definition disjoint_place_marked_lemma {t1 t2} (p : stage_place t1 t2) :=
    t1 <> t -> t2 <> t ->
    prop_marked l p σ' ->
    prop_marked l p σ.

  Lemma disjoint_place_marked_left_ack_left_req : disjoint_place_marked_lemma left_ack_left_req.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    constructor.
      rewrite_back_wf_scoped; try distinguish_events.
      rewrite_back_wf_scoped; try distinguish_events.
      auto.
    Unshelve. 
      all: apply latch_stage_well_formed.
  Qed.

  Lemma disjoint_place_marked_clk_fall_left_ack : disjoint_place_marked_lemma clk_fall_left_ack.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    * compare t clk_rise.
      { (* if the clk+ event happens, contradiction iwth (σ (latch_clk l) = Bit0) *)
        contradict H.
        replace (latch_transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        erewrite (wf_update _ (latch_stage_well_formed l) _ _ _ _ Hstep).
        inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_back_wf_scoped; try distinguish_events.
        auto.
      }

      assert (Hack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
      { rewrite_back_wf_scoped; try distinguish_events.
        auto.
      }

      assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
      { eapply transition_preserves_state0; eauto. }

      apply clk_fall_left_ack_marked; auto.
      { rewrite <- Hclk; auto. }
      { rewrite <- Hack.
        rewrite H0 (* σ0 lack *).
        rewrite Hstate0.
        reflexivity.
      }

    Unshelve. all: auto. 
  Qed.

  Lemma disjoint_place_marked_clk_rise_right_req : disjoint_place_marked_lemma clk_rise_right_req.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    * 

      compare t clk_fall.
      { replace (latch_transition_event l clk_fall σ)
          with  (Event (latch_clk l) Bit0)
          in    Hstep
          by    auto.
        step_inversion_clean.
        combine_state_equiv_on_complex; try (simpl; solve_space_set).

        contradict H (* σ0 clk = Bit1 *).
        rewrite_state_equiv; simpl; try solve_in_dom.
        reduce_eqb.
      }

      assert (Hold_clk : σ (latch_old_clk l) = Bit0).
      { erewrite <- transition_preserves_old_clk; eauto. }

      { assert (Hclk' : σ0 (latch_clk l) = σ (latch_clk l)).
        { eapply wf_scoped; eauto; try distinguish_events.
          rewrite latch_stage_with_env_input, latch_stage_with_env_output.
          solve_space_set.
        }
        apply clk_rise_right_req_marked; auto.
        rewrite <- Hclk'; auto.
      }

    * apply clk_rise_right_req_marked_state0.
      intros Heq; contradict H.
      erewrite transition_preserves_state0; eauto.

      erewrite wf_scoped; eauto.
      2:{ rewrite  latch_stage_with_env_input, latch_stage_with_env_output.
          solve_space_set.
      }
      distinguish_events.
  Unshelve. exact (fun _ => true).
  Qed.

  Lemma disjoint_place_marked_right_req_right_ack : disjoint_place_marked_lemma right_req_right_ack.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.

    apply rreq_rack_marked.
    rewrite_back_wf_scoped; try distinguish_events.
    rewrite_back_wf_scoped; try distinguish_events.
    auto.

  Unshelve. all:solve_wf.
  Qed.

  Lemma disjoint_place_marked_clock_fall : disjoint_place_marked_lemma clock_fall.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.

    * assert (Hwf' : wf_stage_state l σ0).
      { eapply step_wf_state_lemma; eauto. }
      assert (Hclk : σ (latch_clk l) = Bit1).
      { rewrite_back_wf_scoped; auto; distinguish_events. }
      assert (Hold_clk : σ (latch_old_clk l) = Bit0).
      { erewrite <- transition_preserves_old_clk; eauto. }
      assert (Hstate0 : σ (latch_state0 l) = σ0 (latch_state0 l)).
      { erewrite <- transition_preserves_state0; eauto. }
      assert (Hfun : latch_clk_function l σ = Bit1).
      { apply wf_clk_1; auto. }


      apply clock_fall_flop_marked; auto.
      apply func_stable_equiv; try solve_space_set.
      congruence.


  * assert (Hclk : σ (latch_clk l) = Bit1).
    { rewrite_back_wf_scoped; auto; distinguish_events. }
    assert (Hold_clk : σ (latch_old_clk l) = Bit1).
    { erewrite <- transition_preserves_old_clk; eauto. }

    assert (Hfun : latch_clk_function l σ0 = Bit0).
    { compare (latch_clk_function l σ0) Bit1.
      2:{ apply not_eq_sym in Hneq.
          apply val_is_bit_neq in Hneq; try solve_val_is_bit.
          { apply latch_clk_function_bit; auto.
            eapply step_wf_state_lemma; eauto.
          }
      }
      { contradict H1 (* latch_clk_component stable *).
        apply func_stable_equiv; try solve_space_set.
        rewrite Heq. auto.
      }
    }

    assert (Hlack : σ (req (latch_input l)) = σ (ack (latch_input l)) ->
                    latch_clk_function l σ = Bit0).
    { intros Heq.
      compare (latch_clk_function l σ) Bit1; auto.
      2:{ apply not_eq_sym in Hneq.
          apply val_is_bit_neq in Hneq; try solve_val_is_bit.
      }
      { apply latch_clk_function_Bit1_l_req in Heq0; auto.
        contradict Heq0.
        rewrite Heq.
        symmetry in Heq; apply wf_left_env in Heq; auto.
        rewrite Heq.
        apply not_eq_sym.
        destruct l; apply bit_neq_neg_r; simpl; try solve_val_is_bit.
      }
    }

    assert (Hrreq : σ (ack (latch_output l)) = neg_value (σ (req (latch_output l))) ->
                    latch_clk_function l σ = Bit0).
    { intros Heq.
      compare (latch_clk_function l σ) Bit1; auto.
      2:{ apply not_eq_sym in Hneq.
          apply val_is_bit_neq in Hneq; try solve_val_is_bit.
      }
      { apply latch_clk_function_Bit1_r_ack in Heq0; auto.
        contradict Heq0.
        rewrite Heq.
        apply wf_right_env in Heq; auto.
        rewrite Heq.
        apply not_eq_sym.
        destruct l; apply bit_neq_neg_r; simpl; try solve_val_is_bit.
      }
    }

    apply clock_fall_state0_marked; auto.
    { intros Hstable.
      apply func_stable_equiv in Hstable; try solve_space_set.
      rewrite Hclk in Hstable.
      symmetry in Hstable.

      compare t left_req.
      { assert (Hprop_marked : prop_marked l left_ack_left_req σ ).
        { eapply step_implies_prop_marked; eauto. }
        inversion Hprop_marked;
          subst; clear Hprop_marked; rename H2 into Hprop_marked.
        symmetry in Hprop_marked.
        specialize (Hlack Hprop_marked).
        find_contradiction.
      }

      compare t right_ack.
      { assert (Hprop_marked : prop_marked l right_req_right_ack σ ).
        { eapply step_implies_prop_marked; eauto. }
        inversion Hprop_marked;
          subst; clear Hprop_marked; rename H2 into Hprop_marked.
        apply val_is_bit_neg_inversion in Hprop_marked; try solve_val_is_bit.
        symmetry in Hprop_marked.
        specialize (Hrreq Hprop_marked).
        find_contradiction.
      }

      { (* otherwise *)
        contradict Hfun.
        rewrite (latch_clk_function_equiv σ).
        { rewrite Hstable. inversion 1. }
        { intros x Hx.
          decompose_set_structure.
          { (* ctrl_reset_n *)
            replace (global_name "ctrl_reset_n") with ctrl_reset_n; auto.
            erewrite wf_ctrl_reset_n; eauto.
            erewrite wf_ctrl_reset_n; eauto.
            eapply step_wf_state_lemma; eauto.
          }
          { (* state0 *)
            transitivity (σ0 (latch_state0 l)); auto. 
            erewrite transition_preserves_state0; eauto.
          }
          { rewrite_back_wf_scoped; auto. distinguish_events. }
          { rewrite_back_wf_scoped; auto. distinguish_events. }
        }
      }
  }

  Unshelve.
    all: try solve_wf.
    all: exact (fun _ => true).

  Qed.




  Lemma disjoint_place_marked_left_req_clk_rise : disjoint_place_marked_lemma left_req_clk_rise.
  Proof.
    intros Ht1 Ht2 Hmarked.

    dependent destruction Hmarked.
    assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
    { eapply transition_preserves_state0; eauto. }

    (* Need to show:
       1. left_env is stable
       2. σ left_env = if_token l (σ state0)
       3. σ clk = Bit0
    *)
    compare t left_ack.
    { replace (latch_transition_event l left_ack σ)
        with  (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
        in    Hstep
        by    auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      
      destruct Hguard as [Hclk Hnot_state0].

      (* Know: σ lack <> σ lreq \/ σ lack = neg_value (σ lack) *)
      assert (Hneq : σ (ack (latch_input l)) <> σ (req (latch_input l))).
      { destruct Hin as [Hin1 | Hin2]; auto.
        + simpl.
          rewrite <- Hin1.
          apply not_eq_sym; apply bit_neq_neg_l; try solve_val_is_bit.
        + unfold update in Hin2. reduce_eqb.
          contradict Hin2.
          rewrite val_is_bit_neg_neg; try solve_val_is_bit.
      }
      clear Hin.
        
      contradict H0 (* σ0 lreq = if_token l (σ0 state0) *).
      rewrite_state_equiv; try solve_in_dom.
      rewrite_state_equiv; try solve_in_dom.
      simpl.
      replace (σ (local_name l "l_req"))
        with  (neg_value (σ (ack (latch_input l)))).
      2:{ apply val_is_bit_neq; try solve_val_is_bit. }
      simpl. rewrite Heq.
      destruct l;
        try apply bit_neq_neg_l;
        try (apply not_eq_sym; apply bit_neq_neg_l);
        try solve_val_is_bit.
    }

    assert (Hlack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
    { rewrite_back_wf_scoped; try distinguish_events; auto. }
    assert (Hlreq : σ0 (req (latch_input l)) = σ (req (latch_input l))).
    { rewrite_back_wf_scoped; try distinguish_events; auto. }

    compare t clk_fall.
    { replace (latch_transition_event l clk_fall σ)
        with  (Event (latch_clk l) Bit0)
        in    Hstep
        by    auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      assert (Hclk : σ (latch_clk l) = Bit1).
      { apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
        simpl; rewrite <- Hunstable.
        rewrite <- Heq.
        auto.
      }

      assert (Hfun : latch_clk_function l σ0 = Bit0).
      { rewrite latch_clk_function_equiv with (σ' := σ); auto.
        intros x Hx.
        rewrite_state_equiv; try solve_in_dom.
        compare_next; [decompose_set_structure | ].
        compare_next; [decompose_set_structure | ].
        auto.
      }

      assert (Hstable : σ (ack (latch_input l)) = if_token l (neg_value (σ (latch_state0 l)))).
      { rewrite <- Hlack.
        apply val_is_bit_neg_inversion in H.
        2:{ rewrite Hlack. try solve_val_is_bit. }
        rewrite <- H.
        rewrite H0.
        rewrite Hstate0.
        destruct l; simpl; auto.
      }

      (* Know:  H :  σ0 lreq = neg (σ0 lack) 
                  => σ lreq = neg (σ lack)
                H0 : σ0 lreq = if_token l (σ0 state0)
                  => σ lreq = if_token l (σ state0)
                H1 : σ0 clk = Bit0
                  => σ clk = Bit1
                H2 : σ0 old_clk = Bit0

                Heq : latch_clk_function l σ = Bit0

                σ clk = Bit1
                σ old_clk = Bit1
      *)
    (* WTS: σ lreq = neg_value (σ lack)
            σ lreq = if_token l (σ state0)
            σ clk = Bit0
       But this is clearly not the case, so we need to find a contradiction.
       The contradiction is that it should not be the case that latch_clk_function l σ = Bit0
       if σ clk = Bit1 and the left environment and left_ack_component are stable.

       i.e. σ (ack (latch_input l)) = if_token l (neg_value (σ (latch_state0 l))) ->
            latch_clk_function l σ = Bit0 ->
            σ (latch_clk l) = Bit0
    *)
      
     contradict Hclk.
     rewrite INVARIANT; auto.
     inversion 1.
    }

    constructor.
    { rewrite <- Hlreq. rewrite <- Hlack. auto. }
    { rewrite <- Hlreq. rewrite <- Hstate0. auto. }
    { rewrite_back_wf_scoped; auto; try distinguish_events. }
(*    { erewrite <- transition_preserves_old_clk; eauto. }*)

  Unshelve.
    all: try solve_wf.
    all: exact (fun _ => true).

  Admitted (* depends on INVARIANT*).


  Lemma disjoint_place_marked_right_ack_clk_rise : disjoint_place_marked_lemma right_ack_clk_rise.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    rename H into H0_right_env (* σ0 rack = σ0 rreq *).
    rename H0 into H0_right_ack (* σ0 rack = σ0 state0 *).
    rename H1 into H0_clk (* σ0 clk = Bit0 *).
    rename H2 into H0_old_clk (* σ0 old_clk = Bit0 *).
    assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
    { eapply transition_preserves_state0; eauto. }

    (* Need to show:
       1. right_env is stable
       2. σ right_ack = σ state0
       3. σ clk = Bit0
       4. σ old_clk = Bit0
    *)
    compare t right_req.
    { replace (latch_transition_event l right_req σ)
        with  (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
        in    Hstep
        by    auto.
      step_inversion_clean.
      clear Hin0.

      (* Know: σ rreq = σ rack \/ σ rreq = σ0 rreq = σ0 rack = σ rack *)
      assert (Henv : σ (ack (latch_output l)) = σ (req (latch_output l))).
      { destruct Hin as [Hin1 | Hin2]; auto.
        simpl; rewrite Hin2.
        transitivity (σ0 (ack (latch_output l))).
        { rewrite_state_equiv; try solve_in_dom; auto. }
        rewrite H0_right_env.
        rewrite_state_equiv; auto; try solve_in_dom.
      }
      clear Hin.
        
      contradict H0_right_ack (* σ0 rack = σ0 state0 *).
      rewrite_state_equiv; try solve_in_dom.
      rewrite_state_equiv; try solve_in_dom.
      simpl.
      simpl in Henv. rewrite Henv.
      auto. (* Hunstable *)
    }

    assert (Hrack : σ0 (ack (latch_output l)) = σ (ack (latch_output l))).
    { rewrite_back_wf_scoped; try distinguish_events; auto. }
    assert (Hrreq : σ0 (req (latch_output l)) = σ (req (latch_output l))).
    { rewrite_back_wf_scoped; try distinguish_events; auto. }

    compare t clk_fall.
    { replace (latch_transition_event l clk_fall σ)
        with  (Event (latch_clk l) Bit0)
        in    Hstep
        by    auto.
      step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      assert (Hclk : σ (latch_clk l) = Bit1).
      { apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
        simpl; rewrite <- Hunstable.
        rewrite <- Heq.
        auto.
      }
      (* Know:
          Hclk : σ clk = Bit1
          Hstep+Hclk : σ old_clk = Bit1
          Heq : latch_clk_function l σ = Bit0
          
      *)
      symmetry in Heq.
      constructor.
      (* WHAT if this instance of prop_marked ONLY required latch_clk_function = bit0 and not also that clk = Bit0? *)
      { rewrite <- Hrreq. rewrite <- Hrack. auto. }
      { rewrite <- Hrack. rewrite <- Hstate0. auto. }
      { admit. }
      { admit. }
    }
      

    constructor.
    { rewrite <- Hrreq. rewrite <- Hrack. auto. }
    { rewrite <- Hrack. rewrite <- Hstate0. auto. }
    { rewrite_back_wf_scoped; auto; try distinguish_events. }
    { erewrite <- transition_preserves_old_clk; eauto. }

  Unshelve.
    all: try solve_wf.
    all: exact (fun _ => true).
  Admitted.

End disjoint_place_marked.
  

  Lemma disjoint_place_marked : forall l σ σ' t,
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    wf_stage_state l σ ->
    forall t1 t2 (p : stage_place t1 t2),
      t1 <> t ->
      t2 <> t ->
      prop_marked l p σ' ->
      prop_marked l p σ.
  Proof.
    
    intros l σ σ' t Hstep Hwf t1 t2 p Ht1 Ht2 Hmarked.
    dependent destruction p.
    * eapply disjoint_place_marked_left_ack_left_req; eauto.
    * eapply disjoint_place_marked_clk_fall_left_ack; eauto.
    * eapply disjoint_place_marked_clk_rise_right_req; eauto.
    * eapply disjoint_place_marked_right_req_right_ack; eauto.
    * eapply disjoint_place_marked_clock_fall; eauto.
    * eapply disjoint_place_marked_left_req_clk_rise; eauto.
    * eapply disjoint_place_marked_right_ack_clk_rise; eauto.
  Qed.

  (****************)
  (* Epsilon step *)
  (****************)

  Import PropMarkedTactics.

  (* Helper lemmas for relate_implies_marked below *)
  Lemma relate_implies_marked_eps : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    forall {t1 t2} (p : stage_place t1 t2),
    prop_marked l p σ' ->
    prop_marked l p σ.
  Proof.
    intros l σ σ' Hwf Hstep t1 t2 p Hp.
    dependent destruction Hp.
    * (* left_ack_left_req *) 
      (* Because σ0 left_ack = σ0 left_req, if σ →{None} σ0,
         then it must be the case that σ is equivalent to σ0 on left_ack and left_req. *)
      apply lack_lreq_marked.
      rewrite_back_wf_scoped.
      rewrite_back_wf_scoped.
      auto.

    * (* right_req_right_ack *)
      apply rreq_rack_marked.
      rewrite_back_wf_scoped.
      rewrite_back_wf_scoped.
      auto.

    * (* clk_fall_left_ack *)
      assert (Hclk : σ (latch_clk l) = Bit0).
      { rewrite_back_wf_scoped; auto. }
      assert (Hack : σ (ack (latch_input l)) = σ0 (ack (latch_input l))).
      { rewrite_back_wf_scoped; auto. }

      assert (Hstate0 : σ (latch_state0 l) = σ0 (latch_state0 l)).
      { apply step_implies_stage_eps in Hstep; auto.
        inversion Hstep; auto;
          find_contradiction;
          rewrite_state_equiv; try solve_in_dom; simpl; auto.
      }
      apply clk_fall_left_ack_marked; auto.
      rewrite Hack.
      rewrite H0 (* σ0 lack *).
      rewrite Hstate0.
      reflexivity.

(*    * (* clk_fall_left_ack *)
      assert (Hclk : σ (latch_clk l) = Bit0) by (rewrite_back_wf_scoped; auto).

      apply clk_fall_left_ack_state0_marked; auto.

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      + apply val_is_bit_neq in H2 (* σ clk <> σ old_clk *);
          auto; try solve_val_is_bit.
        rewrite <- H2. rewrite Hclk. auto.
      + contradict H0. (* σ old_clk = Bit1 *)
        rewrite <- H3. 2:{ solve_in_dom. }
        unfold update.
        rewrite <- H2. rewrite Hclk. simpl. inversion 1.
*)

    * assert (Hclk : σ (latch_clk l) = Bit1).
      { rewrite_back_wf_scoped; auto. }
      apply clk_rise_right_req_marked; auto.

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      + clear H5 H6 H7 (* extra constraints from step_implies_stage_eps *).
        contradict H0. (* old_clk *)
        rewrite_state_equiv.
        2:{ solve_in_dom. }
        reduce_eqb.
        rewrite Hclk; inversion 1.

      + contradict H0 (* old_clk *).
        rewrite_state_equiv.
        2:{ solve_in_dom. }
        rewrite <- H2, Hclk. simpl. inversion 1.

    * (* clk_rise_right_req *)
      assert (Hclk : σ (req (latch_output l)) = σ0 (req (latch_output l))).
      { rewrite_back_wf_scoped; auto. }

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
(*      + apply clk_rise_right_req_marked_state0.
        contradict H (* σ0 rreq <> σ0 stae0 *).
        rewrite_state_equiv. 2:{ solve_in_dom. }
        rewrite_state_equiv. 2:{ solve_in_dom. }
        simpl. reduce_eqb. auto. (* depends on H : σ rreq = σ state0 *)
*)

      + (* If state0 is getting updated, so σ state0 <> σ0 state0... *)
        clear H4 H5 H6 (* extra from step_implies_stage_eps *).
        apply clk_rise_right_req_marked; auto.
        apply not_eq_sym in H1.
        apply val_is_bit_neq in H1 (* old_clk *); try solve_val_is_bit.

      + apply clk_rise_right_req_marked_state0.
        contradict H.
        rewrite_state_equiv. 2:{ solve_in_dom. }
        rewrite_state_equiv. 2:{ solve_in_dom. }
        simpl. auto.


    * (* clk_fall_flop_marked *)
      assert (Hwf' : wf_stage_state l σ0).
      { eapply step_wf_state_eps; eauto. }
      assert (Hclk : σ (latch_clk l) = Bit1).
      { rewrite_back_wf_scoped; auto. }
      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      2:{ (* not_state gets updated *)
          contradict H0 (* old_clk *).
          rewrite_state_equiv; try solve_in_dom. simpl.
          simpl in *.
          rewrite <- H3 (* old_clk *).
          rewrite Hclk.
          inversion 1.
      }
      { (* state0 gets updated *)
        clear H6 H7 H8 (* extra from step_implies_stage_eps *).
        contradict H0 (* old_clk *).
        rewrite_state_equiv; try solve_in_dom.
        reduce_eqb.
        rewrite Hclk.
        inversion 1.
      }


    * (* clock_fall *)
      assert (Hclk : σ (latch_clk l) = Bit1)
        by (rewrite_back_wf_scoped; auto).

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      +         clear H6 H7 H8 (* extra from step_implies_stage_eps *).
        apply clock_fall_flop_marked; auto.
        { (* old_clk *)
          apply not_eq_sym in H3. (* old_clk *)
          apply val_is_bit_neq in H3 (* latch_old_clk *); try solve_val_is_bit.
        }
        { (* stable *)
          apply func_stable_equiv. { solve_space_set. }
          auto. (* σ clk = latch_clk_function σ *)
        }

      + apply clock_fall_state0_marked; auto.
        { (* old_clk *)
          rewrite <- H3 (* old_clk *). auto.
        }
        { intros Hstable.
          apply H1. (* latch_clk_component not stable *)
          apply func_stable_equiv in Hstable.
          2:{ solve_space_set. }
          apply func_stable_equiv.
          { solve_space_set. }
          rewrite_state_equiv. 2:{ solve_in_dom. }
          simpl.
          rewrite latch_clk_function_equiv with (σ' := σ).
          2:{ intros x Hx. rewrite <- H4 (* state_equiv_on *).
              2:{ decompose_set_structure; solve_in_dom. }
              unfold update. compare_next; auto.
              contradict Hx; solve_space_set.
          }
          auto.
        }

    * (* left_req_clk_rise *)
      assert (Hclk : σ (latch_clk l) = σ0 (latch_clk l)).
      { rewrite_back_wf_scoped; auto. }
      assert (Hstate0 : σ (latch_state0 l) = σ0 (latch_state0 l)).
      { apply step_implies_stage_eps in Hstep; auto.
        inversion Hstep; subst; find_contradiction; clear Hstep.
(*        + rewrite_state_equiv; auto; try solve_in_dom.*)
        + clear H6 H7 H8 (* extra from step_implies_stage_eps *).
          contradict H1 (* σ0 clk = Bit0 *).
          rewrite_state_equiv; auto; try solve_in_dom.
          simpl.
          simpl in H2 (* σ clk = Bit1 *).
          rewrite H2; inversion 1.
        + rewrite_state_equiv; auto; try solve_in_dom.
      }

      apply left_req_clk_rise_marked; auto.
      { rewrite_back_wf_scoped. rewrite_back_wf_scoped.
        auto.
      }
      { rewrite_back_wf_scoped; auto.
        rewrite H0.
        rewrite Hstate0; auto.
      }
      { rewrite Hclk. auto. }
(*
      { (* I don't know this, necessarily, if the step taken by σ → σ0 is the
           flop acknowledging the clock falling. Perhaps we can fix this by
           combining the clk- with old_clk- steps as I'm considering for other
           reasons... *)
        rewrite <- H2.
        apply step_implies_stage_eps in Hstep; auto.
        inversion Hstep; subst; find_contradiction; clear Hstep.
        + contradict Hclk.
          rewrite H1 (* σ0 clk = Bit0 *).
          rewrite H3 (* σ clk = Bit1 *).
          inversion 1.
        + rewrite_state_equiv; auto; try solve_in_dom.
      } 
*)

    * (* right_ack_clk_rise *)
      assert (Hclk : σ (latch_clk l) = σ0 (latch_clk l)).
      { rewrite_back_wf_scoped; auto. }
      assert (Hstate0 : σ (latch_state0 l) = σ0 (latch_state0 l)).
      { apply step_implies_stage_eps in Hstep; auto.
        inversion Hstep; subst; find_contradiction; clear Hstep.
(*        + rewrite_state_equiv; auto; try solve_in_dom.*)
        + contradict H1 (* σ0 clk = Bit0 *).
          rewrite_state_equiv; auto; try solve_in_dom.
          simpl.
          simpl in H3 (* σ clk = Bit1 *).
          rewrite H3; inversion 1.
        + rewrite_state_equiv; auto; try solve_in_dom.
      }

      apply right_ack_clk_rise_marked.
      { rewrite_back_wf_scoped. rewrite_back_wf_scoped. auto. }
      { rewrite_back_wf_scoped; auto.
        rewrite H0.
        rewrite Hstate0; auto.
      }
      { rewrite Hclk. auto. }
      { admit (* true *). }

  Unshelve. all:auto.
  Admitted.

End StepPreservation.
