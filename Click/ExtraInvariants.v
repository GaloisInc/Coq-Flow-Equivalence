
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

Require Import Coq.Program.Equality.


Module ExtraInvariants (Export ClickInvariant : ClickInvariant).

  Module WFStage := WFStage ClickInvariant.
  Import WFStage.
  Import WFStage.ClickTactics.


  Lemma transition_preserves_state0_old_clk : forall l σ σ' x v,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
       σ' (latch_state0 l) = σ (latch_state0 l)
    /\ (σ' (latch_old_clk l) = if ((x =? latch_clk l) && (v =? Bit0))%bool then Bit0
                                                                           else σ (latch_old_clk l)).
  Proof.
    intros l σ σ' x v Hwf Hstep.
    eset (Hdom := wf_space _ _ _ _ _ _ Hstep).
    Unshelve. 2:{ auto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hdom.
    decompose_set_structure; try find_contradiction.

    + step_inversion_clean.
      repeat (rewrite_state_equiv; try solve_in_dom).
      auto.
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
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      apply flop_inversion_clk in Hstep0.
      2:{ solve_all_disjoint. }
      2:{ apply wf_reset_hidden_1; auto. }
      2:{ apply wf_hidden_reset_1; auto. }
      destruct Hstep0.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).

      rewrite_state_equiv; try (simpl; solve_in_dom).
      rewrite_state_equiv; try (simpl; solve_in_dom).
      simpl.
      reduce_eqb.

      simpl.
      
      assert (Hbit : val_is_bit v).
      { subst. solve_val_is_bit. }
      inversion Hbit; auto.

  Unshelve. all:exact (fun _ => true).
  Qed.


  Lemma transition_preserves_state0  : forall l σ σ' x v,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    σ' (latch_state0 l) = σ (latch_state0 l).
  Proof.
    intros ? ? ? ? ? Hwf Hstep.
    apply transition_preserves_state0_old_clk in Hstep; auto.
    destruct Hstep; auto.
  Qed.
  Lemma transition_preserves_old_clk : forall l σ σ' x v,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    (x = latch_clk l -> v = Bit1) ->
    σ' (latch_old_clk l) = σ (latch_old_clk l).
  Proof.
    intros ? ? ? ? ? Hwf Hstep Ht.
    apply transition_preserves_state0_old_clk in Hstep; auto.
    destruct Hstep as [ ? Hstep]; auto.
    rewrite Hstep.
    compare_next; auto.
    simpl. simpl in Hstep.
    compare_next; auto.
    specialize (Ht eq_refl). find_contradiction.
  Qed.
  Lemma transition_preserves_old_clk_fall : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event (latch_clk l) Bit0)} Some σ' ->
    σ' (latch_old_clk l) = Bit0.
  Proof.
    intros ? ? ? Hwf Hstep.
    apply transition_preserves_state0_old_clk in Hstep; auto.
    destruct Hstep as [ ? Hstep]; auto.
    rewrite Hstep. reduce_eqb. simpl. auto.
  Qed.


  Definition wf_lack_clk_Bit0 l σ :=
    σ (ack (latch_input l)) = if_token l (neg_value (σ (latch_state0 l))) ->
    latch_clk_function l σ = Bit0 ->
    σ (latch_clk l) = Bit0.


  Theorem wf_invariant_steps : forall l tr σ,
    latch_stage_with_env l ⊢ σR l →*{tr} Some σ ->
    wf_lack_clk_Bit0 l σ.
  Abort.

  Lemma wf_lack_clk_Bit0_σR : forall l,
    wf_lack_clk_Bit0 l (σR l).
  Proof.
    destruct l; intros Hlack Hfun; unfold σR.
    + simpl. reduce_eqb. auto.
    + simpl. reduce_eqb. auto.
  Qed.

  Lemma wf_lack_clk_Bit0_step_Some_1 : forall l σ x v σ',
    wf_stage_state l σ ->
    wf_lack_clk_Bit0 l σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    wf_lack_clk_Bit0 l σ'.
  Proof.
    intros l σ x v σ' Hwf Hwf' Hstep.
    unfold wf_lack_clk_Bit0 in *.

      compare x (req (latch_input l)).
      { step_inversion_clean.

        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl.
        intros Hack Hfun'.

        assert (Henv_unstable : σ (req (latch_input l)) = σ (ack (latch_input l))).
        { apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
          simpl; rewrite <- Hunstable.
          rewrite val_is_bit_neg_neg; try solve_val_is_bit.
        }

        assert (Hfun1_contra : latch_clk_function l σ <> Bit1).
        { intros Hfun.
          apply latch_clk_function_Bit1_l_req in Hfun; auto.
          contradict Hfun.
          rewrite Henv_unstable.
          simpl.
          rewrite Hack.
          rewrite <- neg_value_if_token.
          apply bit_neq_neg_l.
          destruct l; unfold if_token; simpl; solve_val_is_bit.
        }

        apply not_eq_sym in Hfun1_contra.
        apply val_is_bit_neq in Hfun1_contra; try solve_val_is_bit.
      }
      assert (Hwf'' :  wf_stage_state l σ').
      { eapply step_wf_state_lemma; eauto. }

      compare x (ack (latch_output l)).
      { step_inversion_clean.
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl.
        intros Hack Hfun'.

        assert (Hfun1_contra : latch_clk_function l σ <> Bit1).
        { intros Hfun.

          apply latch_clk_function_Bit1_iff in Hfun; auto.
          destruct Hfun as [Hlreq Hrack].

          assert (Henv : σ (ack (latch_output l)) = neg_value (σ (req (latch_output l)))).
          { symmetry. apply val_is_bit_neq; try solve_val_is_bit. }

          assert (Henv_wf : σ (req (latch_output l)) = σ (latch_state0 l)).
          { apply wf_right_env; auto. }


          contradict Hrack.
          { rewrite <- Henv_wf. auto. }
        }

        apply not_eq_sym in Hfun1_contra.
        apply val_is_bit_neq in Hfun1_contra; try solve_val_is_bit.

      }

      compare x (ack (latch_input l)).
      { step_inversion_clean.
        combine_state_equiv_on_complex; try (simpl; solve_space_set).
        repeat (rewrite_state_equiv; try solve_in_dom).

        simpl. reduce_eqb.
        intros.
        destruct Hguard; auto. (* we know σ clk = Bit0 from the delay_space guard *)
      }

      compare x (latch_clk l); [compare v Bit0 | ].
      { (* clk- *)
        erewrite (wf_update _ _ _ (latch_clk l)); [ | eauto].
        auto.
      }
      { (* clk+ *)
        step_inversion_clean.
        combine_state_equiv_on_complex; try (simpl; solve_space_set).
        combine_state_equiv_on_complex; try (simpl; solve_space_set).
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl. reduce_eqb.

        assert (Hv : v = Bit1).
        { apply not_eq_sym in Hneq2.
          apply val_is_bit_neq in Hneq2; auto; try solve_val_is_bit.
          subst. try solve_val_is_bit.
        }

        subst.
        intros Hlack Hfun.
        contradict Hfun.
        { rewrite (latch_clk_function_equiv σ).
          { rewrite Hv. inversion 1. }
          { intros x Hx. rewrite_state_equiv; try solve_in_dom.
            decompose_set_structure; auto.
          }
        }
      }


     assert (Hlack : σ' (ack (latch_input l)) = σ (ack (latch_input l))).
     {
      eapply (wf_scoped _ _ _ _ _ Hstep (ack (latch_input l))).
      { intros v0. inversion 1. subst. find_contradiction. }
      { rewrite latch_stage_with_env_input, latch_stage_with_env_output.
        solve_in_dom.
      }
     }
     assert (Hclk : σ' (latch_clk l) = σ (latch_clk l)).
     {
      eapply (wf_scoped _ _ _ _ _ Hstep (latch_clk l)).
      { intros v0. inversion 1. subst. 
        apply wf_space in Hstep; auto.
      }
      { rewrite latch_stage_with_env_input, latch_stage_with_env_output.
        solve_in_dom.
      }
     }
    assert (Hlreq : σ' (req (latch_input l)) = σ (req (latch_input l))).
     {
      eapply (wf_scoped _ _ _ _ _ Hstep (req (latch_input l))).
      { intros v0. inversion 1. subst. find_contradiction. }
      { rewrite latch_stage_with_env_input, latch_stage_with_env_output.
        solve_in_dom.
      }
     }
    assert (Hrack : σ' (ack (latch_output l)) = σ (ack (latch_output l))).
     {
      eapply (wf_scoped _ _ _ _ _ Hstep).
      { intros v0. inversion 1. subst. find_contradiction. }
      { rewrite latch_stage_with_env_input, latch_stage_with_env_output.
        solve_in_dom.
      }
     }

    assert (Hstate0 : σ' (latch_state0 l) = σ (latch_state0 l)).
    { eapply transition_preserves_state0; eauto. }

    assert (Hfun : latch_clk_function l σ' = latch_clk_function l σ).
    {
      apply latch_clk_function_equiv.
      intros y Hy.
      decompose_set_structure; auto.
      { erewrite wf_ctrl_reset_n; eauto.
        erewrite wf_ctrl_reset_n; eauto.
      }
    }

    rewrite Hlack.
    rewrite Hstate0.
    rewrite Hfun.
    rewrite Hclk.
    
  Unshelve. all: auto. all:exact (fun _ => true).
  Qed.

  Lemma wf_lack_clk_Bit0_step_None_1 : forall l σ σ',
    wf_stage_state l σ ->
    wf_lack_clk_Bit0 l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_lack_clk_Bit0 l σ'.
  Proof.
    intros ? ? ? Hwf Hinv Hstep.
    unfold wf_lack_clk_Bit0 in *.
    apply step_implies_stage_eps in Hstep; auto.
    inversion Hstep.
    * repeat (rewrite_state_equiv; try solve_in_dom).
      simpl. reduce_eqb.

      assert (Hfun : latch_clk_function l σ = Bit1).
      { rewrite <- H2 (* latch_clk_function *).
        auto.
      }
      apply latch_clk_function_Bit1_iff in Hfun; auto.
      destruct Hfun as [Hlreq _].
      assert (Henv : neg_value (σ (req (latch_input l))) = σ (ack (latch_input l))).
      { rewrite Hlreq. rewrite H3 (* σ lreq *).
        rewrite neg_value_if_token; auto.
      }

      subst. intros Hlack Hfun'.
      assert (Hstate0 : σ (latch_state0 l) = neg_value (σ (latch_not_state0 l))).
      { symmetry.
        apply val_is_bit_neq; auto; try solve_val_is_bit.
      }
      assert (Hlack' : σ (ack (latch_input l)) = if_token l (σ (latch_state0 l))).
      { rewrite Hstate0. auto. }

      apply val_is_bit_neq_neg in Henv; [ | left; try solve_val_is_bit].
      contradict Henv.
      rewrite Hlack'.
      rewrite Hlreq.
      reflexivity.


    * repeat (rewrite_state_equiv; try solve_in_dom).
      simpl.
      rewrite (latch_clk_function_equiv σ); auto.
      { intros x Hx. rewrite_state_equiv; try solve_in_dom.
        compare_next; auto.
        contradict Hx. solve_set.
      }
  Qed.


  Theorem wf_lack_clk_Bit0_steps : forall l tr σ,
    latch_stage_with_env l ⊢ σR l →*{tr} Some σ ->
    σ (ack (latch_input l)) = if_token l (neg_value (σ (latch_state0 l))) ->
    latch_clk_function l σ = Bit0 ->
    σ (latch_clk l) = Bit0.
  Proof.
    intros l tr σ Hstep.
    assert (Hwf : wf_stage_state l σ).
    { eapply step_wf_state; eauto. }
    dependent induction Hstep.
    * apply wf_lack_clk_Bit0_σR.
    * assert (Hwf' : wf_stage_state l σ').
      { eapply step_wf_state; eauto. }
      destruct e as [x v].
      eapply wf_lack_clk_Bit0_step_Some_1; [ | | eauto]; auto.
      unfold wf_lack_clk_Bit0.
      apply (IHHstep σ'); auto.
    * assert (Hwf' : wf_stage_state l σ').
      { eapply step_wf_state; eauto. }
      eapply wf_lack_clk_Bit0_step_None_1; eauto.
      unfold wf_lack_clk_Bit0.
      apply (IHHstep σ'); auto.
  Qed.

End ExtraInvariants.
