Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import MarkedGraph.
Require Import Click.StateSpace.
Require Import Click.Invariants.
Require Import Click.MG.

Require Import Omega.


Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.


Module ClickMGProofs (ClickModule : ClickType).

  Module ClickMG := ClickMG(ClickModule).
  Import ClickMG.
  Import ClickTactics.


  Definition latch_in_flag (l : latch even odd) := swap_token_flag (latch_to_token_flag l).
  Definition latch_out_flag (l : latch even odd) := latch_to_token_flag l.
  Definition latch_stage_MG l := stage_MG (latch_in_flag l) (latch_out_flag l).
  Definition latch_transition_event l := transition_event l (latch_in_flag l).
  Definition latch_stage_MG_SS l := stage_MG_SS l (latch_in_flag l).

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

    Search (_ <> X).
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






  (************************** TODO ********************************)

  (** Intuitively, [prop_marked p σ] is a property that holds on a state σ
  whenever a related marking m satisfies [m(p) > 0]. *)
  Section prop_marked.


  Variable l : latch even odd.
  Inductive prop_marked : forall {t1 t2} (p : stage_place t1 t2) (σ : state name), Prop :=

  (* left_ack -> left_req *)
  | lack_lreq_marked σ :
    σ (ack (latch_input l)) = σ (req (latch_input l)) -> prop_marked left_ack_left_req σ

  (* right_req -> right_ack *)
  | rreq_rack_marked σ :
    σ (req (latch_output l)) = neg_value (σ (ack (latch_output l))) ->
    prop_marked right_req_right_ack σ (* right_req -> right_ack *)

  (* clk- -> left_ack *)
  | clk_fall_left_ack_marked σ :
    σ (latch_clk l) = Bit0 ->
    σ (ack (latch_input l)) = match latch_to_token_flag l with
                              | Token => σ (latch_state0 l)
                              | Nontoken => neg_value (σ (latch_state0 l))
                              end ->
    prop_marked clk_fall_left_ack σ
  | clk_fall_left_ack_state0_marked σ :
    σ (latch_clk l) = Bit0 ->
    σ (latch_old_clk l) = Bit1 ->
    prop_marked clk_fall_left_ack σ


  (* clk+ -> right_req *)
  | clk_rise_right_req_marked σ :
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit0 ->
    prop_marked clk_rise_right_req σ
  | clk_rise_right_req_marked_state0 σ :
    σ (req (latch_output l)) <> σ (latch_state0 l) ->
    prop_marked clk_rise_right_req σ

  (* clk+ -> clk- *)
  | clock_fall_flop_marked σ :
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit0 ->
    stable (latch_clk_component l) σ ->
    prop_marked clock_fall σ
  | clock_fall_state0_marked σ :
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit1 ->
    ~ stable (latch_clk_component l) σ ->
    prop_marked clock_fall σ

  (* left_req -> clk+ *)
  | left_req_clk_rise_marked σ :
    σ (req (latch_input l)) = neg_value (σ (ack (latch_input l))) ->
    ~ stable (latch_clk_component l) σ ->
    prop_marked left_req_clk_rise σ

  (* right_ack -> clk+ *)
  | right_ack_clk_rise_marked σ :
    σ (ack (latch_output l)) = σ (req (latch_output l)) ->
    ~ stable (latch_clk_component l) σ ->
    prop_marked right_ack_clk_rise σ
  .

Import ClickTactics.


Ltac combine_state_equiv_on_domain Hequiv :=
  match type of Hequiv with
  | state_equiv_on ?X (Some ?σ) (Some ?σ') =>
    let Hequiv' := fresh "Hequiv" in
    assert (Hequiv' : state_equiv_on (space_domain (latch_stage_with_env l)) (Some σ) (Some σ'));
    [ let Hx := fresh "Hx" in
      intros ? Hx;
      rewrite dom_latch_stage_with_env in Hx;
      apply Hequiv;
      decompose_set_structure;
      solve_in_dom
    | clear Hequiv
    ]
  end.

  Lemma step_implies_prop_marked : forall σ t σ',
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t), prop_marked p σ.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ t σ' Hwf Hstable Hstep t0 p.
    dependent destruction p.
    { (* left_ack_left_req *)
      constructor.
      unfold latch_transition_event, transition_event in Hstep.
      repeat step_inversion_1.
      repeat combine_state_equiv_on.
      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv.
      combine_state_equiv_on_complex.
      { solve_in_dom. }
      standardize_state_equiv_on_set Hequiv0.
      combine_state_equiv_on_domain Hequiv0.

      apply val_is_bit_neg_inversion in Heq.
      2:{ solve_val_is_bit. }
      simpl.
      rewrite <- Heq.
      apply val_is_bit_neg_inversion.
      { solve_val_is_bit. }
      reflexivity.
    }

    { (* clk_fall_left_ack *)
      unfold latch_transition_event, transition_event in Hstep.
      repeat (step_inversion_1; try combine_state_equiv_on).
      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv2.
      combine_state_equiv_on_complex.
      { solve_in_dom. }
      standardize_state_equiv_on_set Hequiv.
      combine_state_equiv_on_domain Hequiv.

      apply clk_fall_left_ack_marked; auto.
      { apply Hguard. constructor. simpl. solve_set.
      }

      (* rewrite Heq *)
      symmetry in Heq0.
      apply val_is_bit_neg_inversion in Heq0.
      2:{ solve_val_is_bit. }
      simpl.
      rewrite <- Heq0.
      destruct l; simpl; auto.
      rewrite val_is_bit_neg_neg; auto.
      { solve_val_is_bit. } 
    }

    { (* clk_rise_right_req *) 
      replace (latch_transition_event l right_req σ)
        with  (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
        in    Hstep
        by    auto.
      repeat (step_inversion_1; try combine_state_equiv_on).
      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv2.
      combine_state_equiv_on_complex.
      { solve_in_dom. }
      combine_state_equiv_on_domain Hequiv.

      apply clk_rise_right_req_marked_state0.
      apply val_is_bit_neq_neg.
      { left. eapply wf_all_bits; eauto.
        rewrite dom_latch_stage_with_env.
        solve_space_set.
      }
      assumption.
   }

   { (* right_req_right_ack *)
      constructor.
      unfold latch_transition_event, transition_event in Hstep.
      repeat (step_inversion_1; try combine_state_equiv_on).
   }

  { (* clock_fall *)
    unfold latch_transition_event, transition_event in Hstep.
    repeat step_inversion_1.
    repeat combine_state_equiv_on.
    standardize_state_equiv_on_set Hequiv0.
    standardize_state_equiv_on_set Hequiv.
    (* can't combine?? combine_state_equiv_on_complex. is this a bug??? *)


    (* We know that clk_defn σ = Bit0 *)
    (* We know that flop ⊢ σ →{CLK+} Some σ' *)
    admit.

  }

  { (* left_req_clk_rise *)
    unfold latch_transition_event, transition_event in Hstep.
    repeat step_inversion_1.
    repeat combine_state_equiv_on.
    standardize_state_equiv_on_set Hequiv0.
    standardize_state_equiv_on_set Hequiv.
    (* can't combine further *)

    (* We know that clk_defn σ = Bit1 *)
    (* We know that flop ⊢ σ →{CLK+} Some σ' *)

    admit.

    
  }

  { (* right_ack_clk_rise *)
    unfold latch_transition_event, transition_event in Hstep.
    repeat step_inversion_1.
    repeat combine_state_equiv_on.
    standardize_state_equiv_on_set Hequiv0.
    standardize_state_equiv_on_set Hequiv.

    (* We know that clk_defn σ = Bit1 *)
    (* We know that flop ⊢ σ →{CLK+} Some σ' *)
    admit.

  }
  Admitted.



  Lemma stage_eps_decide_state0 : forall σ σ0,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ0 ->
    (σ (latch_state0 l) = σ0 (latch_state0 l)) \/ (σ (latch_old_clk l) = Bit1) \/ σ (latch_clk l) = Bit1.
  Proof.
    intros σ σ' Hwf Hstep.
      (* We keep the same prop_marked witness unless the Epsilon transition was
      on latch_state0, if the transition was Flop_clk_fall *)
      repeat step_inversion_1; repeat combine_state_equiv_on.
      * standardize_state_equiv_on_set Hequiv0.
        inversion Hstep; subst.
        standardize_state_equiv_on_set H2.
        combine_state_equiv_on_complex.
        { simpl; solve_space_set. }
        standardize_state_equiv_on_set Hequiv.
(*        combine_state_equiv_on_domain Hequiv.*)

        apply val_is_bit_neq in H0; try solve_val_is_bit.
        apply val_is_bit_neq in H1; try solve_val_is_bit.
        right. left. rewrite <- H1. auto.

      * standardize_state_equiv_on_set Hequiv1.
        standardize_state_equiv_on_set Hequiv6.
        combine_state_equiv_on_complex.
        { simpl; solve_space_set. }
        standardize_state_equiv_on_set Hequiv.
        rewrite_state_equiv; auto. simpl; solve_space_set.
      * standardize_state_equiv_on_set Hequiv1.
        rewrite_state_equiv; auto.
        simpl; solve_space_set.
      * standardize_state_equiv_on_set Hequiv2.
        rewrite_state_equiv; auto.
        simpl; solve_in_dom.
      * standardize_state_equiv_on_set Hequiv1.
        rewrite_state_equiv; auto.
        simpl. solve_space_set.
      * standardize_state_equiv_on_set Hequiv. 
        standardize_state_equiv_on_set Hequiv1. 
          (* contradiction, flop can't take a step *)
          apply flop_inversion_output in Hstep1; auto.
          2:{ repeat constructor; to_in_list_dec; destruct l; simpl; auto. }
          2:{ destruct l; simpl.
              apply wf_hidden; auto.
              eapply wf_dp_reset_n; eauto.
          }
          2:{ destruct l; simpl.
              eapply wf_dp_reset_n; eauto.
              apply wf_hidden; auto.
          }
          destruct Hstep1 as [? [? [? ?]]].
          right. right. auto.

    Unshelve. intro. exact true.
  Qed.


Arguments wf_scoped {name} S {S_wf} σ e σ' Hstep x : rename.
Ltac rewrite_back_wf_scoped :=
  match goal with
  | [ Hstep : ?S ⊢ ?σ →{ ?e } Some ?σ' |- context[ ?σ ?x ] ] =>
    erewrite <- (wf_scoped S σ e σ' Hstep x);
    [ | try (intro; inversion 1; find_contradiction; fail)
    | rewrite latch_stage_with_env_input, latch_stage_with_env_output;
          solve_space_set
    ]
  end.


  (* Helper lemmas for relate_implies_marked below *)
  Lemma relate_implies_marked_eps : forall σ σ',
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p σ' ->
    prop_marked p σ.
  Proof.
    intros σ σ' Hwf Hstable Hstep t1 t2 p Hp.
    dependent destruction Hp.
    * (* Because σ0 left_ack = σ0 left_req, if σ →{None} σ0,
         then it must be the case that σ is equivalent to σ0 on left_ack and left_req. *)
      apply lack_lreq_marked.

      rewrite_back_wf_scoped.
      rewrite_back_wf_scoped.
      auto.

    * apply rreq_rack_marked.
      rewrite_back_wf_scoped.
      rewrite_back_wf_scoped.
      auto.

    * assert (Hclk : σ (latch_clk l) = Bit0).
      { rewrite_back_wf_scoped; auto. }
      
      assert (Hack : σ (ack (latch_input l)) = σ0 (ack (latch_input l))).
      { rewrite_back_wf_scoped; auto. }

      assert (Hstate0 : σ (latch_state0 l) = σ0 (latch_state0 l) -> prop_marked clk_fall_left_ack σ).
      { intros Hstate0.
        apply clk_fall_left_ack_marked; auto.
        rewrite Hack. rewrite Hstate0. auto.
      }
      assert (Hold_clk : σ (latch_old_clk l) = Bit1 ->
                        prop_marked clk_fall_left_ack σ).
      { intros Hold_clk.
        apply clk_fall_left_ack_state0_marked; auto.
      }
      apply stage_eps_decide_state0 in Hstep; auto.
      destruct Hstep as [Hstep | [Hstep | Hstep]]; auto.
      { find_contradiction. }

    * assert (Hclk : σ (latch_clk l) = Bit0) by (rewrite_back_wf_scoped; auto).
      apply clk_fall_left_ack_state0_marked; auto.
      apply stage_eps_decide_state0 in Hstep; auto.
      destruct Hstep as [Hstep | [Hstep | Hstep]]; auto.
      { admit (*not strong enough information?? *). }
      { find_contradiction. }

    * Print prop_marked.
      admit.
    * admit.      

  Admitted.

  Lemma outgoing_place_not_marked : forall σ σ' t,
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t),
        ~ prop_marked p σ'.
  Proof.
    intros σ σ' t Hwf Hwf_stable Hstep t0 p Hprop.

    dependent destruction Hprop.
    * (* t = left_req *)
      unfold latch_transition_event, transition_event in Hstep.

      assert (Hreq : σ0 (req (latch_input l)) = neg_value (σ (req (latch_input l)))).
      { eapply wf_update; [ | eauto]; auto. }
      assert (Hack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
      { rewrite_back_wf_scoped; auto. }

      repeat step_inversion_1.
      repeat combine_state_equiv_on. 
      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv.
      combine_state_equiv_on_complex.
      { simpl. solve_space_set. destruct l; simpl; auto. }
      standardize_state_equiv_on_set Hequiv0.
(*      combine_state_equiv_on_domain Hequiv0.*)

      assert (Hreq' : val_is_bit (σ (req (latch_input l)))) by solve_val_is_bit.

      contradict Heq.
      simpl in Hack, Hreq.
      rewrite <- Hack.
      rewrite <- Hreq.
      apply val_is_bit_neq_neg.
      { rewrite Hreq. simpl in Hreq'.
        left.
        inversion Hreq'; simpl; constructor.
      }

      simpl in H. congruence.

    * (* t = right_ack *)
      assert (Hreq : σ0 (req (latch_output l)) = σ (req (latch_output l))).
      { rewrite_back_wf_scoped; auto. }
      assert (Hack : σ0 (ack (latch_output l)) = neg_value (σ (ack (latch_output l)))).
      { eapply wf_update; [ | eauto]; auto. }

      unfold latch_transition_event, transition_event in Hstep.
      repeat (step_inversion_1; try combine_state_equiv_on).
      clear Hequiv1 Hequiv2.

      contradict Heq.
      simpl in H, Hreq, Hack.
      rewrite <- Hreq, <- Hack, H.

      assert (Hack' : val_is_bit (σ (ack (latch_output l)))) by solve_val_is_bit.

      inversion Hack'; my_subst; simpl; simpl in Hack;
        rewrite Hack; discriminate.

    * (* t = left_ack (1) *)
      replace (latch_transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.

      assert (Hack : σ0 (ack (latch_input l)) = neg_value (σ (ack (latch_input l)))).
      { erewrite wf_update; [ | | eauto]; auto.
      }
      assert (Hreq : σ0 (req (latch_input l)) = σ (req (latch_input l))).
      { rewrite_back_wf_scoped; auto. }

      repeat step_inversion_1.
      repeat combine_state_equiv_on.
      standardize_state_equiv_on_set Hequiv. clear Hequiv1.

      assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
      { 
        rewrite_state_equiv; auto.
        { simpl. solve_space_set. }
      }

      contradict Heq0.
      simpl in Hack, Hstate0, H0.
      rewrite <- Hack, <- Hstate0, H0.

      assert (Hbit : val_is_bit (σ0 (latch_state0 l))).
      { simpl. rewrite Hstate0. solve_val_is_bit. }
      

      destruct l; simpl; [ eapply bit_neq_neg_l | apply bit_neq_neg_r ]; auto.

   * (* t = left_ack (2) *)

     replace (latch_transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.
      repeat step_inversion_1.
      repeat combine_state_equiv_on.
      standardize_state_equiv_on_set Hequiv.
      standardize_state_equiv_on_set Hequiv1.
      combine_state_equiv_on_complex.
      { simpl; solve_space_set; destruct l; auto. }
      standardize_state_equiv_on_set Hequiv0.

      assert (Hack : σ0 (ack (latch_input l)) = neg_value (σ (ack (latch_input l)))).
      { rewrite_state_equiv; reduce_eqb; auto.
        solve_in_dom.
      }
      assert (Hreq : σ0 (req (latch_input l)) = σ (req (latch_input l))).
      { rewrite_state_equiv; reduce_eqb; auto.
        solve_in_dom.
      }
      assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
      { rewrite_state_equiv; reduce_eqb; auto.
        solve_in_dom.
      }
      assert (Hstate0' : σ0 (latch_not_state0 l) = σ (latch_not_state0 l)).
      { rewrite_state_equiv; reduce_eqb; auto.
        solve_in_dom.
      }

      assert (Hclk' : σ0 (latch_old_clk l) = σ (latch_old_clk l)).
      { rewrite_state_equiv; reduce_eqb; auto.
        solve_in_dom.
      }
      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_state_equiv; reduce_eqb; auto.
        solve_in_dom.
      }

      assert (state0_bit : val_is_bit (σ (local_name l "state0"))).
      { solve_val_is_bit. }

      symmetry in Heq0.
      apply val_is_bit_neg_inversion in Heq0.
      symmetry in Heq0.

      assert (Hstable : ~ stable (latch_left_ack_component l) σ).
      { intros [_ Hstable]. (* if it were, then it would not have taken a step *)
        assert (Hstep' : latch_left_ack_component l ⊢ σ 
                →{Some (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))}
                Some σ0).
        { apply delay_space_output.
          { rewrite <- Hclk, H. reduce_eqb; auto. }
          2:{ simpl. solve_space_set. }
          2:{ intros x Hx. decompose_set_structure. }
          apply func_output.
          { simpl; rewrite Heq0.
            apply bit_neq_neg_l.
            destruct l; simpl; auto.
            inversion state0_bit; simpl; constructor.
          }
          { simpl; rewrite Heq0.
            rewrite val_is_bit_neg_neg; auto.
            destruct l; simpl; auto.
            inversion state0_bit; simpl; constructor.
          }
          { intros x Hx. decompose_set_structure.
            unfold update. reduce_eqb; auto.
          }

        }
        specialize (Hstable _ _ Hstep').
        inversion Hstable as [? Hstable']; subst.
        contradict Hstable'.
        simpl. solve_space_set.
      }

      assert (Hstable' : stable (latch_flop_component l) σ).
      { apply wf_left_ack_stable; auto. }

      contradict Hstable'. 
      apply flop_not_stable_old_clk; auto.
      2:{ solve_val_is_bit. }
      rewrite <- Hclk, <- Hclk'.
      rewrite H, H0.
      inversion 1.

  * (* t = right_req (1) *)
    replace (latch_transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.

    repeat (step_inversion_1). repeat combine_state_equiv_on.
    standardize_state_equiv_on_set Hequiv.
    standardize_state_equiv_on_set Hequiv5.
    combine_state_equiv_on_complex. { solve_in_dom. }
    standardize_state_equiv_on_set Hequiv0.
    admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.

  Admitted.


  Lemma disjoint_place_marked : forall σ σ' t,
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    forall t1 t2 (p : stage_place t1 t2),
      t1 <> t ->
      t2 <> t ->
      prop_marked p σ' ->
      prop_marked p σ.
  Proof.
    intros σ σ' t Hstep Hwf Hwf_stable t1 t2 p Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    * constructor.
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
      }
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
      }
      auto.

    * constructor.
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
      }
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
      }
      auto.

    * compare t clk_rise.
      { (* if the clk+ event happens, contradiction iwth (σ (latch_clk l) = Bit0) *)
        contradict H.
        replace (latch_transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        erewrite (wf_update _ _ (latch_stage_well_formed l) _ _ _ _ Hstep).
        inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_back_wf_scoped.
        2:{ intros v.
            destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
        }
        auto.
      }
      assert (Hstate0: σ0 (latch_state0 l) = σ (latch_state0 l)).
      { destruct t; try find_contradiction;
        unfold latch_transition_event, transition_event in Hstep.
        + repeat step_inversion_1; repeat combine_state_equiv_on.
          standardize_state_equiv_on_set Hequiv1. clear Hequiv.
          rewrite_state_equiv; auto.
          { solve_in_dom. }
        + repeat step_inversion_1; repeat combine_state_equiv_on.
          standardize_state_equiv_on_set Hequiv. clear Hequiv5.
          rewrite_state_equiv; auto.
          { solve_in_dom. }
        + repeat step_inversion_1; repeat combine_state_equiv_on.
          standardize_state_equiv_on_set Hequiv. clear Hequiv7.
          rewrite_state_equiv; auto.
          { solve_in_dom. }
      }

      assert (Hack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
      { rewrite_back_wf_scoped.
        2:{ intros v.
            destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
        }
        auto.
      }

      compare (σ (latch_clk l)) (σ (latch_old_clk l)).
      2:{ (* if these are not equal, then flop_component is not stable. *)
          assert (~ stable (latch_flop_component l) σ).
          { apply flop_not_stable_old_clk; auto. }

          apply clk_fall_left_ack_state0_marked.
          { rewrite <- Hclk; auto. }
          { apply val_is_bit_neq in Hneq0; try solve_val_is_bit.
            { rewrite <- Hneq0, <- Hclk, H. auto. }
          }
      }
      { (* if these are equal, then... *)
        apply clk_fall_left_ack_marked.
        { rewrite <- Hclk; auto. }
        { rewrite <- Hstate0, <- Hack. auto. }
      }

  * compare t clk_rise.
      { (* if the clk+ event happens, contradiction iwth (σ (latch_clk l) = Bit0) *)
        contradict H.
        replace (latch_transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        rewrite (wf_update _ _ (latch_stage_well_formed l) _ _ _ _ Hstep); inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_back_wf_scoped.
        2:{ intros v.
            destruct t; auto; unfold latch_transition_event, transition_event; simpl; inversion 1; find_contradiction.
        }
        auto.
      }
      assert (Hold_clk : σ0 (latch_old_clk l) = σ (latch_old_clk l)).

      { destruct t; try find_contradiction;
        unfold latch_transition_event, transition_event in Hstep.
        + repeat step_inversion_1; repeat combine_state_equiv_on.
          standardize_state_equiv_on_set Hequiv1.
          rewrite <- Hequiv1; auto.
          { destruct l; solve_space_set. }
        + repeat step_inversion_1; repeat combine_state_equiv_on.
          standardize_state_equiv_on_set Hequiv.
          rewrite <- Hequiv; auto.
          { destruct l; solve_space_set. }
        + repeat step_inversion_1; repeat combine_state_equiv_on.
          standardize_state_equiv_on_set Hequiv.
          rewrite <- Hequiv; auto.
          { destruct l; solve_space_set. }
      }

      apply clk_fall_left_ack_state0_marked.
      { rewrite <- Hclk; auto. }
      { rewrite <- Hold_clk. auto. }

    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.

  Admitted.


  (****** TODO: fix bug *)
  Lemma init_relate_implies_marked : forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p (σR l) ->
    init_marking (latch_stage_MG l) _ _ p > 0.
  Proof.
    intros t1 t2 p Hp.
    dependent destruction Hp;
      try (simpl; unfold init_marking_flag; simpl;
      unfold σR in *; simpl in *; reduce_eqb;
      try (destruct l; simpl in *; find_contradiction; auto; fail);
    fail).
    * (* clk_fall_left_ack *)
      destruct l; simpl in H0; inversion H0; simpl; auto.
      2:{ unfold σR in *; simpl in *; reduce_eqb. }
      (* clk_fall_left_ack is never enabled in the initial state, but
         prop_marked holds when l is a token buffer, since:

         σ clk = Bit0 and
         σ (ack (latch_input l)) = σ state0 *)
      unfold σR in *; simpl in *; reduce_eqb. admit.
    * (* clk_rise_right_req *)
      destruct l; simpl in H; find_contradiction.
      2:{ unfold σR in *; simpl in *; reduce_eqb. } Print prop_marked.
      (* clk_fall_left_ack is never enabled in the initial state, but
         prop_marked holds when l is a non-token buffer, since:

         Bit0 = σ (req (latch_output l)) <> σ (latch_state0 l) = Bit1 *)
      { unfold σR in *; simpl in *; reduce_eqb. admit. }

  Admitted.

  Lemma state_relate_marking_steps : forall σ m,
    state_relate_marking l σ m ->
    exists tr, latch_stage_with_env l ⊢ σR l →*{tr} Some σ.
  Proof.
    intros σ m Hrelate.
    induction Hrelate.
    * exists t_empty. constructor.
    * destruct IHHrelate as [tr IH].
      exists (tr ▶ latch_transition_event l t σ).
      econstructor; eauto.
    * destruct IHHrelate as [tr IH].
      exists tr.
      econstructor; eauto.
  Qed.


  Lemma relate_implies_marked : forall σ m,
    state_relate_marking l σ m ->
    forall {t1 t2} (p : stage_place t1 t2),
      prop_marked p σ ->
      0 < m _ _ p.
  Proof.   (* by induction on state_relate_marking *)
    intros σ m Hrelate.
    induction Hrelate as [ | ? ? ? ? ? Hrelate IH Hstep Henabled Hm'
                           | ? ? ? Hrelate IH Hstep]; intros t1 t2 p Hp.
    * apply init_relate_implies_marked; auto.
    * assert (Hwf : wf_stage_state l σ).
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state; eauto.
      }
      assert (Hwf_stable : wf_stage_state_stable l σ).
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state_stable; eauto.
      }

      unfold is_enabled in Henabled.
      rewrite Hm'.
      unfold fire.
      compare_next.
      { inversion p; subst; find_contradiction. }
      compare_next.
      { (* t = t2 *) contradict Hp.
        eapply outgoing_place_not_marked; [ | | eauto]; auto.
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
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state_stable; eauto.
      }
  Qed.

  Theorem state_related_enabled : forall σ σ' t m,
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    state_relate_marking l σ m ->
    is_enabled _ t m.
  Proof.
    intros.
    intros t0 p.
    assert (prop_marked p σ).
    { eapply step_implies_prop_marked; eauto. }
    eapply relate_implies_marked; eauto.
  Qed.


  Lemma step_implies_bit : forall σ x v σ',
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->

    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    val_is_bit v.
  Proof.
    intros ? ? ? ? Hwf Hwf_stable Hstep.
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


  Lemma MG_relate_trace_step_lemma :
    relate_trace_step_lemma _ (latch_stage_with_env l)
                              (latch_stage_MG_SS l)
        (σR l) (init_stage_MG_state l).
  Proof.
    unfold relate_trace_step_lemma.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ1 σ1' σ2 [x v] t Hstep Hrelate.
    assert (Hwfσ1 : wf_stage_state l σ1).
    { eapply step_wf_state.
      eapply relate_trace_project_left.
      eauto.
    }
    assert (Hwfσ1' : wf_stage_state_stable l σ1).
    { eapply step_wf_state_stable.
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
        repeat step_inversion_1. rewrite Heq.
        repeat combine_state_equiv_on. clear Hequiv Hequiv1 Heq0.
        apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
        rewrite val_is_bit_neg_neg in Hunstable; try solve_val_is_bit.
        rewrite Hunstable; auto.

      + exists left_ack; split; [ reflexivity | ].
        simpl.
        repeat step_inversion_1. 
        repeat combine_state_equiv_on. clear Hequiv Hequiv1. simpl in Hguard.
        subst.
        clear Heq.
        Search neg_value.
        symmetry; apply val_is_bit_neq; try solve_val_is_bit.

      + exists right_req; split; [ reflexivity | ].
        repeat step_inversion_1. 
        repeat combine_state_equiv_on. clear Hequiv Hequiv5. clear Heq.
        subst; simpl.
        symmetry; apply val_is_bit_neq; try solve_val_is_bit.

      + exists right_ack; split; [ reflexivity | ].
        repeat step_inversion_1. 
        repeat combine_state_equiv_on. clear Hequiv Hequiv7. clear Heq0.
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
    exact (fun _ => true).
    exact (fun _ => true).
    exact (fun _ => true).
    exact (fun _ => true).
  Qed.

  Lemma place_name_disjoint_SS : forall t1 t2 (p : place (latch_stage_MG l) t1 t2),
    place_name (latch_stage_MG l) p ∉ space_domain (latch_stage_with_env l).
  Proof.
    intros.
    rewrite dom_latch_stage_with_env.
    destruct p; solve_space_set.
  Qed.

  Theorem MG_refines_stage :
    traces_of (latch_stage_with_env l) (σR l) ⊆ traces_of (latch_stage_MG_SS l) (init_stage_MG_state l).
  Proof.
    apply relate_trace_step_subset.
    { intros x Hdom1 Hdom2.
      unfold init_stage_MG_state.

      rewrite dom_latch_stage_with_env in Hdom1.
      simpl in Hdom1.
      decompose_set_structure; auto.
    }
    { apply MG_relate_trace_step_lemma. }
  Qed.


End prop_marked.
End ClickMGProofs.
