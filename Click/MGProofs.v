
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
(*    σ (latch_old_clk l) = Bit0 -> (* i.e. flop component is stable *) *)
    (* The left_ack component is unstable *)
    σ (ack (latch_input l)) = match latch_to_token_flag l with
                              | Token => σ (latch_state0 l)
                              | Nontoken => neg_value (σ (latch_state0 l))
                              end ->
(*    σ (req (latch_input l)) = σ (ack (latch_input l)) -> (* left environment is stable *)*)
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
(*    σ (ack (latch_output l)) <> σ (req (latch_output l)) -> *)
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
    latch_clk_function l σ = Bit1 ->
    σ (latch_clk l) = Bit0 ->
    prop_marked left_req_clk_rise σ

  (* right_ack -> clk+ *)
  | right_ack_clk_rise_marked σ :
    σ (ack (latch_output l)) = σ (req (latch_output l)) ->
    latch_clk_function l σ = Bit1 ->
    σ (latch_clk l) = Bit0 ->
    prop_marked right_ack_clk_rise σ
  .

Import ClickTactics.


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
  Qed.

Lemma wf_reset_hidden_1 : forall σ,
    wf_stage_state l σ ->
    σ match latch_to_token_flag l with
      | Token => dp_reset_n
      | NonToken => latch_hidden l
      end = Bit1.
Proof.
  intros ? Hwf.
  destruct l.
    apply wf_hidden; auto.
    eapply wf_dp_reset_n; eauto.
Qed.
Lemma wf_hidden_reset_1 : forall σ,
    wf_stage_state l σ ->
    σ match latch_to_token_flag l with
      | Token => latch_hidden l
      | NonToken => dp_reset_n
      end = Bit1.
Proof.
  intros ? Hwf.
  destruct l.
    eapply wf_dp_reset_n; eauto.
    apply wf_hidden; auto.
Qed.
Hint Resolve wf_reset_hidden_1 wf_hidden_reset_1 : wf.

Lemma latch_clk_function_is_bit : forall σ,
    wf_stage_state l σ ->
    val_is_bit (latch_clk_function l σ).
Proof.
  intros σ Hwf.
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


  Section step_implies_prop_marked.

    Variable σ σ' : state name.
    Hypothesis Hwf : wf_stage_state l σ.
(*    Hypothesis Hwf_stable : wf_stage_state_stable l σ. *)



  Definition step_implies_prop_marked_spec {t t0} (p : stage_place t0 t) :=
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    prop_marked p σ.

  Lemma step_implies_prop_marked_left_ack_left_req :
    step_implies_prop_marked_spec left_ack_left_req.
  Proof.
    intros Hstep.
      constructor.
      unfold latch_transition_event, transition_event in Hstep.
      step_inversion_clean.
      combine_state_equiv_on_domain.

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
      combine_state_equiv_on_domain.

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
      combine_state_equiv_on_domain.
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
    clear Hin. clear Hdec.
    combine_state_equiv_on_complex. { simpl; solve_space_set. }
    
    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ auto with wf. }
    2:{ auto with wf. }
    destruct Hstep3 as [Hequiv' Hstep3].
    combine_state_equiv_on.
    standardize_state_equiv_on_set Hequiv0.
    combine_state_equiv_on_domain.

    assert (Hclk : σ (latch_clk l) = Bit1).
    { rewrite <- Heq in *.
      apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
    }

    apply clock_fall_state0_marked; auto.
    { (* old_clk *) rewrite <- Hstep3; auto. }
    Print latch_clk_component.
    Search stable func_space.
    intros Hstable; apply func_stable_equiv in Hstable.
    2:{ solve_space_set. }
    contradict Hstable; auto.

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
    clear Hin.
    combine_state_equiv_on_complex. { simpl; solve_space_set. }
    
    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ auto with wf. }
    2:{ auto with wf. }

    destruct Hstep3 as [Hequiv' Hstep3].
    combine_state_equiv_on.
    combine_state_equiv_on_domain.

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
      contradict Hreq.
      apply latch_clk_function_Bit1_l_req; auto.
    }
    { apply val_is_bit_neq in Hunstable;
        try solve_val_is_bit; auto with wf.
        simpl. rewrite <- Hunstable.
        rewrite <- Heq. auto.
    }

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
    clear Hin. clear Hdec.
    combine_state_equiv_on_complex.
    { simpl; solve_space_set. }

    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ auto with wf. }
    2:{ auto with wf. }

    destruct Hstep3 as [Hequiv' Hstep3].

    combine_state_equiv_on.
    combine_state_equiv_on_domain.

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
    { rewrite Hstep3.
      apply val_is_bit_neq in Hunstable; try solve_val_is_bit; auto with wf.
      rewrite <- Hstep3. simpl.
      rewrite <- Hunstable.
      rewrite <- Heq.
      auto.
    }


    Unshelve. exact (fun _ => true).
  Qed.


  End step_implies_prop_marked.

  Lemma step_implies_prop_marked : forall σ t σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t), prop_marked p σ.
  Proof.
    intros σ t σ' Hwf Hstep t0 p.
    dependent destruction p.
    { eapply step_implies_prop_marked_left_ack_left_req; eauto. }
    { eapply step_implies_prop_marked_clk_fall_left_ack; eauto. }
    { eapply step_implies_prop_marked_clk_rise_right_req; eauto. }
    { eapply step_implies_prop_marked_right_req_right_ack; eauto. }
    { eapply step_implies_prop_marked_clock_fall; eauto. }
    { eapply step_implies_prop_marked_left_req_clk_rise; eauto. }
    { eapply step_implies_prop_marked_right_ack_clk_rise; eauto. }
  Qed.

  Lemma stage_eps_decide_state0 : forall σ σ0,
    wf_stage_state l σ ->

    latch_stage_with_env l ⊢ σ →{None} Some σ0 ->
    σ (latch_state0 l) <> σ0 (latch_state0 l) ->
    σ (latch_old_clk l) = Bit1 \/ σ (latch_clk l) = Bit1.
  Proof.
    intros σ σ' Hwf Hstep Hstate0.
    apply step_implies_stage_eps in Hstep; auto.
    inversion Hstep as [ Hclk Hold_clk Hequiv
                       | v Hclk Hold_clk Hv Hclk_function Hl_ack Hr_req Hnot_state0 Hequiv
                       | Hnot_state0 Hclk Hequiv
                       ]; subst; clear Hstep.

    * left.
      apply val_is_bit_neq in Hold_clk; try solve_val_is_bit.
      rewrite <- Hold_clk.
      apply val_is_bit_neq in Hclk; try solve_val_is_bit.

    * right; auto.

    * contradict Hstate0.
      rewrite_state_equiv. 2:{ solve_in_dom. }
      simpl; auto.
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
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p σ' ->
    prop_marked p σ.
  Proof.
    intros σ σ' Hwf Hstep t1 t2 p Hp.
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

      compare (σ (latch_state0 l)) (σ0 (latch_state0 l)); auto.
      apply stage_eps_decide_state0 in Hstep; auto.
      destruct Hstep as [Hstep | Hstep]; auto.
      { find_contradiction. }

    * (* clk_fall_left_ack *)
      assert (Hclk : σ (latch_clk l) = Bit0) by (rewrite_back_wf_scoped; auto).

      apply clk_fall_left_ack_state0_marked; auto.
      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      + apply val_is_bit_neq in H2; auto; try solve_val_is_bit.
        rewrite <- H2. rewrite Hclk. auto.
      + contradict H0.
        rewrite <- H3. 2:{ solve_in_dom. }
        unfold update.
        rewrite <- H2. rewrite Hclk. simpl. inversion 1.


    * assert (Hclk : σ (latch_clk l) = Bit1).
      { rewrite_back_wf_scoped; auto. }
      apply clk_rise_right_req_marked; auto.

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      + contradict H0. (* old_clk *)
        rewrite_state_equiv.
        2:{ solve_in_dom. }
        reduce_eqb.
        rewrite Hclk; inversion 1.

      + contradict H0 (* old_clk *).
        rewrite_state_equiv.
        2:{ solve_in_dom. }
        rewrite <- H2, Hclk. simpl. inversion 1.

    * assert (Hclk : σ (req (latch_output l)) = σ0 (req (latch_output l))).
      { rewrite_back_wf_scoped; auto. }

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      + apply clk_rise_right_req_marked_state0.
        contradict H.
        rewrite_state_equiv. 2:{ solve_in_dom. }
        rewrite_state_equiv. 2:{ solve_in_dom. }
        simpl. auto.

      + (* If state0 is getting updated, so σ state0 <> σ0 state0... *)
        apply clk_rise_right_req_marked; auto.
        apply not_eq_sym in H1.
        apply val_is_bit_neq in H1 (* old_clk *); try solve_val_is_bit.

      + apply clk_rise_right_req_marked_state0.
        contradict H.
        rewrite_state_equiv. 2:{ solve_in_dom. }
        rewrite_state_equiv. 2:{ solve_in_dom. }
        simpl. auto.


    * (* clk_fall *)

      assert (Hclk : σ (latch_clk l) = Bit1).
      { rewrite_back_wf_scoped; auto. }
      assert (Hold_clk : σ (latch_old_clk l) = Bit0).
      { (* In case 1: Bit0 = σ0 old_clk = σ clk = Bit1 
           In case 2: Bit0 = σ0 old_clk = σ clk = Bit1
           In case 3: Bit0 = σ0 old_clk = σ old_clk
        *)
        apply step_implies_stage_eps in Hstep; auto.
        inversion Hstep; subst; find_contradiction; clear Hstep.
        + apply not_eq_sym in H3. (* old_clk *)
          apply val_is_bit_neq in H3 (* old_clk *); try solve_val_is_bit.
        + contradict H0. rewrite_state_equiv.
          2:{ rewrite dom_latch_stage_with_env; solve_space_set. }
          rewrite <- H3, Hclk.
          simpl. inversion 1.
      }
      assert (Hwf' : wf_stage_state l σ0).
      { eapply step_wf_state_eps; eauto. }
      assert (Hl_req : σ (req (latch_input l)) = σ0 (req (latch_input l)))
        by (rewrite_back_wf_scoped; auto).
      assert (Hr_ack : σ (ack (latch_output l)) = σ0 (ack (latch_output l)))
        by (rewrite_back_wf_scoped; auto).

      apply clock_fall_flop_marked; auto.
      (*   In case 1: σ0 state0 = σ state0, so this follows.
           In case 3: σ0 state0 = σ state0, so this follows.

           In case 2: the clk component can go from stable to unstable by changing state0, but not unstable to stable... why must this be the case?

           Lemma: if ⊢ σ →{None} Some σ'
                  and latch_clk_function l σ' = Bit1
                  then latch_clk_function l σ = Bit1
        *)
        apply func_stable_equiv. { solve_space_set. }
        apply func_stable_equiv in H1. 2:{ solve_space_set. }

        apply step_implies_stage_eps in Hstep; auto.
        inversion Hstep; subst; find_contradiction; clear Hstep.
        + auto.
        + compare Bit1 (latch_clk_function l σ); auto.
          { rewrite <- Heq; auto. }
          (* when they are not equal *)
          apply val_is_bit_neq in Hneq; try solve_val_is_bit; auto with wf.
          simpl in Hneq.

          (* If σ == σ0 on everything except latch_not_state0 *)

          rewrite latch_clk_function_equiv with (σ' := σ0).
          { rewrite Hclk.  rewrite <- H. auto. }
          { prove_equiv_subset. }

    * (* clock_fall *)
      assert (Hclk : σ (latch_clk l) = Bit1)
        by (rewrite_back_wf_scoped; auto).

      apply step_implies_stage_eps in Hstep; auto.
      inversion Hstep; subst; find_contradiction; clear Hstep.
      + apply clock_fall_flop_marked; auto.
        { (* old_clk *)
          apply not_eq_sym in H3. (* old_clk *)
          apply val_is_bit_neq in H3 (* latch_old_clk *); try solve_val_is_bit.
        }
        { (* stable *)
          apply func_stable_equiv. { solve_space_set. }
          auto.
        }

      + apply clock_fall_state0_marked; auto.
        { (* old_clk *)
          rewrite <- H3. auto.
        }
        { intros Hstable.
          apply H1.
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

      apply left_req_clk_rise_marked; auto.
      { rewrite_back_wf_scoped. rewrite_back_wf_scoped.
        auto.
      }
      { rewrite latch_clk_function_equiv with (σ' := σ0); auto.
        { apply step_implies_stage_eps in Hstep; auto.
          inversion Hstep; subst; find_contradiction; clear Hstep.
          + intros x Hx.
            decompose_set_structure; rewrite_state_equiv; auto; solve_in_dom.

          + contradict Hclk.
            rewrite H1. (* σ0 clk = Bit0 *)
            rewrite H2. (* σ clk = Bit1 *)
            inversion 1.

          + intros x Hx.
            decompose_set_structure; rewrite_state_equiv; auto; solve_in_dom.
        }
      }
      rewrite Hclk. auto.

    * (* right_ack_clk_rise *)
      assert (Hclk : σ (latch_clk l) = σ0 (latch_clk l)).
      { rewrite_back_wf_scoped; auto. }

      apply right_ack_clk_rise_marked.
      { rewrite_back_wf_scoped. rewrite_back_wf_scoped. auto. }
      { rewrite latch_clk_function_equiv with (σ' := σ0); auto.
        { apply step_implies_stage_eps in Hstep; auto.
          inversion Hstep; subst; find_contradiction; clear Hstep.
          + intros x Hx.
            decompose_set_structure; rewrite_state_equiv; auto; solve_in_dom.

          + contradict Hclk.
            rewrite H1 (* σ0 clk = Bit0 *).
            rewrite H2 (* σ clk = Bit1 *).
            inversion 1.

          + intros x Hx.
            decompose_set_structure; rewrite_state_equiv; auto; solve_in_dom.
        }
      }
      { rewrite Hclk. auto. }

  Unshelve. all:auto.

  Qed.



  Lemma outgoing_place_not_marked : forall σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t),
        ~ prop_marked p σ'.
  Proof.
    intros σ σ' t Hwf Hstep t0 p Hprop.

    dependent destruction Hprop.
    * (* t = left_req *)
      unfold latch_transition_event, transition_event in Hstep.

      step_inversion_clean.
      combine_state_equiv_on_domain.

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
      combine_state_equiv_on_domain.

      (* Know:
         H : σ right_req = σ0 right_req  = neg_value (σ0 right_ack) = neg_value (neg_value (σ right_ack))
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
      combine_state_equiv_on_domain.
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


   * (* t = left_ack (2) *)

     replace (latch_transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.
     step_inversion_clean.
     clear Hin0.
     combine_state_equiv_on_complex; try (simpl; solve_space_set).
     combine_state_equiv_on_domain.
     destruct Hguard as [Hclk Hstate0].
     (* Know:
        H0 : Heq : neg_value l_ack = if_token l (neg_value (σ state0))
        Hunstable : if_token l (neg_value (σ state0)) <> σ l_ack
        Hstate0 : σ not_state0 = neg_value (σ state0)
     *)
     assert (H_ack_stable : ~ stable (latch_left_ack_component l) σ).
     { intros [_ Hstable]. (* if it were, then it would not have taken a step *)
       assert (Hstep' : latch_left_ack_component l ⊢ σ 
                →{Some (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))}
                Some σ0).
        { apply delay_space_output.
          3:{ solve_space_set. }
          3:{ intros x Hx. rewrite_state_equiv; try solve_in_dom.
              compare_next; auto.
              decompose_set_structure.
          }
          { split; auto. }
          apply func_output.
          { simpl. rewrite <- Heq.
            apply bit_neq_neg_r; try solve_val_is_bit.
          }
          { simpl. rewrite <- Heq; auto. }
          { intros x Hx. rewrite_state_equiv; try solve_in_dom.
            auto.
          }
        }
        specialize (Hstable _ _ Hstep').
        inversion Hstable as [? Hstable']; subst.
        contradict Hstable'.
        simpl. solve_space_set.
    }


    set (flop_set := match latch_to_token_flag l with
                     | Token => dp_reset_n
                     | NonToken => latch_hidden l
                     end).
    set (flop_reset := match latch_to_token_flag l with
                       | NonToken => dp_reset_n
                       | Token => latch_hidden l
                     end).
    assert (H_flop_stable : ~ stable (flop flop_set flop_reset
                                           (latch_clk l) (latch_old_clk l)
                                           (latch_not_state0 l) (latch_state0 l))
                                     σ).
    { intros Hstable.
      Print flop_step.
      assert (Hstep : flop flop_set flop_reset
                           (latch_clk l) (latch_old_clk l)
                           (latch_not_state0 l) (latch_state0 l)
                      ⊢ σ →{None} Some (update σ (latch_old_clk l) (σ (latch_clk l)))).
      { apply Flop_clk_fall; auto.
        { rewrite Hclk; inversion 1. }
        { rewrite Hclk.
          replace (σ (latch_old_clk l)) with (σ0 (latch_old_clk l)).
          2:{ rewrite_state_equiv; try solve_in_dom. auto. }
          rewrite H0; inversion 1.
        }
        { intros x Hx. auto. }
       }
       destruct Hstable as [_ Hstable].
       specialize (Hstable _ _ Hstep).
       inversion Hstable.
    }


    (* Know:
       H : σ clk = σ0 clk = Bit0
       H0 : σ old_clk = σ0 old_clk = Bit1
       Heq : neg_value (σ l_ack) = if_token l (neg_value (σ state0))
         aka σ l_ack = if_token l (σ state0)
       Hstate0 : σ not_state0 = neg_value (σ state0)

       Heq+wf_left_env ==> σ l_ack <> σ l_req
    *)
    (* I think we need to modify the timing constraint/delay so that the clk-
    event has time to propogate not just to clk, but also to the flop. Can we do
    this by modifying flop so that clk- events update old_clk automatically??
    *)
    admit.

  * (* t = right_req (1) *)
    replace (latch_transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.
    step_inversion_clean.
    combine_state_equiv_on_domain.
    clear Hin0.
    (* Know:
       H : σ clk = σ0 clk = Bit1
       H0 : σ old_clk = σ0 old_clk = Bit0
       Heq : neg_value (σ r_req) = σ state0
       Hunstable : σ state0 <> σ r_req
    *)
    (* Since the flop is unstable on clk+, it must be the case that
         latch_clk_function σ = Bit1 [ BUT WHY?]
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
    { (* Some invariant about the fact that σ clk = Bit1 and σ old_clk = Bit0.... *)
      admit.
    }
    apply latch_clk_function_Bit1_r_ack in Hfun; auto.
    assert (Hunstable' : σ (ack (latch_output l)) = neg_value (σ (req (latch_output l)))).
    { rewrite Hfun. Search (neg_value _ = _).
      symmetry in Heq. apply val_is_bit_neg_inversion in Heq; try solve_val_is_bit.
      simpl. rewrite <- Heq.
      rewrite val_is_bit_neg_neg; try solve_val_is_bit.
    }
    apply wf_right_env in Hunstable'; auto; find_contradiction.

  * (* t = right_req (2) *)
    replace (latch_transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.
    step_inversion_clean.
    combine_state_equiv_on_domain.
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
    clear Hin. clear Hdec. Search flop.
    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ apply wf_reset_hidden_1; auto. }
    2:{ apply wf_hidden_reset_1; auto. }
    destruct Hstep3 as [Hequiv2 Hclk].
    combine_state_equiv_on.
    combine_state_equiv_on_complex; try (simpl; solve_space_set).
    combine_state_equiv_on_domain.
    (* Know: H : Bit0 = σ0 clk = Bit1 *)
    contradict H. rewrite_state_equiv; try solve_in_dom.
    reduce_eqb; inversion 1.
  * (* t = clk_fall_state0_marked *)
    replace (latch_transition_event l clk_fall σ)
          with (Event (latch_clk l) Bit0)
          in Hstep
          by auto.
    step_inversion_clean.
    clear Hin. clear Hdec. 
    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ apply wf_reset_hidden_1; auto. }
    2:{ apply wf_hidden_reset_1; auto. }
    destruct Hstep3 as [Hequiv2 Hclk].
    combine_state_equiv_on.
    combine_state_equiv_on_complex; try (simpl; solve_space_set).
    combine_state_equiv_on_domain.

    contradict H. rewrite_state_equiv; try solve_in_dom.
    reduce_eqb; inversion 1.

  * (* t = left_req_clk_rise_marked *)
    replace (latch_transition_event l clk_rise σ)
          with (Event (latch_clk l) Bit1)
          in Hstep
          by auto.
    step_inversion_clean.
    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ apply wf_reset_hidden_1; auto. }
    2:{ apply wf_hidden_reset_1; auto. }
    destruct Hstep3 as [Hequiv2 Hclk].
    combine_state_equiv_on.
    combine_state_equiv_on_complex; try (simpl; solve_space_set).
    combine_state_equiv_on_domain.

    clear Hin. clear Hdec. 

    contradict H1.
    rewrite_state_equiv; try solve_in_dom.
    reduce_eqb; inversion 1.
  * (* t = right_ack_clk_rise_marked *)
    replace (latch_transition_event l clk_rise σ)
          with (Event (latch_clk l) Bit1)
          in Hstep
          by auto.
    step_inversion_clean.
    apply flop_inversion_clk in Hstep3.
    2:{ solve_all_disjoint. }
    2:{ apply wf_reset_hidden_1; auto. }
    2:{ apply wf_hidden_reset_1; auto. }
    destruct Hstep3 as [Hequiv2 Hclk].
    combine_state_equiv_on.
    combine_state_equiv_on_complex; try (simpl; solve_space_set).
    combine_state_equiv_on_domain.

    clear Hin. clear Hdec. 

    contradict H1.
    rewrite_state_equiv; try solve_in_dom.
    reduce_eqb; inversion 1.

  Unshelve. all: exact (fun _ => true).

  Admitted.

(*** HERE ****)


Ltac distinguish_events :=
  match goal with
  | [ |- context[ Some (latch_transition_event _ ?t _) <> Some (Event _ _) ] ] =>
    intros; destruct t; auto; inversion 1; fail
  | [ |- context[ None <> Some _ ] ] => intros; inversion 1
  | [ |- context[ Some _ <> None ] ] => intros; inversion 1
  end.


Lemma transition_clk_state0 : forall σ σ' t,
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    σ' (latch_state0 l) = σ (latch_state0 l).
Proof.
    intros σ σ' t Hstep.
    destruct t; try find_contradiction;
        unfold latch_transition_event, transition_event in Hstep.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      rewrite_state_equiv; try solve_in_dom.
      auto.

Unshelve. all:exact (fun _ => true).
Qed.
Lemma transition_clk_old_clk : forall σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    σ' (latch_old_clk l) = σ (latch_old_clk l).
Proof.
    intros σ σ' t Hwf Hstep.
    destruct t; try find_contradiction;
        unfold latch_transition_event, transition_event in Hstep.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      apply flop_inversion_clk in Hstep3.
      2:{ solve_all_disjoint. }
      2:{ auto with wf. }
      2:{ auto with wf. }
      destruct Hstep3.
      combine_state_equiv_on.
      rewrite_state_equiv; try solve_in_dom.
      auto.
    + step_inversion_clean.
      combine_state_equiv_on_complex; try (simpl; solve_space_set).
      apply flop_inversion_clk in Hstep3.
      2:{ solve_all_disjoint. }
      2:{ auto with wf. }
      2:{ auto with wf. }
      destruct Hstep3.
      combine_state_equiv_on.
      rewrite_state_equiv; try solve_in_dom.
      auto.

Unshelve. all:exact (fun _ => true).
Qed.

Section disjoint_place_marked.

  Variable σ σ' : state name.
  Variable t : token_transition.
  Hypothesis Hstep : latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ'.
  Hypothesis Hwf : wf_stage_state l σ. 

  Definition disjoint_place_marked_lemma {t1 t2} (p : stage_place t1 t2) :=
    t1 <> t -> t2 <> t ->
    prop_marked p σ' ->
    prop_marked p σ.

  Lemma disjoint_place_marked_left_ack_left_req : disjoint_place_marked_lemma left_ack_left_req.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    constructor.
      rewrite_back_wf_scoped; try distinguish_events.
      rewrite_back_wf_scoped; try distinguish_events.
      auto.
    Unshelve. all: auto with wf.
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

      compare (σ (latch_clk l)) (σ (latch_old_clk l)).
      2:{ apply clk_fall_left_ack_state0_marked.
          { rewrite <- Hclk; auto. }
          { apply val_is_bit_neq in Hneq0; try solve_val_is_bit.
            rewrite <- Hneq0.
            rewrite <- Hclk.
            rewrite H.
            auto.
          }
      }
      { (* if these are equal, then... *)
        apply clk_fall_left_ack_marked.
        { rewrite <- Hclk; auto. }
        { rewrite <- (transition_clk_state0 σ σ0 t); auto.
          rewrite <- Hack; auto.
        }
      }

    * compare t clk_rise.
      { (* if the clk+ event happens, contradiction iwth (σ (latch_clk l) = Bit0) *)
        contradict H.
        replace (latch_transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        rewrite (wf_update _ (latch_stage_well_formed l) _ _ _ _ Hstep); inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_back_wf_scoped; try distinguish_events.
        auto.
      }

      apply clk_fall_left_ack_state0_marked.
      { rewrite <- Hclk; auto. }
      { erewrite <- transition_clk_old_clk; eauto. }

    Unshelve. all: auto with wf.
  Qed.

  Lemma disjoint_place_marked_clk_rise_right_req : disjoint_place_marked_lemma clk_rise_right_req.
  Proof.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    * assert (Hold_clk : σ (latch_old_clk l) = Bit0).
      { erewrite <- transition_clk_old_clk; eauto. }

      compare t clk_fall.
      { unfold latch_transition_event, transition_event in Hstep.
        step_inversion_clean.
        decide_events_of Hstep.
        apply union_inversion_left_only in Hstep; auto.
        inversion Hstep as [Hstep0 Hequiv0]; clear Hstep.
        step_inversion_clean. clear Hstep3 Hequiv0.
        contradict H (* σ0 clk = Bit1 *).
        rewrite_state_equiv; simpl; try solve_in_dom.
        reduce_eqb.
      }

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
      erewrite transition_clk_state0; eauto.

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
    Print prop_marked.
    intros Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
Print prop_marked.
    * Print token_transition.
      assert (Hwf' : wf_stage_state l σ0).
      { eapply step_wf_state_lemma; eauto. }
      compare t left_req.
      { unfold latch_transition_event, transition_event in Hstep.
        step_inversion_clean.
        decide_events_of Hstep.
        apply union_inversion_left_only in Hstep; auto.
        inversion Hstep as [Hstep0 Hequiv0]; clear Hstep.
        step_inversion_clean.
        apply func_stable_equiv in H1. 2:{ solve_space_set. }

        (* Since left_req had taken a step, it must have been the case that
           left_env was unstable in σ.
           *)
        assert (Henv : σ (req (latch_input l)) = σ (ack (latch_input l))).
        { apply neg_value_inj; auto; try solve_val_is_bit. }
        (* since latch_clk_function l σ0 = Bit1, it must be the case that
           [latch_clk_function_Bit1_l_req] σ0 (req (latch_input l)) = if_token l (σ0 (latch_state0 l))
           and thus neg_value (σ (req (latch_input l))) = if_token l (σ state0).
         *)
        assert (Hreq : σ (req (latch_input l)) = neg_value (if_token l (σ (latch_state0 l)))).
        { rewrite H in H1. 
          symmetry in H1.
          apply latch_clk_function_Bit1_l_req in H1; auto.

          rewrite <- Hequiv1 in H1; auto.
          2:{ solve_in_dom. }
          simpl in H1.
          unfold update in H1. reduce_eqb.
          
          symmetry; apply val_is_bit_neg_inversion; try solve_val_is_bit; symmetry.
          simpl. rewrite H1.
          rewrite_state_equiv; try solve_in_dom.
          simpl.
          auto.
        }
        clear Hin.


        assert (Hclk : σ (latch_clk l) = σ0 (latch_clk l)).
        { rewrite_state_equiv; try solve_in_dom; auto. }
        assert (Hold_clk : σ (latch_old_clk l) = σ0 (latch_old_clk l)).
        { rewrite_state_equiv; try solve_in_dom; auto. }
        compare (latch_clk_function l σ) Bit1.
        - (* latch_clk_function l σ = Bit1 *)
          apply clock_fall_flop_marked; auto.
          { rewrite Hclk; auto. }
          { rewrite Hold_clk; auto. }
          { apply func_stable_equiv; try solve_space_set.
            rewrite Heq0.
            rewrite Hclk; auto.
          }
        - (* latch_clk_function l σ = Bit0 and latch_clk_function l σ0 = Bit1 after changing l_req. *)

          (* Perhaps need to modify prop_marked clock_fall with more information? *)
          admit.
    }        
        
(*
      apply func_stable_equiv in H1; try solve_space_set.
      apply clock_fall_flop_marked; auto.
      { rewrite_back_wf_scoped; auto. distinguish_events. }
      { erewrite <- transition_clk_old_clk; eauto. }
      { apply func_stable_equiv; try solve_space_set.
        (* need to know latch_clk_function l σ = latch_clk_function l σ0... *)
        rewrite_back_wf_scoped; auto; try distinguish_events.
        rewrite (latch_clk_function_equiv σ0); auto.
        (* We know state0 hasn't changed, and ctrl_reset_n. Waht about l_req and r_ack? *)
        intros x Hx.
        decompose_set_structure.
        { admit (* true *). }
        { symmetry; eapply transition_clk_state0; eauto. }
        { compare t 
rewrite_back_wf_scoped; auto.
          compare 

      }

clock_fall_flop_marked
clock_fall_state0_marked
*)

  Admitted.


  Lemma disjoint_place_marked_left_req_clk_rise : disjoint_place_marked_lemma left_req_clk_rise.
  Admitted.


  Lemma disjoint_place_marked_right_ack_clk_rise : disjoint_place_marked_lemma right_ack_clk_rise.
  Admitted.

End disjoint_place_marked.
  

  Lemma disjoint_place_marked : forall σ σ' t,
    latch_stage_with_env l ⊢ σ →{Some (latch_transition_event l t σ)} Some σ' ->
    wf_stage_state l σ ->
    forall t1 t2 (p : stage_place t1 t2),
      t1 <> t ->
      t2 <> t ->
      prop_marked p σ' ->
      prop_marked p σ.
  Proof.
    
    intros σ σ' t Hstep Hwf t1 t2 p Ht1 Ht2 Hmarked.
    dependent destruction p.
    * eapply disjoint_place_marked_left_ack_left_req; eauto.
    * eapply disjoint_place_marked_clk_fall_left_ack; eauto.
    * eapply disjoint_place_marked_clk_rise_right_req; eauto.
    * eapply disjoint_place_marked_right_req_right_ack; eauto.
    * eapply disjoint_place_marked_clock_fall; eauto.
    * eapply disjoint_place_marked_left_req_clk_rise; eauto.
    * eapply disjoint_place_marked_right_ack_clk_rise; eauto.
  Qed.
    dependent destruction Hmarked.
    * 

    * constructor.
      rewrite_back_wf_scoped; try distinguish_events.
      rewrite_back_wf_scoped; try distinguish_events.
      auto.

    * 

  * 

    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.

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
