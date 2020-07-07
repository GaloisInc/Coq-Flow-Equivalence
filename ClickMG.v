Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import MarkedGraph.
Require Import Click.

Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.

Section ClickMG.
  Variable name : Set.
  Context `{eq_dec name}.

Section TokenMG.

  Inductive token_transition :=
  | left_ack : token_transition
  | left_req : token_transition
  | right_req
  | right_ack
  | clk_rise
  | clk_fall
  .
  Instance token_transition_eq_dec : eq_dec token_transition.
  Proof.
    constructor; intros x y;
    destruct x; destruct y;
      try (left; reflexivity); try (right; discriminate).
  Defined.

  Inductive stage_place : token_transition -> token_transition -> Set :=
  (* L.ack -> L.req *)
  (* CLK- -> L.req *)
  (* R.req -> L.req *)
  | left_ack_left_req : stage_place left_ack left_req
  | clk_fall_left_req : stage_place clk_fall left_req
  | right_req_left_req : stage_place right_req left_req

  (* CLK+ -> L.ack *)
  | clk_rise_left_ack : stage_place clk_rise left_ack
  
  (* CLK+ -> R.req *)
  | clk_rise_right_req : stage_place clk_rise right_req

  (* R.req -> R.ack *)
  | right_req_right_ack : stage_place right_req right_req
  
  (* CLK- -> R.ack *)
  (* L.ack -> R.ack *)
  | clk_fall_right_ack : stage_place clk_fall right_ack
  | left_ack_right_ack : stage_place left_ack right_ack
  

  (* CLK+ -> CLK- *)
  | clock_fall : stage_place clk_rise clk_fall
  
  (* left_req -> CLK+ *)
  (* right_ack -> CLK+ *)
  | left_req_clk_rise : stage_place left_req clk_rise
  | right_ack_clk_rise : stage_place right_ack clk_rise
  .


  (** The only thing that is affected by token or non-token stages is the
  initial markings. These are indexed by two boolean values: whether the current
  stage has received a token or not on reset, and whether the current stage
  generates a token or not on reset. *)

Print marked_graph.

  Definition init_marking_flag (in_flag : token_flag) (out_flag : token_flag) 
      : forall t1 t2, stage_place t1 t2 -> nat :=
    match in_flag, out_flag with
    (* Traditional non-token stage *)
    | Token, NonToken => fun t1 t2 p => match p with
                                      | left_req_clk_rise => 1
                                      | right_ack_clk_rise => 1
                                      | _ => 0
                                      end
    (* Traditional token stage *)
    | NonToken, Token => fun t1 t2 p => match p with
                                      | right_req_left_req  => 1
                                      | clk_fall_left_req   => 1
                                      | left_ack_left_req   => 1
                                      | right_req_right_ack => 1
                                      | clk_fall_right_ack  => 1
                                      | left_ack_right_ack  => 1
                                      | _ => 0
                                      end
    (* Token with left token stage *)
    | Token, Token    => fun t1 t2 p => match p with
                                      | left_req_clk_rise => 1
                                      | right_req_right_ack => 1
                                      | clk_fall_right_ack  => 1
                                      | left_ack_right_ack  => 1
                                      | _ => 0
                                      end
    | NonToken, NonToken => fun t1 t2 p => match p with
                                      | right_req_left_req  => 1
                                      | clk_fall_left_req   => 1
                                      | left_ack_left_req   => 1
                                      | right_ack_clk_rise => 1
                                      | _ => 0
                                      end
    end.

  Variable in_flag out_flag : token_flag.

  Definition stage_MG : marked_graph token_transition :=
    {| place := stage_place
     ; init_marking := init_marking_flag in_flag out_flag
     |}.

End TokenMG.

Existing Instance token_transition_eq_dec.

Section SS_to_TokenMG.

  Variable even odd : Set.
  Context `{naming_scheme name even odd}.
  Variable dp_reset_n ctrl_reset_n : name.

  Variable l : latch even odd.
  Variable in_flag : token_flag.
  Definition out_flag := latch_to_token_flag l.
      


  Definition transition_update_value (t : token_transition) (v : value) : value :=
    match t with
    | clk_rise => Bit1
    | clk_fall => Bit0
    | _ => neg_value v
    end.
  Definition transition_name (t : token_transition) : name :=
    match t with
    | left_ack => ack (latch_input l)
    | left_req => req (latch_input l)
    | right_req => req (latch_output l)
    | right_ack => ack (latch_output l)
    | clk_rise  => latch_clk l
    | clk_fall  => latch_clk l
    end.
    

  Definition transition_to_event (t : token_transition) (σ : state name) : event name value :=
    let x := transition_name t in
    Event x (transition_update_value t (σ x)).

  Definition event_to_transition (e : event name value) : option token_transition :=
    match e with
    | Event x v => if x =? ack (latch_input l) then Some left_ack
                   else if x =? req (latch_input l) then Some left_req
                   else if x =? req (latch_output l) then Some right_req
                   else if x =? ack (latch_output l) then Some right_ack
                   else if x =? latch_clk l
                        then if v =? Bit0 then Some clk_fall
                             else if v =? Bit1 then Some clk_rise
                             else None
                   else None
    end.


  Definition visible_domain : list name :=
       req (latch_input l) :: ack (latch_input l)
    :: req (latch_output l) :: ack (latch_output l)
    :: latch_clk l :: nil.
  Hypothesis visible_disjoint : all_disjoint visible_domain.

  Inductive event_equiv_transition_trace : tail_list (event name value) ->
                                                 tail_list token_transition ->
                                                 Prop :=
  | equiv_t_empty : event_equiv_transition_trace t_empty t_empty

  | equiv_t_cons t t' e e' :
    event_equiv_transition_trace t t' ->
    Some e' = event_to_transition e ->
    event_equiv_transition_trace (t ▶ e) (t' ▶ e')
  .



  Inductive state_equiv_marking : state name ->
                                  tail_list (event name value) ->
                                  marking (stage_MG in_flag out_flag) ->
                                  tail_list token_transition ->
                                  Prop :=
  | state_equiv_marking0 (σ : state name) m : 
    σ = σR l false ->
    m = init_marking (stage_MG in_flag out_flag) ->
    state_equiv_marking σ t_empty m t_empty

  | state_equiv_marking_step σ σ' t t' (e : token_transition) (e' : event name value) m m':
    state_equiv_marking σ t m t' ->
    is_enabled (stage_MG in_flag out_flag) e m ->
    e' = transition_to_event e σ ->
    σ' = update_event σ e' ->
    m' = fire e (stage_MG in_flag out_flag) m ->
    state_equiv_marking σ' (t ▶ e') m' (t' ▶ e)

  | state_equiv_marking_epsilon σ σ' t t' m :
    state_equiv_marking σ t m t' ->
    (forall n, n ∈ from_list visible_domain ->
               σ n = σ' n) ->
    state_equiv_marking σ' t m t'

  | state_equiv_marking_internal σ t m t' σ' x v :
    state_equiv_marking σ t m t' ->
    σ' = update_event σ (Event x v) ->
    x ∉ from_list visible_domain ->
    state_equiv_marking σ' (t ▶ Event x v) m t'
  .

  Definition state_MG_traces : Ensemble (tail_list (event name value)) :=
    fun t => exists σ m t', state_equiv_marking σ t m t'.

  (* This is the hard lemma, I suspect *)
  Lemma stage_implies_stage_MG_event : forall σ t m e σ' t',
    state_equiv_marking σ t m t' ->
    latch_stage l ⊢ σ →{Some (transition_to_event e σ)} Some σ' ->
    is_enabled (stage_MG in_flag out_flag) e m.
  Admitted.



  Lemma transition_to_event_reverse : forall e σ,
    event_to_transition (transition_to_event e σ) = Some e.
  Proof.
    intros e σ.
    unfold visible_domain in visible_disjoint.
    destruct e; simpl;
      repeat (compare_next; try my_subst; try reflexivity; find_contradiction).
  Qed.

  Lemma event_equiv_transition_implies_state_equiv_marking : forall σ' t t' m,
    latch_stage l ⊢ σR l false →*{t} Some σ' ->
    [stage_MG in_flag out_flag]⊢ t' ↓ m ->
    event_equiv_transition_trace t t' ->
    state_equiv_marking σ' t m t'.
  Proof.
    intros σ' t t' m Hstep.
    generalize dependent m. generalize dependent t'.

    remember (latch_stage l) as S. 
    generalize dependent HeqS.
    remember (Some σ') as τ.
    generalize dependent σ'.
    induction Hstep; intros σ'' Heqτ HeqS; try inversion Heqτ; subst; try clear Heqτ;
      intros t' m HMG Hequiv.
    * inversion Hequiv; subst.
      inversion HMG; subst.
      constructor; auto.
    * specialize (IHHstep _ eq_refl eq_refl).
      inversion Hequiv; subst.
      inversion HMG; subst.
      eapply state_equiv_marking_step; eauto.
      { admit (* true *). }
      { admit (* true, but harder to show *). }
    * specialize (IHHstep _ eq_refl eq_refl).
      eapply state_equiv_marking_epsilon; eauto.
      { admit (* true *). }
  Admitted.

Lemma event_to_transition_compose : forall x v e σ,
    event_to_transition (Event x v) = Some e ->
    v = transition_update_value e (σ (transition_name e)) ->
    transition_to_event e σ = Event x v.
Proof.
    intros x v e σ He Hv.
    unfold event_to_transition in He.
    unfold transition_to_event.
    repeat (compare_next; [inversion He; subst; auto | ]).
    compare_next. 
    compare_next.
    { my_subst. reduce_eqb. inversion He; subst; auto. }
    compare_next.
    { my_subst. reduce_eqb. inversion He; subst; auto. }
Qed.

Lemma visible_domain_is_transition : forall x v,
    x ∈ from_list visible_domain ->
    exists e0, event_to_transition (Event x v) = Some e0.
Admitted.

Lemma transition_step_value : forall σ σ' x v e,
    latch_stage l ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ from_list visible_domain ->
    event_to_transition (Event x v) = Some e ->
    v = transition_update_value e (σ (transition_name e)).
Admitted.

  Theorem stage_implies_stage_MG_traces : forall t σ',
    latch_stage l ⊢ σR l false →*{t} Some σ' ->
    exists m t', event_equiv_transition_trace t t' /\ ([stage_MG in_flag out_flag]⊢ t' ↓ m).
  Proof.
    intros t σ' Hstep.
    remember (latch_stage l) as S.
    remember (Some σ') as τ.
    generalize dependent HeqS.
    generalize dependent σ'.
    induction Hstep; intros σ'' Heqτ HeqS; try inversion Heqτ; subst; try clear Heqτ.
    * exists (init_marking (stage_MG in_flag out_flag)).
      exists t_empty.
      split; constructor.
    * specialize (IHHstep _ eq_refl eq_refl).
      destruct IHHstep as [m [t' [Hequiv HMG]]].
      destruct e as [x v].

      destruct (In_Dec (from_list visible_domain) x) as [Hin | Hnin].
      + destruct (visible_domain_is_transition _ v Hin) as [e He].
        assert (is_enabled (stage_MG in_flag out_flag) e m).
        { eapply stage_implies_stage_MG_event.
          { apply event_equiv_transition_implies_state_equiv_marking; eauto. }
            
          { erewrite event_to_transition_compose; eauto.
            eapply transition_step_value; eauto.
          }
        }
        exists (fire e (stage_MG in_flag out_flag) m).
        exists (t' ▶ e).
        split.
        { constructor; auto.
        }
        { econstructor; eauto. }
      + (* contradiction *)
        contradict H1. admit.
    * clear H2. specialize (IHHstep _ eq_refl eq_refl).
      destruct IHHstep as [m [t' [Hequiv HMG]]].
      exists m. exists t'. split; auto.
  Admitted.
        

  End SS_to_TokenMG.


  Section Composition.

  End Composition.
End ClickMG.
