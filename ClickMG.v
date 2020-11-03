Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import MarkedGraph.
Require Import Click.

Require Import Omega.


Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.

Module ClickMG (ClickModule : ClickType).
  Export ClickModule.
  Module Desync := Desync(ClickModule).
  Export Desync.
  Module WFClick := WFStage(ClickModule).
  Export WFClick.
  Module SSTactics := StateSpaceTactics(Name).
  Export SSTactics.

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


  (***TODO: See ipad notes, removing timing assumptions here and replace with clk_fall
  → left_ack assumption. Also TODO: incorporate this delay into state space Click controller. *)

  Inductive stage_place : token_transition -> token_transition -> Set :=
  (* L.ack -> L.req *)
  (* CLK- -> L.req *)
  (* R.req -> L.req *)
  (* ENVIRONMENT constraint: we expect handshakes to obey a 2-phase handshake
     protocol, so we don't expect an input on left_req until left_ack has been
     updated by the controller. *)
  | left_ack_left_req : stage_place left_ack left_req
  (* TIMING constraint: changes inside the controller propogate faster than
     communication between controllers. In the controller, if this is not
     respected, it will lead to an error state as the clock component will not
     be stable when the new inputs arrive. *)
  | clk_fall_left_ack : stage_place clk_fall left_ack
  (* TIMING constraint: changes inside the controller propogate faster than
     communication between controllers. In other words, wait for state0 to be
     propogated to both left_ack AND right_req before accepting input on
     left_req. *)

  (* CLK+ -> L.ack *)
  (* REDUNDANT
  | clk_rise_left_ack : stage_place clk_rise left_ack
  *)
  
  (* CLK+ -> R.req *)
  | clk_rise_right_req : stage_place clk_rise right_req

  (* R.req -> R.ack *)
  (* ENVIRONMENT constraint: we expect handshakes to obey a 2-phase handshake
     protocol, so we don't expect an input on right_ack until right_req has been
     updated by the controller  *)
  | right_req_right_ack : stage_place right_req right_ack
  
  (* CLK+ -> CLK- *)
  | clock_fall : stage_place clk_rise clk_fall
  (* REDUNDANT
  | clock_rise : stage_place clk_fall clk_rise
  *)
  
  (* left_req -> CLK+ *)
  (* right_ack -> CLK+ *)
  | left_req_clk_rise : stage_place left_req clk_rise
  | right_ack_clk_rise : stage_place right_ack clk_rise
  .


  (** The only thing that is affected by token or non-token stages is the
  initial markings. These are indexed by two boolean values: whether the current
  stage has received a token or not on reset, and whether the current stage
  generates a token or not on reset. *)


  Definition init_marking_flag (in_flag : token_flag) (out_flag : token_flag) 
      : forall t1 t2, stage_place t1 t2 -> nat :=
    match in_flag, out_flag with
    (* Traditional non-token stage *)
    | Token, NonToken => fun t1 t2 p => match p with
                                      | left_req_clk_rise => 1
                                      | right_ack_clk_rise => 1
(*                                      | clock_rise => 1*)
                                      | _ => 0
                                      end
    (* Traditional token stage *)
    | NonToken, Token => fun t1 t2 p => match p with
                                        | left_ack_left_req => 1
                                        | right_req_right_ack => 1
(*                                        | clock_rise => 1*)
                                        | _ => 0
                                        end
    (* Token with left token stage *)
    | Token, Token    => fun t1 t2 p => match p with
                                      | left_req_clk_rise => 1
                                      | right_req_right_ack => 1
(*                                      | clock_rise => 1*)
                                      | _ => 0
                                      end
    | NonToken, NonToken => fun t1 t2 p => match p with
                                           | left_ack_left_req => 1
                                           | right_ack_clk_rise => 1
(*                                           | clock_rise => 1*)
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
Arguments MG_SS {name name_dec transition transition_dec} MG {MG_scheme}.

  Inductive place_eq : forall {t1 t2 t1' t2' : token_transition}, stage_place t1 t2 -> stage_place t1' t2' -> Prop :=
  | place_refl : forall t1 t2 (p : stage_place t1 t2), place_eq p p.


  Class stage_naming_scheme :=
    { stage_place_name : forall (l : latch even odd) {t1 t2 : token_transition}, stage_place t1 t2 -> name
    ; stage_places_disjoint_transitions : forall l t1 t2 (p : stage_place t1 t2),
      stage_place_name l p ∉ space_domain (latch_stage_with_env l)
    ; stage_places_all_disjoint : forall l f1 f2 {t1 t2 t1' t2'} (p : stage_place t1 t2) (p' : stage_place t1' t2'),
      stage_place_name l p = stage_place_name l p' ->
      StateSpace.place_eq (stage_MG f1 f2) p p'

    }.

  Instance stage_scheme : stage_naming_scheme :=
    {| stage_place_name := fun l t1 t2 p =>
                             match p with
                             | left_ack_left_req => latch_and_nat l "left_ack_left_req"
                             | clk_fall_left_ack => latch_and_nat l "clk_fall_left_ack"
                             | clk_rise_right_req => latch_and_nat l "clk_rise_right_req"
                             | right_req_right_ack => latch_and_nat l "right_req_right_ack"
                             | clock_fall => latch_and_nat l "clock_fall"
                             | left_req_clk_rise => latch_and_nat l "left_req_clk_rise"
                             | right_ack_clk_rise => latch_and_nat l "right_ack_clk_rise"
                             end
    |}.
  * intros l ? ? p.
    Search space_domain latch_stage_with_env.
    rewrite dom_latch_stage_with_env.
    to_in_list_dec.
    simpl.
    destruct p; auto.
  * intros l f1 f2 ? ? ? ? p p' Heq.
    destruct p; destruct p'; find_contradiction;
      constructor.
  Defined.


Section TokenMG_to_SS.

  Variable l : latch even odd.
  Variable in_flag : token_flag.
  Let out_flag := latch_to_token_flag l.

  Definition name_to_stage_place (x : name) : option { t1 : token_transition &
                                                     { t2 : token_transition & stage_place t1 t2 }}.
    refine (if x =? stage_place_name l left_ack_left_req
            then Some (existT _ _ (existT _ _ left_ack_left_req))
            else if x =? stage_place_name l clk_fall_left_ack
            then Some (existT _ _ (existT _ _ clk_fall_left_ack))
            else if x =? stage_place_name l clk_rise_right_req
            then Some (existT _ _ (existT _ _ clk_rise_right_req))
            else if x =? stage_place_name l right_req_right_ack
            then Some (existT _ _ (existT _ _ right_req_right_ack))
            else if x =? stage_place_name l clock_fall
            then Some (existT _ _ (existT _ _ clock_fall))
            else if x =? stage_place_name l left_req_clk_rise
            then Some (existT _ _ (existT _ _ left_req_clk_rise))
            else if x =? stage_place_name l right_ack_clk_rise
            then Some (existT _ _ (existT _ _ right_ack_clk_rise))
            else None).
  Defined.
  Lemma name_to_stage_place_eq : forall x t1 t2 (p : stage_place t1 t2),
    name_to_stage_place x = Some (existT _ _ (existT _ _ p)) ->
    x = stage_place_name l p.
  Proof.
    intros x t1 t2 p; destruct p; simpl; intros Heq;
      unfold name_to_stage_place in Heq;
      repeat compare_next; auto.
  Qed.
  Lemma name_to_stage_place_neq : forall x,
    name_to_stage_place x = None ->
    forall t1 t2 (p : stage_place t1 t2), x <> stage_place_name l p.
  Proof.
    intros x Heq.
    unfold name_to_stage_place in Heq.
    repeat compare_next.
    intros t1 t2 p; destruct p; auto.
  Qed.

  Definition name_is_stage_place_dec x : 
                           {t1 : token_transition &
                           {t2 : token_transition & {p : stage_place t1 t2 & x = stage_place_name l p}}}
                        + {forall t1 t2 (p : stage_place t1 t2), x <> stage_place_name l p}.
    destruct (name_to_stage_place x) as [[t1 [t2 p]] | ] eqn:Hx.
    * left. exists t1; exists t2; exists p.
      apply name_to_stage_place_eq; auto.
    * right. apply name_to_stage_place_neq; auto.
  Defined.

  Definition token_transition_update_value (t : token_transition) (v : value) : value :=
    match t with
    | clk_rise => Bit1
    | clk_fall => Bit0
    | _ => neg_value v
    end.
  Definition token_transition_name (t : token_transition) : name :=
    match t with
    | left_ack => ack (latch_input l)
    | left_req => req (latch_input l)
    | right_req => req (latch_output l)
    | right_ack => ack (latch_output l)
    | clk_rise  => latch_clk l
    | clk_fall  => latch_clk l
    end.
  Lemma token_name_domain : forall t, token_transition_name t ∈ space_domain (latch_stage l).
  Proof.
    intros t.
    unfold space_domain.
    rewrite latch_stage_input, latch_stage_output.
    destruct t; simpl; solve_set.
  Qed.
    

  Program Instance stage_MG_scheme : MG_naming_scheme name (stage_MG in_flag out_flag) :=
  {| transition_name := token_transition_name
   ; place_name := @stage_place_name _ l
   ; name_is_place_dec := name_is_stage_place_dec
   ; transition_update_value := token_transition_update_value
   ; input_transition := from_list [left_req; right_ack]
   |}.
  Next Obligation.
    destruct p; destruct t; inversion 1.
  Qed.
  Next Obligation.
    decompose_set_structure; destruct t'; find_contradiction; auto.
  Qed.
  Next Obligation.
    destruct p; destruct p'; find_contradiction;
      constructor.
  Qed.

  Definition stage_MG_SS : StateSpace name := MG_SS (stage_MG in_flag out_flag).

End TokenMG_to_SS.
Existing Instance stage_MG_scheme.
Arguments name_is_place_dec {name transition} MG {MG_naming_scheme}.
Arguments traces_of {name}.


  Section SS_to_TokenMG.

  Variable l : latch even odd.
  Let out_flag := latch_to_token_flag l.
  (* in_flag is opposite of out_flag here *)
  Let in_flag := match l with
                 | Odd _ => Token
                 | Even _ => NonToken
                 end.

  Definition init_stage_MG_state : state name.
  Proof.
    intros x.
    refine (if x =? stage_place_name l left_ack_left_req
            then Num (init_marking (stage_MG in_flag out_flag) _ _ left_ack_left_req)
            else if x =? stage_place_name l clk_fall_left_ack
            then Num (init_marking (stage_MG in_flag out_flag) _ _ clk_fall_left_ack)
            else if x =? stage_place_name l clk_rise_right_req
            then Num (init_marking (stage_MG in_flag out_flag) _ _ clk_rise_right_req)
            else if x =? stage_place_name l right_req_right_ack
            then Num (init_marking (stage_MG in_flag out_flag) _ _ right_req_right_ack)
            else if x =? stage_place_name l clock_fall
            then Num (init_marking (stage_MG in_flag out_flag) _ _ clock_fall)
            else if x =? stage_place_name l left_req_clk_rise
            then Num (init_marking (stage_MG in_flag out_flag) _ _ left_req_clk_rise)
            else if x =? stage_place_name l right_ack_clk_rise
            then Num (init_marking (stage_MG in_flag out_flag) _ _ right_ack_clk_rise)
            else (σR l x)).
  Defined.


  (* The theorem *)
  Theorem MG_refines_stage :
    traces_of (latch_stage_with_env l) (σR l) ⊆ traces_of (stage_MG_SS l in_flag) init_stage_MG_state.
  Proof.
    unfold traces_of.
    intros t Hstage.
    destruct Hstage as [τ Hstage].
    (* Need to define a relation between <t,τ> acceepted by (latch_stage l) and
    <t,τ'> accepted by (stage_MG_SS l in_flag), and then prove that whenever
    latch_stage l ⊢ σR l →*{t} τ, there exists a τ' such that
    latch_stage l ⊢ init_stage_MG_state →*{t} τ'. *)
  Abort.


  Definition transition_event (t : token_transition) (σ : state name) : event name value :=
    let x := @transition_name name _ (stage_MG in_flag out_flag) _ t in
    let v := @transition_update_value name _ (stage_MG in_flag out_flag) _ t (σ x) in
    Event x v.


  (** When are a state and a marking related? *)
  Inductive state_relate_marking : state name -> marking (stage_MG in_flag out_flag) -> Prop :=
  | R_init : state_relate_marking (σR l) (init_marking (stage_MG in_flag out_flag))
  | R_step σ σ' t m m' : 
    state_relate_marking σ m ->
    latch_stage_with_env l ⊢ σ →{Some (transition_event t σ)} Some σ' ->
    is_enabled _ t m ->
    (forall {t1 t2} (p : stage_place t1 t2), m' _ _ p = fire t _ m _ _ p) ->
    state_relate_marking σ' m'
  | R_Eps σ σ' m:
    state_relate_marking σ m ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    state_relate_marking σ' m
  .

  Lemma dom_MG_SS : space_domain (stage_MG_SS l in_flag)
               == from_list [ token_transition_name l left_ack
                            ; token_transition_name l left_req
                            ; token_transition_name l right_req
                            ; token_transition_name l right_ack
                            ; token_transition_name l clk_rise
                            ; token_transition_name l clk_fall

                            ; stage_place_name l left_ack_left_req
                            ; stage_place_name l clk_fall_left_ack
                            ; stage_place_name l clk_rise_right_req
                            ; stage_place_name l right_req_right_ack
                            ; stage_place_name l clock_fall
                            ; stage_place_name l left_req_clk_rise
                            ; stage_place_name l right_ack_clk_rise
                            ].
  Proof.
    unfold space_domain. constructor; intros x Hx.
    * to_in_list_dec. simpl. simpl in Hx.
      deep_decompose_set_structure; simpl; reduce_eqb; auto;
        subst;
        match goal with
        | [ |- context[ token_transition_name _ ?t =? _ ] ] =>
          destruct t; simpl; reduce_eqb; auto
        | [ |- context[ place_name ?p =? _ ] ] =>
          destruct p; simpl; reduce_eqb; auto
        end.
    * to_in_list_dec. unfold in_list_dec in Hx.
      simpl.
      repeat compare_next;
        try (left; left; eexists; split; [ | reflexivity]; solve_set);
        try (left; right; eexists; split; [ | reflexivity]; solve_set);
        try (right; do 3 eexists; reflexivity).
  Qed. 

  Lemma stage_internal_disjoint :
    space_internal (latch_stage_with_env l) ⊥ space_domain (stage_MG_SS l in_flag).
  Proof.
    rewrite latch_stage_with_env_internal.
    rewrite dom_MG_SS.
    simpl.
    constructor; intros x [? Hx Hy].
    contradict Hy.
    decompose_set_structure;
      solve_space_set.
  Qed.
  Lemma stage_MG_internal_disjoint :
    space_internal (stage_MG_SS l in_flag) ⊥ space_domain (latch_stage_with_env l).
  Proof.
    rewrite dom_latch_stage_with_env. simpl.
    constructor. intros x [? Hx Hy].
    contradict Hy.
    destruct Hx as [t1 [t2 [p Hp]]]; subst.
    destruct p; solve_space_set.
  Qed.
End SS_to_TokenMG.

Hint Resolve stage_internal_disjoint stage_MG_internal_disjoint : click.
Arguments well_formed {name}.

Section SS_to_TokenMG_Proof.

  Variable l : latch even odd.
  Let out_flag := latch_to_token_flag l.
  (* in_flag is opposite of out_flag here *)
  Let in_flag := match l with
                 | Odd _ => Token
                 | Even _ => NonToken
                 end.
  Hint Resolve wf_MG_SS.

  Arguments stage_place_name {stage_naming_scheme} l {t1 t2}.

  Import ClickTactics.


  (** If σ1 is related to σ2 via t, then σ1 and σ2 are equal on all transition names.
  *)
  Lemma stage_relate_trace_domain : forall σ1 t σ2,
    relate_trace name (latch_stage_with_env l) (stage_MG_SS l in_flag)
                      (σR l) (init_stage_MG_state l)
                      σ1 t σ2 ->
    forall x tr,
      x = @transition_name name _ (stage_MG in_flag out_flag) _ tr ->
      σ1 x = σ2 x.
  Proof.
    intros σ1 t σ2 Hrelate x tr Hx.
    subst.
    eapply (relate_trace_domain _ (latch_stage_with_env l)
                                  (stage_MG_SS l in_flag)
            (σR l) (init_stage_MG_state l)); eauto with click.
    2:{ apply stage_internal_disjoint. }
    2:{ apply stage_MG_internal_disjoint. }
    2:{ apply wf_MG_SS. }
    2:{ rewrite dom_latch_stage_with_env.
        to_in_list_dec. simpl.
        destruct tr; simpl; reduce_eqb; auto.
      }
    2:{ unfold in_flag. rewrite dom_MG_SS.
        destruct tr; solve_space_set.
    }
    intros x Hx1 Hx2.
    unfold in_flag in Hx2; rewrite dom_MG_SS in Hx2.
    rewrite dom_latch_stage_with_env in Hx1.
    to_in_list_dec.
    simpl in Hx1, Hx2.
    unfold init_stage_MG_state, σR. simpl.
    repeat (compare_next; auto).
  Qed.

  Require Import Coq.Logic.FunctionalExtensionality.

  Lemma state_relate_marking_equiv : forall σ m1 m2,
    state_relate_marking l σ m1 ->
    (forall t1 t2 (p : stage_place t1 t2), m1 _ _ p = m2 _ _ p) ->
    state_relate_marking l σ m2.
  Proof.
    intros σ m1 m2 Hrelate Hm12.
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


  Arguments place_name {name transition} MG {MG_naming_scheme} {t1 t2}.

  (** Unfolding the definition of fire_in_state *)
  Lemma fire_in_state_place : forall t σ t1 t2 (p : stage_place t1 t2),
    @fire_in_state _ _ _ (stage_MG in_flag (latch_to_token_flag l)) _
                   t σ (place_name (stage_MG in_flag (latch_to_token_flag l)) p) =
      if t =? t2 then dec_value (σ (stage_place_name l p))
      else if t =? t1 then inc_value (σ (stage_place_name l p))
      else σ (stage_place_name l p).
  Proof.
    intros t σ t1 t2 p.
    unfold fire_in_state.
    destruct (name_is_place_dec (stage_MG in_flag (latch_to_token_flag l))
                                (place_name (stage_MG in_flag (latch_to_token_flag l)) p))
      as [[t1' [t2' [p' Hp']]] | Hcontra ].
    *  compare_next. { (* contradiction *) inversion p'. }
        assert (Heq : StateSpace.place_eq (stage_MG in_flag (latch_to_token_flag l)) p p').
        { eapply places_all_disjoint.
          auto. 
        }
        dependent destruction Heq.
        reflexivity.
    * contradiction (Hcontra _ _ p).
      auto.
  Qed.

  Lemma state_relate_marking_implies : forall σ t σ',
    relate_trace name (latch_stage_with_env l) (stage_MG_SS l in_flag)
                      (σR l) (init_stage_MG_state l)
                      σ t σ' ->
    state_relate_marking l σ (state_to_marking σ').
  Proof.
    intros σ t σ' Hrelate.
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
      { unfold transition_event.
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

        assert (@transition_name name _ (stage_MG in_flag out_flag) _ t'
             <> @place_name _ _ (stage_MG in_flag out_flag) _ t1 t2 p).
        { apply transition_place_name_disjoint. }
        reduce_eqb.

        rewrite fire_in_state_place.
        Search inc_value.
        repeat compare_next; auto.
        + rewrite val_to_nat_dec; auto.
        + rewrite val_to_nat_inc; auto.
          
          admit (* place names will always be natural numbers... lemma *).
  Admitted.


Lemma eps_from_σR : forall σ,
      latch_stage_with_env l ⊢ σR l →*{t_empty} Some σ ->
      forall x, x ∈ space_output (latch_stage_with_env l) ->
      σ x = σR l x.
Proof.
  intros σ Hstep x Hx.
  dependent induction Hstep; subst; auto.
  erewrite wf_scoped; [ | | eauto | intro; inversion 1 |]; auto.
  { solve_set. }
Qed.


  (************************** TODO ********************************)

  (** Intuitively, [prop_marked p σ] is a property that holds on a state σ
  whenever a related marking m satisfies [m(p) > 0]. *)
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
                              | NonToken => neg_value (σ (latch_state0 l))
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

  (* right_req -> right_ack *)
  | right_req_right_ack_marked σ :
    σ (req (latch_output l)) <> σ (latch_state0 l) ->
    prop_marked right_req_right_ack σ

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
    latch_stage_with_env l ⊢ σ →{Some (transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t), prop_marked p σ.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ t σ' Hwf Hstep t0 p.
    dependent destruction p.
    { (* left_ack_left_req *)
      constructor.
      unfold transition_event in Hstep.
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
      unfold transition_event in Hstep.
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
      symmetry in Heq.
      apply val_is_bit_neg_inversion in Heq.
      2:{ solve_val_is_bit. }
      simpl.
      rewrite <- Heq.
      destruct l; simpl; auto.
      rewrite val_is_bit_neg_neg; auto.
      { solve_val_is_bit. } 
    }

    { (* clk_rise_right_req *) 
      replace (transition_event l right_req σ)
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
      unfold transition_event in Hstep.
      repeat (step_inversion_1; try combine_state_equiv_on).
   }

  { (* clock_fall *)
    unfold transition_event in Hstep.
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
    unfold transition_event in Hstep.
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
    unfold transition_event in Hstep.
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
        2:{ constructor. }
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
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p σ' ->
    prop_marked p σ.
  Proof.
    intros σ σ' Hwf Hstep t1 t2 p Hp.
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
    latch_stage_with_env l ⊢ σ →{Some (transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t),
        ~ prop_marked p σ'.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ σ' t Hwf Hstep t0 p Hprop.

    dependent destruction Hprop.
    * (* t = left_req *)
      unfold transition_event in Hstep.

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

      unfold transition_event in Hstep.
      repeat (step_inversion_1; try combine_state_equiv_on).
      clear Hequiv1 Hequiv2.

      contradict Heq.
      simpl in H, Hreq, Hack.
      rewrite <- Hreq, <- Hack, H.

      assert (Hack' : val_is_bit (σ (ack (latch_output l)))) by solve_val_is_bit.

      inversion Hack'; my_subst; simpl; simpl in Hack;
        rewrite Hack; discriminate.

    * (* t = left_ack (1) *)
      replace (transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.

      assert (Hack : σ0 (ack (latch_input l)) = neg_value (σ (ack (latch_input l)))).
      { rewrite_step_inversion; auto.
      }
      assert (Hreq : σ0 (req (latch_input l)) = σ (req (latch_input l))).
      { rewrite_step_inversion; auto.
      }

      repeat step_inversion_1.
      repeat combine_state_equiv_on.
      standardize_state_equiv_on_set Hequiv. clear Hequiv1.

      assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
      { 
        rewrite_state_equiv; auto.
        { simpl. solve_space_set. }
      }

      contradict Heq.
      simpl in Hack, Hstate0, H0.
      rewrite <- Hack, <- Hstate0, H0.

      assert (Hbit : val_is_bit (σ0 (latch_state0 l))).
      { simpl. rewrite Hstate0. solve_val_is_bit. }
      

      destruct l; simpl; [ eapply bit_neq_neg_l | apply bit_neq_neg_r ]; auto.

   * (* t = left_ack (2) *)

     replace (transition_event l left_ack σ)
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

      assert (state0_bit : val_is_bit (σ (latch_and_nat l "state0"))).
      { solve_val_is_bit. }

      symmetry in Heq.
      apply val_is_bit_neg_inversion in Heq.
      symmetry in Heq.

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
          { simpl; rewrite Heq.
            apply bit_neq_neg_l.
            destruct l; simpl; auto.
            inversion state0_bit; simpl; constructor.
          }
          { simpl; rewrite Heq.
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
    replace (transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.

    repeat (step_inversion_1). repeat combine_state_equiv_on.
    standardize_state_equiv_on_set Hequiv.
    standardize_state_equiv_on_set Hequiv5.
    combine_state_equiv_on_complex. { solve_in_dom. }
    standardize_state_equiv_on_set Hequiv0.
    admit.
    

  Admitted.


  Lemma disjoint_place_marked : forall σ σ' t,
    latch_stage_with_env l ⊢ σ →{Some (transition_event l t σ)} Some σ' ->
    wf_stage_state l σ ->
    forall t1 t2 (p : stage_place t1 t2),
      t1 <> t ->
      t2 <> t ->
      prop_marked p σ' ->
      prop_marked p σ.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ σ' t Hstep Hwf t1 t2 p Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    * constructor.
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }
      auto.

    * constructor.
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }
      rewrite_back_wf_scoped.
      2:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }
      auto.

    * compare t clk_rise.
      { (* if the clk+ event happens, contradiction iwth (σ (latch_clk l) = Bit0) *)
        contradict H.
        replace (transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        rewrite_step_inversion. inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_back_wf_scoped.
        2:{ intros v.
            destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
        }
        auto.
      }
      assert (Hstate0: σ0 (latch_state0 l) = σ (latch_state0 l)).
      { destruct t; try find_contradiction;
        unfold transition_event in Hstep.
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
            destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
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
        replace (transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        rewrite_step_inversion. inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { rewrite_back_wf_scoped.
        2:{ intros v.
            destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
        }
        auto.
      }
      assert (Hold_clk : σ0 (latch_old_clk l) = σ (latch_old_clk l)).

      { destruct t; try find_contradiction;
        unfold transition_event in Hstep.
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

    * 

  Admitted.


  Lemma init_relate_implies_marked : forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p (σR l) ->
    init_marking (stage_MG in_flag out_flag) _ _ p > 0.
  Admitted.

  Lemma state_relate_marking_steps : forall σ m,
    state_relate_marking l σ m ->
    exists tr, latch_stage_with_env l ⊢ σR l →*{tr} Some σ.
  Proof.
    intros σ m Hrelate.
    induction Hrelate.
    * exists t_empty. constructor.
    * destruct IHHrelate as [tr IH].
      exists (tr ▶ transition_event l t σ).
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
About step_wf_state.
    induction Hrelate as [ | ? ? ? ? ? Hrelate IH Hstep Henabled Hm'
                           | ? ? ? Hrelate IH Hstep]; intros t1 t2 p Hp.
    * apply init_relate_implies_marked; auto.
    * assert (Hwf : wf_stage_state l σ).
      { apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state; eauto.
      }

      unfold is_enabled in Henabled.
      rewrite Hm'.
      unfold fire.
      compare_next.
      { inversion p; subst; find_contradiction. }
      compare_next.
      { (* t = t2 *) contradict Hp.
        eapply outgoing_place_not_marked; [ | eauto]; auto.
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

  Theorem state_related_enabled : forall σ σ' t m,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (transition_event l t σ)} Some σ' ->
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
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    val_is_bit v.
  Proof.
    intros ? ? ? ? Hwf Hstep.
    assert (v = σ' x).
    { apply wf_update in Hstep; auto. }
    subst.
    assert (x ∈ space_domain (latch_stage_with_env l)).
    { apply wf_space in Hstep; auto.
      unfold space_domain. solve_set.
    }
    apply step_wf_state_lemma in Hstep; auto.
    clear Hwf. Print wf_stage_state.
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

(**********)
(** HERE **)
(**********)

Import ClickTactics.

  (* How to prove this? Maybe build on prop_marked?? *)
  Lemma step_implies_event_step : forall t σ x v σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    x = @transition_name name _ (stage_MG in_flag out_flag) _ t ->
    exists t', v = @transition_update_value _ _ (stage_MG in_flag out_flag) _ t' (σ x).
(*
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    x = @transition_name name _ (stage_MG in_flag out_flag) _ t ->
    v = @transition_update_value name _ (stage_MG in_flag out_flag) _ t (σ x).
*)
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros t σ x v σ' Hwf Hstep.
    assert (Hv : val_is_bit v).
    { eapply step_implies_bit; eauto. }

    remember t as t'.
    destruct t'; simpl; intros Hx.
    5:{ (* clk_rise *)
        
  Abort.


(*

  


  Notation "σ1 'R{' t '}' σ2" := (relate_trace name (latch_stage l) (stage_MG_SS l in_flag)
                      (σR l) init_stage_MG_state
                      σ1 t σ2)
    (left associativity, at level 92).

      

  Lemma left_req_relation_enabled : forall σ1 t σ2,
    σ1 R{t} σ2 ->
    stable latch_clk_component σ1 ->
    is_enabled (stage_MG in_flag out_flag) left_req (state_to_marking σ2).
  Admitted.
  Lemma right_ack_relation_enabled : forall σ1 t σ2,
    σ1 R{t} σ2 ->
    stable latch_clk_component σ1 ->
    is_enabled (stage_MG in_flag out_flag) right_ack (state_to_marking σ2).
  Admitted.
  Lemma left_ack_relation_enabled : forall σ1 t σ2,
    σ1 R{t} σ2 ->
    ~ stable latch_left_ack_component σ1 ->
    is_enabled (stage_MG in_flag out_flag) left_ack (state_to_marking σ2).
  Admitted.
  Lemma right_req_relation_enabled : forall σ1 t σ2,
    σ1 R{t} σ2 ->
    σ1 (req (latch_output l)) <> σ1 (latch_state0 l) ->
    is_enabled (stage_MG in_flag out_flag) right_req (state_to_marking σ2).
  Admitted.

  (* This isn't quite right... *)
  Lemma clk_rise_relation_enabled : forall σ1 t σ2,
    σ1 R{t} σ2 ->
    σ1 (latch_clk l) = σ1 (latch_old_clk l) ->
    σ1 (latch_clk l) = Bit0 ->
    ~ stable latch_clk_component σ1 ->
    is_enabled (stage_MG in_flag out_flag) clk_rise (state_to_marking σ2).
  Admitted.
  Lemma clk_fall_relation_enabled : forall σ1 t σ2,
    σ1 R{t} σ2 ->
    σ1 (latch_clk l) = σ1 (latch_old_clk l) ->
    σ1 (latch_clk l) = Bit1 ->
    ~ stable latch_clk_component σ1 ->
    is_enabled (stage_MG in_flag out_flag) clk_fall (state_to_marking σ2).
  Admitted.

*) 


  Lemma MG_relate_trace_step_lemma :
    relate_trace_step_lemma _ (latch_stage_with_env l) (stage_MG_SS l in_flag) (σR l) (init_stage_MG_state l).
  Proof.
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
    assert (Ht : exists t, x = @transition_name _ _ (stage_MG in_flag out_flag) _ t
                      /\   v = @transition_update_value _ _ (stage_MG in_flag out_flag) _ t (σ1 x)).
    {
      rewrite latch_stage_with_env_input in Hx.
      rewrite latch_stage_with_env_output in Hx.
      decompose_set_structure.
      + exists left_req; split; [ reflexivity | ].
        simpl.
        repeat step_inversion_1. rewrite Heq. admit (* why is l_ack = l_req? *).
      + exists left_ack; split; [ reflexivity | ].
        simpl.
        admit (* step_inversion_unstable. solve_bit_neq_neg.*).
      + exists right_req; split; [ reflexivity | ].
        admit (*step_inversion_unstable. solve_bit_neq_neg.*).
      + exists right_ack; split; [ reflexivity | ].
        admit (*step_inversion_unstable. solve_bit_neq_neg.*).
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
  Admitted.

  Lemma place_name_disjoint_SS : forall t1 t2 (p : place (stage_MG in_flag out_flag) t1 t2),
    place_name (stage_MG in_flag out_flag) p ∉ space_domain (latch_stage_with_env l).
  Proof.
    intros.
    rewrite dom_latch_stage_with_env.
    destruct p; solve_space_set.
  Qed.

  Theorem MG_refines_stage :
    traces_of (latch_stage_with_env l) (σR l) ⊆ traces_of (stage_MG_SS l in_flag) (init_stage_MG_state l).
  Proof.
    apply relate_trace_step_subset.
    { intros x Hdom1 Hdom2.
      unfold init_stage_MG_state. fold in_flag. fold out_flag.

      rewrite dom_latch_stage_with_env in Hdom1.
      simpl in Hdom1.
      decompose_set_structure; auto.
    }
    { apply MG_relate_trace_step_lemma. }
  Qed.


  End SS_to_TokenMG_Proof.


End ClickMG.
