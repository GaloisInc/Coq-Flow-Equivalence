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

Module ClickMG (Export name : NameType).
  Module Click_name := Click(name).
  Export Click_name.
  Module SSTactics := StateSpaceTactics(name).
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

Module Type StageNamingScheme.
  Declare Module EO : EvenOddType.
  Export EO.

  Class stage_naming_scheme :=
    { stage_place_name : forall (l : latch EO.even EO.odd) {t1 t2 : token_transition}, stage_place t1 t2 -> name
    ; stage_places_disjoint_transitions : forall l t1 t2 (p : stage_place t1 t2),
      stage_place_name l p ∉ space_domain (latch_stage l)
    ; stage_places_all_disjoint : forall l f1 f2 {t1 t2 t1' t2'} (p : stage_place t1 t2) (p' : stage_place t1' t2'),
      stage_place_name l p = stage_place_name l p' ->
      StateSpace.place_eq (stage_MG f1 f2) p p'

    }.

  Parameter x_scheme : stage_naming_scheme.
  Existing Instance x_scheme.

  Module Stage := WFStage(EO).
  Export Stage.

End StageNamingScheme.

Module TokenMG_to_SS (Export XScheme : StageNamingScheme).
Section TokenMG_to_SS.

  Variable l : latch even odd.
  Variable in_flag : token_flag.
  Let out_flag := latch_to_token_flag l.

  Definition name_is_stage_place_dec : forall x,
                           {t1 : token_transition &
                           {t2 : token_transition & {p : stage_place t1 t2 & x = stage_place_name l p}}}
                        + {forall t1 t2 (p : stage_place t1 t2), x <> stage_place_name l p}.
  Proof.
    intros x.

    Ltac compare_place_name x p :=
      compare x (stage_place_name l p);
        [ left; do 3 eexists; reflexivity | ].
    compare_place_name x left_ack_left_req. Print stage_place.
    compare_place_name x clk_fall_left_ack.
(*    compare_place_name x clk_rise_left_ack.*)
    compare_place_name x clk_rise_right_req.
    compare_place_name x right_req_right_ack.
    compare_place_name x clock_fall.
(*    compare_place_name x clock_rise.*)
    compare_place_name x left_req_clk_rise.
    compare_place_name x right_ack_clk_rise.
    right. intros t1 t2 p; destruct p; auto.
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
    set (Hdisjoint := stage_places_disjoint_transitions l _ _ p).
    intro t_eq_p.
    contradict Hdisjoint.
    rewrite <- t_eq_p.
    apply token_name_domain.
  Qed.
  Next Obligation.
    set (Hdisjoint := scheme_all_disjoint l).
    destruct t; destruct t';
      try (find_contradiction; fail);
      try (decompose_set_structure; fail);
      try (simpl; intro; find_contradiction; fail).
  Qed.
  Next Obligation.
    eapply stage_places_all_disjoint; eauto.
  Qed.

  Definition stage_MG_SS : StateSpace name := MG_SS (stage_MG in_flag out_flag).

End TokenMG_to_SS.
Existing Instance stage_MG_scheme.
Arguments name_is_place_dec {name transition} MG {MG_naming_scheme}.
Arguments traces_of {name}.
End TokenMG_to_SS.



Module SS_to_TokenMG(Export XScheme : StageNamingScheme).
  Module StageMG := TokenMG_to_SS(XScheme).
  Export StageMG.
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
    destruct (name_is_place_dec (stage_MG in_flag out_flag) x)
      as [[t1 [t2 [p x_is_p]]] | x_not_p]; [ | exact (σR l x)].
    (* here, x = stage_place_name p, so the value should be the value in the initial marking *)
    exact (Num (init_marking (stage_MG in_flag out_flag) _ _ p)).
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



(*
(* Not true in general due to extra  assumptions *)
Lemma func_space_input_inversion : forall I o f σ x v σ',
    o ∉ I ->
    func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ I ->
    stable (func_space I o f) σ.
Proof.
  intros ? ? ? ? ? ? ? Hwf Hstep Hx.
  inversion Hstep; subst; auto.
  * (* x ∈ I  case *)
    apply func_stable_equiv; auto.
  * (* f σ = f (update σ x v ) *)
    unfold update in H4.
    admit (* not true??? *).
  * find_contradiction.
Abort.
  

  Lemma left_req_inversion : forall σ σ' v,
    latch_stage l ⊢ σ →{Some (Event (req (latch_input l)) v)} Some σ' ->
    stable (latch_clk_component l) σ 
    /\ v = neg_value (σ (req (latch_input l))).
  Proof.
    intros ? ? ? Hstep.
    set (Hdisjoint := scheme_all_disjoint l).
    assert (Hclk : latch_clk_component l ⊢ σ →{ Some (Event (req (latch_input l)) v)} Some σ').
    { unfold latch_stage in Hstep.
      apply hide_inversion in Hstep.
      apply hide_inversion in Hstep.
      apply hide_inversion in Hstep.
      unfold latch_stage_with_reset in Hstep.
      apply union_inversion_left in Hstep.
      2:{ unfold space_domain. simpl. solve_set. }
      apply union_inversion_left in Hstep.
      2:{ unfold space_domain. simpl. solve_set. }
      apply union_inversion_left in Hstep.    
     2:{ unfold space_domain. simpl. solve_set. }
      apply union_inversion_left in Hstep.    
      2:{ unfold space_domain. simpl. solve_set. }
      apply union_inversion_left in Hstep.    
      2:{ unfold space_domain. simpl. solve_set. }
      assumption.
    }

    inversion Hclk; subst.

    unfold latch_clk_component, clk_component.
    split.
    { apply func_stable_equiv. About func_stable_equiv.


     
    * set (HH := scheme_all_disjoint l).
      simpl.
      intro Hclk. decompose_set_structure.
    * admit.
    * admit (* needs work *).
  Admitted.
  Lemma right_ack_inversion : forall σ σ' v,
    latch_stage l ⊢ σ →{Some (Event (ack (latch_output l)) v)} Some σ' ->
    stable (latch_clk_component l) σ.
  Admitted.
  Lemma left_ack_inversion : forall σ σ' v,
    latch_stage l ⊢ σ →{Some (Event (ack (latch_input l)) v)} Some σ' ->
    ~ stable (latch_left_ack_component l) σ.
  Admitted.
  Lemma right_req_inversion : forall σ σ' v,
    latch_stage l ⊢ σ →{Some (Event (req (latch_output l)) v)} Some σ' ->
    σ (req (latch_output l)) <> σ (latch_state0 l).
  Admitted.
  Lemma clk_inversion : forall σ σ' v,
    latch_stage l ⊢ σ →{Some (Event (latch_clk l) v)} Some σ' ->
       σ (latch_clk l) = σ (latch_old_clk l)
    /\ ~ stable (latch_clk_component l) σ.
  Admitted.
*)


  (** If σ1 R{t} σ2, then the stage_relation_property will hold on σ1 and
  (state_to_marking σ2). The conclusion of each of these steps is that a certain
  place in the marked graph is marked. *)

  
  (*Lemma pipeline_env := *)
    (* Normal environment: NOT lack lreq ∥ forward rreq rack *)
    (* Timing constraint: wait for both lack AND rreq before enabling either lreq or rack *)
    (* Timing constraint: clk should fall BEFORE lreq changes, and clk should fall BEFORE rack changes 
       NOTE: why is this timing constraint necessary? *)

(*

  Record stage_relation_property (σ : state name) (m : marking (stage_MG in_flag out_flag)) :=
  { (* ENVIRONMENT constraints *)
    R_left_ack_left_req :
      σ (ack (latch_input l)) = σ (req (latch_input l)) ->
      m _ _ left_ack_left_req > 0
  ; R_right_req_right_ack :
      σ (req (latch_output l)) = σ (ack (latch_output l)) ->
      m _ _ right_req_right_ack > 0

    (* TIMING constraints *)
  ; R_clk_fall_left_req :
      (* the clock has fallen, and a new left request hasn't happened yet. *)
      σ (latch_clk l) = Bit0 ->
      σ (latch_state0 l) <> σ (req (latch_input l)) ->
      m _ _ clk_fall_left_req > 0
  ; R_clk_fall_right_ack :
      σ (latch_clk l) = Bit0 ->
      σ (latch_state0 l) <> σ (ack (latch_output l)) ->
      m _ _ clk_fall_right_ack > 0

  (* TIMING constraints *)
(*
  ; R_right_req_left_req :
    (* don't think this is correct/enough *)
      ~ stable (latch_right_req_component l) σ ->
      m _ _ right_req_left_req > 0
  ; R_left_ack_right_ack :
     (* don't think this is correct/enough *)
      ~ stable (latch_left_ack_component l) σ ->
      m _ _ left_ack_right_ack > 0
*)

  ; R_clk_rise_left_ack :
       ~ stable (latch_flop_component l) σ
    \/ ~ stable (latch_left_ack_component l) σ ->
      m _ _ clk_rise_left_ack > 0
  ; R_clk_rise_right_req :
       ~ stable (latch_flop_component l) σ 
    \/ ~ stable (latch_right_req_component l) σ ->
      m _ _ clk_rise_right_req > 0

  ; R_clk_fall :
       ~ stable (latch_flop_component l) σ
    \/ (σ (latch_clk l) = Bit1 /\ ~ stable (latch_clk_component l) σ) ->
      m _ _ clock_fall > 0

  ; R_left_req_clk_rise :
       (* a request has come in from the left, but clk+ has not yet occurred.  *)
       stable (latch_flop_component l) σ (* the flop is stable, so state0 is up-to-date *) ->
       stable (left_env_component l) σ (* a request has come in on the left *) ->
       (* either: (1) state0 has not yet propogated to rreq; (2) state0 has
       propogated to rreq but an acknowledgement has not yet come in on rack; or
       (3) state0 has propogated to rreq, acknowledgment has come in on rack,
       but the result has not yet propogated through to clk. *)
       (  ~ stable (latch_right_req_component l) σ
       \/ (stable (latch_right_req_component l) σ /\ ~ stable (right_env_component l) σ)
       \/ (stable (latch_right_req_component l) σ /\ stable (right_env_component l) σ
          /\ ~ stable (latch_clk_component l) σ)) ->
       m _ _ left_req_clk_rise > 0

  ; R_right_ack_clk_rise : 
       (* a request has come in from the right, but clk+ has not yet occurred.  *)
       stable (latch_flop_component l) σ (* the flop is stable, so state0 is up-to-date *) ->
       stable (right_env_component l) σ (* an acknowledgement has come in on the right *) ->
       (* either: (1) state0 has not yet propogated to lack; (2) state0 has
       propogated to lack but a request has not yet come in on lreq; or
       (3) state0 has propogated to lack, request has come in on lreq,
       but the result has not yet propogated through to clk. *)
       (  ~ stable (latch_left_ack_component l) σ
       \/ (stable (latch_left_ack_component l) σ /\ ~ stable (left_env_component l) σ)
       \/ (stable (latch_left_ack_component l) σ /\ stable (left_env_component l) σ
          /\ ~ stable (latch_clk_component l) σ)) ->
       m _ _ right_ack_clk_rise > 0

  }.
*)



(*  Context `{mg_scheme : MG_naming_scheme name _ (stage_MG in_flag out_flag)}.*)

  Definition transition_event (t : token_transition) (σ : state name) : event name value :=
    let x := @transition_name name _ (stage_MG in_flag out_flag) _ t in
    let v := @transition_update_value name _ (stage_MG in_flag out_flag) _ t (σ x) in
    Event x v.


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

  Lemma stage_internal_disjoint :
    space_internal (latch_stage_with_env l) ⊥ space_domain (stage_MG_SS l in_flag).
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    unfold space_domain. simpl.
    constructor. intros ?x.
    intro.
    deep_decompose_set_structure;
    simpl in *;
    try find_contradiction;
    try match goal with
    | [ H : token_transition_name _ ?t = _ |- _ ] =>
        destruct t; inversion H;
        simpl in *;
        find_contradiction;
        fail
    | [ H : _ = stage_place_name ?l ?p |- _ ] =>
      let Hdisjoint := fresh "Hdisjoint" in
      set (Hdisjoint := stage_places_disjoint_transitions l _ _ p);
      contradict Hdisjoint;
      rewrite <- H;
      unfold space_domain; solve_set;
      fail
    end.
  Qed.
  Lemma stage_MG_internal_disjoint :
    space_internal (stage_MG_SS l in_flag) ⊥ space_domain (latch_stage_with_env l).
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    unfold space_domain. simpl.
    constructor. intros ?x.
    intro.
    deep_decompose_set_structure;
    simpl in *;
    try find_contradiction;
    try (destruct l; simpl in *; find_contradiction; fail);
    try match goal with
    | [ H : token_transition_name _ ?t = _ |- _ ] =>
        destruct t; inversion H;
        simpl in *;
        find_contradiction;
        fail
    | [ H : _ = stage_place_name ?l ?p |- _ ] =>
      let Hdisjoint := fresh "Hdisjoint" in
      set (Hdisjoint := stage_places_disjoint_transitions l _ _ p);
      contradict Hdisjoint;
      rewrite <- H;
      unfold space_domain; solve_set;
      fail
    end.
  Qed.
End SS_to_TokenMG.

Hint Resolve stage_internal_disjoint stage_MG_internal_disjoint : click.
About init_stage_MG_state.


End SS_to_TokenMG.

Arguments well_formed {name}.

Module SS_to_TokenMG_Proof(Export XScheme : StageNamingScheme).
  Module SSMG := SS_to_TokenMG(XScheme).
  Export SSMG.
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
  Ltac reduce_name_is_stage_place_dec :=

      match goal with
      | [ |- context[ name_is_stage_place_dec ?l ?x ]] =>
        let t1 := fresh "t1" in
        let t2 := fresh "t2" in
        let p  := fresh "p"  in
        let Hp := fresh "Hp" in
        let Heq :=fresh "Heq" in
        match x with
        | stage_place_name _ ?p' =>
        (* first, we see if x is equal to a place *)
        destruct (name_is_stage_place_dec l x)
          as [[t1 [t2 [p Hp]]] | Hp];
          [ (* p = p' *)
            apply stage_places_all_disjoint in Hp;
            dependent destruction Hp
          | (* contradiction *)
            contradict Hp; intros Hp; eapply Hp; reflexivity ]
        | _ =>
        (* otherwise, we try to contradict the left *)
        destruct (name_is_stage_place_dec l x)
          as [[t1 [t2 [p Hp]]] | Hp];

        [ contradict Hp; simpl; intros Heq;
          contradiction (stage_places_disjoint_transitions l _ _ p);
          rewrite <- Heq;
          unfold space_domain; simpl; solve_set
        | auto ]
        end

        end.

Import ClickTactics. Search space_domain.
Lemma dom_latch_stage : space_domain (latch_stage l)
    == from_list [req (latch_input l); ack (latch_output l); ack (latch_input l); req (latch_output l); 
                  latch_clk l; latch_state0 l; latch_not_state0 l; latch_old_clk l; latch_hidden l;
                  ctrl_reset_n (odd:=odd); dp_reset_n (odd:=odd)].
Proof.
  set (Hdisjoint := scheme_all_disjoint l).

  intros. split; intros x Hx; unfold space_domain in *; simpl in *;
    decompose_set_structure; try solve_set;
    try (destruct l; simpl; solve_set).
Qed.


  Lemma stage_relate_trace_domain : forall σ1 t σ2,
    relate_trace name (latch_stage_with_env l) (stage_MG_SS l in_flag)
                      (σR l) (init_stage_MG_state l)
                      σ1 t σ2 ->
    forall x tr,
      x = @transition_name name _ (stage_MG in_flag out_flag) _ tr ->
      σ1 x = σ2 x.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).

    intros σ1 t σ2 Hrelate x tr Hx.
    subst.
    eapply (relate_trace_domain _ (latch_stage_with_env l)
                                  (stage_MG_SS l in_flag)
            (σR l) (init_stage_MG_state l)); eauto with click.
    2:{ apply stage_internal_disjoint. }
    2:{ apply stage_MG_internal_disjoint. }
    2:{ apply wf_MG_SS. }
    2:{ destruct tr; unfold space_domain; simpl; solve_set. }
    2:{ unfold space_domain. simpl.
        (* first check if tr ∈ input *)
        compare tr left_req.
        { left. left. econstructor; split; eauto; solve_set. }
        compare tr right_ack.
        { left. left. econstructor; split; eauto; solve_set. }
        (* otherwise, tr ∈ output *)
        left. right. econstructor; split; auto.
        solve_set.
    }

    intros x Hx1 Hx2.
    rewrite dom_latch_stage_with_env in Hx1.
    unfold space_domain in *. simpl in *.
    unfold init_stage_MG_state, σR; simpl.

    destruct (name_is_stage_place_dec l x) as [[t1 [t2 [p Hp]]] | ].
    2:{ repeat (compare_next; auto). }
    { (* contradiction of Hx1 *)
      contradiction (stage_places_disjoint_transitions l t1 t2 p).
      rewrite dom_latch_stage; rewrite <- Hp.
      repeat decompose_set_structure; solve_set.
    }

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


Lemma val_to_nat_dec : forall v, val_to_nat (dec_value v) = val_to_nat v - 1.
Proof. intros v; destruct v; auto. Qed.
Lemma val_to_nat_inc : forall v, v <> X -> val_to_nat (inc_value v) = val_to_nat v + 1.
Proof. intros v Hv; destruct v; auto. find_contradiction. Qed.

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
      unfold init_marking_flag, state_to_marking, init_stage_MG_state. simpl.
      destruct (name_is_stage_place_dec l (stage_place_name l p))
        as [[t1' [t2' [p' Hp']]] | Hp].
      + apply stage_places_all_disjoint with (f1 := in_flag) (f2 := out_flag) in Hp';
        dependent destruction Hp'.
        destruct l; simpl; auto.
      + specialize (Hp t1 t2 p); find_contradiction.

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
        unfold state_to_marking. unfold update.
        assert (@transition_name name _ (stage_MG in_flag out_flag) _ t'
             <> @place_name _ _ (stage_MG in_flag out_flag) _ t1 t2 p).
        { apply transition_place_name_disjoint. }
        reduce_eqb.
        unfold fire_in_state.
        simpl.
        destruct (name_is_stage_place_dec l (stage_place_name l p))
          as [[t1' [t2' [p' Hp]]] | Hp].
        2:{ specialize (Hp _ _ p); find_contradiction. }

         apply stage_places_all_disjoint with (f1 := in_flag) (f2 := out_flag) in Hp.
         dependent destruction Hp.
            

           repeat compare_next; auto.
           { rewrite val_to_nat_dec; auto. }
           { rewrite val_to_nat_inc; auto.
             eapply relate_trace_project_right in Hrelate.
             unfold stage_MG_SS in Hrelate.
             apply MG_SS_val_not_X with (p := p) in Hrelate.
             { apply Hrelate. }
             { simpl. unfold init_stage_MG_state. simpl.
               destruct (name_is_stage_place_dec l (stage_place_name l p))
                 as [[t1' [t2' [p' Hp']]] | Hneq'].
               2:{ specialize (Hneq' _ _ p); find_contradiction. }
               inversion 1.
             }
           }
        }
  Qed.

  Lemma left_req_val_inversion : forall σ v σ',
    latch_stage_with_env l ⊢ σ →{Some (Event (req (latch_input l)) v)} Some σ' ->
    v = neg_value (σ (ack (latch_input l))).
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros ? ? ? Hstep.
      set (Hstep' := Hstep).
      apply union_inversion_left in Hstep'.
      2:{ unfold space_domain. simpl. solve_set. }
      apply union_inversion_left in Hstep'.
      2:{ unfold space_domain. simpl. solve_set. }
      unfold left_env_component, NOT in Hstep'.
      apply func_space_output_inversion in Hstep'; auto.
      { solve_set. }
  Qed.



Lemma eps_from_σR : forall σ,
      latch_stage_with_env l ⊢ σR l →*{t_empty} Some σ ->
      forall x, x ∈ space_output (latch_stage_with_env l) ->
      σ x = σR l x.
Proof.
  intros σ Hstep x Hx.
  assert (wf : well_formed (latch_stage_with_env l)).
  { Search well_formed latch_stage_with_env.
    apply latch_stage_well_formed.
  }
  dependent induction Hstep; subst; auto.
  erewrite wf_scoped; [ | | eauto | intro; inversion 1 |]; auto.

  { destruct wf. intro Hinternal.
    destruct space_output_internal as [space_output_internal].
    apply (space_output_internal x). solve_set.
  }
Qed.

Print stage_place.


  (************************** TODO ********************************)

  (** Intuitively, [prop_marked p σ] is a property that holds on a state σ
  whenever a related marking m satisfies [m(p) > 0]. *)
  Inductive prop_marked : forall {t1 t2} (p : stage_place t1 t2) (σ : state name), Prop :=

  | lack_lreq_marked σ :
    σ (ack (latch_input l)) = σ (req (latch_input l)) -> prop_marked left_ack_left_req σ

  | rreq_rack_marked σ :
    σ (req (latch_output l)) = neg_value (σ (ack (latch_output l))) ->
    prop_marked right_req_right_ack σ (* right_req -> right_ack *)

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


  | clk_rise_right_req_marked σ :
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit0 ->
    prop_marked clk_rise_right_req σ

  | clk_rise_right_req_marked_state0 σ :
    σ (req (latch_output l)) <> σ (latch_state0 l) ->
    prop_marked clk_rise_right_req σ

  .

Import ClickTactics.

      
Lemma val_is_bit_neq_neg : forall v1 v2,
    val_is_bit v1 \/ val_is_bit v2 ->
    neg_value v1 = v2 ->
    v1 <> v2.
Proof.
  intros v1 v2 [H | H] Heq; inversion H; subst; try (inversion 1; fail);
    destruct v1 as [[|[|n]]|]; try find_contradiction.
Qed.



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
      step_inversion_eq.
      simpl in Hstep. Search neg_value val_is_bit.
      rewrite <- val_is_bit_neg_neg; [ | solve_val_is_bit].
      rewrite Hstep.
      rewrite val_is_bit_neg_neg; [ | solve_val_is_bit].
      auto.
    }

    { (* clk_fall_left_ack *)
      assert (Hstep' : latch_left_ack_component l ⊢ σ →{Some (transition_event l left_ack σ)} Some σ').
      { do 9 step_inversion_1. auto. }
      clear Hstep.
      Print delay_space. Print delay_space_step.
      inversion Hstep'.
      { (* contradiction *) subst. contradict H3. simpl. solve_set. }
      subst. clear H4.

      apply clk_fall_left_ack_marked; auto.

      step_inversion_eq.
      apply eq_sym in H2.
      apply val_is_bit_neg_inversion in H2; [ | solve_val_is_bit].
      rewrite <- H2.
      destruct l; simpl; auto; rewrite val_is_bit_neg_neg; [auto| solve_val_is_bit].
    }

    { (* clk_rise_right_req *) 
      replace (transition_event l right_req σ)
        with  (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
        in    Hstep
        by    auto.
      apply clk_rise_right_req_marked_state0.
      assert (Hstate0 : σ' (latch_state0 l) = σ (latch_state0 l))
        by (step_inversion_neq; auto).
      assert (Hreq : σ' (req (latch_output l)) = neg_value (σ (req (latch_output l))))
        by (rewrite_step_inversion; auto).

      assert (Hstable : ~ stable (latch_right_req_component l) σ).
      { repeat step_inversion_1.
        intros [_ Hstable].
        specialize (Hstable _ _ Hstep).
        inversion Hstable; subst. contradict pf. solve_set.
      }
      intros Heq.
      contradict Hstable.
        Search stable func_space.
      apply func_stable_equiv; auto. solve_set.
   }

   { (* right_req_right_ack *)
      constructor.
      step_inversion_eq.
      simpl in Hstep. auto.
   }
  Admitted.

  (* Helper lemmas for relate_implies_marked below *)
  Lemma relate_implies_marked_eps : forall σ σ',
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p σ' ->
    prop_marked p σ.
  Admitted.

  Lemma flop_not_stable : forall σ,
(*    σ (latch_clk l) = Bit0 ->*)
    wf_stage_state l σ ->
    σ (latch_state0 l) <> σ (latch_not_state0 l) ->
    σ (latch_clk l) <> σ (latch_old_clk l) ->
    ~ stable (latch_flop_component l) σ.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ Hwf Hstate0 Hold.
    assert (Hclk : val_is_bit (σ (latch_clk l))) by solve_val_is_bit.
    inversion Hclk as [H0 | H1].
    {
      assert (Hstep' : exists τ, latch_flop_component l ⊢ σ →{None} τ).
      { eexists. Print hide_step.
        apply Hide_Neq; [ | inversion 1].
        apply Hide_Neq; [ | inversion 1].
        Print union_step.
        apply union_step_1; [ inversion 1 | |].
        apply union_step_1; [ inversion 1 | |].
        apply Flop_clk_fall; auto.
        { rewrite <- H0; inversion 1. }
        { intros x Hx. unfold space_domain in *; simpl in *.
          unfold update. compare_next; auto. contradict Hx; solve_set. }
        { intros x Hx. unfold space_domain in *; simpl in *.
          unfold update. compare_next; auto. contradict Hx; solve_set. }
      }
      destruct Hstep' as [τ Hstep'].
      intros [_ Hstable].
      specialize (Hstable None τ Hstep').
      contradict Hstable. inversion 1.
    }
    { assert (σ (@dp_reset_n even odd _) = Bit1).
      { Print wf_stage_state. eapply wf_dp_reset_n; eauto. }
      assert (σ (latch_hidden l) = Bit1).
      { apply wf_hidden; auto. }

      assert (Hstep' : exists τ,
        latch_flop_component l ⊢ σ →{Some (Event (latch_state0 l) (neg_value (σ (latch_state0 l))))}
                                      τ).
      { eexists.
        apply Hide_Neq. 2:{ inversion 1; subst. contradict pf; solve_set. }
        apply Hide_Neq. 2:{ inversion 1; subst. contradict pf; solve_set. }
        apply union_step_1. 1:{ inversion 1; subst. contradict pf. unfold space_domain; solve_set. }
        apply union_communicate.
        { apply driven_by_1; constructor; solve_set. }
        2:{ apply func_input_stable; [solve_set | | ].
            Search neg_value. symmetry.
            apply val_is_bit_neq; auto; try solve_val_is_bit.
            intro. shelve.
        }
        
        { apply Flop_clk_rise; [ destruct l; simpl; auto
                               | destruct l; simpl; auto
                               | auto
                               | auto
                               | |].
          { intros Heq. rewrite Heq in Hold.
            apply Hold. auto.
          }
          { apply val_is_bit_neq; auto; solve_val_is_bit. }
        }
        { intros x Hx. unfold space_domain in Hx; simpl in Hx.
          decompose_set_structure.
          unfold update. repeat compare_next; auto.
        }
    Unshelve.
        { unfold update. 
          compare_next. compare_next; auto.
repeat compare_next; auto.


          { unfold update. apply functional_extensionality; intros x.
            compare_next; auto. compare_next; auto.
            compare_next.
            (* clk = 1, old_clk = 0, state0 = 1


Print wf_stage_state.
            2:{ (* TODO: add wf_dp_reset_n *) admit. }
            { (* latch_hidden *)

            compare (σ (latch_not_state0 l))
                    (σ (latch_state0 l)).

            { About func_input_unstable. apply func_input_unstable; [solve_set | | |].
              { rewrite Heq.
                inversion Hstate0; inversion 1. }
              { unfold update. reduce_eqb.

              symmetry.
              apply val_is_bit_neq.



Print func_step.

            apply func_input_stable; [ solve_set | |shelve].
            { (* if they are equal, then FLOP is not stable *)
  Qed.



  Lemma outgoing_place_not_marked : forall σ σ' t,
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some (transition_event l t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t),
        ~ prop_marked p σ'.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ σ' t Hwf Hstep t0 p Hprop.
Print prop_marked.
    dependent destruction Hprop.
    * (* t = left_req *)
      assert (Hreq : σ0 (req (latch_input l)) = neg_value (σ (req (latch_input l)))).
      { eapply wf_update; [ | eauto]. auto.
      }
      assert (Hack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
      { eapply wf_scoped; [ | eauto | |]; auto.
        { intro v; inversion 1; subst. rewrite H2 in Hdisjoint. find_contradiction. }
        { simpl; solve_set. }
      }
      step_inversion_eq.
      contradict Hstep. simpl.
      assert (Hreq' : val_is_bit (σ (req (latch_input l)))) by solve_val_is_bit.

      rewrite <- Hreq, <- Hack, H.

      inversion Hreq'; my_subst; simpl; simpl in Hreq; clear Hreq';
        rewrite Hreq; discriminate.

    * (* t = right_ack *)
      assert (Hreq : σ0 (req (latch_output l)) = σ (req (latch_output l))).
      { eapply wf_scoped; [ | eauto | |]; auto.
        { intro v; inversion 1; subst. rewrite H2 in Hdisjoint. find_contradiction. }
        { simpl; solve_set. }
      }
      assert (Hack : σ0 (ack (latch_output l)) = neg_value (σ (ack (latch_output l)))).
      { eapply wf_update; [ | eauto]. auto. }
      step_inversion_eq. simpl in Hstep. contradict Hstep.

      rewrite <- Hreq, <- Hack, H.

      assert (Hack' : val_is_bit (σ (ack (latch_output l)))) by solve_val_is_bit.
      inversion Hack'; my_subst; simpl; simpl in Hack;
        rewrite Hack; discriminate.

    * (* t = left_ack (1) *)

      assert (Hack : σ0 (ack (latch_input l)) = neg_value (σ (ack (latch_input l)))).
      { replace (transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.
        rewrite_step_inversion; auto.
      }
      assert (Hreq : σ0 (req (latch_input l)) = σ (req (latch_input l))).
      { replace (transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.
        rewrite_step_inversion; auto.
      }
      assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
      { replace (transition_event l left_ack σ)
          with (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))
          in Hstep
          by auto.
        step_inversion_neq; auto.
      }
    
      step_inversion_eq. simpl in Hstep. contradict Hstep.
      rewrite <- Hack, <- Hstate0, H0.

      assert (Hbit : val_is_bit (σ0 (latch_state0 l))) by (rewrite Hstate0; solve_val_is_bit).

      (* contradiction *) destruct l; simpl; intro Heq; inversion Hbit; my_subst; inversion Heq.

   * (* t = left_ack (2) *)

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
      assert (Hstate0 : σ0 (latch_state0 l) = σ (latch_state0 l)).
      { step_inversion_neq; auto.
      }
      assert (Hclk' : σ0 (latch_old_clk l) = σ (latch_old_clk l)).
      { step_inversion_neq; auto. }
      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { step_inversion_neq; auto. }

      assert (Hstable : ~ stable (latch_left_ack_component l) σ).
      { intros [_ Hstable]. (* if it were, then it would not have taken a step *)
        assert (Hstep' : latch_left_ack_component l ⊢ σ 
                →{Some (Event (ack (latch_input l)) (neg_value (σ (ack (latch_input l)))))}
                Some σ0).
        { do 9 step_inversion_1; auto. }
        specialize (Hstable _ _ Hstep').
        inversion Hstable; subst. contradict pf. solve_set.
      }

      apply (wf_left_ack_stable Hwf) in Hstable.
      destruct Hstable as [H_clk_stable H_flop_stable].

      contradict H_flop_stable.
      apply flop_not_stable.
      { rewrite <- Hclk; auto. }
      { rewrite <- Hclk, <- Hclk'.
        rewrite H, H0.
        inversion 1.
      }

  * (* t = right_req (1) *)
    replace (transition_event l right_req σ)
          with (Event (req (latch_output l)) (neg_value (σ (req (latch_output l)))))
          in Hstep
          by auto.
    replace (σ0 (latch_clk l)) with (σ (latch_clk l)) in *
      by (step_inversion_neq; auto).
    replace (σ0 (latch_old_clk l)) with (σ (latch_old_clk l)) in *
      by (step_inversion_neq; auto).
    assert (~ stable (latch_flop_component l) σ).
    { Search stable latch_flop_component.
      
    step_inversion_eq.

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
      erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto.
      3:{ simpl. solve_set. }
      2:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }
      erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto.
      2:{ simpl. solve_set. }
      1:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }

    * constructor.
      erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto.
      3:{ simpl. solve_set. }
      2:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }
      erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto.
      2:{ simpl. solve_set. }
      1:{ intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
      }

    * Print prop_marked.
      compare t clk_rise.
      { (* if the clk+ event happens, contradiction iwth (σ (latch_clk l) = Bit0) *)
        contradict H.
        replace (transition_event l clk_rise σ) with (Event (latch_clk l) Bit1) in Hstep
          by auto.
        rewrite_step_inversion. inversion 1.
      }

      assert (Hclk : σ0 (latch_clk l) = σ (latch_clk l)).
      { erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto;
          [ | solve_set].
        { intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
        }
      }
      assert (Hstate0: σ0 (latch_state0 l) = σ (latch_state0 l)).
      { Print wf_scoped.
        destruct t; try find_contradiction;
          (repeat step_inversion_1;
            erewrite <- wf_scoped with (σ := σ) (σ' := σ0);
              [reflexivity | | apply Hstep | | ]; [solve_wf | | solve_set];
            intros v; inversion 1; find_contradiction).
      }

      assert (Hack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
      { erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto;
          [ | solve_set].
        { intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
        }
      }

      compare (σ (latch_clk l)) (σ (latch_old_clk l)).
      2:{ (* if these are not equal, then flop_component is not stable. *)
          assert (~ stable (latch_flop_component l) σ).
          { apply flop_not_stable; auto.
            rewrite <- Hclk; auto.
          }

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
      { erewrite <- (wf_scoped _ _ (latch_stage_well_formed l) σ _ σ0); eauto;
          [ | solve_set].
        { intros v.
          destruct t; auto; unfold transition_event; simpl; inversion 1; find_contradiction.
        }
      }
      assert (Hold_clk : σ0 (latch_old_clk l) = σ (latch_old_clk l)).
      { destruct t; try find_contradiction;
          (repeat step_inversion_1;
            erewrite <- wf_scoped with (σ := σ) (σ' := σ0);
              [reflexivity | | apply Hstep | | ]; [solve_wf | | solve_set];
            intros v; inversion 1; find_contradiction).
      }

      apply clk_fall_left_ack_state0_marked.
      { rewrite <- Hclk; auto. }
      { rewrite <- Hold_clk. auto. }

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
Print state_relate_marking.
    induction Hrelate as [ | ? ? ? ? ? Hrelate IH Hstep Henabled Hm'
                           | ? ? ? Hrelate IH Hstep]; intros t1 t2 p Hp.
    * apply init_relate_implies_marked; auto.
    * unfold is_enabled in Henabled.
      rewrite Hm'.
      unfold fire.
      compare_next.
      { inversion p; subst; find_contradiction. }
      compare_next.
      { (* t = t2 *) contradict Hp.
        eapply outgoing_place_not_marked; eauto.
        apply state_relate_marking_steps in Hrelate.
        destruct Hrelate as [tr Hsteps].
        eapply step_wf_state; eauto.
      }
      compare_next.
      { omega. }
      { apply IH.
        eapply disjoint_place_marked; eauto.
      }
    * apply IH.
      eapply relate_implies_marked_eps; eauto.
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
  Admitted.


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


Import ClickTactics.

  (* How to prove this? Maybe build on prop_marked?? *)
  (* Note: this is not enough to distinguish CLK+ from CLK- *)
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
    destruct t'; simpl; intros Hx;
     try (exists t; subst; step_inversion_unstable; simpl;
          erewrite val_is_bit_neq; eauto; solve_val_is_bit).
    - (* clk_rise *)
      inversion Hv; subst; [exists clk_fall | exists clk_rise]; auto.

    - (* clk_fall *)
      inversion Hv; subst; [exists clk_fall | exists clk_rise]; auto.
  Qed.




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
      rewrite latch_stage_input in Hx.
      rewrite latch_stage_output in Hx.
      decompose_set_structure.
      + exists left_req; split; [ reflexivity | ].
        step_inversion_unstable. try solve_bit_neq_neg. 
      + exists right_ack; split; [ reflexivity | ].
        step_inversion_unstable. solve_bit_neq_neg.
      + exists left_ack; split; [ reflexivity | ].
        step_inversion_unstable. solve_bit_neq_neg.
      + exists right_req; split; [ reflexivity | ].
        step_inversion_unstable. solve_bit_neq_neg.
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
  Qed.

  Lemma place_name_disjoint_SS : forall t1 t2 (p : place (stage_MG in_flag out_flag) t1 t2),
    place_name p ∉ space_domain (latch_stage_with_env l).
  Proof.
    intros.
    rewrite dom_latch_stage_with_env.
    apply stage_places_disjoint_transitions.
  Qed.

  Theorem MG_refines_stage :
    traces_of (latch_stage_with_env l) (σR l) ⊆ traces_of (stage_MG_SS l in_flag) (init_stage_MG_state l).
  Proof.
    Search relate_trace_step_lemma.
    apply relate_trace_step_subset.
    { intros x Hdom1 Hdom2.
      unfold init_stage_MG_state. fold in_flag. fold out_flag.
      destruct (name_is_place_dec (stage_MG in_flag out_flag) x)
        as [[t1 [t2 [p Hplace]]] | Htransition].
      + subst.
        contradict Hdom1.
        apply place_name_disjoint_SS.
      + reflexivity.
    }
    { apply MG_relate_trace_step_lemma. }
  Qed.



(*
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
*)

  End SS_to_TokenMG_Proof.
  End SS_to_TokenMG_Proof.


End ClickMG.
