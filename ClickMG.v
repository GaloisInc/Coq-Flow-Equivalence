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
  (* ENVIRONMENT constraint: we expect handshakes to obey a 2-phase handshake
     protocol, so we don't expect an input on left_req until left_ack has been
     updated by the controller. *)
  | left_ack_left_req : stage_place left_ack left_req
  (* TIMING constraint: changes inside the controller propogate faster than
     communication between controllers. In the controller, if this is not
     respected, it will lead to an error state as the clock component will not
     be stable when the new inputs arrive. *)
  (* NOTE: really, this should perhaps be that CLK- must occur before BOTH
     left_req and right_ack inputs change, not just either one... Since this
     can't be encoded simply as a marked graph, perhaps it needs to be encoded
     into the environment of latch_stage? *)
  | clk_fall_left_req : stage_place clk_fall left_req
  (* TIMING constraint: changes inside the controller propogate faster than
     communication between controllers. In other words, wait for state0 to be
     propogated to both left_ack AND right_req before accepting input on
     left_req. *)
(*  | right_req_left_req : stage_place right_req left_req *)

  (* CLK+ -> L.ack *)
  | clk_rise_left_ack : stage_place clk_rise left_ack
  
  (* CLK+ -> R.req *)
  | clk_rise_right_req : stage_place clk_rise right_req

  (* R.req -> R.ack *)
  (* ENVIRONMENT constraint: we expect handshakes to obey a 2-phase handshake
     protocol, so we don't expect an input on right_ack until right_req has been
     updated by the controller  *)
  | right_req_right_ack : stage_place right_req right_ack
  
  (* CLK- -> R.ack *)
  (* L.ack -> R.ack *)
  (* TIMING constraint: See the note on clk_fall_left_req. *)
  | clk_fall_right_ack : stage_place clk_fall right_ack
  (* TIMING constraint: See the note on right_req_left_req. *)
(*  | left_ack_right_ack : stage_place left_ack right_ack *)

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
(*                                      | right_req_left_req  => 1*)
                                      | clk_fall_left_req   => 1
                                      | left_ack_left_req   => 1
                                      | right_req_right_ack => 1
                                      | clk_fall_right_ack  => 1
(*                                      | left_ack_right_ack  => 1*)
                                      | _ => 0
                                      end
    (* Token with left token stage *)
    | Token, Token    => fun t1 t2 p => match p with
                                      | left_req_clk_rise => 1
                                      | right_req_right_ack => 1
                                      | clk_fall_right_ack  => 1
(*                                      | left_ack_right_ack  => 1*)
                                      | _ => 0
                                      end
    | NonToken, NonToken => fun t1 t2 p => match p with
(*                                      | right_req_left_req  => 1*)
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
Arguments MG_SS {name name_dec transition transition_dec} MG {MG_scheme}.

Section TokenMG_to_SS.

  Variable even odd : Set.

  Class stage_naming_scheme `{scheme : naming_scheme name even odd} :=
    { stage_place_name : forall (l : latch even odd) {t1 t2 : token_transition}, stage_place t1 t2 -> name
    ; stage_places_disjoint_transitions : forall l t1 t2 (p : stage_place t1 t2),
      stage_place_name l p ∉ space_domain (latch_stage l)
    ; stage_places_all_disjoint : forall l {t1 t2 t1' t2' : token_transition} (p : stage_place t1 t2) (p' : stage_place t1' t2'),
      stage_place_name l p <> stage_place_name l p'
    }.



  Variable l : latch even odd.
  Variable in_flag : token_flag.
  Let out_flag := latch_to_token_flag l.
  Context `{x_scheme : stage_naming_scheme}.



  Definition name_is_stage_place_dec : forall x,
                           {t1 : token_transition &
                           {t2 : token_transition & {p : stage_place t1 t2 & x = stage_place_name l p}}}
                        + {forall t1 t2 (p : stage_place t1 t2), x <> stage_place_name l p}.
  Proof.
    intros x.

    Ltac compare_place_name x p :=
      compare x (stage_place_name l p);
        [ left; do 3 eexists; reflexivity | ].
    compare_place_name x left_ack_left_req.
    compare_place_name x clk_fall_left_req.
(*    compare_place_name x right_req_left_req.*)
    compare_place_name x clk_rise_left_ack.
    compare_place_name x clk_rise_right_req.
    compare_place_name x right_req_right_ack.
    compare_place_name x clk_fall_right_ack.
(*    compare_place_name x left_ack_right_ack.*)
    compare_place_name x clock_fall.
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
   ; place_name := @stage_place_name _ _ _
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

  Definition stage_MG_SS : StateSpace name := MG_SS (stage_MG in_flag out_flag).

End TokenMG_to_SS.

Arguments name_is_place_dec {name transition} MG {MG_naming_scheme}.
Existing Instance stage_MG_scheme.
About stage_MG_scheme.
Arguments traces_of {name}.
About stage_MG_SS.
Arguments stage_MG_SS {even odd} l f {scheme x_scheme} : rename.

Section SS_to_TokenMG.

  Variable even odd : Set.
(*  Context `{scheme : naming_scheme name even odd}.*)
  Context `{x_scheme : stage_naming_scheme even odd}.


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

  Definition left_env_component (l : latch even odd) :=
    NOT (ack (latch_input l)) (req (latch_input l)).
  Definition right_env_component (l : latch even odd) :=
    forward (req (latch_output l)) (ack (latch_output l)).


(*  any click circuit with output ho, input handshake hi:
    C ⊆ left_env_component ho ∥ right_env_component hi 

   l -> l'
   l -> l''

   latch_stage l = state space with clock l
   stageMG l = marked graph (as a state space)

    hide l''_in ((stageMG l ∥ fanout l_out l'_in l''_in) ∥ stageMG l')
    ⊆ stageMG l [l_out ↦ l'_in] ∥ stageMG l'

    if t ∈ hide everything else except local clocks (C ∥ latch_stage l ∥ latch_stage l')

    fanout h h1 h2 ⊆ h ↔ h1 ∥ h ↔ h2
    then t ∈ (left_env_component ∥ latch_stage l ∥ lout ↔ lin ∥ latch_stage l' ∥ right_env_component)
    modulo hiding

    and we are proving therefore t ∈ rise_decoupled
*)
  Definition latch_stage_with_env l := left_env_component l ∥ latch_stage l ∥ right_env_component l.

  Lemma latch_stage_with_env_input : forall l,
    space_input (latch_stage_with_env l) == ∅.
  Proof.
    intros l'. split.
    2:{ intros x Hx; inversion Hx. } Print naming_scheme.
    set (Hdisjoint := scheme_all_disjoint l').
    intros x Hx. simpl in Hx. decompose_set_structure. 
    destruct l'; simpl in *; decompose_set_structure; find_contradiction.
    destruct l'; simpl in *; decompose_set_structure; find_contradiction.
  Qed.
  Lemma latch_stage_with_env_output : forall l,
    space_output (latch_stage_with_env l) == space_input (latch_stage l) ∪ space_output (latch_stage l).
  Proof.
    intros l'.
    set (Hdisjoint := scheme_all_disjoint l').
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
  Qed.
  Lemma latch_stage_with_env_internal : forall l,
    space_internal (latch_stage_with_env l) == space_internal (latch_stage l).
  Proof.
    intros l'.
    set (Hdisjoint := scheme_all_disjoint l').
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
  Qed.
  Lemma dom_latch_stage_with_env : forall l,
    space_domain (latch_stage_with_env l) == space_domain (latch_stage l).
  Proof.
    intros l'.
    unfold space_domain.
    rewrite latch_stage_with_env_input.
    rewrite latch_stage_with_env_output.
    rewrite latch_stage_with_env_internal.
    (* monoid *)
    admit.
  Admitted.


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


Lemma union_inversion_left : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S1 ->
    S1 ⊢ σ →{Some (Event x v)} Some σ'.
Proof.
  intros ? ? ? ? ? ? Hstep Hdom.
  inversion Hstep; subst; auto.
  (* the only remaining case is when x ∉ dom(S1), a contradiction *)
  { contradict H0. constructor. auto. }
Qed.

Lemma union_inversion_right : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S2 ->
    S2 ⊢ σ →{Some (Event x v)} Some σ'.
Proof.
  intros ? ? ? ? ? ? Hstep Hdom.
  inversion Hstep; subst; auto.
  (* the only remaining case is when x ∉ dom(S2), a contradiction *)
  { contradict H0. constructor. auto. }
Qed.

Lemma hide_inversion : forall (S : StateSpace name) σ x e σ',
    (hide x S) ⊢ σ →{Some e} Some σ' ->
    S ⊢ σ →{Some e} Some σ'.
Proof.
  intros ? ? ? ? ? Hstep.
  inversion Hstep; auto.
Qed.

Lemma func_space_output_inversion : forall I (o : name) f (σ : state name) x v σ',
    o ∉ I ->
    func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
    x = o ->
    v = f σ.
Proof.
  intros ? ? ? ? ? ? ? Ho Hstep ?. subst.
    inversion Hstep; try find_contradiction.
    subst. auto.
Qed.

Lemma func_space_output_unstable : forall I (o : name) f σ x v σ',
    o ∉ I ->
    func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
    x = o ->
    σ x <> v.
Proof.
    intros ? ? ? ? ? ? ? ? Hstep Heq.
    subst.
    inversion Hstep; subst; try find_contradiction; auto.
Qed.

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
Print stage_place.

  
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
  Existing Instance stage_MG_scheme.

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

  Lemma stage_relate_trace_domain : forall σ1 t σ2,
    relate_trace name (latch_stage_with_env l) (stage_MG_SS l in_flag)
                      (σR l) init_stage_MG_state
                      σ1 t σ2 ->
    forall x tr,
      x = @transition_name name _ (stage_MG in_flag out_flag) _ tr ->
      σ1 x = σ2 x.
  Proof.
    intros σ1 t σ2 Hrelate x tr Hx.
    eapply relate_trace_domain; [ auto | | eauto | | ].
    * intros y HSS HMG.
      unfold init_stage_MG_state.
      destruct (name_is_place_dec (stage_MG in_flag out_flag) y)
        as [[t1 [t2 [p Hp]]] | ]; auto.
      { (* contradiction *)
        subst.
        contradict HSS.
        rewrite dom_latch_stage_with_env.
        apply stage_places_disjoint_transitions.
      }      

    * rewrite dom_latch_stage_with_env. 
      unfold space_domain.
      rewrite latch_stage_output, latch_stage_input.
      destruct tr; subst; simpl; solve_set.


    * unfold space_domain.
      left. subst.
      destruct tr;
      try (right; eexists; split; [ | reflexivity];
           simpl; intro; decompose_set_structure; fail);
      try (left; eexists; split; [ | reflexivity]; simpl; solve_set).
  Qed.


  Lemma state_relate_marking_implies : forall σ t σ',
    relate_trace name (latch_stage_with_env l) (stage_MG_SS l in_flag)
                      (σR l) init_stage_MG_state
                      σ t σ' ->
    state_relate_marking σ (state_to_marking σ').
  Proof.
    intros σ t σ' Hrelate.
    induction Hrelate.
    * replace (state_to_marking init_stage_MG_state)
        with  (init_marking (stage_MG in_flag out_flag))
        by    admit.
      apply R_init.
    * eapply R_Eps; eauto.
    * inversion H0.
    * inversion H1.

        replace e with (transition_event t0 σ1) in *.
          2:{ subst. unfold transition_event.
              f_equal. f_equal.
              eapply stage_relate_trace_domain; eauto.
              }
          subst.


      eapply R_step; eauto. 
      { intros t1 t2 p. 
        simpl. unfold fire, state_to_marking. simpl.
        unfold update.
        set (Hp := stage_places_disjoint_transitions _ _ l _ _ p).
        
        compare (token_transition_name _ _ l t0)
                (stage_place_name _ _ l p).
        { (* contradiction *) contradict Hp.
          rewrite <- Heq. constructor.
          rewrite latch_stage_input, latch_stage_output.
          destruct t0; simpl; solve_set.
        }
        unfold fire_in_state.
        destruct (name_is_place_dec (stage_MG in_flag (latch_to_token_flag l))
                                      (stage_place_name even odd l p))
            as [[t1' [t2' [p' Hp']]] | Hdec].
        2:{ (* contradiction *)
             specialize (Hdec _ _ p).
             simpl in Hdec. find_contradiction.
        }
        simpl in *.
        (* stage_place_name should be injective, not currently enforced *)
        replace t1' with t1 in * by admit.
        replace t2' with t2 in * by admit.
        (*replace p' with p in * by admit.*)
        compare_next; auto.
        compare_next; auto.
        { unfold dec_value.
          unfold val_to_nat.
          destruct (σ2 (stage_place_name even odd l p)); auto.
          admit (* mismatch here, maybe difference between Bit0 and Num 0?? *).
        }
        compare_next; auto.
        { unfold inc_value.
          unfold val_to_nat.
          destruct (σ2 (stage_place_name even odd l p)); auto.
          admit (* mismatch here, maybe difference between Bit0 and Num 0?? *).
          admit (* mismatch here, maybe difference between Bit0 and Num 0?? *).
          admit (* mismatch here, maybe difference between Bit0 and Num 0?? *).
        }
  Admitted.

About left_env_component.

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

(*
  Lemma left_input_0_1 : forall σ t,
    latch_stage_with_env l ⊢ σR l →*{t} Some σ ->
       σ (ack (latch_input l)) = σ (req (latch_input l))
    \/ σ (ack (latch_input l)) = neg_value (σ (req (latch_input l))).
  Proof.
    intros σ t Hsteps.
    dependent induction Hsteps.
    * unfold σR. repeat compare_next; auto;
        destruct l; auto.
    * specialize (IHHsteps _ _ _ _ _ eq_refl eq_refl eq_refl).
      destruct IHHsteps as [IH | IH].
      + destruct e as [x v].
        compare x (ack (latch_input l)).
Print well_formed.
        assert (σ (ack (latch_input l)) = v).
        { eapply wf_update; eauto. admit (* true *). }
        erewrite left_req_val_inversion in H2. eauto.
        apply func_space_output_inversion in H0.
  Qed.
*)



  Arguments well_formed {name}.

    
Lemma in_dec_union : forall A (X Y : Ensemble A), in_dec X -> in_dec Y -> in_dec (X ∪ Y).
Admitted.
Lemma in_dec_intersect : forall A (X Y : Ensemble A), in_dec X -> in_dec Y -> in_dec (X ∩ Y).
Admitted.
Lemma in_dec_setminus : forall A (X Y : Ensemble A), in_dec X -> in_dec Y -> in_dec (X ∖ Y).
Admitted.
Lemma in_dec_empty : forall A, in_dec (Empty_set A).
Admitted.
Hint Resolve in_dec_union in_dec_intersect in_dec_setminus in_dec_singleton in_dec_empty : sets.


  Lemma latch_stage_well_formed : well_formed (latch_stage_with_env l).
  Proof.
    Print naming_scheme.
    set (Hdisjoint := scheme_all_disjoint l).
    unfold latch_stage_with_env, left_env_component, right_env_component, latch_stage,
           latch_stage_with_reset, latch_flop_component.
    repeat match goal with
    | [ |- well_formed _] => apply wf_union; auto; try unfold space_domain
    | [ |- well_formed _ ] => apply hide_wf; auto; simpl; try solve_set
    | [ |- well_formed _ ] => apply func_wf; solve_set
    | [ |- in_dec _ ] => simpl; auto 30 with sets; fail
    | [ |- _ ⊥ _ ] => constructor; intros x Hx; simpl in *; decompose_set_structure; fail
    end.

    apply flop_wf.
    destruct l; simpl; repeat (constructor; try_solve_set).

  Qed.
  Hint Resolve latch_stage_well_formed.
  


Lemma eps_from_σR : forall σ,
      latch_stage_with_env l ⊢ σR l →*{t_empty} Some σ ->
      forall x, x ∈ space_output (latch_stage_with_env l) ->
      σ x = σR l x.
Proof.
  intros σ Hstep x Hx.
  assert (wf : well_formed (latch_stage_with_env l)) by auto.
  dependent induction Hstep; subst; auto.
  erewrite wf_scoped; [ | | eauto | intro; inversion 1 |]; auto.
  { destruct wf. intro Hinternal.
    destruct space_output_internal as [space_output_internal].
    apply (space_output_internal x). solve_set.
  }
Qed.

(*
  Lemma step_implies_event_step : forall t σ x v σ',
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    x = @transition_name name _ (stage_MG in_flag out_flag) _ t ->
    v = @transition_update_value name _ (stage_MG in_flag out_flag) _ t (σ x).
  Proof.
    destruct t; intros σ x v σ' Hstep Hx.
    * subst. simpl.
  *)

  Inductive val_is_bit : value -> Prop :=
  | val_bit0 : val_is_bit Bit0
  | val_bit1 : val_is_bit Bit1.
  Inductive wf_handshake (h : handshake name) (σ : state name) : Prop :=
  | handshake_in_sync : σ (req h) = σ (ack h) -> wf_handshake h σ
  | handshake_out_of_sync : σ (req h) = neg_value (σ (ack h)) -> wf_handshake h σ.
  Record wf_stage_state (σ : state name) : Prop :=
    { wf_all_bits : forall x, x ∈ space_output (latch_stage_with_env l) -> val_is_bit (σ x)
    ; wf_latch_input  : wf_handshake (latch_input l)  σ
    ; wf_latch_output : wf_handshake (latch_output l) σ
    ; wf_clk : val_is_bit (σ (latch_clk l))
    }.

  Lemma step_wf_state_σR : 
    wf_stage_state (σR l).
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
      split.
      { intros x Hx. unfold σR.
        repeat (compare_next; try constructor);
          destruct l; try constructor.
      }
      { assert (Hack : σR l (ack (latch_input l)) = Bit0).
        { unfold σR; reduce_eqb.
          repeat (compare_next; auto).
        }
        assert (Hreq : σR l (req (latch_input l)) = if is_token_latch l then Bit0 else Bit1).
        { unfold σR; reduce_eqb.
          repeat (compare_next; auto).
          { rewrite Heq in Hdisjoint. find_contradiction. }
          { rewrite Heq in Hdisjoint. find_contradiction. }
        }
        destruct l; simpl in Hreq.
        * (* Odd==not token latch *)
          apply handshake_out_of_sync.
          rewrite Hack, Hreq; auto.
        * (* Even==token latch *)
          apply handshake_in_sync.
          rewrite Hack, Hreq; auto.
      }
      { assert (Hack : σR l (ack (latch_output l)) = Bit0).
        { unfold σR; reduce_eqb; auto. }
        assert (Hreq : σR l (req (latch_output l)) = if is_token_latch l then Bit1 else Bit0).
        { unfold σR; reduce_eqb.
          repeat (compare_next; auto).
          { rewrite Heq in Hdisjoint. find_contradiction. }
          { rewrite Heq in Hdisjoint. find_contradiction. }
          { rewrite Heq in Hdisjoint. find_contradiction. }
        }
        destruct l; simpl in Hreq.
        * (* Odd==not token latch *)
          apply handshake_in_sync.
          rewrite Hack, Hreq; auto.
        * (* Even==token latch *)
          apply handshake_out_of_sync.
          rewrite Hack, Hreq; auto.
      }
      { unfold σR; reduce_eqb.
        repeat (compare_next; try constructor);
          destruct l; try constructor.
      }
  Qed.

  Lemma step_wf_state_lemma : forall σ e σ',
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state σ'.
  Proof.
    intros σ [x v] σ' Hwf Hstep.
Print well_formed.
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { eapply wf_space; eauto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hx.
    rewrite latch_stage_input, latch_stage_output in Hx.

    decompose_set_structure.
    * (* x = left req *)
      
  Admitted.
  Lemma step_wf_state_eps : forall σ σ',
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state σ'.
  Admitted.
  Lemma step_wf_state : forall tr σ,
    latch_stage_with_env l ⊢ σR l →*{tr} Some σ ->
    wf_stage_state σ.
  Proof.
    intros tr σ Hstep.
    set (Hdisjoint := scheme_all_disjoint l).
    remember (Some σ) as τ; generalize dependent σ.
    induction Hstep; intros σ Hτ; subst.
    * inversion Hτ; subst.
      apply step_wf_state_σR.
    * eapply step_wf_state_lemma; eauto.
    * eapply step_wf_state_eps; eauto.
  Qed.



  (** Intuitively, [prop_marked p σ] is a property that holds on a state σ
  whenever a related marking m satisfies [m(p) > 0]. *)
  Inductive prop_marked : forall {t1 t2} (p : stage_place t1 t2) (σ : state name), Prop :=

  | lack_lreq_marked σ :
    σ (ack (latch_input l)) = σ (req (latch_input l)) -> prop_marked left_ack_left_req σ
  .

  Ltac step_inversion_1 :=
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_left in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S1) *)
      [ | unfold space_domain; left; right; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_right in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S2) *)
      [ | unfold space_domain; left; right; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply hide_inversion in Hstep
  end.
  Ltac step_inversion_eq :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply func_space_output_inversion in Hstep;
        [ | simpl; solve_set; fail | simpl; solve_set; fail]
  end.
  Ltac step_inversion_unstable :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      eapply func_space_output_unstable in Hstep; eauto;
        [ | simpl; solve_set; fail ]
  end.




  Lemma step_implies_prop_marked : forall σ t σ',
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{Some (transition_event t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t), prop_marked p σ.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ t σ' Hwf Hstep t0 p.
    dependent destruction p.
    { (* left_ack_left_req *)
      constructor.
      step_inversion_eq.
      simpl in Hstep.
      assert (Hack : val_is_bit (σ (ack (latch_input l)))).
      { apply wf_all_bits; auto. simpl; solve_set. }
      assert (Hreq : val_is_bit (σ (req (latch_input l)))).
      { apply wf_all_bits; auto. simpl; solve_set. }
      inversion Hack; my_subst; inversion Hreq; my_subst; auto.
    }
  Admitted.

  (* Helper lemmas for relate_implies_marked below *)
  Lemma relate_implies_marked_eps : forall σ σ',
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p σ' ->
    prop_marked p σ.
  Admitted.

  Lemma outgoing_place_not_marked : forall σ σ' t,
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{Some (transition_event t σ)} Some σ' ->
    forall t0 (p : stage_place t0 t),
        ~ prop_marked p σ'.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ σ' t Hwf Hstep t0 p Hprop.
    dependent destruction Hprop.
    * (* t = left_req *)
      assert (Hreq : σ0 (req (latch_input l)) = neg_value (σ (req (latch_input l)))).
      { eapply wf_update; eauto. }
      assert (Hack : σ0 (ack (latch_input l)) = σ (ack (latch_input l))).
      { eapply wf_scoped; eauto.
        { intro v; inversion 1; subst. rewrite H3 in Hdisjoint. find_contradiction. }
        { simpl; solve_set. }
      }
      step_inversion_eq.
    contradict Hstep. simpl.
    assert (Hreq' : val_is_bit (σ (req (latch_input l)))).
    { apply wf_all_bits; auto. simpl; solve_set. }
    assert (Hack' : val_is_bit (σ (ack (latch_input l)))).
    { apply wf_all_bits; auto. simpl; solve_set. }


    rewrite <- Hreq, <- Hack.
    rewrite H0.

    inversion Hreq'; my_subst; clear Hreq';
    inversion Hack'; my_subst; clear Hack';
    rewrite Hreq; simpl; discriminate.
    
  Admitted.

  Lemma disjoint_place_marked : forall σ σ' t,
    latch_stage_with_env l ⊢ σ →{Some (transition_event t σ)} Some σ' ->
    forall t1 t2 (p : stage_place t1 t2),
      t1 <> t ->
      t2 <> t ->
      prop_marked p σ' ->
      prop_marked p σ.
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ σ' t Hstep t1 t2 p Ht1 Ht2 Hmarked.
    dependent destruction Hmarked.
    * constructor.
      erewrite <- (wf_scoped _ _ latch_stage_well_formed σ _ σ0); eauto.
      3:{ simpl. solve_set. }
      2:{ intros v. inversion 1; subst. 
          Print stage_naming_scheme.
          contradict H3.
          admit (* true *).
      }
      erewrite <- (wf_scoped _ _ latch_stage_well_formed σ _ σ0); eauto.
      2:{ simpl. solve_set. }
      1:{ intros v. inversion 1; subst. 
          contradict H3.
          admit (* true *).
      }
  Admitted.


  Lemma init_relate_implies_marked : forall {t1 t2} (p : stage_place t1 t2),
    prop_marked p (σR l) ->
    init_marking (stage_MG in_flag out_flag) _ _ p > 0.

  Admitted.

  Lemma state_relate_marking_steps : forall σ m,
    state_relate_marking σ m ->
    exists tr, latch_stage_with_env l ⊢ σR l →*{tr} Some σ.
  Proof.
    intros σ m Hrelate.
    induction Hrelate.
    * exists t_empty. constructor.
    * destruct IHHrelate as [tr IH].
      exists (tr ▶ transition_event t σ).
      econstructor; eauto.
    * destruct IHHrelate as [tr IH].
      exists tr.
      econstructor; eauto.
  Qed.

  Lemma relate_implies_marked : forall σ m,
    state_relate_marking σ m ->
    forall {t1 t2} (p : stage_place t1 t2),
      prop_marked p σ ->
      0 < m _ _ p.
  Proof.   (* by induction on state_relate_marking *)
    intros σ m Hrelate.
    induction Hrelate; intros t1 t2 p Hp.
    * apply init_relate_implies_marked; auto.
    * unfold is_enabled in H1.
      rewrite H2.
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
      { apply IHHrelate.
        eapply disjoint_place_marked; eauto.
      }
    * apply IHHrelate.
      eapply relate_implies_marked_eps; eauto.
  Qed.

  Theorem state_related_enabled : forall σ σ' t m,
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{Some (transition_event t σ)} Some σ' ->
    state_relate_marking σ m ->
    is_enabled _ t m.
  Proof.
    intros.
    intros t0 p.
    assert (prop_marked p σ).
    { eapply step_implies_prop_marked; eauto. }
    eapply relate_implies_marked; eauto.
  Qed.


  Lemma step_implies_bit : forall σ x v σ',
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    val_is_bit v.
  Admitted.


Ltac destruct_bit v :=
  match goal with
  | [ H : val_is_bit v |- _ ] => inversion H; subst
  | [ H : wf_stage_state ?σ |- _ ] =>
    match v with
    | (σ ?x) => let H' := fresh "H" in
                assert (H' : val_is_bit (σ x))
                  by (apply wf_all_bits; simpl; solve_set);
                inversion H'; my_subst
   end
  end.

Ltac solve_bit_neq_neg :=
  match goal with
  | [ H : ?v <> ?v' |- _ ] => destruct_bit v;
                              destruct_bit v';
                              auto; find_contradiction
  end.

  (* How to prove this? Maybe build on prop_marked?? *)
  (* Note: this is not enough to distinguish CLK+ from CLK- *)
  Lemma step_implies_event_step : forall t σ x v σ',
    wf_stage_state σ ->
    latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
    x = @transition_name name _ (stage_MG in_flag out_flag) _ t ->
    v = @transition_update_value name _ (stage_MG in_flag out_flag) _ t (σ x).
  Proof.
    set (Hdisjoint := scheme_all_disjoint l).
    intros t σ x v σ' Hwf Hstep.
    assert (Hv : val_is_bit v).
    { eapply step_implies_bit; eauto. }
    destruct t; simpl; intros Hx; subst;
      try (step_inversion_unstable;
           solve_bit_neq_neg; fail).
    * admit (* not enough *).
    * admit (* not enough *).

  Admitted.




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
    relate_trace_step_lemma name (latch_stage_with_env l) (stage_MG_SS l in_flag) (σR l) init_stage_MG_state.
  Proof.
    unfold relate_trace_step_lemma.
    set (Hdisjoint := scheme_all_disjoint l).
    intros σ1 σ1' σ2 [x v] t Hstep Hrelate.
    assert (Hwfσ1 : wf_stage_state σ1).
    { eapply step_wf_state.
      eapply relate_trace_project_left.
      eauto.
    }
    assert (Hv : val_is_bit v).
    { eapply step_implies_bit; eauto. }

    assert (Hwf : well_formed (latch_stage_with_env l)) by (exact latch_stage_well_formed).
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
        step_inversion_unstable. solve_bit_neq_neg.
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
    set (Hdisjoint := @stage_places_all_disjoint _ _ scheme x_scheme l).
    intros t1 t2 p. simpl.
    rewrite dom_latch_stage_with_env.
    unfold space_domain.
    rewrite latch_stage_input, latch_stage_output.
    auto.
    intro Hin.
    decompose_set_structure; try(specialize (Hdisjoint _ _ _ _ p p); find_contradiction; fail).
  Qed.

  Theorem MG_refines_stage :
    traces_of (latch_stage_with_env l) (σR l) ⊆ traces_of (stage_MG_SS l in_flag) init_stage_MG_state.
  Proof.
    Search relate_trace_step_lemma.
    apply relate_trace_step_subset.
    { intros x Hdom1 Hdom2.
      unfold init_stage_MG_state.
      destruct (name_is_place_dec (stage_MG in_flag out_flag) x)
        as [[t1 [t2 [p Hplace]]] | Htransition].
      + subst.
About places_set.
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


  End SS_to_TokenMG.


End ClickMG.
