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
                             | left_ack_left_req => local_name l "left_ack_left_req"
                             | clk_fall_left_ack => local_name l "clk_fall_left_ack"
                             | clk_rise_right_req => local_name l "clk_rise_right_req"
                             | right_req_right_ack => local_name l "right_req_right_ack"
                             | clock_fall => local_name l "clock_fall"
                             | left_req_clk_rise => local_name l "left_req_clk_rise"
                             | right_ack_clk_rise => local_name l "right_ack_clk_rise"
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
   ; name_to_place := name_to_stage_place
   ; transition_update_value := token_transition_update_value
   ; input_transition := from_list [left_req; right_ack]
   |}.
  Next Obligation.
    split; intros Hx.
    { apply name_to_stage_place_eq in Hx; subst. reflexivity. }
    { destruct p; subst; simpl; unfold name_to_stage_place; simpl; reduce_eqb; reflexivity. }
  Qed.
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

  Definition transition_event (t : token_transition) (σ : state name) : event name value :=
    let x := @transition_name name _ (stage_MG in_flag out_flag) _ t in
    let v := @transition_update_value name _ (stage_MG in_flag out_flag) _ t (σ x) in
    Event x v.


End TokenMG_to_SS.
Existing Instance stage_MG_scheme.
About name_to_place.
Arguments name_to_place {name transition} MG {MG_naming_scheme}.
Arguments traces_of {name}.


  Section SS_to_TokenMG.

  Variable l : latch even odd.
  Let out_flag := latch_to_token_flag l.
  (* in_flag is opposite of out_flag here *)
  Let in_flag := swap_token_flag (latch_to_token_flag l).

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
Hint Resolve wf_MG_SS : click.
Arguments well_formed {name}.
Arguments stage_place_name {stage_naming_scheme} l {t1 t2}.
Arguments place_name {name transition} MG {MG_naming_scheme} {t1 t2}.


End ClickMG.
