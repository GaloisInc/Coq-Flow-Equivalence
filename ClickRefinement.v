Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import MarkedGraph.
Require Import Click.
Require Import ClickMG.

Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import Coq.Program.Equality.

Section MG_to_SS.

  Print marked_graph.
  Variable name : Set.
  Context `{name_dec : eq_dec name}.

  Variable transition : Set.
  Context `{transition_dec : eq_dec transition}.
  Variable MG : marked_graph transition.

  Variable transition_name : transition -> name.
  Variable place_name : forall t1 t2, place MG t1 t2 -> name.

  Definition places_set : Ensemble name :=
    fun x => exists t1 t2 (p : place MG t1 t2), x = place_name _ _ p.
  Definition state_to_marking (σ : state name) : marking MG :=
    fun t1 t2 p => val_to_nat (σ (place_name _ _ p)).

  Hypothesis name_is_place_dec : forall x,
                           {t1 : transition & {t2 : transition
                                            & {p : place MG t1 t2 & x = place_name _ _ p}}}
                         + {forall t1 t2 (p : place MG t1 t2), x <> place_name _ _ p}.

  Definition fire_in_state (t : transition) (σ : state name) : state name :=
    fun x =>
    match name_is_place_dec x with
    (* if x is not a place, do nothign *)
    | inright _ => σ x
    | inleft (existT _ tin (existT _ tout (existT _ p x_is_p))) =>
      (* corner case: do nothing *)
      if tin =? tout then σ x
      (* if x is a place leading into t, increment the value *)
      else if t =? tout then dec_value (σ x)
      (* if x is a place leading out of t, decrement the value *)
      else if t =? tin then inc_value (σ x)
      (* otherwise do nothing *)
      else σ x
    end.

  Variable transition_update_value : transition -> value -> value.
  (* Condition: input_transition, output_transition should partition the set of all transitions *)
  Variable input_transition : Ensemble transition.
  Variable output_transition : Ensemble transition.

  Inductive MG_SS_step
    : state name -> option (event name value) -> option (state name) -> Prop :=

  | transition_enabled σ σ' x v (t : transition) :
    x = transition_name t ->
    is_enabled MG t (state_to_marking σ) ->
    v = transition_update_value t (σ x) ->
    σ' = update (fire_in_state t σ) x v ->
    MG_SS_step σ (Some (Event x v)) (Some σ')

  | input_not_enabled σ x v t :
    x = transition_name t ->
    t ∈ input_transition ->
    ~ is_enabled MG t (state_to_marking σ) ->
   MG_SS_step σ (Some (Event x v)) None
  .

  Definition MG_SS : StateSpace name :=
  {| space_input := fmap transition_name input_transition
   ; space_output := fmap transition_name output_transition
   ; space_internal := places_set
   ; space_step := MG_SS_step
   |}.

End MG_to_SS.

Section ClickRefinement.

Variable name : Set.
Context `{name_dec : eq_dec name}.
Variable even odd : Set.
Context `{scheme : naming_scheme name even odd}.

Variable l : latch even odd.

(** Define a state space [latch_stage_refinement such that every trace accepted
by [latch_stage l] is also accepted by [latch_stage_refinement l] *)

Require Import ClickMG. 
Class extended_naming_scheme :=
    {place_name : forall {t1 t2 : token_transition}, stage_place t1 t2 -> name}.
Context `{extended_naming_scheme}.
Print stage_place.
Definition name_is_place_dec : forall x,
                          {t1 : token_transition &
                           {t2 : token_transition & {p : stage_place t1 t2 & x = place_name p}}}
                        + {forall t1 t2 (p : stage_place t1 t2), x <> place_name p}.
Proof.
  intros x. Print stage_place.

  Ltac compare_place_name x p :=
    compare x (place_name p);
      [ left; do 3 eexists; reflexivity | ].
  compare_place_name x left_ack_left_req.
  compare_place_name x clk_fall_left_req.
  compare_place_name x right_req_left_req.
  compare_place_name x clk_rise_left_ack.
  compare_place_name x clk_rise_right_req.
  compare_place_name x right_req_right_ack.
  compare_place_name x clk_fall_right_ack.
  compare_place_name x left_ack_right_ack.
  compare_place_name x clock_fall.
  compare_place_name x left_req_clk_rise.
  compare_place_name x right_ack_clk_rise.
  right. intros t1 t2 p; destruct p; auto.
Defined.


Definition places_set : Ensemble name :=
  fun x => exists t1 t2 (p : stage_place t1 t2), x = place_name p.



Definition state_to_marking (σ : state name) : marking stage_MG :=
  fun t1 t2 p => val_to_nat (σ (place_name p)).
Print naming_scheme. Print token_transition.
Print stage_MG. Print stage_place. Print value. Print enumerate.
Arguments enumerate A {enumerable}.
Print sig.
  

(** A transition should only fire if the caller has independently checked that it
  is enabled. *) Print sigT. Print sumor.
Search eq_dec token_transition.
Existing Instance token_transition_eq_dec.
Program Definition fire_in_state (t : token_transition) (σ : state name) : state name :=
  fun x =>
    match name_is_place_dec x with
    (* if x is not a place, do nothign *)
    | inright _ => σ x
    | inleft (existT _ tin (existT _ tout (existT _ p x_is_p))) =>
      (* corner case: do nothing *)
      if tin =? tout then σ x
      (* if x is a place leading into t, increment the value *)
      else if t =? tout then dec_value (σ x)
      (* if x is a place leading out of t, decrement the value *)
      else if t =? tin then inc_value (σ x)
      (* otherwise do nothing *)
      else σ x
    end.

Print transition_name.
Arguments transition_name {name even odd H0}.


Inductive latch_step_refinement
  : state name -> option (event name value) -> option (state name) -> Prop :=

| transition_enabled σ σ' x v (t : token_transition) :
  x = transition_name l t ->
  is_enabled stage_MG t (state_to_marking σ) ->
  v = transition_update_value t (σ x) ->
  σ' = update (fire_in_state t σ) x v ->
  latch_step_refinement σ (Some (Event x v)) (Some σ')

| input_not_enabled σ x v t :
  x ∈ space_input (latch_stage l) ->
  x = transition_name l t ->
  ~ is_enabled stage_MG t (state_to_marking σ) ->
  latch_step_refinement σ (Some (Event x v)) None
.



(** the internal wires are all the wire names corresponding to places in the
marked graph *)



Definition latch_state_refinement : StateSpace name :=
  {| space_input := space_input (latch_stage l)
   ; space_output := space_output (latch_stage l)
   ; space_internal := places_set 
   ; space_step := latch_step_refinement
   |}.


End ClickRefinement.
