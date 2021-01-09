
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

Module Type PropMarkedType.
  Declare Module ClickModule : ClickType.
  Export ClickModule.
  Module ClickMG := ClickMG(ClickModule).
  Export ClickMG.
  Export ClickTactics.

  Definition latch_in_flag (l : latch even odd) := swap_token_flag (latch_to_token_flag l).
  Definition latch_out_flag (l : latch even odd) := latch_to_token_flag l.
  Definition latch_stage_MG l := stage_MG (latch_in_flag l) (latch_out_flag l).
  Definition latch_transition_event l := transition_event l (latch_in_flag l).
  Definition latch_stage_MG_SS l := stage_MG_SS l (latch_in_flag l).

  (** Intuitively, [prop_marked p σ] is a property that holds on a state σ
  whenever a related marking m satisfies [m(p) > 0]. *)


  Inductive prop_marked (l : latch even odd) : forall {t1 t2} (p : stage_place t1 t2) (σ : state name), Prop :=

  (* left_ack -> left_req *)
  | lack_lreq_marked σ :
    σ (ack (latch_input l)) = σ (req (latch_input l)) -> prop_marked l left_ack_left_req σ

  (* right_req -> right_ack *)
  | rreq_rack_marked σ :
    σ (req (latch_output l)) = neg_value (σ (ack (latch_output l))) ->
    prop_marked l right_req_right_ack σ (* right_req -> right_ack *)

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
    prop_marked l clk_fall_left_ack σ

  | clk_fall_left_ack_state0_marked σ :
    σ (latch_clk l) = Bit0 ->
    σ (latch_old_clk l) = Bit1 ->
    prop_marked l clk_fall_left_ack σ

  (* clk+ -> right_req *)
  | clk_rise_right_req_marked σ :
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit0 ->
    prop_marked l clk_rise_right_req σ
  | clk_rise_right_req_marked_state0 σ :
    σ (req (latch_output l)) <> σ (latch_state0 l) ->
(*    σ (ack (latch_output l)) <> σ (req (latch_output l)) -> *)
    prop_marked l clk_rise_right_req σ

  (* clk+ -> clk- *)
  | clock_fall_flop_marked σ : (* the clk has just risen, and hasn't propogated through the flop yet *)
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit0 ->
    stable (latch_clk_component l) σ ->
    prop_marked l clock_fall σ
  | clock_fall_state0_marked σ : (* the clk has propogated through the flop, updating state0 *)
    σ (latch_clk l) = Bit1 ->
    σ (latch_old_clk l) = Bit1 ->
    ~ stable (latch_clk_component l) σ ->
    prop_marked l clock_fall σ

  (* left_req -> clk+ *)
  | left_req_clk_rise_marked σ :
    σ (req (latch_input l)) = neg_value (σ (ack (latch_input l))) ->
    σ (req (latch_input l)) = if_token l (σ (latch_state0 l)) ->
    σ (latch_clk l) = Bit0 ->
    σ (latch_old_clk l) = Bit0 -> (* need extra info *)
    prop_marked l left_req_clk_rise σ

  (* right_ack -> clk+ *)
  | right_ack_clk_rise_marked σ :
    σ (ack (latch_output l)) = σ (req (latch_output l)) ->
    (* latch_clk_function l σ = Bit1 -> *)
    σ (ack (latch_output l)) = σ (latch_state0 l) ->
    σ (latch_clk l) = Bit0 ->
    σ (latch_old_clk l) = Bit0 -> (* need extra info *)
    prop_marked l right_ack_clk_rise σ
  .

End PropMarkedType.

Module PropMarkedTactics (Import PropMarked : PropMarkedType).

  Lemma init_relate_implies_marked : forall {l t1 t2} (p : stage_place t1 t2),
    prop_marked l p (σR l) ->
    init_marking (latch_stage_MG l) _ _ p > 0.
  Proof.
    intros l t1 t2 p Hp.
    dependent destruction Hp;
      try (simpl; unfold init_marking_flag; simpl;
      unfold σR in *; simpl in *; reduce_eqb;
      try (destruct l; simpl in *; find_contradiction; auto; fail);
    fail).
  Qed.

(************)
(** Lemmas **)
(************)

  Lemma stage_eps_decide_state0 : forall l σ σ0,
    wf_stage_state l σ ->

    latch_stage_with_env l ⊢ σ →{None} Some σ0 ->
    σ (latch_state0 l) <> σ0 (latch_state0 l) ->
    σ (latch_old_clk l) = Bit1 \/ σ (latch_clk l) = Bit1.
  Proof.
    intros l σ σ' Hwf Hstep Hstate0.
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

(************)
(** Tactics *)
(************)


Arguments wf_scoped {name} S {S_wf} σ e σ' Hstep x : rename.

Ltac rewrite_back_wf_scoped :=
  match goal with
  | [ Hstep : ?S ⊢ ?σ →{ ?e } Some ?σ' |- context[ ?σ ?x ] ] =>
    erewrite <- (@wf_scoped _ S _ σ e σ' Hstep x);
    [ | try (intro; inversion 1; find_contradiction; fail)
    | rewrite latch_stage_with_env_input, latch_stage_with_env_output;
          solve_space_set
    ]
  end.


Ltac distinguish_events :=
  match goal with
  | [ |- context[ Some (latch_transition_event _ ?t _) <> Some (Event _ _) ] ] =>
    intros; destruct t; auto; inversion 1; fail
  | [ |- context[ None <> Some _ ] ] => intros; inversion 1
  | [ |- context[ Some _ <> None ] ] => intros; inversion 1
  end.

End PropMarkedTactics.
