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

Section ClickRefinement.

  Variable even odd : Set.
  Variable name : Set.
  Context `{name_dec : eq_dec name}.
  Context `{scheme : naming_scheme name even odd}
          `{x_scheme : stage_naming_scheme name even odd}.

  Definition input_environment (h : handshake name) : StateSpace name :=
    NOT (ack h) (req h).
  Definition output_environment (h : handshake name) : StateSpace name :=
    forward (req h) (ack h).
  Definition brick_stage (hin hout : handshake name) : StateSpace name :=
      input_environment hin
    ∥ output_environment hout
    ∥ forward (req hin) (req hout)
    ∥ forward (ack hout) (ack hin).
  Lemma brick_stage_input : forall hin hout, 
    all_disjoint [req hin; req hout; ack hin; ack hout] ->
    space_input (brick_stage hin hout) == ∅.
  Proof.
    intros.
    constructor.
    * intros x Hx; simpl in *; decompose_set_structure; solve_set.
    * intros x Hx. inversion Hx.
  Qed.
  Lemma brick_stage_output : forall hin hout, 
    all_disjoint [req hin; req hout; ack hin; ack hout] ->
    space_output (brick_stage hin hout) == from_list [req hin; req hout; ack hin; ack hout].
  Proof.
    intros.
    constructor;
      intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.


  Variable l : latch even odd. Print naming_scheme. About NOT.
  Let out_flag := latch_to_token_flag l.
  (* in_flag is opposite of out_flag here *)
  Let in_flag := match l with
                 | Odd _ => Token
                 | Even _ => NonToken
                 end.

About traces_of.
Arguments traces_of {name}.
About stage_MG_SS.
Arguments stage_MG_SS {name} {name_dec} {even odd} l f {scheme x_scheme} : rename.
About init_stage_MG_state.
Arguments init_stage_MG_state {name name_dec even odd scheme x_scheme} : rename.
  Lemma stage_is_brick :
      traces_of (hide (latch_clk l) (stage_MG_SS l in_flag)) (init_stage_MG_state l)
    ⊆ traces_of (brick_stage (latch_input l) (latch_output l)) (σR l).
  Proof.
    Search traces_of.
    apply relate_trace_step_subset.
    * admit (* true *).
    * unfold relate_trace_step_lemma.
      intros σ1 σ1' σ2 e t Hstep Hrelate.
      inversion Hstep; subst.
      inversion H1; subst.
      (* seems easier to reason about if brick_stage is a marked graph *)
      admit.
  Admitted.


End ClickRefinement.
