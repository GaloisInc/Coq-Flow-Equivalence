Require Import Base.
Require Import Circuit.
Require Import Monad.
Require Import Setoid.

Require Import StateSpace.Definitions.
Require Import StateSpace.Tactics.

Require Import Program.Equality.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Import EnsembleNotation.
Open Scope ensemble_scope.

Section MG_to_SS.

  Set Implicit Arguments.
  (** ** Convert a marked graph to a state space *)
  Variable name : Set.
  Context `{name_dec : eq_dec name}.

  Variable transition : Set.
  Context `{transition_dec : eq_dec transition}.
  Variable MG : marked_graph transition.

  Import EnsembleNotation.
  Open Scope ensemble_scope.

  Inductive place_eq : forall {t1 t2 t1' t2' : transition}, place MG t1 t2 -> place MG t1' t2' -> Prop :=
  | place_refl : forall t1 t2 (p : place MG t1 t2), place_eq p p.


  Class MG_naming_scheme :=
  { transition_name : transition -> name
  ; place_name : forall {t1 t2} (p : place MG t1 t2), name

(*
  ;  name_is_place_dec : forall (x : name),
     {t1 : transition & {t2 : transition & {p : place MG t1 t2 & x = place_name p}}}
   + {forall t1 t2 (p : place MG t1 t2), x <> place_name p}
*)
  ; name_to_place : name -> option {t1 & {t2 & place MG t1 t2}}
  ; name_to_place_correct : forall x tin tout (p : place MG tin tout),
        name_to_place x = Some (existT _ tin (existT _ tout p))
    <-> x = place_name p

  ; transition_update_value : transition -> value -> value

  ; input_transition : Ensemble transition
  ; input_transition_dec : `{in_dec input_transition}

  ; transition_place_name_disjoint : forall t {t1 t2} (p : place MG t1 t2),
    transition_name t <> place_name p

    (* I'm not sure if t ∈ input_transition is the right restriction here, but
    we need this fact for proving well_formed, and it does not hold without this
    transition for click, e.g. with CLK+ and CLK-. On the other hand, what about
    4 phase handshake protocols? *)
  ; transition_name_injective : forall t t', t ∈ input_transition ->
    t <> t' -> transition_name t <> transition_name t'

   ; places_all_disjoint : forall {t1 t2 t1' t2' : transition}
                                        (p : place MG t1 t2) (p' : place MG t1' t2'),
      place_name p = place_name p' ->
      place_eq p p'

  }.
  Context `{MG_scheme : MG_naming_scheme}.

  Definition places_set : Ensemble name :=
    fun x => exists t1 t2 (p : place MG t1 t2), x = place_name p.
  Definition state_to_marking (σ : state name) : marking MG :=
    fun t1 t2 p => val_to_nat (σ (place_name p)).

  Lemma name_to_place_eq : forall t1 t2 (p : place MG t1 t2),
    name_to_place (place_name p) = Some (existT _ t1 (existT _ t2 p)).
  Proof.
    intros.
    apply name_to_place_correct; auto.
  Qed.
  Lemma name_to_place_neq : forall t,
    name_to_place (transition_name t) = None.
  Proof.
    intros t.
    destruct (name_to_place (transition_name t)) as [[t1 [t2 p]] | ] eqn:contra; auto.
    apply name_to_place_correct in contra.
    apply transition_place_name_disjoint in contra.
    contradiction.
  Qed.

  Definition fire_in_state (t : transition) (σ : state name) : state name :=
    fun x =>
    match name_to_place x with
    (* if x is not a place, do nothing *)
    | None => σ x
    | Some (existT _ tin (existT _ tout p)) =>
         (* corner case: do nothing *)
         if tin =? tout then σ x
         (* if x is a place leading into t, increment the value *)
         else if t =? tout then dec_value (σ x)
         (* if x is a place leading out of t, decrement the value *)
         else if t =? tin then inc_value (σ x)
         (* otherwise do nothing *)
         else σ x
    end.

  (* NOTE: this may not be the right relation for all marked graphs--get example from Peter *)
  Let transition_set : Ensemble name := fmap transition_name (fun (t : transition) => True).

  Inductive MG_SS_step
    : state name -> option (event name value) -> option (state name) -> Prop :=

  | transition_enabled σ σ' x v (t : transition) :
    x = transition_name t ->
    is_enabled MG t (state_to_marking σ) ->
    v = transition_update_value t (σ x) ->
    state_equiv_on (transition_set ∪ places_set)
                   (Some σ') 
                   (Some (update (fire_in_state t σ) x v)) ->
    MG_SS_step σ (Some (Event x v)) (Some σ')

  | input_not_enabled σ x v t :
    x = transition_name t ->
    t ∈ input_transition ->
    ~ is_enabled MG t (state_to_marking σ) ->
   MG_SS_step σ (Some (Event x v)) None
  .

  Let output_transition : Ensemble transition :=
    (fun t => True) ∖ input_transition.
(*    fun t => t ∉ input_transition.*)
  Definition MG_SS : StateSpace name :=
  {| space_input := fmap transition_name input_transition
   ; space_output := fmap transition_name output_transition
   ; space_internal := places_set
   ; space_step := MG_SS_step
   |}.

  Lemma places_all_numbers_step : forall σ σ' e {t1 t2} (p : place MG t1 t2),
    σ (place_name p) <> X ->
    MG_SS ⊢ σ →{e} Some σ' ->
    σ' (place_name p) <> X.
  Proof.
    intros σ σ' e t1 t2 p Hwf Hstep.
    inversion Hstep; subst.
    rewrite H5.
    2:{ right. exists t1. exists t2. exists p. reflexivity. }
    unfold update.
    set (Hneq := transition_place_name_disjoint t p).
    reduce_eqb.
    unfold fire_in_state.
    rewrite name_to_place_eq.
    compare_next; auto.
    compare_next; auto.
    { destruct (σ (place_name p)); find_contradiction. }
    compare_next; auto.
    { destruct (σ (place_name p)); find_contradiction. }
  Qed.


  Lemma places_all_numbers : forall σ σ' tr {t1 t2} (p : place MG t1 t2),
    σ (place_name p) <> X ->
    MG_SS ⊢ σ →*{tr} Some σ' ->
    σ' (place_name p) <> X.
  Proof.
    intros ? ? ? ? ? ? ? Hstep.
    remember MG_SS as S.
    remember (Some σ') as τ.
    generalize dependent σ'.
    generalize dependent t2. generalize dependent t1.
    induction Hstep; intros t1 t2 p Hneq σ'' Hτ; subst.
    * inversion Hτ; subst; auto.
    * destruct e as [x v].
      inversion H; subst; clear H.
      rewrite H7.
        2:{ right. do 3 eexists. reflexivity. }
        unfold update.
        set (Hneq' := transition_place_name_disjoint t0 p).
        reduce_eqb.
        unfold fire_in_state.
        rewrite name_to_place_eq.
        specialize (IHHstep _ _ p Hneq σ' eq_refl).
        compare_next; auto.
        compare_next; auto.
        { destruct (σ' (place_name p)); find_contradiction. }
        compare_next; auto.
        { destruct (σ' (place_name p)); find_contradiction. }

    * inversion H.
  Qed.

  Arguments well_formed {name}.
  Lemma wf_MG_SS : well_formed MG_SS.
  Proof.
    set (Hdec := input_transition_dec).
    constructor;
    try match goal with
    | [ |- _ ⊥ _ ] =>
      simpl; constructor;
      intros x Hx; deep_decompose_set_structure;
      match goal with
      | [ H : transition_name ?t1 = transition_name ?t2 |- _ ] =>
        compare t1 t2;
        try (eapply transition_name_injective; eauto; fail)

      | [ H : transition_name ?t = place_name ?p |- _ ] =>
        let Hdisjoint := fresh "Hdisjoint" in
        set (Hdisjoint := transition_place_name_disjoint t p);
        find_contradiction
      end
    end.

    * intros ? ? ? ? Hstep.
      inversion Hstep; subst; simpl.
      { destruct (t ∈? input_transition).
        + left. econstructor; eauto.
        + right. econstructor; split; eauto.
          unfold output_transition. solve_set.
       }
      { destruct (t ∈? input_transition).
        + left. econstructor; eauto.
        + right. econstructor; split; eauto.
          unfold output_transition. solve_set.
       }
    * intros ? ? ? Hstep ? He Hexternal.
      inversion Hstep; subst.
      rewrite H5.
      2:{ simpl in Hexternal. deep_decompose_set_structure; subst;
          left; exists x0; split; auto; constructor.
      }
      unfold update.
      compare_next; auto.
      { contradiction (He (transition_update_value t (σ (transition_name t)))); auto. }
      unfold fire_in_state.
      assert (Hx : forall t1 t2 (p : place MG t1 t2), x <> place_name p).
      { simpl in Hexternal. deep_decompose_set_structure; subst;
        apply transition_place_name_disjoint.
      }
      assert (Hx' : name_to_place x = None).
      { simpl in Hexternal; deep_decompose_set_structure; subst;
          rewrite name_to_place_neq; auto.
      }
      rewrite Hx'; auto.

    * intros ? ? ? ? Hstep.
      inversion Hstep; subst.
      rewrite H6.
      2:{ left. exists t; split; auto; constructor. }
      unfold update; simpl.
      reduce_eqb. auto.
  Qed.



  Lemma MG_SS_val_not_X : forall σ0 tr σ,
    MG_SS ⊢ σ0 →*{tr} Some σ ->
    forall {t1 t2} (p : place MG t1 t2), 
    σ0 (place_name p) <> X ->
    σ (place_name p) <> X.
  Proof.
    intros σ0 tr σ Hstep.
    remember (Some σ) as τ; generalize dependent σ.
    induction Hstep; intros σ Hτ t1 t2 p Hwf; inversion Hτ; subst; auto.
    * specialize (IHHstep σ' eq_refl t1 t2 p Hwf).
      inversion H; subst.
      rewrite H7.
      2:{ right. eexists. eexists. exists p. reflexivity. }
      unfold update. compare_next.
      { apply transition_place_name_disjoint in Heq; contradiction.
      }
      unfold fire_in_state.
      rewrite name_to_place_eq.
      compare_next; auto.
      compare_next. { destruct (σ' (place_name p)); try (inversion 1; fail); find_contradiction. }
      compare_next. { destruct (σ' (place_name p)); try (inversion 1; fail); find_contradiction. }
      auto.

    * specialize (IHHstep σ' eq_refl t1 t2 p Hwf).
      inversion H; subst.
  Qed.

  Unset Implicit Arguments.
End MG_to_SS.
