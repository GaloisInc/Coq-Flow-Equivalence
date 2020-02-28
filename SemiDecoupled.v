Require Import Base.
Require Import FlowEquivalence.
Require Import RiseDecoupled. 
Import FE_Tactics.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.

Require Import PeanoNat.

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.


(** * Definition of semi-decoupled marked graph *)
Section SemiDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive sd_place : event even odd -> event even odd -> Set :=
  | SD_latch_fall l : sd_place (Rise l) (Fall l)
  | SD_latch_rise l : sd_place (Fall l) (Rise l)
  (* E- → O- for (E,O) *)
  (* O- → E- for (O,E) *)
  | SD_neighbor_fall_fall l l' : neighbor c l l' ->
                                 sd_place (Fall l) (Fall l')
  (* O+ → E+ for (O,E) *)
  (* E+ → O+ for (E,O) *)
  | SD_neighbor_rise_rise l l' : neighbor c l l' ->
                                 sd_place (Rise l) (Rise l')

  (* l'- → l+ for (l,l') *)
  | SD_neighbor_fall_rise l l' : neighbor c l l' ->
                                 sd_place (Fall l') (Rise l)
  .

  Definition semi_decoupled : marked_graph (event even odd) :=
    {| place := sd_place
     ; init_marking := fun t1 t2 p => match p with
                                      | SD_latch_fall (Odd _) => 1
                                      | SD_latch_rise (Even _) => 1
                                      | SD_neighbor_rise_rise (Odd _) (Even _) _ => 1
                                      | SD_neighbor_fall_fall (Even _) (Odd _) _ => 1
                                      | _ => 0
                                      end
    |}.


  Open Scope nat_scope.

  (** * Specialized is_enabled predicate *)
  Inductive is_enabled_SD : event even odd -> marking semi_decoupled -> Prop :=
  | fall_enabled_SD l (m : marking semi_decoupled) :
    0 < m _ _ (SD_latch_fall l) ->
    (forall l0 (pf : neighbor c l0 l),
        0 < m _ _ (SD_neighbor_fall_fall l0 l pf)) ->
    is_enabled_SD (Fall l) m

  | rise_enabled_SD l (m : marking semi_decoupled) :
    0 < m _ _ (SD_latch_rise l) ->
    (forall l' (pf : neighbor c l l'),
        0 < m _ _ (SD_neighbor_fall_rise l l' pf)) ->
    (forall l0 (pf : neighbor c l0 l),
        0 < m _ _ (SD_neighbor_rise_rise l0 l pf)) ->
    is_enabled_SD (Rise l) m
  .
  Lemma SD_is_enabled_equiv : forall e m,
    is_enabled_SD e m -> is_enabled semi_decoupled e m.
  Proof.
    destruct e as [l | l];
      intros m; inversion 1; subst;
      intros e0 p;
      simpl in p;
      dependent destruction p;
      auto.
  Qed.
 

  Lemma is_enabled_SD_equiv : forall e m,
    is_enabled semi_decoupled e m ->
    is_enabled_SD e m.
  Proof.
    intros e m Henabled.
    unfold is_enabled in *.
    destruct e as [l | l];
      constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
  Qed.

Arguments path_cost {transition M t1 t2}.


  Lemma sd_loop : forall t m,
    {semi_decoupled}⊢ t ↓ m ->
    forall l,
    m _ _ (SD_latch_fall l) + m _ _ (SD_latch_rise l) = 1.
  Proof.
    intros t m Ht l.
    solve_loop. destruct l; auto.
  Qed.


End SemiDecoupled.

About SD_latch_fall.
Print sd_place.
  Arguments SD_latch_fall {even odd}.
  Arguments SD_latch_rise {even odd}.
  Arguments SD_neighbor_fall_fall {even odd}.
  Arguments SD_neighbor_rise_rise {even odd}.
  Arguments SD_neighbor_fall_rise {even odd}. 

  Arguments latch_fall {even odd}.
  Arguments latch_rise {even odd}.
  Arguments neighbor_fall_fall {even odd}.
  Arguments neighbor_fall_rise {even odd}. 

  Arguments semi_decoupled {even odd}.

  Ltac get_enabled_constraints :=
    try match goal with
    | [ H : is_enabled (semi_decoupled _) _ _ |- _ ] =>
      apply is_enabled_SD_equiv in H; inversion H; subst
    end; 
    specialize_enabled_constraints.


Section SD_RD_relate.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).

Print sd_place.
  Inductive SD_RD : 
        forall {e1 e2}, place (semi_decoupled c) e1 e2 -> 
        forall {e1' e2'}, place (rise_decoupled c) e1' e2' -> Prop :=
  | SD_RD_fall l : SD_RD (SD_latch_fall c l) (latch_fall c l)
  | SD_RD_rise l : SD_RD (SD_latch_rise c l) (latch_rise c l)
  | SD_RD_fall_rise l l' pf :
    SD_RD (SD_neighbor_fall_rise c l l' pf) (neighbor_fall_rise c l l' pf)
  | SD_RD_fall_fall l l' pf :
    SD_RD (SD_neighbor_fall_fall c l l' pf) (neighbor_fall_fall c l l' pf)
  .



  Lemma SD_RD_enabled_equiv : forall t m m' e1 e2 (p : place _ e1 e2) 
                                            e1' e2' (p' : place _ e1' e2'),
    {semi_decoupled c}⊢ t ↓ m ->
    {rise_decoupled c}⊢ t ↓ m' ->
    SD_RD p p' ->
    m _ _ p = m' _ _ p'.
  Proof.
    induction t; intros m m' e1 e2 p e1' e2' p' Hm Hm' Hrel.
    * inversion Hm; inversion Hm'; subst.
      dependent destruction Hrel; auto.

    * dependent destruction Hm.
      dependent destruction Hm'.
      unfold fire.

      dependent destruction Hrel;
        simpl;
        repeat (compare_next; erewrite IHt; eauto; constructor; fail).
Qed.


  Lemma semi_decoupled_refines_rise_decoupled : forall t m,
    { semi_decoupled c }⊢ t ↓ m ->
    exists m', (({rise_decoupled c}⊢ t ↓ m')).
  Proof.
    intros t m Ht.
    induction Ht.
    * eexists. econstructor.
    * subst.
      destruct IHHt as [m' IHHt].
      eexists. econstructor; eauto.

      apply is_enabled_SD_equiv in H. inversion H; subst.

      + apply RD_is_enabled_equiv.
        constructor.
        ++ erewrite <- SD_RD_enabled_equiv; [ | eauto | eauto | constructor ]. 
           auto.
        ++ intros l' pf.
           erewrite <- SD_RD_enabled_equiv; [ | eauto | eauto | constructor ]. 
           auto.
      + apply RD_is_enabled_equiv.
        constructor.
        ++ erewrite <- SD_RD_enabled_equiv; [ | eauto | eauto | constructor ]. 
           auto.
        ++ intros l' pf.
           erewrite <- SD_RD_enabled_equiv; [ | eauto | eauto | constructor ]. 
           auto.
  Qed.

  (** * Flow equivalence proof *)
  Theorem semi_decoupled_flow_equivalence :
    flow_equivalence (semi_decoupled c) c init_st.
  Proof.
    intros l t v [m Hm] Hrel.
    apply rise_decoupled_flow_equivalence; auto.
    eapply semi_decoupled_refines_rise_decoupled; eauto.
  Qed.
