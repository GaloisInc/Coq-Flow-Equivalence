Require Import Base.
Require Import FlowEquivalence.
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


(** * Definition of rise-decoupled marked graph *)
Section RiseDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive rd_place : event even odd -> event even odd -> Set :=
  | latch_fall l : rd_place (Rise l) (Fall l)
  | latch_rise l : rd_place (Fall l) (Rise l)
  (* E- → O- for (E,O) *)
  (* O- → E- for (O,E) *)
  | neighbor_fall_fall l l' : neighbor c l l' ->
                              rd_place (Fall l) (Fall l')
  (* O- → E+ for (E,O) *)
  (* E- → O+ for (O,E) *)
  | neighbor_fall_rise l l' : neighbor c l l' ->
                              rd_place (Fall l') (Rise l)
  .


  Definition rise_decoupled : marked_graph (event even odd) :=
    {| place := rd_place
     ; init_marking := fun t1 t2 p => match p with
                                      | latch_fall (Odd _) => 1
                                      | latch_rise (Even _) => 1
                                      | neighbor_fall_fall (Even _) (Odd _) _ => 1
                                      | _ => 0
                                      end
    |}.

Open Scope nat_scope.

(** * Specialized is_enabled predicate *)
Inductive is_enabled_RD : event even odd -> marking rise_decoupled -> Prop :=
| fall_enabled_RD l (m : marking rise_decoupled) :
    0 < m _ _ (latch_fall l) ->
    (forall l0 (pf : neighbor c l0 l),
        0 < m _ _ (neighbor_fall_fall l0 l pf)) ->
    is_enabled_RD (Fall l) m

| rise_enabled_RD l (m : marking rise_decoupled) :
    0 < m _ _ (latch_rise l) ->
    (forall l' (pf : neighbor c l l'),
        0 < m _ _ (neighbor_fall_rise l l' pf)) ->
    is_enabled_RD (Rise l) m
.
Lemma RD_is_enabled_equiv : forall e m,
    is_enabled_RD e m -> is_enabled rise_decoupled e m.
Proof.
  destruct e as [l | l];
    intros m; inversion 1; subst;
    intros e0 p;
    simpl in p;
    dependent destruction p;
    auto.
Qed.
 

Lemma is_enabled_RD_equiv : forall e m,
    is_enabled rise_decoupled e m ->
    is_enabled_RD e m.
Proof.
  intros e m Henabled.
  unfold is_enabled in *.
  destruct e as [l | l];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.





Ltac get_enabled_constraints :=
  try match goal with
  | [ H : is_enabled rise_decoupled _ _ |- _ ] => apply is_enabled_RD_equiv in H; inversion H; subst
  end; 
(*
  try match goal with
  | [ H : neighbor _ ?l ?l' |- _ ] =>
    let H' := fresh "H" in
    set (H' := neighbor_neq _ _ _ H)
  end; 
*)
  specialize_enabled_constraints.


(** * Helper lemmas *)
Lemma rd_loop : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall l,
    m _ _ (latch_fall l) + m _ _ (latch_rise l) = 1.
Proof.
  intros t m Ht l.
  solve_loop. destruct l; auto.
Qed.


Lemma rd_loop_neighbor : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall l l' (pf : neighbor c l l'),
      m _ _ (latch_fall l) + m _ _ (neighbor_fall_fall _ _ pf)
                           + m _ _ (neighbor_fall_rise _ _ pf) = 1.
Proof.
  intros.
  solve_loop.
  inversion pf; auto.
Qed.

Lemma fall_enabled_opaque : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall l l' (pf : neighbor c l l'),
    0 < m _ _ (neighbor_fall_fall l l' pf) ->
    transparent t l = Opaque.
Proof.
  intros t m Hm; induction Hm; intros l l' Hneighbor Henabled.
    * simpl in *.
      inversion Hneighbor; subst; find_contradiction; auto.
    * simpl.
      subst. unfold fire in Henabled.
      set (loop := rd_loop_neighbor _ _ Hm _ _ Hneighbor).
      assert (Rise l <> e).
      { inversion 1; subst.
        repeat get_enabled_constraints.
        compare_next; try omega.
        { inversion e; subst. reduce_eqb. omega. }
        { simpl in *. omega. }
      }
      reduce_eqb.

      repeat (compare_next; find_event_contradiction); auto.
      { contradict Henabled. omega. }
      { eapply IHHm. eauto. }
Qed.

Lemma fall_enabled_even_odd_strong : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall E O (pf : neighbor c (Even E) (Odd O)),
    (0 < m _ _ (neighbor_fall_fall _ _ pf) ->
        num_events (Fall (Odd O)) t = num_events (Fall (Even E)) t) /\

    (0 < m _ _ (neighbor_fall_rise _ _ pf) ->
        num_events (Fall (Odd O)) t = 1+num_events (Fall (Even E)) t) /\
    (0 < m _ _ (latch_fall (Even E)) ->
        num_events (Fall (Odd O)) t = 1+num_events (Fall (Even E)) t).
Proof.
  intros t m Hm; induction Hm; intros E O pf;
    repeat split; intros Henabled;
    subst; unfold fire in Henabled;
    try (simpl in Henabled; find_contradiction; fail);

    simpl;
    specialize (IHHm _ _ pf);
    destruct IHHm as [IH1 [IH2 IH3]];
    set (Hloop := rd_loop_neighbor _ _ Hm _ _ pf);
    repeat (compare_next; find_event_contradiction); auto;
    try (contradict Henabled; omega).

    { get_enabled_constraints; omega. }
Qed.


Lemma fall_enabled_odd_even_strong : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall O E (pf : neighbor c (Odd O) (Even E)),
    (0 < m _ _ (neighbor_fall_fall _ _ pf) ->
        num_events (Fall (Odd O)) t = 1+num_events (Fall (Even E)) t) /\

    (0 < m _ _ (neighbor_fall_rise _ _ pf) ->
        num_events (Fall (Odd O)) t = num_events (Fall (Even E)) t) /\

    (0 < m _ _ (latch_fall (Odd O)) ->
        num_events (Fall (Odd O)) t = num_events (Fall (Even E)) t).
Proof.
  intros t m Hm; induction Hm; intros E O pf;
    repeat split; intros Henabled;
    subst; unfold fire in Henabled;
    try (simpl in Henabled; find_contradiction; fail);

    simpl;
    specialize (IHHm _ _ pf);
    destruct IHHm as [IH1 [IH2 IH3]];
    set (Hloop := rd_loop_neighbor _ _ Hm _ _ pf);
    repeat (compare_next; find_event_contradiction); auto;
    try (contradict Henabled; omega).

    { get_enabled_constraints; omega. }
Qed.


Lemma fall_enabled_num_events : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall l, is_enabled rise_decoupled (Fall l) m ->
    forall l', neighbor c l' l ->
    num_events (Fall l') t = match l with
                             | Odd _ => num_events (Fall l) t
                             | Even _ => 1+num_events (Fall l) t
                             end.
Proof.
  intros t m Hm l Henabled l' Hneighbor.
  get_enabled_constraints.
  inversion Hneighbor; subst.
  + edestruct fall_enabled_even_odd_strong as [EO1 [EO2 EO3]]; eauto.
    rewrite EO1; eauto.
  + edestruct fall_enabled_odd_even_strong as [EO1 [EO2 EO3]]; eauto.
Qed.
  

(** * Flow equivalence proof *)
Theorem rise_decoupled_flow_equivalence : flow_equivalence rise_decoupled c init_st.
Proof.
  intros l t v [m Hm] Hrel.
  revert m Hm.
  dependent induction Hrel; intros m Hm.
  * auto.
  * inversion Hm as [ | e0 m0 ? t0' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    repeat compare_next.
    eapply IHHrel; eauto.

  * inversion Hm as [ | e0 m0 ? t0' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    reduce_eqb.
    erewrite sync_eval_S; eauto.
    intros l' Hl'.
    erewrite H1; eauto.
    2:{ eapply fall_enabled_opaque; eauto. }

    { erewrite fall_enabled_num_events; eauto.
      destruct l; auto.
    }
    Unshelve.
    auto.
  Qed.

End RiseDecoupled.

Arguments rise_decoupled {even odd}.
Ltac RD_get_enabled_constraints :=
  try match goal with
  | [ H : is_enabled rise_decoupled _ _ |- _ ] => apply is_enabled_RD_equiv in H; inversion H; subst
  end;
  specialize_enabled_constraints.
