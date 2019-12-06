Require Import Base.
Require Import FlowEquivalence.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.

Require Import PeanoNat.

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Section Desynchronization.


  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive desync_place : event even odd -> event even odd -> Set :=
  | Even_fall (E : even) : desync_place (Rise (Even E)) (Fall (Even E))
  | Even_rise (E : even) : desync_place (Fall (Even E)) (Rise (Even E))
  | Odd_fall  (O : odd) : desync_place (Rise (Odd O)) (Fall (Odd O))
  | Odd_rise  (O : odd) : desync_place (Fall (Odd O)) (Rise (Odd O))
  | Even_rise_odd_fall E O : In (E,O) (even_odd_neighbors c) ->
                             desync_place (Rise (Even E)) (Fall (Odd O))
  | Odd_fall_even_rise E O : In (E,O) (even_odd_neighbors c) ->
                             desync_place (Fall (Odd O)) (Rise (Even E))
  | Odd_rise_even_fall O E : In (O,E) (odd_even_neighbors c) ->
                             desync_place (Rise (Odd O)) (Fall (Even E))
  | Even_fall_odd_rise O E : In (O,E) (odd_even_neighbors c) ->
                             desync_place (Fall (Even E)) (Rise (Odd O)).

  Definition desynchronization : marked_graph (event even odd) :=
    {| place := desync_place
     ; init_marking := fun t1 t2 p => match p with
                                      | Even_fall _ => 1
                                      | Odd_rise  _ => 1
                                      | Even_rise_odd_fall _ _ _ => 1
                                      | Even_fall_odd_rise _ _ _ => 1
                                      | _ => 0
                                      end
    |}.

  Definition P_FD : tstate even odd :=
    fun l => match l with
             | Even _ => Transparent
             | Odd _  => Opaque
             end.

Inductive is_enabled_desync : event even odd -> marking desynchronization -> Prop :=
| Even_fall_enabled E (m : marking desynchronization) :
  0 < m _ _ (Even_fall E) ->
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m _ _ (Odd_rise_even_fall O E pf)) ->
  is_enabled_desync (Fall (Even E)) m
| Even_rise_enabled E (m : marking desynchronization) :
  0 < m _ _ (Even_rise E) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m _ _ (Odd_fall_even_rise E O pf)) ->
  is_enabled_desync (Rise (Even E)) m
| Odd_fall_enabled O (m : marking desynchronization) :
  0 < m _ _ (Odd_fall O) ->
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m _ _ (Even_rise_odd_fall E O pf)) ->
  is_enabled_desync (Fall (Odd O)) m
| Odd_rise_enabled O (m : marking desynchronization) :
  0 < m _ _ (Odd_rise O) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m _ _ (Even_fall_odd_rise O E pf)) ->
  is_enabled_desync (Rise (Odd O)) m

.



Lemma desync_is_enabled_equiv : forall e m,
    is_enabled_desync e m -> is_enabled desynchronization e m.
Proof.
  destruct e as [[O | E] | [O | E]];
    intros m; inversion 1; subst;
    intros e0 p;
    simpl in p;
    dependent destruction p;
    auto.
Qed.


Lemma is_enabled_desync_equiv : forall e m,
    is_enabled desynchronization e m ->
    is_enabled_desync e m.
Proof.
  intros e m Henabled.
  unfold is_enabled in *.
  destruct e as [[O | E] | [O | E]];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.


End Desynchronization.

Arguments P_FD {even odd}.
Arguments desynchronization {even odd}.

Section Counterexample.


  Inductive d_even := A | C.
  Inductive d_odd := B.
  Instance d_even_eq_dec : eq_dec d_even.
  Proof. 
    split. intros [ | ] [ | ];
      try (left; reflexivity); try (right; discriminate).
  Defined.
  Instance d_odd_eq_dec : eq_dec d_odd.
  Proof. 
    split. intros [ ] [ ];
      try (left; reflexivity).
  Defined.


  Variable next_state_A : unit -> value.
  Variable next_state_B : value -> value.
  Variable next_state_C : value -> value.

  Program Definition c : circuit d_even d_odd :=
    {| even_odd_neighbors := [ (A,B) ]
     ; odd_even_neighbors := [ (B,C) ]
     ; next_state_e := fun e =>
        match e with
        | A => fun _ => next_state_A tt
        | C => fun st => next_state_C (st (existT _ B _))
        end
     ; next_state_o := fun o =>
        match o with
        | B => fun st => next_state_B (st (existT _ A _))
        end
     |}.

  Lemma exists_not_forall : forall A (P : A -> Prop),
    (exists x, ~P x) ->
    ~ forall x, P x.
  Proof.
    intros A P [x H] contr.
    specialize (contr x).
    contradiction.
  Qed.


Lemma c_odd_even_neighbors : forall O E,
    In (O,E) (odd_even_neighbors c) ->
    O = B /\ E = C.
Proof.
    intros O E [H | []].
    inversion H.
    auto.
Qed.
Lemma c_even_odd_neighbors : forall E O,
    In (E,O) (even_odd_neighbors c) ->
    E = A /\ O = B.
Proof.
    intros E O [H | []].
    inversion H.
    auto.
Qed.


  Variable init_st : state (latch d_even d_odd).

  Definition counter_trace : trace d_even d_odd :=
    t_empty :> Rise (Odd B) :> Fall (Odd B) 
            :> Fall (Even C) :> Rise (Even C)
            :> Rise (Odd B) :> Fall (Even C)
            :> Fall (Even A) :> Rise (Even A)
            :> Fall (Odd B)
            :> Fall (Even A) :> Rise (Even A) :> Fall (Even A)
            :> Rise (Odd B) :> Fall (Odd B)
            :> Rise (Even C) :> Fall (Even C).

    
Ltac inversion_neighbors :=
  repeat match goal with
  | [ H : neighbor c _ _ |- _ ] =>
    inversion H; clear H
  | [ H : In (_, _) (odd_even_neighbors c) |- _ ] =>
    destruct (c_odd_even_neighbors _ _ H); try discriminate; subst; clear
  | [ H : In (_, _) (even_odd_neighbors c) |- _ ] =>
    destruct (c_even_odd_neighbors _ _ H); try discriminate; subst; clear
  end.

    

  Lemma counter_trace_well_formed : exists m, 
    { desynchronization c }⊢ counter_trace ↓ m.
  Proof.
    eexists.
    unfold counter_trace.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);

    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors;
       try (repeat (unfold fire at 1; simpl; auto); fail).
  Qed.    

 Lemma counter_eval :
    ⟨c,init_st,P_FD⟩⊢ counter_trace ↓ Even C ↦{Opaque}
        sync_eval c init_st 2 (Even C).
  Proof.
    unfold counter_trace.

    set (st := fun (l0 : latch d_even d_odd) =>
             match l0 with
             | Even A => next_state_A tt
             | Odd B => next_state_B (next_state_A tt)
             | Even C => next_state_C (next_state_B (next_state_A tt))
             end).
    apply async_opaque_fall with (st := st); [reflexivity | | reflexivity ].
    intros l' Hl'.
    inversion_neighbors.
    constructor; [ reflexivity | discriminate | ].
    apply async_opaque_fall with (st := st); [reflexivity | | reflexivity ].
    intros l' Hl'.
    inversion_neighbors.
    simpl.
    constructor; [ reflexivity | discriminate | ].
    apply async_opaque_fall with (st := st); [reflexivity | | reflexivity ].
    intros l' Hl'. inversion_neighbors.
  Qed.    

  (* In the Coq model, this is not technically true, since the value of A will
     always be next_state_A (), which is determinsitic. How to refine this??

     1. Let values in the formalization be abstract, and initialize them with a
   monad with internal state that can update over time.

     2. Encode environment?

     3. Consider only the 6-state cycle, which is closed.
 *)
  Hypothesis sync_2_3_neq :
    sync_eval c init_st 2 (Even C) <> sync_eval c init_st 3 (Even C).

  Theorem desynchronization_not_flow_equivalent :
    ~ flow_equivalence (desynchronization c) c init_st P_FD.
  Proof.
    unfold flow_equivalence.
    apply exists_not_forall.
    exists (Even C).
    apply exists_not_forall.
    exists counter_trace.
    apply exists_not_forall.
    exists (sync_eval c init_st 2 (Even C)).
    apply exists_not_forall.
    exists (counter_trace_well_formed).
    apply exists_not_forall.
    exists counter_eval.

    replace (num_events (Fall (Even C)) counter_trace) with 3 by reflexivity.

    apply sync_2_3_neq.
  Qed.


End Counterexample.
