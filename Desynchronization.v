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
  | latch_fall (l : latch even odd) : desync_place (Rise l) (Fall l)
  | latch_rise (l : latch even odd) : desync_place (Fall l) (Rise l)
  | neighbor_fall : forall l l', neighbor c l l' -> desync_place (Rise l) (Fall l')
  | neighbor_rise : forall l l', neighbor c l l' -> desync_place (Fall l') (Rise l).

  Definition desynchronization : marked_graph (event even odd) :=
    {| place := desync_place
     ; init_marking := fun t1 t2 p => match p with
                                      | latch_rise _ => 1
                                      | neighbor_fall (Even _) (Odd _) _ => 1
                                      | neighbor_rise (Odd _) (Even _) _ => 1
                                      | _ => 0
                                      end
    |}.

  Definition P_D : tstate even odd :=
    fun l => match l with
             | Even _ => Opaque
             | Odd _  => Opaque
             end.

Inductive is_enabled_desync : event even odd -> marking desynchronization -> Prop :=
| latch_fall_enbled l (m : marking desynchronization) :
    0 < m _ _ (latch_fall l) ->
    (forall l0 (pf : neighbor c l0 l), 0 < m _ _ (neighbor_fall l0 l pf)) ->
    is_enabled_desync (Fall l) m
| latch_rise_enabled l (m : marking desynchronization) :
    0 < m _ _ (latch_rise l) ->
    (forall l' (pf : neighbor c l l'), 0 < m _ _ (neighbor_rise l l' pf)) ->
    is_enabled_desync (Rise l) m
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

Arguments P_D {even odd}.
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
  Variable init_st : state (latch d_even d_odd).


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

  Lemma sync_2_3_neq :
    sync_eval c init_st 1 (Even C) <> sync_eval c init_st 2 (Even C).
  simpl.



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




  Definition counter_trace : trace d_even d_odd :=
    t_empty ▷ Rise (Odd B)
            ▷ Rise (Even C)
            ▷ Fall (Odd B)
            ▷ Fall (Even C)
            ▷ Rise (Even C)
            ▷ Rise (Odd B)
            ▷ Fall (Even C)
(* should be an error here *)
(*
            ▷ Rise (Even A)
            ▷ Fall (Odd B)
            ▷ Fall (Even A)
            ▷ Rise (Even A)
            ▷ Rise (Odd B)
            ▷ Fall (Even A)
            ▷ Fall (Odd B)
            ▷ Rise (Even C)
            ▷ Rise (Even A)
            ▷ Fall (Even C)
            ▷ Fall (Even A)
*).

    
Ltac inversion_neighbors :=
  repeat match goal with
  | [ H : neighbor c _ _ |- _ ] =>
    inversion H; clear H
  | [ H : In (_, _) (odd_even_neighbors c) |- _ ] =>
    destruct (c_odd_even_neighbors _ _ H); try discriminate; subst; clear
  | [ H : In (_, _) (even_odd_neighbors c) |- _ ] =>
    destruct (c_even_odd_neighbors _ _ H); try discriminate; subst; clear
  end;
  match goal with
  | [ H : neighbor c _ _ |- _ ] =>
    inversion H
  end.

    

  Lemma counter_trace_well_formed : exists m, 
    { desynchronization c }⊢ counter_trace ↓ m.
  Proof.
    eexists.
    unfold counter_trace.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);
    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors.
(*       try (repeat (unfold fire at 1; simpl; auto); fail).*)
  Admitted.

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
