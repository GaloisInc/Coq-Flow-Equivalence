Require Import Base.
Require Import Circuit.
Import Circuit_Tactics.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.

Require Import PeanoNat.

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(** * Definition of desynchronization marked graph *)
Section Desynchronization.


  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive desync_place : event (latch even odd) bool -> event (latch even odd) bool -> Set :=
  | latch_fall (l : latch even odd) : desync_place (Rise l) (Fall l)
  | latch_rise (l : latch even odd) : desync_place (Fall l) (Rise l)
  | neighbor_fall : forall l l', neighbor c l l' -> desync_place (Rise l) (Fall l')
  | neighbor_rise : forall l l', neighbor c l l' -> desync_place (Fall l') (Rise l).

  Definition desynchronization : marked_graph (event (latch even odd) bool) :=
    {| place := desync_place
     ; init_marking := fun t1 t2 p => match p with
                                      | latch_rise (Even _) => 1
                                      | latch_fall (Odd _) => 1
                                      | neighbor_fall _ _ _ => 1
                                      | _ => 0
                                      end
    |}.

(** * Specialized is_enabled constraint *)
Inductive is_enabled_desync : event (latch even odd) bool -> marking desynchronization -> Prop :=
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
  destruct e as [[O | E] v];
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
  destruct e as [[O | E] [|]];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.


End Desynchronization.

Arguments desynchronization {even odd}.

  Lemma exists_not_forall : forall A (P : A -> Prop),
    (exists x, ~P x) ->
    ~ forall x, P x.
  Proof.
    intros A P [x H] contr.
    specialize (contr x).
    contradiction.
  Qed.


(** * Definition of circuit that demonstrates counterexample *)

(** Pipeline SRC <-> A -> B -> C <-> SNK *)
Section EnvPipeline. 

  Inductive even := A | C.
  Inductive odd := SRC | B | SNK.


  Definition eEven : even -> latch even odd := Even.
  Coercion eEven : even >-> latch.
  Definition eOdd : odd -> latch even odd := Odd.
  Coercion eOdd : odd >-> latch.

  Instance even_eq_dec : eq_dec even.
  Proof. 
    split. intros [ | ] [ | ];
      try (left; reflexivity); try (right; discriminate).
  Defined.
  Instance odd_eq_dec : eq_dec odd.
  Proof. 
    split. intros [ ] [ ];
      try (left; reflexivity); try (right; discriminate).
  Defined.

  (** The pipeline increments the value received at every stage *)
  Definition inc_value (v : value) : value :=
    match v with
    | Num n => Num (1+n)
(*    | Bit0 => Bit1
    | Bit1 => Bit0*)
    | X => Num 0
    end.
  Lemma inc_value_inj : forall v1 v2,
    inc_value v1 = inc_value v2 ->
    v1 = v2.
  Proof.
    intros [x | ] [y | ] Heq; auto; simpl in *;
      inversion Heq; auto.
  Qed.

  Program Definition c : circuit even odd :=
    {| even_odd_neighbors := (A,SRC) :: (A,B) :: (C,SNK) :: nil
     ; odd_even_neighbors := (SRC,A) :: (B,C) :: (SNK,C) :: nil
     ; next_state_e := fun e =>
        match e with
        | A => fun st => st (existT _ SRC _)
        | C => fun st => inc_value (st (existT _ B _))
        end
     ; next_state_o := fun o =>
        match o with
        | SRC => fun st => inc_value (st (existT _ A _))
        | B => fun st   => inc_value (st (existT _ A _))
        | SNK => fun st => Num 0
        end
     |}.
  Definition st0 : state (latch even odd) := fun l => X.


  (** ** Lemmas about the behavior of each latch *)

  Lemma sync_A : forall n,
    sync_eval c st0 n A = match n with
                          | 0 => X
                          | S n' => Num n'
                          end.
  Proof.
    induction n; auto.
    * simpl; unfold odd_state; simpl; unfold even_state; simpl.
      unfold eEven in IHn.
      rewrite IHn.
      unfold inc_value.
      destruct n; auto. 
  Qed.

  Lemma sync_B : forall n,
    sync_eval c st0 (S n) B = inc_value (sync_eval c st0 n A).
  Proof.
    induction n; auto. 
  Qed.

  Lemma sync_C : forall n, n > 0 ->
    sync_eval c st0 n C = inc_value (sync_eval c st0 n B).
  Proof.
    induction n; intros Hn; auto.
    find_contradiction.
  Qed.

  Lemma sync_neq : forall n, sync_eval c st0 n C <> sync_eval c st0 (S n) C.
  Proof.
    induction n; auto.
    * simpl. discriminate.
    * repeat (rewrite sync_C; [ | omega]).
      repeat rewrite sync_B.
      repeat rewrite sync_A.

      intros H.
      repeat apply inc_value_inj in H.
      destruct n; [discriminate | ].
      inversion H. omega.
  Qed.


  (** ** Counterexample trace *)
  Definition counter_trace : trace (latch even odd) bool :=
    t_empty ▶ Fall SNK ▶ Rise C
            ▶ Fall B
            ▶ Fall C
            ▶ Rise SNK ▶ Fall SNK ▶ Rise C
            ▶ Rise B
            ▶ Fall C
(** The trace illustrated in the figure continues as follows *)
(*
            ▶ Rise SRC ▶ Fall SRC ▶ Rise A
            ▶ Fall B
            ▶ Fall A
            ▶ Rise SRC ▶ Fall SRC ▶ Rise A
            ▶ Rise B
            ▶ Fall A
            ▶ Fall B
            ▶ Rise SNK ▶ Fall SNK ▶ Rise C
            ▶ Rise SRC ▶ Fall SRC ▶ Rise A
            ▶ Fall C
            ▶ Fall A.
*).


  (** The counterexample is consistent with the desynchronization protocol. *)
  Lemma counter_trace_well_formed : exists m, 
    [ desynchronization c ]⊢ counter_trace ↓ m.
  Proof.
    eexists.
    unfold counter_trace.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);
    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors;
       try (repeat (unfold fire at 1; simpl; auto); fail).
  Qed.


  (** The counterexample results in C having the value C_1 instead of C_2. *)
 Lemma counter_eval :
    ⟨c,st0⟩⊢ counter_trace ↓ C ↦{Opaque}
        sync_eval c st0 1 C.
  Proof.
    unfold counter_trace. unfold eEven. unfold eOdd.
    repeat async_constructor; reflexivity.
  Qed.

  (** ** Proof that desynchronization is violated *)
  Theorem desynchronization_not_flow_equivalent2 :
    ~ flow_equivalence (desynchronization c) c st0.
  Proof.
    unfold flow_equivalence.
    apply exists_not_forall.
    exists C.
    apply exists_not_forall.
    exists counter_trace.
    apply exists_not_forall.
    exists (sync_eval c st0 1 C).
    apply exists_not_forall.
    exists (counter_trace_well_formed).
    apply exists_not_forall.
    exists counter_eval.

    replace (num_events (Fall C) counter_trace) with 2 by reflexivity.
    apply sync_neq.
  Qed.


End EnvPipeline.

