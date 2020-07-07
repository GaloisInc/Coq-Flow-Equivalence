Require Export Base.
Require Export MarkedGraph.

Require Import Monad.
Import MonadNotations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.

Require Import Lia (* Linear integer arithmetic tactics *).


Section Circuit.

(** Latches are either even or odd *)
Variable even odd : Set.

(** Equality over latches is decidable *)
Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.  

(** * Latches, events, and traces *)
Section LatchSequence.

  (** Latches are either even or odd *)
  Inductive latch : Set := 
  | Odd : odd -> latch
  | Even : even -> latch
  .


  (** An event is a pair of a key and a value. *)
  Inductive event key val :=
  | Event : key -> val -> event key val.
  
  (* OLD DEFINITION:
   (** Events are either the rise or fall of a latch's clock *)
   Inductive event : Set :=
  | Rise : latch -> event
  | Fall : latch -> event
  . *)
  Arguments Event {key val}.

  (** A trace is a list of events *)
  Definition trace latch val := tail_list (event latch val).


  (** Latches need not hold single bits; they can also hold numeric values, the
  symbolic value X (don't care), and the symbolic value Z (floating). *)
  Inductive value := 
  | Num : nat -> value
  | Bit0 : value
  | Bit1 : value
  | X  : value.

  Definition Rise l : event latch bool := Event l true.
  Definition Fall l : event latch bool := Event l false.
  Definition val_to_nat (v : value) : nat :=
  match v with
  | Num n => n
  | Bit0  => 0
  | Bit1  => 1
  | X     => 0
  end.



  (** A transparency state records whether latches are currently transparent or opaque. *)
  Inductive transparency := Transparent | Opaque.
  Definition tstate := latch -> transparency.



  (** ** Decidability of values, latches, and events *)


  Instance value_eq_dec : eq_dec value.
  Proof.
    constructor. intros [x | | |] [y | | |];
    try (left; reflexivity);
    try (right; discriminate).
    compare x y; auto.
    right. congruence.
  Defined.
  Instance latch_eq_dec : eq_dec latch.
  Proof.
    split.
    intros [o1 | e1] [o2 | e2];
    try (right; inversion 1; fail).
    * destruct Hodd as [H].
      destruct (H o1 o2);
        [subst; left; reflexivity | right; inversion 1; contradiction].
    * destruct Heven as [H].
      destruct (H e1 e2);
        [subst; left; reflexivity | right; inversion 1; contradiction].
  Defined.
  Instance event_eq_dec {key val} `{eq_dec key} `{eq_dec val} : eq_dec (event key val).
  Proof.
    constructor.
    intros [l1 v1] [l2 v2];
      try (left; reflexivity);
      try (right; inversion 1; fail).
    destruct (Dec l1 l2); destruct (Dec v1 v2); subst;
      try (left; reflexivity);
    try (right; inversion 1; contradiction).
(*. OLD PROOF:
    intros [l1 | l1] [l2 | l2].
    * destruct (Dec l1 l2); [ subst; auto | ].
      right. inversion 1. contradiction.
    * right. inversion 1.
    * right. inversion 1.
    * destruct (Dec l1 l2); [ subst; auto | ].
      right. inversion 1. contradiction.
*)
  Defined.


  (** Calculate the number of occurrences of an event in a trace *)
  Fixpoint num_events {A} `{eq_dec A} (e : event latch A) (t : trace latch A) : nat :=
    match t with
    | t_empty => 0
    | t' ▶ e' => if e =? e'
                 then 1 + num_events e t'
                 else num_events e t'
    end.



  (** Calculate the set of transparent latches after executing the trace t *)
  Fixpoint transparent (t : trace latch bool) : tstate :=
    match t with
    | t_empty => fun l => match l with
                          | Even _ => Opaque
                          | Odd _ => Transparent
                          end
    | t' ▶ e => fun l => if Rise l =? e then Transparent
                              else if Fall l =? e then Opaque
                              else transparent t' l
    end.



End LatchSequence.

Existing Instance latch_eq_dec.
Existing Instance value_eq_dec.
Existing Instance event_eq_dec.


(** * Circuits *)
Section Circuits.

  (** A state (e.g. of a set of latches) maps each of those latches to values *)
  Definition state (tp : Set) := tp -> value.

  Definition update {X : Set} `{eq_dec X} (σ : state X) (x : X) (v : value) : state X :=
    fun y => if x =? y then v
             else σ y.
  Definition update_event {X : Set} `{eq_dec X} (σ : state X) (e : event X value) : state X :=
    match e with
    | Event _ _ i v => update σ i v
    end.

  (** Restrict a state to only its even or odd members. *)
  Definition odd_state {P : odd -> Prop}
                       (s : state latch) : state {o : odd & P o} :=
    fun o => s (Odd (projT1 o)).
  Definition even_state {P : even -> Prop}
                        (s : state latch) : state {e : even & P e} :=
    fun o => s (Even (projT1 o)).

  (** A circuit consists of (1) lists of its even-odd and odd-even neighbors;
  and (2) for each latch, a next_state function. *)
  Record circuit : Set :=
  { even_odd_neighbors : list (even * odd)
  ; odd_even_neighbors : list (odd * even)
  ; next_state_e (e : even) : state {o : odd  & In (o,e) odd_even_neighbors} -> value
  ; next_state_o  (o : odd)  : state {e : even & In (e,o) even_odd_neighbors} -> value
  }.

  (** A generalization of even-odd and odd-even neighbors *)
  Inductive neighbor c : latch -> latch  -> Prop :=
  | EO_neighbor E O : In (E,O) (even_odd_neighbors c) -> neighbor c (Even E) (Odd O)
  | OE_neighbor O E : In (O,E) (odd_even_neighbors c) -> neighbor c (Odd O) (Even E).

  (** The next-state function *)
  Definition next_state (c : circuit) (st : state latch) (l : latch) : value :=
    match l with
    | Even e => next_state_e c e (odd_state st)
    | Odd o  => next_state_o c o (even_state st)
    end.

  (** * Asynchronous execution *)

  Reserved Notation "⟨ c , st ⟩⊢ t ↓ l ↦{ O } v" (no associativity, at level 90).
  Inductive async (c : circuit) (st0 : state latch)
                    : trace latch bool -> latch -> transparency -> value -> Prop :=
  | async_nil : forall E, 
    ⟨c,st0⟩⊢ t_empty ↓ Even E ↦{Opaque} st0 (Even E)

  | async_transparent : forall l t st v,
    transparent t l = Transparent ->
    (forall l', neighbor c l' l -> ⟨c,st0⟩⊢ t ↓ l' ↦{transparent t l'} st l') ->
    v = next_state c st l ->
    ⟨c,st0⟩⊢ t ↓ l ↦{Transparent} v

  | async_opaque : forall l e t' v,
    e <> Fall l ->
    transparent (t' ▶ e) l = Opaque ->
    ⟨c,st0⟩⊢ t' ↓ l ↦{Opaque} v ->
    ⟨c,st0⟩⊢ t' ▶ e ↓ l ↦{Opaque} v
 
  | async_opaque_fall : forall l e t' v st,
    e = Fall l ->
    (forall l', neighbor c l' l -> ⟨c,st0⟩⊢ t' ↓ l' ↦{transparent t' l'} st l') ->
    v = next_state c st l ->
    ⟨c,st0⟩⊢ t' ▶ e ↓ l ↦{Opaque} v

  where "⟨ c , st ⟩⊢ t ↓ l ↦{ O } v" := (async c st t l O v).

  (** ** Helper lemmas *)
Lemma async_b : forall c st0 l O t v,
    ⟨c,st0⟩⊢ t ↓ l ↦{O} v ->
    transparent t l = O.
Proof.
  intros c st0 l O t v H.
  induction H; auto. simpl.
  subst. simpl. 
  compare_next; auto.
Qed.

Lemma next_state_eq : forall c st1 st2 l,
  (forall l', neighbor c l' l -> st1 l' = st2 l') ->
  next_state c st1 l = next_state c st2 l.
Proof.
  intros c st1 st2 l H.
  destruct l as [O | E]; simpl; apply f_equal; unfold even_state, odd_state;
    apply functional_extensionality; intros [l' Hl']; simpl;
    apply H; constructor; auto.
Qed.


Lemma async_injective : forall c st0 l b1 t v1,
    ⟨c,st0⟩⊢ t ↓ l ↦{b1} v1 ->
    forall b2 v2, ⟨c,st0⟩⊢ t ↓ l ↦{b2} v2 ->
    v1 = v2.
Proof.
  intros c st0 l b1 t v1 H1.
  induction H1; intros b2 v2 H2';
    inversion H2'; subst; simpl in *; find_contradiction; auto.

  * apply next_state_eq.
    intros l' Hl'.
    eapply H1; eauto.
  * compare_next.
  * compare (Rise l) e.
    eapply IHasync; eauto.
  * compare_next.
  * apply next_state_eq.
    intros l' Hl'.
    eapply H1; eauto.
Qed.

 
  (** * Synchronous execution *)

  (** Single unit of update for odd/even latches *)

  Definition sync_update_odd (c : circuit) (st : state latch) : state latch :=
    fun l =>
    match l with
    | Odd o => next_state_o c o (even_state st)
    | Even e => st (Even e)
    end.

  Definition sync_update_even (c : circuit) (st : state latch) : state latch :=
    fun l =>
    match l with
    | Odd o => st (Odd o)
    | Even e => next_state_e c e (odd_state st)
    end.

  (** Main definition of synchronous execution *)

  Fixpoint sync_eval (c : circuit) (st : state latch) (n : nat) : state latch :=
    match n with
    | 0 => st
    | S n' => sync_update_even c (sync_update_odd c (sync_eval c st n'))
    end.

  (** ** Helper lemmas *)
  Lemma sync_eval_odd_0 : forall c st E,
        sync_eval c st 0 (Even E) = st (Even E).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma sync_eval_even : forall (c : circuit) (st : state latch) n E,
        sync_eval c st (S n) (Even E) = next_state_e c E (odd_state (sync_eval c st (S n))).
  Proof. auto. Qed.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = next_state_o c O (even_state (sync_eval c st n)).
  Proof. auto. Qed.

  Lemma sync_eval_S : forall c init_st n l st,
    (forall l', neighbor c l' l ->
                 st l' = match l with
                        | Even _ => sync_eval c init_st (S n) l'
                        | Odd _  => sync_eval c init_st n l'
                        end) ->
    sync_eval c init_st (S n) l = next_state c st l.
  Proof.
    intros c init_st n [O | E] st Hst; subst.
      + simpl. apply f_equal. apply functional_extensionality. intros [E HE]. simpl.
        unfold even_state. simpl. rewrite Hst; auto. constructor; auto.
      + simpl. apply f_equal. apply functional_extensionality. intros [O HO]. simpl.
        unfold odd_state. simpl. rewrite Hst; auto. constructor; auto.
  Qed.

  Lemma sync_eval_gt : forall c init_st n l st,
    0 < n ->
    (forall l', neighbor c l' l ->
                 st l' = match l with
                        | Even _ => sync_eval c init_st n l'
                        | Odd _  => sync_eval c init_st (n-1) l'
                        end) ->
    sync_eval c init_st n l = next_state c st l.
  Proof.
    intros.
    destruct n; [find_contradiction | ].
    replace (S n - 1) with n in * by omega.
    apply sync_eval_S; auto.
  Qed.



End Circuits.

Notation "⟨ c , st  ⟩⊢ t ↓ l ↦{ O } v" := (async c st t l O v) (no associativity, at level 90).



(** * Flow equivalence 

A marked graph [M] is *flow equivalent* to a circuit [c] at state [st0] if, for all traces [t] accepted by the marked graph [M]: if [l] maps to [v] in the state obtained by asynchronously executing [t] in the circuit [c] from the state [st0], then [v] is the ith *synchronous* value latched by [l], where [i] is the number of occurrences of [Fall l] in [t].
  

*)



Section FlowEquivalence.

  Definition flow_equivalence (M : marked_graph (event latch bool))
                              (c : circuit) 
                              (st0 : state latch) :=
    forall l t v,
      (exists m, [M]⊢ t ↓ m) ->
      ⟨c,st0⟩⊢ t ↓ l ↦{Opaque} v ->
       v = sync_eval c st0 (num_events (Fall l) t) l.


End FlowEquivalence.

End Circuit.

(* begin hide *)
Arguments flow_equivalence {even odd Heven Hodd} M.

Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments transparent {even odd Heven Hodd}.

Arguments neighbor {even odd}.

Arguments Event {key val}.
Arguments Rise {even odd}.
Arguments Fall {even odd}.
Arguments num_events {even odd Heven Hodd A Adec} : rename.

Arguments odd_even_neighbors {even odd}.
Arguments even_odd_neighbors {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.

Arguments next_state {even odd}.

Arguments next_state_o {even odd}.
Arguments next_state_e {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.
Arguments sync_eval {even odd}.
Arguments is_enabled {transition}.

(*Arguments fire_tstate {even odd Heven Hodd}.*)

Existing Instance nat_eq_dec.
Existing Instance value_eq_dec.
Existing Instance event_eq_dec.
 
Arguments async {even odd Heven Hodd}.
Notation "⟨ c , st ⟩⊢ t ↓ l ↦{ O } v" := (async c st t l O v) 
          (no associativity, at level 90).
(* end hide *)

(** * Tactics *)
Module Circuit_Tactics.

Lemma neighbor_neq : forall {even odd} (c : circuit even odd) l l',
    neighbor c l l' -> l <> l'.
Proof.
  intros even odd c l l' H.
  destruct H; discriminate.
Qed.

(** Use [find_event_contradiction] when there is a hypothesis that contains a
contradiction regarding events. *)
Ltac find_event_contradiction :=
  try match goal with
      | [ H : Fall _ = Rise _ |- _ ] => inversion H 
      | [ H : Fall (Even _) = Fall (Odd _) |- _ ] => inversion H
      | [ H : Fall (Odd _) = Fall (Even _) |- _ ] => inversion H
      | [ H : Rise _ = Fall _ |- _ ] => inversion H
      | [ H : Rise (Even _) = Rise (Odd _) |- _ ] => inversion H
      | [ H : Rise (Odd _) = Rise (Even _) |- _ ] => inversion H
      | [ H : neighbor _ ?l ?l'
        , H' : Rise _ = Rise _ |- _ ] =>
        absurd (l = l'); [ apply (neighbor_neq _ _ _ H) | inversion H'; auto ]
      | [ H : neighbor _ ?l ?l'
        , H' : Fall _ = Fall _ |- _ ] =>
        absurd (l = l'); [ apply (neighbor_neq _ _ _ H) | inversion H'; auto ]
      | [ H : neighbor _ (Odd _ ) (Odd _) |- _ ] => inversion H
      | [ H : neighbor _ (Even _ ) (Even _) |- _ ] => inversion H
      end.

(** Specialize hypotheses generated by is_enabled constraints (instantiated by
the tactic [get_enabled_constraints] in [RiseDecoupled.v] and [FallDecoupled.v] *)
Ltac specialize_enabled_constraints :=
  repeat match goal with
  | [ HEO : In (_,_) (even_odd_neighbors _)
    , H : forall x, In _ (even_odd_neighbors ?c) -> _
    |- _] => specialize (H _ HEO)
  | [ HEO : In (_,_) (even_odd_neighbors _)
    , H : forall x y, In _ (even_odd_neighbors _) -> _
    |- _] => specialize (H _ _ HEO)
  | [ HOE : In (_,_) (odd_even_neighbors _)
    , H : forall x, In _ (odd_even_neighbors _) -> _
    |- _] => specialize (H _ HOE)
  | [ HOE : In (_,_) (odd_even_neighbors _)
    , H : forall x y, In _ (odd_even_neighbors _) -> _
    |- _] => specialize (H _ _ HOE)

  | [ Hneighbor : neighbor _ ?l ?l'
    , H' : forall x, neighbor _ ?l x -> _
    |- _ ] => specialize (H' l' Hneighbor)
  | [ Hneighbor : neighbor _ ?l ?l'
    , H' : forall x, neighbor _ x ?l' -> _
    |- _ ] => specialize (H' l Hneighbor)
  | [ Hneighbor : neighbor _ ?l ?l'
    , H' : forall x y, neighbor _ _ _ -> _
    |- _ ] => specialize (H' _ _ Hneighbor)

  | [ O : ?odd , HO : forall (o' : ?odd), _ = _ |- _ ] => specialize (HO O)
  | [ E : ?even , HE : forall (e' : ?even), _ = _ |- _ ] => specialize (HE E)
  | [ O : ?odd , HO : forall (o' : ?odd), _ < _ |- _ ] => specialize (HO O)
  | [ E : ?even , HE : forall (e' : ?even), _ < _ |- _ ] => specialize (HE E)
  | [ O : ?odd , Hl : forall (l : latch _ _), _ = _ |- _ ] => specialize (Hl (Odd O))
  | [ E : ?even , Hl : forall (l : latch _ _), _ = _ |- _ ] => specialize (Hl (Even E))
  | [ l : latch _ _ , Hl : forall (l : latch _ _), _ = _ |- _ ] => specialize (Hl l)
  | [ O : ?odd , Hl : forall (l : latch _ _), _ < _ |- _ ] => specialize (Hl (Odd O))
  | [ E : ?even , Hl : forall (l : latch _ _), _ < _ |- _ ] => specialize (Hl (Even E))
  | [ l : latch _ _ , Hl : forall (l : latch _ _), _ < _ |- _ ] => specialize (Hl l)

  | [ H : ?P, H' : ?P -> _ |- _ ] => specialize (H' H)
  end.

(** [inversion_neighbors] can be used when you have a hypothesis of the form
[neighbor c l1 l2] and you want to do case analysis on whether the neighbors are
even-odd or odd-even *)
Ltac inversion_neighbors :=
  match goal with
  | [ H : neighbor _ _ _ |- _ ] =>
    inversion H; subst
  end;
  repeat match goal with
  | [ H : In (_, _) (odd_even_neighbors _) |- _ ] => simpl in H
  | [ H : In (_, _) (even_odd_neighbors _) |- _ ] => simpl in H
  | [ H : (_,_) = (_,_) \/ _ |- _ ] => destruct H as [H | H]; [inversion H; subst | ]
  | [ H : False |- _ ] => contradiction 
  end.


  (* Solve goals of the form ⟨c,st⟩⊢ t ↓ l ↦ v *)
  Ltac async_constructor :=
    match goal with
    | [ |- ⟨_,_⟩⊢ _ ↓ _ ↦{ Transparent } _] =>
      eapply async_transparent;
        [reflexivity | intros l' Hl'; inversion_neighbors; clear Hl'; simpl | ]
    | [ |- ⟨_,_⟩⊢ _ ▶ Fall ?l ↓ ?l ↦{ Opaque } _ ] =>
      eapply async_opaque_fall; 
        [reflexivity | intros l' Hl'; inversion_neighbors; clear Hl'; simpl | ]
    | [ |- ⟨_,_⟩⊢ _ ▶ _ ↓ _ ↦{ Opaque } _ ] =>
      eapply async_opaque; [try discriminate | reflexivity | ]
    | [ |- ⟨_,_⟩⊢ t_empty ↓ _ ↦{ Opaque } _ ] =>
      apply async_nil; reflexivity
    end.
End Circuit_Tactics.
