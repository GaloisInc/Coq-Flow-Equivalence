Require Export Base.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.


Inductive value := 
| B0 : value
| B1 : value
| X  : value
| Z  : value.


Section LatchSequence.

  Context (even odd : Set).
  Inductive latch : Set := 
  | Odd : odd -> latch
  | Even : even -> latch
  .
  Arguments latch : clear implicits.
  Inductive event : Set :=
  | Pos : latch -> event
  | Neg : latch -> event
  . 

  Inductive CLK : Set := CLK0 | CLK1.
  Definition step_CLK (clk : CLK) : CLK :=
    match clk with
    | CLK0 => CLK1
    | CLK1 => CLK0
    end.

  Definition latch_set := latch -> bool.

  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.  

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
  Instance event_eq_dec : eq_dec event.
  Proof.
    constructor.
    intros [l1 | l1] [l2 | l2].
    * destruct (Dec l1 l2); [ subst; auto | ].
      right. inversion 1. contradiction.
    * right. inversion 1.
    * right. inversion 1.
    * destruct (Dec l1 l2); [ subst; auto | ].
      right. inversion 1. contradiction.
  Defined.


  Definition event_refers_to_latch (e : event) (l : latch) : bool :=
    match e with
    | Pos l' => eqb l l'
    | Neg l' => eqb l l'
    end.

  Definition event_becomes_transparent (e : event) : bool :=
  match e with
  | Pos _ => true
  | Neg _  => false
  end.

  Definition step_latch_set (e : event) (t : latch_set) : latch_set :=
    fun l => if event_refers_to_latch e l
             then event_becomes_transparent e
             else t l.

  Definition is_even (l : latch) : bool :=
  match l with
  | Even _ => true
  | _ => false
  end.
  Definition is_odd (l : latch) : bool := negb (is_even l).


  (* A latch sequence is a snoc-list of events, ending with a set of transparent latches. *)
  Inductive latch_sequence : Set :=
  | ls_empty_async (transparent_set : latch_set) : latch_sequence
  | ls_async (e : event)
             (next : latch_sequence)
           : latch_sequence
  .

  (* Calculate the set of transparent latches after executing the latch sequence s *)
  Fixpoint is_transparent (s : latch_sequence) : latch_set :=
    match s with
    | ls_empty_async ls  => ls
    | ls_async e s' => step_latch_set e (is_transparent s')
    end.


  Fixpoint num_events (e : event) (s : latch_sequence) : nat :=
    match s with
    | ls_empty_async _ => 0
    | ls_async e' s' => if e =? e'
                        then 1 + num_events e s'
                        else num_events e s'
    end.


End LatchSequence.

Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments is_transparent {even odd Heven Hodd}.

Arguments ls_empty_async {even odd}.
Arguments ls_async {even odd}.

Arguments Pos {even odd}.
Arguments Neg {even odd}.
Arguments num_events {even odd Heven Hodd}.

(*************)
(** Circuits *)
(*************)

Section Circuits.

  Variable even odd : Set.
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.  

  Definition state (tp : Set) := tp -> value.

  Definition odd_state {P : odd -> Prop}
                       (s : state (latch even odd)) : state {o : odd & P o} :=
    fun o => s (Odd (projT1 o)).
  Definition even_state {P : even -> Prop}
                        (s : state (latch even odd)) : state {e : even & P e} :=
    fun o => s (Even (projT1 o)).

  Record circuit : Set :=
  { even_odd_neighbors : list (even * odd)
  ; odd_even_neighbors : list (odd * even)
  ; evenF : forall (e : even), state {o : odd & In (o,e) odd_even_neighbors} -> value
  ; oddF : forall (o : odd), state {e : even & In (e,o) even_odd_neighbors} -> value
  }.

  Definition get_latch_value (c : circuit)
                             (prev : state (latch even odd))
                             (l : latch even odd) : value :=
    match l with
    | Even e => evenF c e (odd_state prev)
    | Odd o  => oddF c o (even_state prev)
    end.


  (** Async execution *)

  Definition state_respects_transparencies (c : circuit)
                                        (s : latch_sequence even odd)
                                        (st : state (latch even odd)) :=
    forall l, is_transparent s l = true -> st l = get_latch_value c st l.

  Definition state_respects_opacities (s : latch_sequence even odd)
                                      (st1 st2 : state (latch even odd)) :=
    forall l, is_transparent s l = false -> st1 l = st2 l.


  Reserved Notation " c '⊢' st '⇒' s '⇒' st' " (no associativity, at level 80).
  Inductive eval (c : circuit) (init : state (latch even odd))
               : latch_sequence even odd -> state (latch even odd) -> Prop :=
  | eval_nil lset : 
    state_respects_transparencies c (ls_empty_async lset) init ->
    c ⊢ init ⇒ ls_empty_async lset ⇒ init
  | eval_cons e s st st' :
    c ⊢ init ⇒s⇒ st ->
    state_respects_opacities (ls_async e s) st' st ->
    state_respects_transparencies c (ls_async e s) st' ->
    c ⊢ init ⇒ls_async e s⇒ st'
  where " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st').

  Lemma eval_transparent : forall c st s st',
    c ⊢ st ⇒ s ⇒ st' ->
    forall l, is_transparent s l = true -> st' l = get_latch_value c st' l.
  Proof.
    intros c st s st' H.
    induction H; intros invariant l; auto.
  Qed.


 
  (** Syncronous execution *)
  Fixpoint sync_even (c : circuit) (st : state (latch even odd)) (n : nat)
                            {struct n} : state even :=
    fun E =>
    evenF c E (fun O => match n with
                        | 0 => st (Odd (projT1 O))
                        | S n' => oddF c (projT1 O) (fun E => sync_even c st n' (projT1 E))
                        end).
  Fixpoint sync_odd (c : circuit) (st : state (latch even odd)) (n : nat) 
                            {struct n} : state odd :=
    fun O =>
    match n with
    | 0 => st (Odd O)
    | S n' => oddF c O (fun E => sync_even c st n' (projT1 E))
    end.
  Lemma sync_even_eq : forall c st n E,
    sync_even c st n E = evenF c E (fun O => sync_odd c st n (projT1 O)).
  Proof.
    intros.
    induction n.
    * simpl. reflexivity.
    * simpl. reflexivity. 
  Qed.

  Definition sync_eval (c : circuit) (st : state (latch even odd)) (n : nat) 
                   : state (latch even odd) := fun l =>
    match l with
    | Even E => sync_even c st n E
    | Odd o  => sync_odd c st n o
    end.

  Lemma sync_eval_even : forall (c : circuit) (st : state (latch even odd)) n E,
        sync_eval c st n (Even E) = evenF c E (odd_state (sync_eval c st n)).
  Proof.
    intros c st n E. simpl. 
    rewrite sync_even_eq. reflexivity.
  Qed.
  Lemma sync_eval_odd_0 : forall c st O,
        sync_eval c st 0 (Odd O) = st (Odd O).
  Proof.
    reflexivity.
  Qed.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = oddF c O (even_state (sync_eval c st n)).
  Proof.
    reflexivity.
  Qed.
  Lemma sync_eval_even_0_opp : forall c st E,
        sync_eval c st 0 (Even E) = st (Even E).
  Admitted.
  Lemma sync_eval_even_opp : forall c st n E,
        sync_eval c st (S n) (Even E) = evenF c E (odd_state (sync_eval c st n)).
  Admitted.
  Lemma sync_eval_odd_opp : forall c st n O,
        sync_eval c st n (Odd O) = oddF c O (even_state (sync_eval c st n)).
  Admitted.

End Circuits.

Arguments eval {even odd Heven Hodd}.
Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).

Arguments odd_even_neighbors {even odd}.
Arguments even_odd_neighbors {even odd}.


Class Enumerable (A : Set) :=
  { enumerate : list A }.


(******************)
(** Marked graphs *)
(******************)

Section MarkedGraphs.

  Context (events : Set).
  Context (transitions : Set).
  Context `{Hevents : eq_dec events}.
  Context `{Htransitions : eq_dec transitions}.
(*  Context `{Enumerable transitions}. *)

  Definition marking := transitions -> nat.

  Record marked_graph : Set :=
  { input_event_output : list (events * transitions * events) }.
  Definition input_event (M : marked_graph) : list (events * transitions) :=
    fmap fst (input_event_output M).
  Definition output_event (M : marked_graph) : list (transitions * events) :=
    fmap (fun ete => (snd (fst ete),snd ete)) (input_event_output M).

  Definition in_transitions (M : marked_graph) (e : events) : list transitions :=
    let f := fun ete => if snd ete =? e then [snd (fst ete)] else [] in
    flat_map f (input_event_output M).

  Definition enabled (e : events)
                     (M : marked_graph)
                     (m : marking)
                   : bool :=
    forallb (fun t => Nat.ltb 0 (m t)) (in_transitions M e).
  Definition is_enabled (M : marked_graph) (e : events) (m : marking) :=
    enabled e M m = true.

  (* An event should only fire if the caller has independently checked that it
  is enabled. *) 

  Definition fire (e : events)
                  (M : marked_graph)
                  (m : marking)
                : marking :=
  fun t => if in_dec' (t,e) (output_event M) (* e0 →t→ e *)
           then m t - 1 (* remove markings on in-edges of e *)
           else if in_dec' (e,t) (input_event M) (* e →t→ e0 *)
           then m t + 1 (* add marking to out-edges of e *)
           else m t.


End MarkedGraphs.

Arguments in_transitions {events transitions}.


Arguments Pos {even odd}.
Arguments Neg {even odd}.
Arguments enabled {events transitions Hevents}.
Arguments fire {events transitions Hevents Htransitions}.


Arguments get_latch_value {even odd}.

Arguments oddF {even odd}.
Arguments evenF {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.
Arguments sync_eval {even odd}.
Arguments is_enabled {events transitions Hevents}.


(*********************)
(** Flow Equivalence *)
(*********************)


Section FlowEquivalence.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Context (transitions : Set).
  Context `{Htrans : eq_dec transitions}.

  Variable M : marked_graph (event even odd) transitions.
  Variable init : marking transitions.

  Existing Instance event_eq_dec.


  (* An initial marking indicates an initial state in that for each latch l, if
  l+ is enabled first, then l=0, and if l- is enabled first, then l=1. *)
  Definition marking_to_state (m : marking transitions) : state (latch even odd) := 
    fun l => if enabled (Pos l) M m then B0
             else if enabled (Neg l) M m then B1
             else X.

  Inductive ls_consistent_with_MG : latch_sequence even odd -> marking transitions -> Prop :=
  | lsc_empty lset : 
    (forall l, is_enabled M (Pos l) init -> lset l = false) ->
    (forall l, is_enabled M (Neg l) init -> lset l = true) ->
    ls_consistent_with_MG (ls_empty_async lset) init
  | lsc_cons e m m' s' : is_enabled M e m ->
                fire e M m = m' ->
                ls_consistent_with_MG s' m ->
                ls_consistent_with_MG (ls_async e s') m'
  .

  Definition consistent (s : latch_sequence even odd) : Prop := exists m, ls_consistent_with_MG s m.


  Definition flow_equivalence (c : circuit even odd) :=
    forall (s : latch_sequence even odd),
        consistent s ->
        forall st,
        eval c (marking_to_state init) s st ->
        forall l, is_transparent s l = false ->
                  st l = sync_eval c (marking_to_state init) (num_events (Neg l) s) l.


End FlowEquivalence.


Arguments consistent {even odd Heven Hodd transitions Htrans}.
Arguments flow_equivalence {even odd Heven Hodd transitions Htrans}.
Arguments marking_to_state {even odd Heven Hodd transitions}.
Arguments sync_eval {even odd} c. 

Arguments ls_consistent_with_MG {even odd Heven Hodd transitions Htrans}.
Notation "MG ⊢ m → s → m'" := (ls_consistent_with_MG MG m s m')
                                (no associativity, at level 90).
