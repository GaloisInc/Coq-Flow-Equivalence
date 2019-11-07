Require        Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Numbers.BinNums.

Require Import Coq.Arith.PeanoNat.
Open Scope nat_scope.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Inductive value := 
| B0 : value
| B1 : value
| X  : value
| Z  : value.


Class eq_dec A := { Dec : forall (a b : A), {a = b} + {a <> b} }.
Definition eqb {A} `{eq_dec A} (a b : A) : bool :=
  if Dec a b then true else false.
Infix "=?" := eqb.


Lemma eqb_eq : forall A `{eq_dec A} (a : A), a =? a = true.
Proof. intros. unfold eqb. destruct (Dec a a); auto. Qed.
Lemma eqb_neq : forall A `{eq_dec A} (a b : A), a <> b -> a =? b = false.
Proof. intros. unfold eqb. destruct (Dec a b); auto. contradiction. Qed.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Fixpoint in_list_dec {A} `{eq_dec A} (a : A) (ls : list A) : bool :=
  match ls with
  | [] => false
  | b :: ls' => if a =? b then true else in_list_dec a ls'
  end.
Notation "a ∈ ls" := (in_list_dec a ls = true) (no associativity, at level 90).
Notation "a ∈? ls" := (in_list_dec a ls) (no associativity, at level 90).

Definition in_dec' {A} `{HA : eq_dec A} : forall (a:A) l, {In a l} + {~(In a l)}.
Proof.
  apply in_dec.
  apply HA.
Defined.



Section LatchSequence.
  (* 1. isTransparent : nat -> odd+even -> bool (* for circuit *)
     2. list events (* for petri net *)
     3. given a latch sequence, find the time at which the ith occurence of an event occurs.
   *)


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
  (* Odd latches are transparent on 1, so if then event o+
     occurs, then o is no longer transparent. *)
  | Pos (Odd o) => true
  | Pos (Even e) => true
  | Neg (Odd o)  => false
  | Neg (Even e) => false
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


  Inductive latch_sequence : Set :=
  | ls_empty_async : latch_set -> latch_sequence
  | ls_async (e : event)
             (next : latch_sequence)
           : latch_sequence
  .

  Fixpoint is_transparent (s : latch_sequence) : latch_set :=
    match s with
    | ls_empty_async ls  => ls
    | ls_async e s' => step_latch_set e (is_transparent s')
    end.

  Fixpoint latch_in_event_list (l : latch) (es : list event) : option event :=
    match es with
    | [] => None
    | e :: es' => if event_refers_to_latch e l then Some e
                  else latch_in_event_list l es'
    end.


  Definition step_latch_sequence (s : latch_sequence) : latch_sequence :=
    match s with
    | ls_empty_async ls => ls_empty_async ls
    | ls_async ls s' => s'
    end.

  Fixpoint step_latch_sequence_n (s : latch_sequence) (n : nat)
                               : latch_sequence :=
    match n with 
    | 0 => s
    | S n' => step_latch_sequence (step_latch_sequence_n s n')
    end.


  (* At time i, is a particular latch transparent? *)
  Fixpoint is_transparent_at (i : nat) (s : latch_sequence) (l : latch) : bool :=
    is_transparent (step_latch_sequence_n s i) l.


 
  (* partitions the list of events around where the event occurs. 
     Satisfies: if find_next_occurrence e es = Some (es1,es2), then es = es1 ++ [e] ++ es2.
                if find_next_occurrence e es = None, then e ∉ es.
   *)
  Fixpoint find_next_occurrence_a (e : event) (es : list event) : option (nat * list event) :=
    match es with
    | [] => None
    | e0 :: es' => if e =? e0 then Some (0, es')
                   else match find_next_occurrence_a e es' with
                        | Some (n,es2) => Some (S n, es2)
                        | None => None
                        end
    end.

  Definition event_occurs_on_next_clk (e : event) (clk : bool) : bool :=
    match e, clk with
      (* if the clock is currently low, then the next occurrence of l+ occurs at
      the next time step*)
    | Pos _, false => true
    | Pos _, true  => false
    | Neg _, true  => true
    | Neg _, false => false
    end.

  (* Returns the number of timesteps at which the event will occur. *)
  Fixpoint find_next_occurrence (e : event) (s : latch_sequence)
                              : option nat :=
  match s with
  | ls_empty_async _ => None
  | ls_async e0 s' => if eqb e e0
                      then Some 1
                      else fmap S (find_next_occurrence e s')
  end.

  Fixpoint find_ith_occurrence (e : event) (s : latch_sequence) (i : nat) : option nat :=
    match i with
    | 0    => find_next_occurrence e s
    | S i' => do t ← find_next_occurrence e s;
              find_ith_occurrence e (step_latch_sequence_n s t) i'
    end.

End LatchSequence.

Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments is_transparent {even odd Heven Hodd}.

Arguments ls_empty_async {even odd}.
Arguments ls_async {even odd}.

Arguments Pos {even odd}.
Arguments Neg {even odd}.

(*************)
(** Circuits *)
(*************)

Section Circuits.

  Variable even odd : Set.
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.  

  Definition state (tp : Set) := tp -> value.

  Definition odd_state (P : odd -> Prop)
                       (s : state (latch even odd)) : state {o : odd & P o} :=
    fun o => s (Odd (projT1 o)).
  Definition even_state (P : even -> Prop)
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
    | Even e => evenF c e (odd_state _ prev)
    | Odd o  => oddF c o (even_state _ prev)
    end.

  Definition transparent_event (l : latch even odd) : event even odd :=
    match l with
    | Even e => Pos (Even e)
    | Odd o  => Pos (Odd o)
    end.
  Definition opaque_event (l : latch even odd) : event even odd :=
    match l with
    | Even e => Neg (Even e)
    | Odd o  => Neg (Odd o)
    end.
    

  (* step odd latches *)
  Definition eval_sync_odd_1 (c : circuit) (prev : state (latch even odd))
                      : state (latch even odd) :=
    fun l => match l with
             | Odd o => get_latch_value c prev (Odd o)
             | _ => prev l
             end.
  (* step even latches *)
  Existing Instance event_eq_dec.
  Definition eval_sync_even_1 (c : circuit) (prev : state (latch even odd))
                             : state (latch even odd) :=
    fun l => match l with
             | Even e => get_latch_value c prev (Even e)
             | _ => prev l
             end. 
  Definition eval_async_1 (c : circuit) (prev : state (latch even odd)) (e : event even odd) 
                        : state (latch  even odd) :=
    fun l => if transparent_event l =? e (*event_refers_to_latch even odd e l && event_becomes_transparent _ _ e*)
             then get_latch_value c prev l
             else prev l.

(*
  Fixpoint eval (c : circuit) (prev : state (latch even odd))
                (s : latch_sequence even odd)
                : state (latch even odd) :=
    match s with
    | ls_empty_async lset => prev
    | ls_async e s'       => let st := eval c prev s' in
                             eval_async_1 c st e
    end.
*)

  Reserved Notation " c '⊢' st '⇒' s '⇒' st' " (no associativity, at level 80).
  Inductive eval (c : circuit) (init : state (latch even odd))
               : latch_sequence even odd -> state (latch even odd) -> Prop :=
  | eval_nil lset : 
    (forall l, lset l = true -> init l = get_latch_value c init l) ->
    c ⊢ init ⇒ ls_empty_async lset ⇒ init
  | eval_cons e s st st' :
    c ⊢ init ⇒s⇒ st ->
    (forall l, is_transparent (ls_async e s) l = false -> st' l = st l) ->
    (forall l, is_transparent (ls_async e s) l = true -> st' l = get_latch_value c st' l) ->
    c ⊢ init ⇒ls_async e s⇒ st'
  where " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st').

  Lemma eval_transparent : forall c st s st',
    c ⊢ st ⇒ s ⇒ st' ->
    forall l, is_transparent s l = true -> st' l = get_latch_value c st' l.
  Proof.
    intros c st s st' H.
    induction H; intros invariant l; auto.
  Qed.

End Circuits.

Arguments eval {even odd Heven Hodd}.
Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).

Arguments transparent_event {even odd}.
Arguments opaque_event {even odd}.
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
(*
  Definition in_transitions (M : marked_graph) (e : events) : list transitions :=
    filter (fun (t : transitions) => eqb (output_event M t) e) (enumerate).
*)

  Lemma in_in_transitions : forall T M e,
    In T (in_transitions M e) ->
    exists e0, In (e0,T,e) (input_event_output M).
  Proof.
  Admitted.

  Definition enabled (e : events)
                     (M : marked_graph)
                     (m : marking)
                   : bool :=
    forallb (fun t => Nat.ltb 0 (m t)) (in_transitions M e).


  Instance prod_eq_dec {A B} `{eq_dec A} `{eq_dec B} : eq_dec (A*B).
  Proof.
    split. intros [a b] [a' b'].
    destruct (Dec a a'); destruct (Dec b b');
      subst; auto;
      right; inversion 1; contradiction.
  Defined.

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

  Reserved Notation "M ⊢ init → es → m" (no associativity, at level 70).
  Inductive reachable (M : marked_graph) (init : marking)
                  : list events -> marking -> Prop :=
  | R0 : M ⊢ init →[]→ init
  | RStep e es m m' : M ⊢ init →es→ m ->
                      enabled e M m = true ->
                      fire e M m = m' ->
                      M ⊢ init →e::es→ m'
  where "M ⊢ init → es → m" := (reachable M init es m).


  Definition feasible (M : marked_graph)
                      (init : marking)
                      (es : list events) : Prop :=
  exists m, M ⊢ init →es→ m.


  Definition traces (M : marked_graph)
                    (trace : nat -> marking) : Prop :=
    forall n, exists e, enabled e M (trace n) = true /\ fire e M (trace n) = trace (S n).

End MarkedGraphs.

Arguments in_transitions {events transitions}.

(*********************)
(** Flow Equivalence *)
(*********************)


Arguments Pos {even odd}.
Arguments Neg {even odd}.
Arguments enabled {events transitions Hevents}.
Arguments traces {events transitions} {Hevents Htransitions}.
Arguments step_latch_sequence {even odd}.
Arguments step_latch_sequence_n {even odd}.
Arguments find_ith_occurrence {even odd Heven Hodd}.
Arguments fire {events transitions Hevents Htransitions}.

Section FlowEquivalence.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Context (transitions : Set).
  Context `{Htrans : eq_dec transitions}.

  Variable M : marked_graph (event even odd) transitions.
  Variable init : marking transitions.

  Existing Instance event_eq_dec.

  Definition is_enabled (e : event even odd) (m : marking transitions) : Prop :=
    enabled e M m = true.

  Inductive ls_consistent_with_MG : latch_sequence even odd -> marking transitions -> Prop :=
  | lsc_empty lset : 
    (forall l, is_enabled (Pos l) init -> lset l = false) ->
    (forall l, is_enabled (Neg l) init -> lset l = true) ->
    ls_consistent_with_MG (ls_empty_async lset) init
  | lsc_cons e m m' s' : is_enabled e m ->
                fire e M m = m' ->
                ls_consistent_with_MG s' m ->
                ls_consistent_with_MG (ls_async e s') m'
  .

  Definition consistent (s : latch_sequence even odd) : Prop := exists m, ls_consistent_with_MG s m.

  (* An initial marking indicates an initial state in that for each latch l, if
  l+ is enabled first, then l=0, and if l- is enabled first, then l=1. *)
  Definition marking_to_state (m : marking transitions) : state (latch even odd) := 
    fun l => if enabled (Pos l) M m then B0
             else if enabled (Neg l) M m then B1
             else X.
(*  Definition init_state := marking_to_state init.*)


  Definition transparent_on_clock (l : latch even odd) (clk : CLK) : bool :=
    match l, clk with
    | Even _, CLK0 => true
    | Odd _, CLK1 => true
    | _, _  => false
    end.

  Fixpoint ls_length (s : latch_sequence even odd) : nat :=
    match s with
    | ls_empty_async _ => 0
    | ls_async _ s' => 1 + ls_length s'
    end.

(*
  Fixpoint sync_eval (c : circuit even odd) (st : state (latch even odd)) (n : nat) :=
    match n with
    | 0 => st
    | S n' => let st' := sync_eval c st n' in
              fun l => get_latch_value _ _ c st' l
    end.
*)

  Arguments get_latch_value {even odd}.

About get_latch_value.
About evenF.
Search state.
Arguments oddF {even odd}.
Arguments evenF {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.

  Fixpoint sync_even (c : circuit even odd) (st : state (latch even odd)) (n : nat)
                            {struct n} : state even :=
    fun E =>
    evenF c E (fun O => match n with
                        | 0 => st (Odd (projT1 O))
                        | S n' => oddF c (projT1 O) (fun E => sync_even c st n' (projT1 E))
                        end).
  Fixpoint sync_odd (c : circuit even odd) (st : state (latch even odd)) (n : nat) 
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

  Definition sync_eval (c : circuit even odd) (st : state (latch even odd)) (n : nat) 
                   : state (latch even odd) := fun l =>
    match l with
    | Even E => sync_even c st n E
    | Odd o  => sync_odd c st n o
    end.
  Lemma sync_eval_even : forall c st n E,
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

  Fixpoint num_events (e : event even odd) (s : latch_sequence even odd) : nat :=
    match s with
    | ls_empty_async _ => 0
    | ls_async e' s' => if e =? e'
                        then 1 + num_events e s'
                        else num_events e s'
    end.


  Definition flow_equivalence (c : circuit even odd) :=
    forall (s : latch_sequence even odd),
        consistent s ->
        forall st,
        eval c (marking_to_state init) s st ->
        forall l, is_transparent s l = false ->
                  st l = sync_eval c (marking_to_state init) (num_events (Neg l) s) l.


End FlowEquivalence.


Arguments flow_equivalence {even odd Heven Hodd transitions Htrans}.
Arguments marking_to_state {even odd Heven Hodd transitions}.
Arguments sync_eval {even odd} c. 
