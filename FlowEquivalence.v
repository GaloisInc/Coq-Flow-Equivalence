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


Class eq_dec A := { dec : forall (a b : A), {a = b} + {a <> b} }.
Definition eqb {A} `{eq_dec A} (a b : A) : bool :=
  if dec a b then true else false.
Infix "=?" := dec.



Require Import List.
Import ListNotations.
Open Scope list_scope.

  Fixpoint in_list_dec {A} `{eq_dec A} (a : A) (ls : list A) : bool :=
  match ls with
  | [] => false
  | b :: ls' => if dec a b then true else in_list_dec a ls'
  end.
  Infix "∈" := in_list_dec (no associativity, at level 90).



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

  Inductive kind := Sync | Async.

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
    * destruct (dec l1 l2); [ subst; auto | ].
      right. inversion 1. contradiction.
    * right. inversion 1.
    * right. inversion 1.
    * destruct (dec l1 l2); [ subst; auto | ].
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
  | Pos (Even e) => false
  | Neg (Odd o)  => false
  | Neg (Even e) => true
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


  Inductive latch_sequence : kind -> Set :=
  | ls_empty_sync : CLK -> latch_sequence Sync
  | ls_empty_async : latch_set -> latch_sequence Async
  | ls_async (e : event)
             (next : latch_sequence Async)
           : latch_sequence Async
  | ls_sync (clk : CLK)
            (next : latch_sequence Sync)
           : latch_sequence Sync
  .

  Fixpoint is_transparent {k} (s : latch_sequence k) : latch_set :=
    match s with
    | ls_empty_sync CLK0 => is_even
    | ls_empty_sync CLK1 => is_odd
    | ls_empty_async ls  => ls
    | ls_sync CLK0 _ => is_even
    | ls_sync CLK1 _ => is_odd
    | ls_async e s' => step_latch_set e (is_transparent s')
    end.

  Fixpoint latch_in_event_list (l : latch) (es : list event) : option event :=
    match es with
    | [] => None
    | e :: es' => if event_refers_to_latch e l then Some e
                  else latch_in_event_list l es'
    end.


  Definition step_latch_sequence {k} (s : latch_sequence k) : latch_sequence k :=
    match s with
    | ls_empty_sync clk => ls_empty_sync (step_CLK clk)
    | ls_empty_async ls => ls_empty_async ls
    | ls_async ls s' => s'
    | ls_sync clk s' => s'
    end.

  Fixpoint step_latch_sequence_n {k} (s : latch_sequence k) (n : nat)
                               : latch_sequence k :=
    match n with 
    | 0 => s
    | S n' => step_latch_sequence (step_latch_sequence_n s n')
    end.


  (* At time i, is a particular latch transparent? *)
  Fixpoint is_transparent_at {k} (i : nat) (s : latch_sequence k) (l : latch) : bool :=
    is_transparent (step_latch_sequence_n s i) l.


 
  (* partitions the list of events around where the event occurs. 
     Satisfies: if find_next_occurrence e es = Some (es1,es2), then es = es1 ++ [e] ++ es2.
                if find_next_occurrence e es = None, then e ∉ es.
   *)
  Fixpoint find_next_occurrence_a (e : event) (es : list event) : option (nat * list event) :=
    match es with
    | [] => None
    | e0 :: es' => if dec e e0 then Some (0, es')
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

  (* Returns the number of timesteps at which the event will occur. Will never
  return Some 0. *)
  Fixpoint find_next_occurrence {k} (e : event) (s : latch_sequence k)
                              : option nat :=
  match s with
  | ls_empty_sync _ => None
  | ls_empty_async _ => None
  | ls_sync CLK0 _ => match e with
                      | Pos _ => (* The even l+ will occur when the clock goes
                                    high, so on the next time step. *)
                                 Some 1
                      | Neg _ => Some 2
                      end
  | ls_sync CLK1 _ => match e with
                      | Pos _ => (* The even l+ will occur when the clock goes
                                    high *)
                                 Some 2
                      | Neg _ => Some 1
                      end
  | ls_async e0 s' => if eqb e e0
                      then Some 1
                      else fmap S (find_next_occurrence e s')
  end.

  Fixpoint find_ith_occurrence {k} (e : event) (s : latch_sequence k) (i : nat) : option nat :=
    match i with
    | 0    => find_next_occurrence e s
    | S i' => do t ← find_next_occurrence e s;
              find_ith_occurrence e (step_latch_sequence_n s t) i'
    end.

End LatchSequence.

Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments is_transparent {even odd Heven Hodd k}.

Arguments ls_empty_sync {even odd}.
Arguments ls_empty_async {even odd}.
Arguments ls_async {even odd}.
Arguments ls_sync {even odd}.



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
  ; evenF : forall (e : even), state {o : odd & In (e,o) even_odd_neighbors} -> value
  ; odd_even_neighbors : list (odd * even)
  ; oddF : forall (o : odd), state {e : even & In (o,e) odd_even_neighbors} -> value
  }.

(*
  Record circuit : Set :=
  { evenF : even -> state odd -> value
  ; oddF : odd -> state even -> value
  }.
*)

(*
  Definition even_neighbors_left (e : even) : list odd :=
    filter 

    evenF : even -> state odd  -> value
  ; oddF  : odd  -> state even -> value
  }.
*)

  Definition get_latch_value (c : circuit)
                             (prev : state (latch even odd))
                             (l : latch even odd) : value :=
    match l with
    | Even e => evenF c e (odd_state _ prev)
    | Odd o  => oddF c o (even_state _ prev)
    end.

  Definition eval_latch_sequence_1 {k : kind} 
                                   (c : circuit)
                                   (prev : state (latch even odd))
                                   (s : latch_sequence even odd k)
                                   : state (latch even odd) :=
    fun l => if is_transparent s l
             then get_latch_value c prev l
             else prev l.

  Fixpoint eval {k} (c : circuit) (init : state (latch even odd))
                (s : latch_sequence even odd k)
                (n : nat)
                : state (latch even odd) :=
  match n with
  | 0 => init
  | S n' => eval_latch_sequence_1 c (eval c init s n') s
  end.

(*
  Fixpoint repeat {A} (n : nat) (ls : list A) : list A :=
    match n with
    | 0 => []
    | S n' => ls ++ repeat n' ls
    end.
*)

End Circuits.

Arguments eval {even odd Heven Hodd k}.


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
    let f := fun ete => if fst (fst ete) =? e then [snd (fst ete)] else [] in
    flat_map f (input_event_output M).
(*
  Definition in_transitions (M : marked_graph) (e : events) : list transitions :=
    filter (fun (t : transitions) => eqb (output_event M t) e) (enumerate).
*)

  Definition enabled (e : events)
                     (M : marked_graph)
                     (m : marking)
                   : bool :=
    forallb (fun t => Nat.ltb 0 (m t)) (in_transitions M e).


  Instance prod_eq_dec {A B} `{eq_dec A} `{eq_dec B} : eq_dec (A*B).
  Admitted.

  (* An event should only fire if the caller has independently checked that it
  is enabled. *) 


About in_dec.
Definition in_dec' {A} `{HA : eq_dec A} : forall (a:A) l, {In a l} + {~(In a l)}.
Proof.
  apply in_dec.
  apply HA.
Defined.

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
Arguments step_latch_sequence {even odd k}.
Arguments step_latch_sequence_n {even odd k}.
Arguments find_ith_occurrence {even odd Heven Hodd k}.

Section FlowEquivalence.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Context (transitions : Set).
  Context `{Htrans : eq_dec transitions}.

  Variable M : marked_graph (event even odd) transitions.
  Variable init : marking transitions.
(*  Context `{Enumerable transitions}. *)

  Existing Instance event_eq_dec.
  Definition isEnabled (e : event even odd) (m : marking transitions) : Prop :=
    enabled e M m = true.

  Record marking_consistent_with_latch_sequence {k}
         (m : marking transitions) (s : latch_sequence even odd k) :=
    { PosEvenEnabled : forall (e : even),
                       isEnabled (Pos (Even e)) m -> is_transparent s (Even e) = true
    ; NegEvenEnabled : forall (e : even),
                       isEnabled (Neg (Even e)) m -> is_transparent s (Even e) = false
    ; PosOddEnabled : forall (o : odd),
                      isEnabled (Pos (Odd o)) m -> is_transparent s (Odd o) = false
    ; NegOddEnabled : forall (o : odd),
                      isEnabled (Neg (Odd o)) m -> is_transparent s (Odd o) = true
    }.

  Definition consistent_with_MG {k} (s : latch_sequence even odd k) :=
    forall (trace : nat -> marking transitions),
      traces M trace ->
      forall i,
        marking_consistent_with_latch_sequence (trace i) (step_latch_sequence_n s i).

  (* An initial marking indicates an initial state in that for each latch l, if
  l+ is enabled first, then l=0, and if l- is enabled first, then l=1. *)
  Definition marking_to_state (m : marking transitions) : state (latch even odd) := 
    fun l => if enabled (Pos l) M m then B0
             else if enabled (Neg l) M m then B1
             else X.
(*  Definition init_state := marking_to_state init.*)

  Definition transparent_event (l : latch even odd) : event even odd :=
    match l with
    | Even e => Neg (Even e)
    | Odd o  => Pos (Odd o)
    end.

Print latch_sequence. Print eval. Search CLK.


  Definition transparent_on_clock (l : latch even odd) (clk : CLK) : bool :=
    match l, clk with
    | Even _, CLK0 => true
    | Odd _, CLK1 => true
    | _, _  => false
    end.

  Search state. Print eval_latch_sequence_1. 
Arguments eval_latch_sequence_1 {even odd Heven Hodd k}.

Print get_latch_value.


  Fixpoint projection {k} (c : circuit even odd) (s : latch_sequence even odd k)
                          (l : latch even odd)
                          (old_st : state (latch even odd))
                          (i : nat) (* the ith value latched by l *) 
                       :  value :=
    match s with
    | ls_empty_sync _ => old_st l
    | ls_empty_async lset => old_st l
    | ls_async e s' => match i with
                       | 0    => old_st l
                       | S i' => if eqb e (transparent_event l)
                                 then projection c s' l (eval_latch_sequence_1 c old_st s) i'
                                 else projection c s' l (eval_latch_sequence_1 c old_st s) (S i')
                       end
    | ls_sync clk s' => match i with
                        | 0 => old_st l
                        | S i' => if transparent_on_clock l clk
                                  then projection c s' l (eval_latch_sequence_1 c old_st s) i'
                                  else projection c s' l (eval_latch_sequence_1 c old_st s) (S i')
                        end
    end.
                                  

(*
  (* The projection of a circuit onto a latch l is the list of values latched by
  l. A latch "gets latched" when is_transparent moves from true to false. *)
  (* Can we define projection by induction on s? *)
  Fixpoint projection {k} (c : circuit even odd)
                      (s : latch_sequence even odd k)
                      (l : latch even odd)
                      (i : nat) (* the ith value latched by l *)
                      : value :=
      match i with
      | 0 => init_state l
      | S i' => (* find the time step at which the ith latch of l occurrs in transparent_latches *)
                match find_ith_occurrence (transparentEvent l) s i' with
                | None   => (* if no more latches of l occur, then the latch
                               just retains its old value *)
                            projection c s l i'
                | Some t => (* if the ith latch of l occurs at time t, evaluate
                               the circuit to time t and check the value of l *)
                    (eval c init_state s t) l
                end
      end.
*)

  Fixpoint ls_length {k} (s : latch_sequence even odd k) : nat :=
    match s with
    | ls_empty_sync _ => 0
    | ls_empty_async _ => 0
    | ls_async _ s' => 1 + ls_length s'
    | ls_sync _ s' => 1 + ls_length s'
    end.

  Fixpoint sync_latch_sequence (n : nat) (clk : CLK) : latch_sequence even odd Sync :=
    match n with
    | 0 => ls_empty_sync clk
    | S n' => ls_sync clk (sync_latch_sequence n' (step_CLK clk))
    end.

  Definition flow_equivalence (c : circuit even odd) (init_clk : CLK) :=
    forall (s : latch_sequence even odd Async),
      consistent_with_MG s ->
      forall (l : latch even odd) (i : nat),
        projection c s l (marking_to_state init) i 
      = projection c (sync_latch_sequence (ls_length s) init_clk) l (marking_to_state init) i.

End FlowEquivalence.

Arguments flow_equivalence {even odd Heven Hodd transitions Htrans}.
