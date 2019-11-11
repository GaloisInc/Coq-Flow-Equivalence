Require Export Base.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.


Section FE.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.  



Section LatchSequence.

  Inductive latch : Set := 
  | Odd : odd -> latch
  | Even : even -> latch
  .
  Arguments latch : clear implicits.
  Inductive event : Set :=
  | Rise : latch -> event
  | Fall : latch -> event
  . 

  Inductive CLK : Set := CLK0 | CLK1.
  Definition step_CLK (clk : CLK) : CLK :=
    match clk with
    | CLK0 => CLK1
    | CLK1 => CLK0
    end.

  Definition transparency_predicate := latch -> bool.

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

  Definition update_transparency_predicate (e : event) (P : transparency_predicate) : transparency_predicate :=
    fun l => if Rise l =? e
             then true
             else if Fall l =? e
             then false
             else P l.

  Definition is_even (l : latch) : bool :=
  match l with
  | Even _ => true
  | _ => false
  end.
  Definition is_odd (l : latch) : bool := negb (is_even l).


  (* A trace is a snoc-list of events, ending with a set of transparent latches. *)
  Inductive trace : Set :=
  | empty_trace (P : transparency_predicate) : trace
  | next_trace (e : event)
             (next : trace)
           : trace
  .

  (* Calculate the set of transparent latches after executing the latch sequence s *)
  Fixpoint transparent (s : trace) : transparency_predicate :=
    match s with
    | empty_trace ls  => ls
    | next_trace e s' => update_transparency_predicate e (transparent s')
    end.


  Fixpoint num_events (e : event) (s : trace) : nat :=
    match s with
    | empty_trace _ => 0
    | next_trace e' s' => if e =? e'
                        then 1 + num_events e s'
                        else num_events e s'
    end.


End LatchSequence.


(*************)
(** Circuits *)
(*************)

Section Circuits.

  Inductive value := 
  | B0 : value
  | B1 : value
  | X  : value
  | Z  : value.

  Definition state (tp : Set) := tp -> value.

  Definition odd_state {P : odd -> Prop}
                       (s : state latch) : state {o : odd & P o} :=
    fun o => s (Odd (projT1 o)).
  Definition even_state {P : even -> Prop}
                        (s : state latch) : state {e : even & P e} :=
    fun o => s (Even (projT1 o)).

  Record circuit : Set :=
  { even_odd_neighbors : list (even * odd)
  ; odd_even_neighbors : list (odd * even)
  ; evenF : forall (e : even), state {o : odd & In (o,e) odd_even_neighbors} -> value
  ; oddF : forall (o : odd), state {e : even & In (e,o) even_odd_neighbors} -> value
  }.

  Definition get_latch_value (c : circuit)
                             (prev : state latch)
                             (l : latch) : value :=
    match l with
    | Even e => evenF c e (odd_state prev)
    | Odd o  => oddF c o (even_state prev)
    end.

  (** Async execution *)

  Definition state_respects_transparencies (c : circuit)
                                           (P : transparency_predicate)
                                           (st : state latch) :=
    forall l, P l = true -> st l = get_latch_value c st l.

  Definition state_respects_opacities (P : transparency_predicate)
                                      (st1 st2 : state latch) :=
    forall l, P l = false -> st1 l = st2 l.


  Reserved Notation " c '⊢' st '⇒' s '⇒' st' " (no associativity, at level 80).
  Inductive eval (c : circuit) (init : state latch)
               : trace -> state latch -> Prop :=
  | eval_nil P : 
    state_respects_transparencies c P init ->
    c ⊢ init ⇒ empty_trace P ⇒ init
  | eval_cons e s st st' :
    c ⊢ init ⇒s⇒ st ->
    state_respects_opacities (transparent (next_trace e s)) st' st ->
    state_respects_transparencies c (transparent (next_trace e s)) st' ->
    c ⊢ init ⇒next_trace e s⇒ st'
  where " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st').

  Lemma eval_transparent : forall c st s st',
    c ⊢ st ⇒ s ⇒ st' ->
    forall l, transparent s l = true -> st' l = get_latch_value c st' l.
  Proof.
    intros c st s st' H.
    induction H; intros invariant l; auto.
  Qed.


 
  (** Syncronous execution *)
  Fixpoint sync_odd (c : circuit) (st : state latch) (n : nat)
                    {struct n} : state odd. Admitted.
(*
    fun O =>
    match n with
    | 0 => st (Odd O)
    | S n' => oddF c O (fun E => evenF c (projT1 E) (fun O => sync_odd c st n' (projT1 O)))
    end.
*)
  Fixpoint sync_even (c : circuit) (st : state latch) (n : nat) 
                            {struct n} : state even. Admitted.
(*
    fun E =>
    match n with
    | 0 => st (Even E)
    | S n' => evenF c E (fun O => sync_odd c st n' (projT1 O))
    end.
*)

  Definition sync_eval (c : circuit) (st : state latch) (n : nat) 
                   : state latch := fun l =>
    match l with
    | Even E => sync_even c st n E
    | Odd o  => sync_odd c st n o
    end.


(* NOTE: if your execution model starts with the clock going low (e.g. even first), then you would need to reverse the order of synchronous execution and derive the following results:
*)

  Lemma sync_eval_even : forall (c : circuit) (st : state latch) n E,
        sync_eval c st n (Even E) = evenF c E (odd_state (sync_eval c st n)).
  Admitted.
  Lemma sync_eval_even_0 : forall c st E,
        sync_eval c st 0 (Even E) = st (Even E).
  Admitted.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = oddF c O (even_state (sync_eval c st n)).
  Admitted.


(*
  Lemma sync_eval_0 : forall c st O,
        sync_eval c st 0 (Odd O) = st (Odd O).
  Proof.
(*
    intros. destruct l; reflexivity.
  Qed.
*)
  Admitted.

  Lemma sync_eval_even: forall c st n E,
        sync_eval c st (S n) (Even E) = evenF c E (odd_state (sync_eval c st n)).
  Proof.
(*
    intros. simpl. reflexivity.
  Qed.
*)
Admitted.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = oddF c O (even_state (sync_eval c st (S n))).
  Proof.
(*
    intros. simpl.
    destruct n; auto.
  Qed.
*)
Admitted.
*)


End Circuits.

Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).

(******************)
(** Marked graphs *)
(******************)

Section MarkedGraphs.

(*
  Context (transitions : Set).
  Context (places : Set).
  Context `{Htransitions : eq_dec transitions}.
  Context `{Hplaces : eq_dec places}.
*)

  Definition marking places := places -> nat.

  Record marked_graph (transitions : Set) (places : Set) : Set :=
  { input_event_output : list (transitions * places * transitions) }.
  Arguments input_event_output {transitions places}.
  Definition input_event {transitions places} 
                         (M : marked_graph transitions places) : list (transitions * places) :=
    fmap fst (input_event_output M).
  Definition output_event {transitions places}
                          (M : marked_graph transitions places) : list (places * transitions) :=
    fmap (fun ete => (snd (fst ete),snd ete)) (input_event_output M).

  Definition in_places {transitions places : Set}
                       `{eq_dec transitions}
                       (M : marked_graph transitions places) (t : transitions) : list places :=
    let f := fun ete => if snd ete =? t then [snd (fst ete)] else [] in
    flat_map f (input_event_output M).

  Definition enabled {transitions places : Set} `{Htransitions : eq_dec transitions}
                     (e : transitions)
                     (M : marked_graph transitions places)
                     (m : marking places)
                   : bool :=
    forallb (fun t => Nat.ltb 0 (m t)) (in_places M e).
  Definition is_enabled {transitions places : Set}  `{Htransitions : eq_dec transitions}
                        (M : marked_graph transitions places)
                        (e : transitions)
                        (m : marking places) :=
    enabled e M m = true.

  (* An event should only fire if the caller has independently checked that it
  is enabled. *) 
  Definition fire {transitions places : Set}
                  `{Htransitions : eq_dec transitions}
                  `{Hplaces : eq_dec places}
                  (t : transitions)
                  (M : marked_graph transitions places)
                  (m : marking places)
                : marking places :=
  fun p => if in_dec' (p,t) (output_event M) (* e0 →t→ e *)
           then m p - 1 (* remove markings on in-edges of e *)
           else if in_dec' (t,p) (input_event M) (* e →t→ e0 *)
           then m p + 1 (* add marking to out-edges of e *)
           else m p.



End MarkedGraphs.

(*********************)
(** Flow Equivalence *)
(*********************)

Existing Instance event_eq_dec.


Section FlowEquivalence.


  Reserved Notation "{ MG }⊢ m → s → m'" (no associativity, at level 90).
About is_enabled.

  Inductive ls_consistent_with_MG {places : Set} `{Hplaces : eq_dec places}
                                  (M : marked_graph event places)
                                  (init_m : marking places)
                                : trace -> marking places -> Prop :=
  | lsc_empty lset : 
    (forall l, is_enabled M (Rise l) init_m -> lset l = false) ->
    (forall l, is_enabled M (Fall l) init_m -> lset l = true) ->
    {M}⊢ init_m →empty_trace lset→ init_m
  | lsc_cons e m m' s' : is_enabled M e m ->
                fire e M m = m' ->
                {M}⊢ init_m →s'→ m ->
                {M}⊢ init_m →next_trace e s'→ m'
  where
    "{ MG }⊢ m → s → m'" := (ls_consistent_with_MG MG m s m').


  Definition flow_equivalence {places : Set} `{Hplaces : eq_dec places}
                              (M : marked_graph event places)
                              (init_m : marking places)
                              (c : circuit) 
                              (init_st : state latch) :=
    forall (t : trace),
        (exists m, {M}⊢ init_m →t→ m) ->
        forall st, c ⊢ init_st ⇒ t ⇒ st ->
        forall l, transparent t l = false ->
                  st l = sync_eval c init_st (num_events (Fall l) t) l.


End FlowEquivalence.

End FE.

Arguments flow_equivalence {even odd Heven Hodd places Hplaces}.
(*Arguments sync_eval {even odd} c. *)

Arguments ls_consistent_with_MG {even odd Heven Hodd places Hplaces}.
Notation "{ MG }⊢ m → s → m'" := (ls_consistent_with_MG MG m s m')
                                (no associativity, at level 90).


Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments transparent {even odd Heven Hodd}.

Arguments empty_trace {even odd}.
Arguments next_trace {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.
Arguments num_events {even odd Heven Hodd}.

Arguments eval {even odd Heven Hodd}.
Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).

Arguments odd_even_neighbors {even odd}.
Arguments even_odd_neighbors {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.

Arguments get_latch_value {even odd}.


Arguments in_places {transitions places}.


Arguments enabled {transitions places Htransitions}.
Arguments fire {transitions places Htransitions Hplaces}.


Arguments oddF {even odd}.
Arguments evenF {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.
Arguments sync_eval {even odd}.
Arguments is_enabled {transitions places Htransitions}.
Arguments state_respects_transparencies {even odd}.
Arguments state_respects_opacities {even odd}.

Existing Instance event_eq_dec.
 
