Require Export Base.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.


Section FE.

  Variable even odd : Set.
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
  ; next_state_even (e : even) : state {o : odd  & In (o,e) odd_even_neighbors} -> value
  ; next_state_odd  (o : odd)  : state {e : even & In (e,o) even_odd_neighbors} -> value
  }.

  Definition next_state (c : circuit) (st : state latch) (l : latch) : value :=
    match l with
    | Even e => next_state_even c e (odd_state st)
    | Odd o  => next_state_odd c o (even_state st)
    end.

  (** Async execution *)

  Definition respects_transparencies (c : circuit)
                                     (P : transparency_predicate)
                                     (st : state latch) :=
    forall (l : latch), P(l) = true -> st(l) = next_state c st l.

  Definition opaque_equivalence (P : transparency_predicate) (st1 st2 : state latch) :=
    forall (l : latch), P(l) = false -> st1 l = st2 l.


  Reserved Notation " c '⊢' st '⇒' s '⇒' st' " (no associativity, at level 80).
  Inductive eval (c : circuit) (init : state latch)
               : trace -> state latch -> Prop :=
  | eval_nil P : 
    respects_transparencies c P init ->
    c ⊢ init ⇒ empty_trace P ⇒ init
  | eval_next e s st st' :
    c ⊢ init ⇒s⇒ st ->
    opaque_equivalence (transparent (next_trace e s)) st' st ->
    respects_transparencies c (transparent (next_trace e s)) st' ->
    c ⊢ init ⇒next_trace e s⇒ st'
  where " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st').

  Lemma eval_transparent : forall c st s st',
    c ⊢ st ⇒ s ⇒ st' ->
    forall l, transparent s l = true -> st' l = next_state c st' l.
  Proof.
    intros c st s st' H.
    induction H; intros invariant l; auto.
  Qed.

  Record async_step (c : circuit) (P : transparency_predicate)
                    (st : state latch) (e : event) (st' : state latch) :=
    { step_opaque : opaque_equivalence (update_transparency_predicate e P) st' st
    ; step_transparent : respects_transparencies c (update_transparency_predicate e P) st'
    }.

  (* This is true for all marked graphs, not just fall decoupled *)
  Lemma event_fall_invariant : forall c init_st t st l st',
    c ⊢ init_st ⇒t⇒ st ->
    async_step c (transparent t) st (Fall l) st' ->
    forall l', st'(l') = st(l').
  Proof.
    intros c init_st t st l st' Ht [Hopaque Htransparent] l'.
    destruct ((update_transparency_predicate (Fall l) (transparent t)) l')
      eqn:Hl'.
    * (* l' is transparent *)

      rewrite Htransparent; auto.

      unfold update_transparency_predicate in Hl'.
      simpl in Hl'.
      assert (Fall l' <> Fall l).
      { inversion 1; subst. rewrite eqb_eq in Hl'. inversion Hl'. }
      rewrite eqb_neq in Hl'; auto.

      erewrite (eval_transparent _ _ t st); eauto.
      admit (* need induction? *).
    * (* l' is opaque *)
      unfold update_transparency_predicate in Hl'.
      simpl in Hl'.
Existing Instance latch_eq_dec.
      destruct (Dec l' l).
      ** subst.
         erewrite Hopaque; eauto.
      ** rewrite eqb_neq in Hl'; [ | inversion 1; contradiction].
         rewrite Hopaque; auto.
         unfold update_transparency_predicate. simpl.
         rewrite eqb_neq; auto.
         inversion 1; contradiction.
  Admitted.



 
  (** Synchronous execution *)
  Fixpoint sync_odd (c : circuit) (st : state latch) (n : nat)
                    {struct n} : state odd. Admitted.
(*
    fun O =>
    match n with
    | 0 => st (Odd O)
    | S n' => next_state_odd c O (fun E => next_state_even c (projT1 E) (fun O => sync_odd c st n' (projT1 O)))
    end.
*)
  Fixpoint sync_even (c : circuit) (st : state latch) (n : nat) 
                            {struct n} : state even. Admitted.
(*
    fun E =>
    match n with
    | 0 => st (Even E)
    | S n' => next_state_even c E (fun O => sync_odd c st n' (projT1 O))
    end.
*)

  Definition sync_eval (c : circuit) (st : state latch) (n : nat) 
                   : state latch. Admitted.
(* := fun l =>
    match l with
    | Even E => sync_even c st n E
    | Odd o  => sync_odd c st n o
    end.
*)

  (* Yes, this is what the paper says too *)
  Lemma sync_eval_odd_0 : forall c st O,
        sync_eval c st 0 (Odd O) = st (Odd O).
  Proof.
(*
    intros. destruct l; reflexivity.
  Qed.
*)
  Admitted.


(* NOTE: if your execution model starts with the clock going low (e.g. even first), then you would need to reverse the order of synchronous execution and derive the following results:
*)

  Lemma sync_eval_even : forall (c : circuit) (st : state latch) n E,
        sync_eval c st (S n) (Even E) = next_state_even c E (odd_state (sync_eval c st n)).
  Admitted.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = next_state_odd c O (even_state (sync_eval c st (S n))).
  Admitted.


(*
  Lemma sync_eval_even: forall c st n E,
        sync_eval c st (S n) (Even E) = next_state_even c E (odd_state (sync_eval c st n)).
  Proof.
(*
    intros. simpl. reflexivity.
  Qed.
*)
Admitted.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = next_state_odd c O (even_state (sync_eval c st (S n))).
  Proof.
(*
    intros. simpl.
    destruct n; auto.
  Qed.
*)
Admitted.
*)


Reserved Notation "{ c // init_st }⊢ l ⇓^{ n } v" (no associativity, at level 80).
Inductive sync_rel (c : circuit) (init_st : state latch) : nat -> latch -> value -> Prop :=
| Sync_odd_0 (O : odd) : { c // init_st }⊢ Odd O ⇓^{0} init_st(Odd O)
| Sync_odd_S (O : odd) (n : nat) (st0 : state latch) :
    (forall (E : even) (pf : In (E,O) (even_odd_neighbors c)), 
            { c // init_st }⊢ Even E ⇓^{S n} st0(Even E)) ->
    { c // init_st }⊢ Odd O ⇓^{S n} next_state c st0 (Odd O)
| Sync_even_S (E : even) (n : nat) (st0 : state latch) :
    (forall (O : odd) (pf : In (O,E) (odd_even_neighbors c)), 
            { c // init_st }⊢ Odd O ⇓^{n} st0(Odd O)) ->
    { c // init_st }⊢ Even E ⇓^{S n} next_state c st0 (Even E)

where
  "{ c // init_st }⊢ l ⇓^{ n } v" := (sync_rel c init_st n l v).

End Circuits.

Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).
Notation "{ c // init_st }⊢ l ⇓^{ n } v" := (sync_rel c init_st n l v) (no associativity, at level 80).


(******************)
(** Marked graphs *)
(******************)

Section MarkedGraphs.

  Definition marking (places : Set) := places -> nat.

  Record marked_graph (transitions : Set) (places : Set) : Set :=
  { mg_triples : list (transitions * places * transitions)
  ; mg_init    : marking places
  }.
  Arguments mg_triples {transitions places}.
  Definition input_event {transitions places} 
                         (M : marked_graph transitions places) : list (transitions * places) :=
    fmap fst (mg_triples M).
  Definition output_event {transitions places}
                          (M : marked_graph transitions places) : list (places * transitions) :=
    fmap (fun ete => (snd (fst ete),snd ete)) (mg_triples M).

  Definition preset {transitions places : Set}
                       `{eq_dec transitions}
                       (M : marked_graph transitions places) (t : transitions) : list places :=
    let f := fun ete => if snd ete =? t then [snd (fst ete)] else [] in
    flat_map f (mg_triples M).

  Definition enabled {transitions places : Set} `{Htransitions : eq_dec transitions}
                     (e : transitions)
                     (M : marked_graph transitions places)
                     (m : marking places)
                   : bool :=
    forallb (fun t => Nat.ltb 0 (m t)) (preset M e).
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



Lemma is_enabled_fire_neq : forall {transitions : Set} `{eq_dec transitions}
                                   (M : marked_graph event transitions)
                                   m e l,
    e <> Rise l ->
    e <> Fall l ->
    is_enabled M (Fall l) (fire e M m) ->
    is_enabled M (Fall l) m.
Proof.
    intros transitions Htransitions M m e l Hel1 Hel2 Henabled.
    unfold is_enabled in *.
    unfold enabled in *.
    
    apply forallb_forall. intros T Hin.

    assert (Hfire : Nat.ltb 0 (fire e M m T) = true).
    { destruct (forallb_forall (fun t => Nat.ltb 0 (fire e M m t)) (preset M (Fall l)))
        as [H1 H2].
      apply H1; auto.
    }
    unfold fire in Hfire.
    destruct (in_dec' (T,e) (output_event M)) as [Hin' | Hin'].
    { apply PeanoNat.Nat.ltb_lt in Hfire.
      apply PeanoNat.Nat.ltb_lt.
      apply PeanoNat.Nat.lt_add_lt_sub_r in Hfire.
      transitivity 1; auto.
    }
    destruct (in_dec' (e,T) (input_event M)) as [Hin'' | Hin''].
    { (* e -T-> Fall l *)
      admit.
    }
    { assumption. }
Admitted.


Section FlowEquivalence.


  Reserved Notation "{ MG }⊢ s ↓ m" (no associativity, at level 90).

  Arguments mg_init {transitions places}.

  Inductive ls_consistent_with_MG {places : Set} `{Hplaces : eq_dec places}
                                  (M : marked_graph event places)
                                : trace -> marking places -> Prop :=
  | lsc_empty P : 
    (forall l, is_enabled M (Rise l) (mg_init M) -> P l = false) ->
    (forall l, is_enabled M (Fall l) (mg_init M) -> P l = true) ->
    {M}⊢ empty_trace P ↓ mg_init M
  | lsc_cons e m m' t' : is_enabled M e m ->
                fire e M m = m' ->
                {M}⊢ t' ↓ m ->
                {M}⊢ next_trace e t' ↓ m'
  where
    "{ MG }⊢ s ↓ m'" := (ls_consistent_with_MG MG s m').


  Lemma fall_enabled_transparent : forall {places : Set} `{Hplaces : eq_dec places}
                                          (M : marked_graph event places)
                                          (t : trace)
                                          (m : marking places)
                                          (l : latch),
    {M}⊢ t ↓ m ->
    is_enabled M (Fall l) m ->
    transparent t l = true.
  Proof.
    intros places Hplaces M t m l pf.
    induction pf as [lset Htransparent Hopaque | ]; intros Henabled.
    * simpl. apply Hopaque.
      assumption.
    * simpl.
      destruct l as [O | E]; inversion Henabled; subst.
      ** unfold update_transparency_predicate.
         destruct (Dec (Rise (Odd O)) e).
         { subst. rewrite eqb_eq. auto. }
         rewrite eqb_neq; auto.
         destruct (Dec (Fall (Odd O)) e).
         { subst. rewrite eqb_eq. admit (* true *). }
         rewrite eqb_neq; auto.
         rewrite IHpf; auto.
         eapply is_enabled_fire_neq; eauto.
      ** unfold update_transparency_predicate.
         destruct (Dec (Rise (Even E)) e).
         { subst. rewrite eqb_eq. auto. }
         rewrite eqb_neq; auto.
         destruct (Dec (Fall (Even E)) e).
         { subst. rewrite eqb_eq. admit (* true *). }
         rewrite eqb_neq; auto.
         rewrite IHpf; auto.
         eapply is_enabled_fire_neq; eauto.
    Admitted.

Lemma rise_enabled_opaque :  forall {places : Set} `{Hplaces : eq_dec places}
                                          (M : marked_graph event places)
                                          (t : trace)
                                          (m0 m : marking places)
                                          (l : latch),
    {M}⊢ t ↓ m ->
    is_enabled M (Rise l) m ->
    transparent t l = false.
Admitted.


  Definition flow_equivalence {places : Set} `{Hplaces : eq_dec places}
                              (M : marked_graph event places)
                              (c : circuit) 
                              (init_st : state latch) :=
    forall (t : trace),
        (exists m, {M}⊢ t ↓ m) ->
        forall st, c ⊢ init_st ⇒ t ⇒ st ->
        forall l, transparent t l = false ->
                  st l = sync_eval c init_st (num_events (Fall l) t) l.


End FlowEquivalence.

End FE.

Arguments flow_equivalence {even odd Heven Hodd places Hplaces}.
(*Arguments sync_eval {even odd} c. *)

Arguments ls_consistent_with_MG {even odd Heven Hodd places Hplaces}.

Arguments mg_triples {transitions places}.
Arguments mg_init {transitions places}.

Notation "{ MG }⊢ s ↓ m'" := (ls_consistent_with_MG MG s m')
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

Arguments next_state {even odd}.


Arguments preset {transitions places}.


Arguments enabled {transitions places Htransitions}.
Arguments fire {transitions places Htransitions Hplaces}.


Arguments next_state_odd {even odd}.
Arguments next_state_even {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.
Arguments sync_eval {even odd Heven Hodd}.
Arguments is_enabled {transitions places Htransitions}.
Arguments respects_transparencies {even odd}.
Arguments opaque_equivalence {even odd}.

Arguments update_transparency_predicate {even odd Heven Hodd}.


Arguments sync_rel {even odd}.
Notation "< c // init_st >⊢ l ⇓^{ n } v" := (sync_rel c init_st n l v) (no associativity, at level 80).

Existing Instance event_eq_dec.
 
Arguments async_step {even odd Heven Hodd}.
