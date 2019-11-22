Require Export Base.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Coq.Logic.FunctionalExtensionality.



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

  Inductive opacity := Transparent | Opaque.
  Definition transparency_predicate := latch -> opacity.

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
             then Transparent
             else if Fall l =? e
             then Opaque
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
  | next_trace (next : trace) (e : event) : trace.       

  (* Calculate the set of transparent latches after executing the latch sequence s *)
  Fixpoint transparent (s : trace) : transparency_predicate :=
    match s with
    | empty_trace P   => P
    | next_trace s' e => fun l => if Rise l =? e then Transparent
                                  else if Fall l =? e then Opaque
                                  else transparent s' l
    end.


  Fixpoint num_events (e : event) (s : trace) : nat :=
    match s with
    | empty_trace _ => 0
    | next_trace s' e' => if e =? e'
                          then 1 + num_events e s'
                          else num_events e s'
    end.


End LatchSequence.

Existing Instance event_eq_dec.


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

(*
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
*)

  Inductive neighbor c : latch -> latch  -> Prop :=
  | EO_neighbor E O : In (E,O) (even_odd_neighbors c) -> neighbor c (Even E) (Odd O)
  | OE_neighbor O E : In (O,E) (odd_even_neighbors c) -> neighbor c (Odd O) (Even E).


(* Alternative async evaluation *)
  Inductive async_rel c init_st : latch -> opacity -> trace -> value -> Prop :=
| async_nil l P : P l = Opaque -> async_rel c init_st l Opaque (empty_trace P) (init_st l)
| async_transparent l t st v :
  transparent t l = Transparent ->
  (forall l', neighbor c l' l -> async_rel c init_st l' (transparent t l') t (st l')) ->
  v = next_state c st l ->
  async_rel c init_st l Transparent t v

| async_opaque l e t v :
  transparent (next_trace t e) l = Opaque ->
  e <> Fall l ->
  async_rel c init_st l Opaque t v ->
  async_rel c init_st l Opaque (next_trace t e) v

| async_opaque_fall l e t v st :
  e = Fall l -> (* i.e. l is transparent in t *)
  (forall l', neighbor c l' l -> async_rel c init_st l' (transparent t l') t (st l')) ->
  v = next_state c st l ->
  async_rel c init_st l Opaque (next_trace t e) v
.

Lemma async_rel_b : forall c init_st l b t v,
    async_rel c init_st l b t v ->
    transparent t l = b.
Proof.
  intros c init_st l b t v H.
  induction H; auto.
  subst. simpl. reduce_eqb. auto.
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


Lemma async_rel_injective : forall c init_st l b1 t v1,
    async_rel c init_st l b1 t v1 ->
    forall b2 v2, async_rel c init_st l b2 t v2 -> v1 = v2.
Proof.
  intros c init_st l b1 t v1 H1.
  induction H1; intros b2 v2 H2';
    inversion H2'; subst; simpl in *; find_contradiction; auto.

  * apply next_state_eq.
    intros l' Hl'.
    eapply H1; eauto.
  * reduce_eqb; find_contradiction. 
  * compare (Rise l) e.
    eapply IHasync_rel; eauto.
  * reduce_eqb; find_contradiction.
  * apply next_state_eq.
    intros l' Hl'.
    eapply H1; eauto.
Qed.

 
  (** Synchronous execution *)
  Fixpoint sync_odd (c : circuit) (st : state latch) (n : nat)
                    {struct n} : state odd := fun O =>
    match n with
    | 0 => st (Odd O)
    | S n' => next_state_odd c O (fun E => next_state_even c (projT1 E) (fun O => sync_odd c st n' (projT1 O)))
    end.

  Fixpoint sync_even (c : circuit) (st : state latch) (n : nat) 
                            {struct n} : state even := fun E =>
    match n with
    | 0 => st (Even E)
    | S n' => next_state_even c E (fun O => sync_odd c st n' (projT1 O))
    end.

  Definition sync_eval (c : circuit) (st : state latch) (n : nat) 
                   : state latch := fun l =>
    match l with
    | Even E => sync_even c st n E
    | Odd o  => sync_odd c st n o
    end.

  Lemma sync_eval_odd_0 : forall c st O,
        sync_eval c st 0 (Odd O) = st (Odd O).
  Proof.
    intros. reflexivity.
  Qed.


  (* NOTE: if your execution model starts with the clock going low (e.g. even
     first), then you would need to reverse the order of synchronous execution. *)

  Lemma sync_eval_even : forall (c : circuit) (st : state latch) n E,
        sync_eval c st (S n) (Even E) = next_state_even c E (odd_state (sync_eval c st n)).
  Proof. auto. Qed.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = next_state_odd c O (even_state (sync_eval c st (S n))).
  Proof. auto. Qed.

  Lemma sync_eval_S : forall c init_st n l st,
    (forall l', neighbor c l' l ->
                 st l' = match l with
                        | Even _ => sync_eval c init_st n l'
                        | Odd _  => sync_eval c init_st (S n) l'
                        end) ->
    sync_eval c init_st (S n) l = next_state c st l.
  Proof.
    intros c init_st n [O | E] st Hst; subst.
      + simpl. apply f_equal. apply functional_extensionality. intros [E HE]. simpl.
        unfold even_state. simpl. rewrite Hst; auto. constructor; auto.
      + simpl. apply f_equal. apply functional_extensionality. intros [O HO]. simpl.
        unfold odd_state. simpl. rewrite Hst; auto. constructor; auto.
  Qed.


(*
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
*)

End Circuits.

(*Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).*)
(*
Notation "{ c // init_st }⊢ l ⇓^{ n } v" := (sync_rel c init_st n l v) (no associativity, at level 80).
*)

(******************)
(** Marked graphs *)
(******************)

Section MarkedGraphs.

  Variable transition : Set.
  Variable place : Set.

  Definition marking := place -> nat.

  Record marked_graph :=
  { mg_triples : transition -> place -> transition -> Prop
  ; mg_init    : marking
  }.

  Context `{Htransition : eq_dec transition} `{Hplace : eq_dec place}.

  Definition is_enabled (M : marked_graph)
                        (e : transition)
                        (m : marking) :=
    forall (p : place), (exists e0, mg_triples M e0 p e) -> 0 < m p.


  Class mg_input_dec (M : marked_graph) :=
    { input_dec : forall t p, {exists t', mg_triples M t p t'} + {~exists t', mg_triples M t p t'} }.
  Class mg_output_dec (M : marked_graph) :=
    { output_dec : forall p t, {exists t', mg_triples M t' p t} + {~exists t', mg_triples M t' p t} }.

  Arguments input_dec M {mg_input_dec}.
  Arguments output_dec M {mg_output_dec}.


  (* An event should only fire if the caller has independently checked that it
  is enabled. *) 
  Definition fire (t : transition)
                  (M : marked_graph) `{mg_input_dec M} `{mg_output_dec M}
                  (m : marking)
                : marking :=
  fun p => if output_dec M p t (* if ∃ t', t' →p→ t *)
           then m p - 1 (* remove markings on in-edges of e *)
           else if input_dec M t p (* if ∃ t', t →p→ t' *)
           then m p + 1 (* add marking to out-edges of e *)
           else m p.


(*
  (* A marked graph is one such that each place has preset(p) <= 1 and postset(p) <= 1. *)
  Definition wf_marked_graph (M : marked_graph) :=
    forall p t1 t2 t1' t2', mg_triples M t1 p t2 ->
                            mg_triples M t1' p t2' ->
                            t1 = t1' /\ t2 = t2'.
*)


End MarkedGraphs.

(*********************)
(** Flow Equivalence *)
(*********************)


Arguments mg_triples {transition place}.


Lemma map_in : forall {A B : Type} (f : A -> B) (l : list A) (x : B),
    In x (map f l) ->
    exists y, In y l /\ x = f y.
Proof.
  induction l; intros x H.
  * inversion H.
  * simpl in H.
    destruct H as [H | H]; subst.
    + simpl. exists a; auto.
    + destruct (IHl x H) as [Y [H1 H2]].
      subst. exists Y. simpl. auto.
Qed.

Section FlowEquivalence.


  Reserved Notation "{ MG }⊢ s ↓ m" (no associativity, at level 90).

  Arguments mg_init {transition place}.
  Arguments is_enabled {transition place}.
  Arguments fire {transition place} t M {M_input_dec M_output_dec} : rename.

  Arguments mg_input_dec {transition place}.
  Arguments mg_output_dec {transition place}.


(*
  Inductive consistent_P {place : Set} `{Hplace : eq_dec place}
                         (M : marked_graph event place)
                        `{Hinput : mg_input_dec _ _ M} `{Houtput : mg_output_dec _ _ M}
                         (P : transparency_predicate)
                       : marking place -> latch -> Prop :=
  | consistent_rise m l : is_enabled M (Rise l) m -> P l = Opaque -> consistent_P M P m l
  | consistent_fall m l : is_enabled M (Fall l) m -> P l = Transparent -> consistent_P M P m l  
  | consistent_next m l : 
    ~ is_enabled M (Rise l) m ->
    ~ is_enabled M (Fall l) m ->
    (forall e, is_enabled M e m -> consistent_P M P (fire e M m) l) ->
    consistent_P M P m l
  .
*)

  Inductive ls_consistent_with_MG {place : Set} `{Hplace : eq_dec place}
                                  (M : marked_graph event place)
                                  `{Hinput : mg_input_dec _ _ M} `{Houtput : mg_output_dec _ _ M}
                                : trace -> marking place -> Prop :=
  | lsc_empty P : 
    (forall l, is_enabled M (Rise l) (mg_init M) -> P l = Opaque) ->
    (forall l, is_enabled M (Fall l) (mg_init M) -> P l = Transparent) ->
    {M}⊢ empty_trace P ↓ mg_init M
  | lsc_cons e m m' t' : is_enabled M e m ->
                fire e M m = m' ->
                {M}⊢ t' ↓ m ->
                {M}⊢ next_trace t' e ↓ m'
  where
    "{ MG }⊢ s ↓ m'" := (ls_consistent_with_MG MG s m').


  Definition flow_equivalence {place : Set} `{Hplace : eq_dec place}
                              (M : marked_graph event place)
                              `{Hinput : mg_input_dec _ _ M} `{Houtput : mg_output_dec _ _ M}
                              (c : circuit) 
                              (init_st : state latch) :=
    forall l t v,
      async_rel c init_st l Opaque t v ->
      (exists m, {M}⊢ t ↓ m) ->
       v = sync_eval c init_st (num_events (Fall l) t) l.


End FlowEquivalence.

End FE.

Arguments flow_equivalence {even odd Heven Hodd place Hplace} M {Hinput Houtput}.

Arguments ls_consistent_with_MG {even odd place Hplace} M {Hinput Houtput}.

Arguments mg_triples {transition place}.
Arguments mg_init {transition place}.

Notation "{ MG }⊢ s ↓ m'" := (ls_consistent_with_MG MG s m')
                             (no associativity, at level 90).


Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments transparent {even odd Heven Hodd}.

Arguments empty_trace {even odd}.
Arguments next_trace {even odd}.

Arguments neighbor {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.
Arguments num_events {even odd Heven Hodd}.

(*Arguments eval {even odd Heven Hodd}.*)
(*Notation " c '⊢' st '⇒' s '⇒' st' " := (eval c st s st') (no associativity, at level 80).*)

Arguments odd_even_neighbors {even odd}.
Arguments even_odd_neighbors {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.

Arguments next_state {even odd}.


(*Arguments preset {transition place}.*)


(*Arguments enabled {transitions places Htransitions}.*)
Arguments fire {transition place} t M {Hinput Houtput} : rename.


Arguments next_state_odd {even odd}.
Arguments next_state_even {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.
Arguments sync_eval {even odd}.
Arguments is_enabled {transition place}.
(*
Arguments respects_transparencies {even odd}.
Arguments opaque_equivalence {even odd}.
*)

Arguments update_transparency_predicate {even odd Heven Hodd}.


(*Arguments sync_rel {even odd}.
Notation "< c // init_st >⊢ l ⇓^{ n } v" := (sync_rel c init_st n l v) (no associativity, at level 80).
*)

Existing Instance event_eq_dec.
 
(*Arguments async_step {even odd Heven Hodd}.*)
Arguments async_rel {even odd Heven Hodd}.

Arguments mg_input_dec {transition place}.
Arguments mg_output_dec {transition place}.


Module FE_Tactics.
Ltac reduce_transparent := try unfold update_transparency_predicate in *; simpl in *; reduce_eqb.
End FE_Tactics.
