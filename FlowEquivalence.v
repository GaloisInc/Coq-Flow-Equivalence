Require Export Base.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.



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
  Definition tstate := latch -> opacity.

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


  Definition fire_tstate (e : event) (P : tstate) : tstate :=
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

  Inductive tail_list (A : Type) :=
  | t_empty : tail_list A
  | t_next : tail_list A -> A -> tail_list A.
  Arguments t_empty {A}.
  Arguments t_next {A}.
  Infix "▷" := t_next (left associativity, at level 73).


  Definition trace := tail_list event.

  (* Calculate the set of transparent latches after executing the trace t *)
  Fixpoint transparent (t : trace) (P : tstate) : tstate :=
    match t with
    | t_empty => P
    | t' ▷ e => fun l => if Rise l =? e then Transparent
                              else if Fall l =? e then Opaque
                              else transparent t' P l
    end.

  Fixpoint num_events (e : event) (t : trace) : nat :=
    match t with
    | t_empty => 0
    | t' ▷ e' => if e =? e'
                 then 1 + num_events e t'
                 else num_events e t'
    end.


End LatchSequence.

Arguments t_empty {A}.
Arguments t_next {A}.
Infix "▷" := t_next (left associativity, at level 73).

Existing Instance event_eq_dec.


(*************)
(** Circuits *)
(*************)

Section Circuits.

  (* Latches need not hold single bits; in practice, they will hold arbitrary values *)
  Inductive value := 
  | Bit : bool -> value
  | Int : Z -> value
  | X  : value.

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
  ; next_state_e (e : even) : state {o : odd  & In (o,e) odd_even_neighbors} -> value
  ; next_state_o  (o : odd)  : state {e : even & In (e,o) even_odd_neighbors} -> value
  }.

  Inductive neighbor c : latch -> latch  -> Prop :=
  | EO_neighbor E O : In (E,O) (even_odd_neighbors c) -> neighbor c (Even E) (Odd O)
  | OE_neighbor O E : In (O,E) (odd_even_neighbors c) -> neighbor c (Odd O) (Even E).


  Definition next_state (c : circuit) (st : state latch) (l : latch) : value :=
    match l with
    | Even e => next_state_e c e (odd_state st)
    | Odd o  => next_state_o c o (even_state st)
    end.

  (** Async execution *)


  Reserved Notation "⟨ c , st , P ⟩⊢ t ↓ l ↦{ O } v" (no associativity, at level 90).
  Inductive async (c : circuit) (st0 : state latch) (P0 : tstate)
                    : trace -> latch -> opacity -> value -> Prop :=
  | async_nil : forall l, 
    P0 l = Opaque ->
    ⟨c,st0,P0⟩⊢ t_empty ↓ l ↦{Opaque} st0 l

  | async_transparent : forall l t st v,
    transparent t P0 l = Transparent ->
    (forall l', neighbor c l' l -> ⟨c,st0,P0⟩⊢ t ↓ l' ↦{transparent t P0 l'} st l') ->
    v = next_state c st l ->
    ⟨c,st0,P0⟩⊢ t ↓ l ↦{Transparent} v

  | async_opaque : forall l e t' v,
    transparent (t' ▷ e) P0 l = Opaque ->
    e <> Fall l ->
    ⟨c,st0,P0⟩⊢ t' ↓ l ↦{Opaque} v ->
    ⟨c,st0,P0⟩⊢ t' ▷ e ↓ l ↦{Opaque} v

  | async_opaque_fall : forall l e t' v st,
    e = Fall l ->
    (forall l', neighbor c l' l -> ⟨c,st0,P0⟩⊢ t' ↓ l' ↦{transparent t' P0 l'} st l') ->
    v = next_state c st l ->
    ⟨c,st0,P0⟩⊢ t' ▷ e ↓ l ↦{Opaque} v

  where "⟨ c , st , P ⟩⊢ t ↓ l ↦{ O } v" := (async c st P t l O v).

Lemma async_b : forall c st0 P0 l b t v,
    ⟨c,st0,P0⟩⊢ t ↓ l ↦{b} v ->
    transparent t P0 l = b.
Proof.
  intros c st0 P0 l b t v H.
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


Lemma async_injective : forall c st0 P0 l b1 t v1,
    ⟨c,st0,P0⟩⊢ t ↓ l ↦{b1} v1 ->
    forall b2 v2, ⟨c,st0,P0⟩⊢ t ↓ l ↦{b2} v2 ->
    v1 = v2.
Proof.
  intros c st0 P0 l b1 t v1 H1.
  induction H1; intros b2 v2 H2';
    inversion H2'; subst; simpl in *; find_contradiction; auto.

  * apply next_state_eq.
    intros l' Hl'.
    eapply H1; eauto.
  * reduce_eqb; find_contradiction. 
  * compare (Rise l) e.
    eapply IHasync; eauto.
  * reduce_eqb; find_contradiction.
  * apply next_state_eq.
    intros l' Hl'.
    eapply H1; eauto.
Qed.

 
  (** Synchronous execution *)
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

  Fixpoint sync_eval (c : circuit) (st : state latch) (n : nat) : state latch :=
    match n with
    | 0 => st
    | S n' => sync_update_odd c (sync_update_even c (sync_eval c st n'))
    end.

  Lemma sync_eval_odd_0 : forall c st O,
        sync_eval c st 0 (Odd O) = st (Odd O).
  Proof.
    intros. reflexivity.
  Qed.


  (* NOTE: if your execution model starts with the clock going low (e.g. even
     first), then you would need to reverse the order of synchronous execution. *)

  Lemma sync_eval_even : forall (c : circuit) (st : state latch) n E,
        sync_eval c st (S n) (Even E) = next_state_e c E (odd_state (sync_eval c st n)).
  Proof. auto. Qed.
  Lemma sync_eval_odd : forall c st n O,
        sync_eval c st (S n) (Odd O) = next_state_o c O (even_state (sync_eval c st (S n))).
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

  Lemma sync_eval_gt : forall c init_st n l st,
    0 < n ->
    (forall l', neighbor c l' l ->
                 st l' = match l with
                        | Even _ => sync_eval c init_st (n-1) l'
                        | Odd _  => sync_eval c init_st n l'
                        end) ->
    sync_eval c init_st n l = next_state c st l.
  Proof.
    intros.
    destruct n; [find_contradiction | ].
    replace (S n - 1) with n in * by omega.
    apply sync_eval_S; auto.
  Qed.



End Circuits.

Notation "⟨ c , st , P ⟩⊢ t ↓ l ↦{ O } v" := (async c st P t l O v) (no associativity, at level 90).


(******************)
(** Marked graphs *)
(******************)

Section MarkedGraphs.

  Variable transition : Set.
  Context `{Htransition : eq_dec transition}.

  Record marked_graph :=
  { place : transition -> transition -> Set
  ; init_marking : forall t1 t2, place t1 t2 -> nat
  }.

  Definition marking (M : marked_graph) := forall t1 t2, place M t1 t2 -> nat.
(*
  Definition get_marking {M} {t1 t2} (m : marking M) (p : place M t1 t2) : nat := m _ _ p.
  Coercion get_marking : marking >-> Funclass.
*)

  Definition is_enabled (M : marked_graph)
                        (t : transition)
                        (m : marking M) :=
    forall (t0 : transition) (p : place M t0 t), 0 < m _ _ p.

  (* A transition should only fire if the caller has independently checked that it
  is enabled. *) 
  Definition fire (t : transition) 
                  (M : marked_graph)
                  (m : marking M)
                : marking M :=
    fun tin tout p =>
        if t =? tout (* i.e. if p occurs before t *)
        then m _ _ p - 1
        else if t =? tin (* i.e. if p occurs after t *)
        then m _ _ p + 1
        else m _ _ p.


(*
  (* A marked graph is one such that each place has preset(p) <= 1 and postset(p) <= 1. *)
  Definition wf_marked_graph (M : marked_graph) :=
    forall p t1 t2 t1' t2', mg_triples M t1 p t2 ->
                            mg_triples M t1' p t2' ->
                            t1 = t1' /\ t2 = t2'.
*)

  Reserved Notation "{ MG }⊢ t ↓ m" (no associativity, at level 90). 
  Inductive mg_reachable (M : marked_graph)
                        : tail_list transition -> marking M -> Prop :=
  | mg_empty : {M}⊢ t_empty ↓ init_marking M
  | mg_cons : forall e m m' t',
    is_enabled M e m ->
    fire e M m = m' ->
    {M}⊢ t' ↓ m ->
    {M}⊢ t' ▷ e ↓ m'
  where
    "{ MG }⊢ t ↓ m'" := (mg_reachable MG t m').


  Inductive mg_path (M : marked_graph) : transition -> transition -> Set :=
  | mg_single_path t1 t2 : place M t1 t2 -> mg_path M t1 t2
  | mg_step_path t1 t2 t3 : place M t1 t2 -> mg_path M t2 t3 -> mg_path M t1 t3
  .
  Arguments mg_single_path {M t1 t2}.
  Arguments mg_step_path {M t1 t2 t3}.
  Definition mg_loop (M : marked_graph) (t : transition) := mg_path M t t.

  Fixpoint path_cost {M} {t1 t2} (m : marking M) (p : mg_path M t1 t2) : nat :=
    match p with
    | mg_single_path p => m _ _ p
    | mg_step_path p p' => m _ _ p + path_cost m p'
    end.

  Definition fire_effect (t : transition) {M t1 t2} (p : place M t1 t2) (res : nat) : nat :=
    if t =? t2 then res-1
    else if t =? t1 then res+1
    else res.

  Fixpoint path_effect (t : transition) {M t1 t2} (p : mg_path M t1 t2) (res : nat) : nat :=
    match p with
    | mg_single_path p => fire_effect t p res
    | mg_step_path p p' => path_effect t p' (fire_effect t p res)
    end.

  Lemma fire_effect_plus : forall (t : transition) {M t1 t2} (p : place M t1 t2) (res1 res2 : nat),
    res2 > 0 ->
    fire_effect t p (res1 + res2) = res1 + fire_effect t p res2.
  Proof.
    induction res1; intros; auto.
    simpl.
    unfold fire_effect. 
    repeat compare_next; omega.
  Qed.

  Lemma path_effect_plus : forall (t : transition) {M t1 t2} (p : mg_path M t1 t2) (res1 res2 : nat),
    res2 > 0 ->
    path_effect t p (res1 + res2) = res1 + path_effect t p res2.
  Proof.
    induction p; intros.
    * simpl. apply fire_effect_plus; auto.
    * simpl.
      rewrite fire_effect_plus; auto.
      rewrite IHp; auto.
  Abort.

  Lemma fire_preserves_paths : forall M t1 t2 (p : mg_path M t1 t2) e m,
    is_enabled M e m ->
    path_cost (fire e M m) p = path_effect e p (path_cost m p).
  Proof.
    intros M t1 t2 p.
    induction p; intros e m Henabled.
    + simpl. reflexivity. 
    + simpl.
      rewrite IHp; auto.
      unfold fire.
      compare_next.
      ++ unfold is_enabled in Henabled.
         specialize (Henabled t1 p).
         unfold fire_effect.
         reduce_eqb.
         transitivity (path_effect t2 p0 ((m t1 t2 p - 1) + path_cost m p0)).
         2:{ f_equal. omega. }

         admit (*??*).
      ++ compare_next.
         2:{ 
   Abort.
   

  Lemma fire_preserves_loops : forall M t (p : mg_loop M t) e m,
    is_enabled M e m ->
    path_cost (fire e M m) p = path_cost m p.
  Abort.

  Lemma mg_preserves_loops : forall M ts m,
    {M}⊢ ts ↓ m ->
    forall t (p : mg_loop M t),
      path_cost m p = path_cost (init_marking M) p.
  Proof.
    intros M ts m Hm.
    induction Hm as [ | e m m' ts' Henabled Hfire Hm];
      intros t p.
    * reflexivity.
    * subst.
(*      rewrite fire_preserves_loops; auto.*)
  Abort.


End MarkedGraphs.

(*********************)
(** Flow Equivalence *)
(*********************)

Arguments mg_reachable {transition Htransition} M.
Notation "{ MG }⊢ s ↓ m" := (mg_reachable MG s m) (no associativity, at level 90).


Section FlowEquivalence.



  Arguments init_marking {transition}.
  Arguments is_enabled {transition}.
  Arguments fire {transition Htransition} t M.

(*
  Arguments mg_input_dec {transition place}.
  Arguments mg_output_dec {transition place}.
*)

  Definition flow_equivalence (M : marked_graph event)
                              (c : circuit) 
                              (st0 : state latch)
                              (P0 : tstate) :=
    forall l t v,
      (exists m, {M}⊢ t ↓ m) ->
      ⟨c,st0,P0⟩⊢ t ↓ l ↦{Opaque} v ->
       v = sync_eval c st0 (num_events (Fall l) t) l.


End FlowEquivalence.

End FE.

Arguments flow_equivalence {even odd Heven Hodd} M.

Arguments mg_reachable {transition Htransition} M.
Notation "{ MG }⊢ s ↓ m'" := (mg_reachable MG s m')
                             (no associativity, at level 90).


Arguments place {transition}.
Arguments init_marking {transition}.



Arguments Odd {even odd}.
Arguments Even {even odd}.
Arguments transparent {even odd Heven Hodd}.


Arguments neighbor {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.
Arguments num_events {even odd Heven Hodd}.


Arguments odd_even_neighbors {even odd}.
Arguments even_odd_neighbors {even odd}.

Arguments Rise {even odd}.
Arguments Fall {even odd}.

Arguments next_state {even odd}.



Arguments fire {transition place} t M {Hinput Houtput} : rename.


Arguments next_state_o {even odd}.
Arguments next_state_e {even odd}.
Arguments even_state {even odd P}.
Arguments odd_state {even odd P}.
Arguments sync_eval {even odd}.
Arguments is_enabled {transition}.

Arguments fire_tstate {even odd Heven Hodd}.


Existing Instance event_eq_dec.
 
Arguments async {even odd Heven Hodd}.
Notation "⟨ c , st , P ⟩⊢ t ↓ l ↦{ O } v" := (async c st P t l O v) 
          (no associativity, at level 90).


Arguments marking {transition}.
(*Arguments get_marking {transition} M {t1 t2}.*)


Arguments t_empty {A}.
Arguments t_next {A}.
Infix "▷" := t_next (left associativity, at level 73).


(*
Arguments mg_input_dec {transition place}.
Arguments mg_output_dec {transition place}.
*)

Module FE_Tactics.

Lemma neighbor_neq : forall {even odd} (c : circuit even odd) l l',
    neighbor c l l' -> l <> l'.
Proof.
  intros even odd c l l' H.
  destruct H; discriminate.
Qed.


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
End FE_Tactics.
