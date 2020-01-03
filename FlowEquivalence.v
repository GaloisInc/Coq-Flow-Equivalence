Require Export Base.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.

Require Import Lia (* Linear integer arithmetic tactics *).


Section FE.

(** Even and odd latches *)
Variable even odd : Set.

(** Decidable equality *)
Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.  

(** * Latches, events, and traces *)
Section LatchSequence.

  (** Latches are either even or odd *)
  Inductive latch : Set := 
  | Odd : odd -> latch
  | Even : even -> latch
  .

  (** Events are either the rise or fall of a latch's clock *)
  Inductive event : Set :=
  | Rise : latch -> event
  | Fall : latch -> event
  . 

  (** A transparency state records whether latches are currently transparent or opaque. *)
  Inductive transparency := Transparent | Opaque.
  Definition tstate := latch -> transparency.

  (** Decidability *)
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

  (** Tail/snoc lists *)
  Inductive tail_list (A : Type) :=
  | t_empty : tail_list A
  | t_next : tail_list A -> A -> tail_list A.
  Arguments t_empty {A}.
  Arguments t_next {A}.
  Infix "▶" := t_next (left associativity, at level 73).

  (** A trace is a list of events *)
  Definition trace := tail_list event.

  (** Calculate the set of transparent latches after executing the trace t *)
  Fixpoint transparent (t : trace) : tstate :=
    match t with
    | t_empty => fun l => match l with
                          | Even _ => Opaque
                          | Odd _ => Transparent
                          end
    | t' ▶ e => fun l => if Rise l =? e then Transparent
                              else if Fall l =? e then Opaque
                              else transparent t' l
    end.

  (** Calculate the number of occurrences of an event in a trace *)
  Fixpoint num_events (e : event) (t : trace) : nat :=
    match t with
    | t_empty => 0
    | t' ▶ e' => if e =? e'
                 then 1 + num_events e t'
                 else num_events e t'
    end.


End LatchSequence.

Arguments t_empty {A}.
Arguments t_next {A}.
Infix "▶" := t_next (left associativity, at level 73).

Existing Instance event_eq_dec.


(** * Circuits *)
Section Circuits.

  (** Latches need not hold single bits; in practice, they will hold numeric
  values *)
  Inductive value := 
  | Num : nat -> value
  | X  : value.

  (** A state (e.g. of a set of latches) maps each of those latches to values *)
  Definition state (tp : Set) := tp -> value.

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
                    : trace -> latch -> transparency -> value -> Prop :=
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
  * reduce_eqb; find_contradiction. 
  * compare (Rise l) e.
    eapply IHasync; eauto.
  * reduce_eqb; find_contradiction.
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


(** * Marked graphs *)
Section MarkedGraphs.

  Variable transition : Set.
  Context `{Htransition : eq_dec transition}.

  Record marked_graph :=
  { place : transition -> transition -> Set
  ; init_marking : forall t1 t2, place t1 t2 -> nat
  }.

  Definition marking (M : marked_graph) := forall t1 t2, place M t1 t2 -> nat.

  Definition is_enabled (M : marked_graph)
                        (t : transition)
                        (m : marking M) :=
    forall (t0 : transition) (p : place M t0 t), 0 < m _ _ p.

  (** A transition should only fire if the caller has independently checked that it
  is enabled. *) 
  Definition fire (t : transition) 
                  (M : marked_graph)
                  (m : marking M)
                : marking M :=
    fun tin tout p =>
        if tin =? tout
        then m _ _ p (* corner case *)
        else if t =? tout (* i.e. if p occurs before t *)
        then m _ _ p - 1
        else if t =? tin (* i.e. if p occurs after t *)
        then m _ _ p + 1
        else m _ _ p.

  (** Reachability *)
  Reserved Notation "{ MG }⊢ t ↓ m" (no associativity, at level 90). 
  Inductive mg_reachable (M : marked_graph)
                        : tail_list transition -> marking M -> Prop :=
  | mg_empty : {M}⊢ t_empty ↓ init_marking M
  | mg_cons : forall e m m' t',
    is_enabled M e m ->
    fire e M m = m' ->
    {M}⊢ t' ↓ m ->
    {M}⊢ t' ▶ e ↓ m'
  where
    "{ MG }⊢ t ↓ m'" := (mg_reachable MG t m').


  (** * Paths and loops in a marked graph *)
  Inductive mg_path (M : marked_graph) : transition -> transition -> Set :=
  | mg_single_path t1 t2 : place M t1 t2 -> mg_path M t1 t2
  | mg_step_path t1 t2 t3 : place M t1 t2 -> mg_path M t2 t3 -> mg_path M t1 t3
  .
  Arguments mg_single_path {M t1 t2}.
  Arguments mg_step_path {M t1 t2 t3}.
  Definition mg_loop (M : marked_graph) (t : transition) := mg_path M t t.

  (** Add up the markings on each leg of the path *)
  Fixpoint path_cost {M} {t1 t2} (m : marking M) (p : mg_path M t1 t2) : nat :=
    match p with
    | mg_single_path p => m _ _ p
    | mg_step_path p p' => m _ _ p + path_cost m p'
    end.

  Definition addZ (n : nat) (z : Z) : nat := Z.to_nat (Z.of_nat n + z).
(*
    match z with
    | Z0 => n
    | Zpos p => n + Pos.to_nat p
    | Zneg p => n - Pos.to_nat p
    end.
*)

Lemma addZ_N_assoc : forall n1 n2 z,
    (0 <= Z.of_nat n2 + z)%Z ->
    addZ (n1 + n2) z = n1 + addZ n2 z.
Proof.
  intros.
  unfold addZ. 
  rewrite Nat2Z.inj_add.

  rewrite <- Z.add_assoc.
  rewrite Z2Nat.inj_add.
  2:{ apply Nat2Z.is_nonneg. }
  rewrite Nat2Z.id; auto.
  auto.
Qed.

Lemma addZ_0 : forall n, addZ n 0%Z = n.
Proof.
  intros. unfold addZ. 
  replace (Z.of_nat n + 0)%Z with (Z.of_nat n) by lia.
  rewrite Nat2Z.id.
  reflexivity.
Qed.
Hint Resolve addZ_0 : addZ.
Lemma addZ_neg1 : forall n, n > 0 -> addZ n (-1) = n - 1.
Proof.
  intros. unfold addZ.
  replace (Z.of_nat n + (-1))%Z with (Z.of_nat (n-1)) by lia.
  rewrite Nat2Z.id. reflexivity.
Qed.
Hint Resolve addZ_neg1 : addZ.

Lemma addZ_minus : forall n z, addZ n (z - 1) = addZ n z - 1.
Proof.
  intros. unfold addZ.
  rewrite Z.add_sub_assoc.
  rewrite Z2Nat.inj_sub; auto.
  lia.
Qed.

Lemma addZ_pos1 : forall n, addZ n 1 = n + 1.
Proof.
  intros. unfold addZ.
  replace (Z.of_nat n + 1)%Z with (Z.of_nat (n+1)) by lia.
  rewrite Nat2Z.id. reflexivity.
Qed.
Hint Resolve addZ_pos1 : addZ.

Lemma addZ_plus : forall n z, (0 <= Z.of_nat n + z)%Z -> addZ n (1+z) = 1+addZ n z.
Proof.
  intros. unfold addZ.
  transitivity (Z.to_nat (1 + (Z.of_nat n + z))%Z).
  { f_equal. lia. }

  rewrite Z2Nat.inj_add; auto.
  { lia. }
Qed.


  (** After firing the transition t, update the accumulator by the effect on the place p. *)
  Definition fire_effect (t : transition) {M t1 t2} (p : place M t1 t2) : Z :=
    if andb (t =? t2) (t =? t1) then 0
    else if t =? t1 then 1
    else if t =? t2 then -1
    else 0.

  (** After firing the transition t, update the accumulator by the effect on the path p. *)
  Fixpoint path_effect (t : transition) {M t1 t2} (p : mg_path M t1 t2) : Z :=
    match p with
    | mg_single_path p => fire_effect t p
    | mg_step_path p p' => fire_effect t p + path_effect t p'
    end.




Lemma path_effect_result : forall M t1 t2 (p : mg_path M t1 t2) t,
     (t <> t1 -> t <> t2 -> path_effect t p = 0%Z)
  /\ (t = t1 -> t <> t2 -> path_effect t p = 1%Z)
  /\ (t = t2 -> t <> t1 -> path_effect t p = (-1)%Z )
  /\ (t = t1 -> t = t2 -> path_effect t p = 0%Z).
Proof.
  induction p; intros; 
    try (specialize (IHp t); destruct IHp as [IH1 [IH2 [IH3 IH4]]]);
    repeat split; intros;
    simpl; unfold fire_effect; subst; reduce_eqb;
    try reflexivity.
  * compare_next.
    { rewrite IH2; auto. }
    { rewrite IH1; auto. }
  * compare_next.
    { rewrite IH2; auto. }
    { rewrite IH1; auto. }
  * compare_next.
    { rewrite IH4; auto. }
    { rewrite IH3; auto. }
  * compare_next.
    { rewrite IH4; auto. }
    { rewrite IH3; auto. }
Qed.

Lemma path_effect_neq : forall M t1 t2 (p : mg_path M t1 t2) t,
     t <> t1 -> t <> t2 -> path_effect t p = 0%Z.
Proof.
  intros. destruct (path_effect_result M t1 t2 p t) as [IH1 [IH2 [IH3 IH4]]].
  rewrite IH1; auto.
Qed.
    
Lemma path_effect_eq : forall M t1 t2 (p : mg_path M t1 t2) t,
      t = t1 -> t = t2 -> path_effect t p = 0%Z.
Proof.
  intros. destruct (path_effect_result M t1 t2 p t) as [IH1 [IH2 [IH3 IH4]]].
  rewrite IH4; auto.
Qed.
Lemma path_effect_input : forall M t1 t2 (p : mg_path M t1 t2) t,
     t = t1 -> t <> t2 -> path_effect t p = 1%Z.
Proof.
  intros. destruct (path_effect_result M t1 t2 p t) as [IH1 [IH2 [IH3 IH4]]].
  rewrite IH2; auto.
Qed.
Lemma path_effect_output : forall M t1 t2 (p : mg_path M t1 t2) t,
     t = t2 -> t <> t1 -> path_effect t p = (-1)%Z.
Proof.
  intros. destruct (path_effect_result M t1 t2 p t) as [IH1 [IH2 [IH3 IH4]]].
  rewrite IH3; auto.
Qed.


  Lemma enabled_fact : forall M t1 t2 (p : mg_path M t1 t2) e m,
    is_enabled M e m ->
    (0 <= Z.of_nat (path_cost m p) + path_effect e p)%Z.
  Proof.
    induction p; intros.
    +  simpl. unfold fire_effect.
      repeat compare_next; simpl; try lia.
      assert (m t1 t2 p > 0). { apply H. }
      omega.
    + simpl. specialize (IHp e m H).
      rewrite Nat2Z.inj_add.
      repeat rewrite Z.add_assoc.
      unfold fire_effect.
      repeat compare_next; simpl; try lia.
      assert (m _ _ p > 0) by apply H.
      omega.
  Qed.

  Lemma fire_preserves_paths : forall M t1 t2 (p : mg_path M t1 t2) e m,
    is_enabled M e m ->
    path_cost (fire e M m) p = addZ (path_cost m p) (path_effect e p).
  Proof.
    intros M t1 t2 p.
    induction p; intros e m Henabled.
    + simpl. unfold fire_effect. unfold fire.
      repeat compare_next; simpl; auto with addZ.
      assert (m _ _ p > 0).
      { apply Henabled. }
      rewrite addZ_neg1; auto.
    + assert (Hfact : (0 <= Z.of_nat (path_cost m p0) + path_effect e p0)%Z)
        by (apply enabled_fact; auto).
      simpl.
      rewrite IHp; auto.
      unfold fire, fire_effect.
      repeat compare_next; try (simpl; auto with addZ; fail).
      { rewrite addZ_N_assoc; auto. }
      { rewrite addZ_N_assoc; auto. }
      { unfold andb.
        replace (-1 + path_effect t2 p0)%Z with (path_effect t2 p0 - 1)%Z by lia.
        rewrite addZ_minus.
        rewrite addZ_N_assoc; auto.
        assert (m _ _ p > 0) by apply Henabled.
        omega.
      }
      { unfold andb.
        rewrite addZ_N_assoc by lia.
        rewrite addZ_plus; try omega.
      }
      { unfold andb.
        rewrite addZ_N_assoc; auto.
      }
  Qed.
        

  Lemma fire_preserves_loops : forall M t (p : mg_loop M t) e m,
    is_enabled M e m ->
    path_cost (fire e M m) p = path_cost m p.
  Proof.
    intros.
    rewrite fire_preserves_paths; auto.
    compare e t.
    { rewrite path_effect_eq; auto with addZ. }
    { rewrite path_effect_neq; auto with addZ. }
  Qed.


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
      rewrite fire_preserves_loops; auto.
  Qed.


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
                              (st0 : state latch) :=
    forall l t v,
      (exists m, {M}⊢ t ↓ m) ->
      ⟨c,st0⟩⊢ t ↓ l ↦{Opaque} v ->
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

(*Arguments fire_tstate {even odd Heven Hodd}.*)


Existing Instance event_eq_dec.
 
Arguments async {even odd Heven Hodd}.
Notation "⟨ c , st ⟩⊢ t ↓ l ↦{ O } v" := (async c st t l O v) 
          (no associativity, at level 90).


Arguments marking {transition}.


Arguments t_empty {A}.
Arguments t_next {A}.
Infix "▶" := t_next (left associativity, at level 73).


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
End FE_Tactics.
