Require Import Circuit.
Import Circuit_Tactics.

Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Monad.



Require Import PeanoNat.
Infix "<?" := (Nat.ltb).

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Omega. 

(** * Definition of fall-decoupled marked graph *)
Section FallDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive fd_place : event (latch even odd) bool -> event (latch even odd) bool -> Set :=

  | latch_fall l : fd_place (Rise l) (Fall l)
  | latch_rise l : fd_place (Fall l) (Rise l)
  (* E+ → O+ for (E,O) *)
  (* O+ → E+ for (O,E) *)
  | neighbor_rise_rise l l' : neighbor c l l' ->
                              fd_place (Rise l) (Rise l')
  (* O- → E+ for (E,O) *)
  (* E- → O+ for (O,E) *)
  | neighbor_fall_rise l l' : neighbor c l l' ->
                              fd_place (Fall l') (Rise l)
  .


  Definition fall_decoupled 
           : marked_graph (event (latch even odd) bool) :=
    {| place := fd_place
     ; init_marking := fun t1 t2 p => match p with
                                      | neighbor_rise_rise (Odd _) (Even _) _ => 1
                                      | latch_rise (Even _) => 1
                                      | latch_fall (Odd _) => 1
                                      | _ => 0
                                      end
   |}.


(** * Specialized is_enabled predicate *)
Inductive is_enabled_FD : event (latch even odd) bool -> marking fall_decoupled -> Prop :=

| fall_enabled_FD l (m : marking fall_decoupled) :
    0 < m _ _ (latch_fall l) ->
    is_enabled_FD (Fall l) m

| rise_enabled_RD l (m : marking fall_decoupled) :
    0 < m _ _ (latch_rise l) ->
    (forall l0 (pf : neighbor c l0 l),
        0 < m _ _ (neighbor_rise_rise l0 l pf)) ->
    (forall l' (pf : neighbor c l l'),
        0 < m _ _ (neighbor_fall_rise l l' pf)) ->
    is_enabled_FD (Rise l) m.



Lemma FD_is_enabled_equiv : forall e m,
    is_enabled_FD e m -> is_enabled fall_decoupled e m.
Proof.
  destruct e as [[O | E] [ | ]];
    intros m; inversion 1; subst;
    intros e0 p;
    simpl in p;
    dependent destruction p;
    auto.
Qed.


Lemma is_enabled_FD_equiv : forall e m,
    is_enabled fall_decoupled e m ->
    is_enabled_FD e m.
Proof.
  intros e m Henabled.
  unfold is_enabled in *.
  destruct e as [[O | E] [ | ]];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.
  


Ltac get_enabled_constraints :=
  try match goal with
  | [ H : is_enabled fall_decoupled _ _ |- _ ] => apply is_enabled_FD_equiv in H; inversion H; subst
  end; specialize_enabled_constraints.

(** * Helper lemmas *)
Section loop_lemmas.

  Variable t : trace (latch even odd) bool.
  Variable m : marking fall_decoupled.

  Hypothesis fd_t_m : [fall_decoupled]⊢ t ↓ m.

  Lemma fd_loop : forall l,
    m _ _ (latch_fall l) + m _ _ (latch_rise l) = 1.
  Proof.
    intros. solve_loop. destruct l; auto.
    (*
    induction fd_t_m; intros [O | E]; try reflexivity.
    + specialize (IHm0 m0 (Odd O)).
      subst; unfold fire;
      repeat compare_next; get_enabled_constraints; try omega.
    + specialize (IHm0 m0 (Even E)).
      subst; unfold fire;
      repeat compare_next; get_enabled_constraints; try omega.
    *)
  Qed.

  Lemma fd_loop_neighbor : forall l l' (pf : neighbor c l l'),
      m _ _ (latch_fall l') + m _ _ (neighbor_fall_rise _ _ pf)
                            + m _ _ (neighbor_rise_rise _ _ pf) = 1.
  Proof.
    intros.
    solve_loop.
    destruct pf; auto.
(*
    induction fd_t_m; intros [O | E] [O' | E'] pf;
      try reflexivity;
      find_event_contradiction;
      subst; unfold fire;
      repeat (compare_next; find_event_contradiction);
        get_enabled_constraints;
        simpl in *;
        try omega.
*)
  Qed.


End loop_lemmas.

Section fd_lemmas.

  Variable t : trace (latch even odd) bool.
  Variable m : marking fall_decoupled.

  Hypothesis fd_t_m : [fall_decoupled]⊢ t ↓ m.

  Lemma marking_fall : forall l,
    m _ _ (latch_fall l) = match transparent t l with
                         | Opaque => 0
                         | Transparent => 1
                         end.
  Proof.
    induction fd_t_m; intros l; auto.
    * destruct l; auto.
    * simpl.
      set (loop := fd_loop t' m m0 l);
      subst. unfold fire. 
      repeat compare_next.
      { get_enabled_constraints. omega. }
      { get_enabled_constraints. omega. }
      { rewrite IHm0; auto. }
  Qed.

  Lemma marking_rise : forall l,
    m _ _ (latch_rise l) = match transparent t l with
                         | Opaque => 1
                         | Transparent => 0
                         end.
  Proof.
    induction fd_t_m; intros l; auto.
    * destruct l; auto.
    * simpl.
      set (loop := fd_loop t' m m0 l).
      subst. unfold fire. 
      repeat compare_next.
      { get_enabled_constraints. omega. }
      { get_enabled_constraints. omega. }
      { rewrite IHm0; auto. }
  Qed.

  Lemma odd_num_events : forall O,
    ( m _ _ (latch_rise (Odd O)) > 0 ->
      num_events (Fall (Odd O)) t = 1+num_events (Rise (Odd O)) t)
    /\
    ( m _ _ (latch_fall (Odd O)) > 0 ->
      num_events (Fall (Odd O)) t = num_events (Rise (Odd O)) t).
  Proof.
    induction fd_t_m; intros O; split; intros Hrise; auto.
    { contradict Hrise. simpl. inversion 1. }
    { simpl in *.
      set (loop := fd_loop t' m m0 (Odd O)).
      specialize (IHm0 m0 O).
      destruct IHm0 as [IH1 IH2].
      subst; unfold fire in Hrise.
      repeat compare_next; reduce_eqb.
      { rewrite IH2; auto. }
      { contradict Hrise. omega. }
      { apply IH1; auto. }
    }
    { simpl in *.
      set (loop := fd_loop t' m m0 (Odd O)).
      specialize (IHm0 m0 O).
      destruct IHm0 as [IH1 IH2].
      subst; unfold fire in Hrise.
      repeat compare_next; reduce_eqb.
      { contradict Hrise. omega. }
      { rewrite IH1; auto. }
      { apply IH2; auto. }
    }
  Qed.

  Lemma even_num_events : forall E,
    ( m _ _ (latch_rise (Even E)) > 0 ->
      num_events (Rise (Even E)) t = num_events (Fall (Even E)) t)
    /\
    ( m _ _ (latch_fall (Even E)) > 0 ->
      num_events (Rise (Even E)) t = 1+num_events (Fall (Even E)) t).
  Proof.
    induction fd_t_m; intros E; split; intros Hrise; auto.
    { contradict Hrise. simpl. inversion 1. }
    { simpl in *.
      set (loop := fd_loop t' m m0 (Even E)).
      specialize (IHm0 m0 E).
      destruct IHm0 as [IH1 IH2].
      subst; unfold fire in Hrise.
      repeat compare_next; reduce_eqb.
      { contradict Hrise. omega. }
      { rewrite IH2; auto. }
      { rewrite IH1; auto. }
    }
    { simpl in *.
      set (loop := fd_loop t' m m0 (Even E)).
      specialize (IHm0 m0 E).
      destruct IHm0 as [IH1 IH2].
      subst; unfold fire in Hrise.
      repeat compare_next; reduce_eqb.
      { rewrite IH1; auto. }
      { contradict Hrise. omega. }
      { apply IH2; auto. }
    }
  Qed.

  Lemma opaque_num_events : forall l,
    transparent t l = Opaque ->
    num_events (Fall l) t = match l with
                            | Odd _ => 1+num_events (Rise l) t
                            | Even _ => num_events (Rise l) t
                            end.
  Proof.
    intros [O | E] Hopaque.
    * destruct (odd_num_events O) as [H _].
      rewrite H; auto.
      rewrite marking_rise.
      rewrite Hopaque.
      auto.
    * destruct (even_num_events E) as [H _].
      rewrite H; auto.
      rewrite marking_rise.
      rewrite Hopaque.
      auto.
  Qed.

  Lemma transparent_num_events : forall l,
    transparent t l = Transparent ->
    num_events (Rise l) t = match l with
                            | Odd _ => num_events (Fall l) t
                            | Even _ => 1+num_events (Fall l) t
                            end.
  Proof.
    intros [O | E] Htransparent.
    * destruct (odd_num_events O) as [_ H].
      rewrite H; auto.
      rewrite marking_fall.
      rewrite Htransparent.
      auto.
    * destruct (even_num_events E) as [_ H].
      rewrite H; auto.
      rewrite marking_fall.
      rewrite Htransparent.
      auto.
  Qed.


  Section even_odd.
    Variable E : even.
    Variable O : odd.
    Hypothesis Hin : neighbor c (Even E) (Odd O).
    
    Lemma even_odd_num_events : 
       (m _ _ (latch_fall (Odd O)) > 0 ->
        num_events (Rise (Even E)) t = num_events (Rise (Odd O)) t)
    /\ (m _ _ (neighbor_fall_rise _ _ Hin) > 0 ->
        num_events (Rise (Even E)) t = num_events (Rise (Odd O)) t)
    /\ (m _ _ (neighbor_rise_rise _ _ Hin) > 0 ->
        num_events (Rise (Even E)) t = 1+num_events (Rise (Odd O)) t).
    Proof.
      induction fd_t_m;
        try set (Hloop := fd_loop_neighbor t' m m0 _ _ Hin);
        try destruct (IHm0 m0) as [IH1 [IH2 IH3]];
        repeat split; intros Hgt; simpl in *; auto;
        find_contradiction;
        subst; unfold fire in Hgt;
        try (repeat compare_next; auto;
             get_enabled_constraints; contradict Hgt; omega).
    Qed.
  End even_odd.

  Section odd_even.
    Variable O : odd.
    Variable E : even.
    Hypothesis Hin : neighbor c (Odd O) (Even E). 
    
    Lemma odd_even_num_events : 
       (m _ _ (latch_fall (Even E)) > 0 ->
        num_events (Rise (Even E)) t = 1+num_events (Rise (Odd O)) t)
    /\ (m _ _ (neighbor_fall_rise _ _ Hin) > 0 ->
        num_events (Rise (Even E)) t = 1+ num_events (Rise (Odd O)) t)
    /\ (m _ _ (neighbor_rise_rise _ _ Hin) > 0 ->
        num_events (Rise (Even E)) t = num_events (Rise (Odd O)) t).
    Proof.
      induction fd_t_m;
        try set (Hloop := fd_loop_neighbor t' m m0 _ _ Hin);
        try destruct (IHm0 m0) as [IH1 [IH2 IH3]];
        repeat split; intros Hgt; simpl in *; auto;
        find_contradiction;
        subst; unfold fire in Hgt;
        try (repeat compare_next; auto;
             get_enabled_constraints; contradict Hgt; omega).
  Qed.
  End odd_even.
  

  Lemma transparent_neighbor_num_events : forall l,
    transparent t l = Transparent ->
    forall l' (pf : neighbor c l' l),
      num_events (Rise l) t = match l with
                              | Even _ => 1+num_events (Rise l') t
                              | Odd _ => num_events (Rise l') t
                              end.
  Proof.
    intros [O | E] Htransparent l' pf; inversion pf; subst.
    * destruct (even_odd_num_events _ _ pf) as [H _].
      rewrite H; auto.
      rewrite marking_fall.
      rewrite Htransparent.
      auto.

    * destruct (odd_even_num_events _ _ pf) as [H _].
      rewrite H; auto.
      rewrite marking_fall.
      rewrite Htransparent.
      auto.
  Qed.
  
End fd_lemmas.

  (** * Flow equivalence proof *)

  (** Induction invariant *)
  Lemma fall_decoupled_strong : forall l t o v,
    ⟨ c , init_st ⟩⊢ t ↓ l ↦{ o } v ->
      forall m, [fall_decoupled]⊢ t ↓ m ->
      forall n,
      n = match l with
          | Odd _  => 1+num_events (Rise l) t
          | Even _ => num_events (Rise l) t
          end ->
      v = sync_eval c init_st n l.
  Proof.
    intros l t O v Hrel.
    induction Hrel; intros m Hm n Hn.
    * (* Because l is opaque in the initial marking, l must be even. *)
      inversion Hm; subst. auto.
    * (* l is transparent *)
      rewrite H2.

      assert (n > 0).
      { (* n > 0 *)
        subst.
        destruct l as [O | E]; try omega.
        erewrite transparent_num_events; eauto.
        omega.
      }

      erewrite sync_eval_gt; eauto.


    intros l' Hl'. 
    erewrite H1; eauto.

    transitivity (sync_eval c init_st (num_events (Rise l) t) l').
    2:{ inversion Hl'; f_equal; subst; omega. }

    f_equal.
    erewrite transparent_neighbor_num_events with (l := l); eauto.
    inversion Hl'; auto.

  * inversion Hm; subst.
    simpl in *.
    compare_next.
    erewrite IHHrel; eauto.

  * inversion Hm.
    assert (n > 0).
    { subst. destruct l as [O | E]; try omega.
      set (Hopaque := opaque_num_events _ _ Hm (Even E)).
      simpl in Hopaque.
      compare_next.
      specialize (Hopaque eq_refl).
      simpl.
      compare_next.
      rewrite <- Hopaque; omega.
    }

    erewrite sync_eval_gt; eauto.
    intros l' Hl'.

    inversion Hm; subst.

    erewrite H1; eauto.

    assert (transparent t' l = Transparent).
    { get_enabled_constraints.
      rewrite marking_fall with (t := t') in *; auto.
      destruct (transparent t' l); auto; find_contradiction. 
    }
    simpl.
    transitivity (sync_eval c init_st (num_events (Rise l) t') l').
    2:{ destruct l; compare_next; simpl; f_equal; omega. }

    f_equal.
    erewrite transparent_neighbor_num_events with (l := l) (l' := l'); eauto.
    inversion Hl'; auto.
Qed.


  (** Main theorem statement *)
  Theorem fall_decoupled_flow_equivalence :
    flow_equivalence fall_decoupled c init_st.
  Proof.
    intros l t v [m Hm] Heval.
    erewrite (fall_decoupled_strong l t Opaque v Heval m Hm); eauto.
    erewrite opaque_num_events; eauto.
    { eapply async_b; eauto. }
  Qed.

End FallDecoupled.
