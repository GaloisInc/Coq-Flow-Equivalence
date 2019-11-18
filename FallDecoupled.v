Require Import FlowEquivalence.
Require Import List.
Import ListNotations.
Open Scope list_scope.



Require Import PeanoNat.
Infix "<?" := (Nat.ltb).

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Import Coq.Logic.ProofIrrelevance.


Section FallDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive transitions_FD : Set :=
  | Even_fall (A : even) : transitions_FD
  | Even_rise (A : even) : transitions_FD
  | Odd_fall  (B : odd) : transitions_FD
  | Odd_rise  (B : odd) : transitions_FD
  | Even_rise_odd_rise (E : even) (O : odd) : In (E,O) (even_odd_neighbors c) -> transitions_FD (* E+ → O+ *)
  | Odd_fall_even_rise (E : even) (O : odd) : In (E,O) (even_odd_neighbors c) -> transitions_FD (* O- → E+ *)
  | Odd_rise_even_rise (O : odd) (E : even) : In (O,E) (odd_even_neighbors c) -> transitions_FD (* O+ → E+ *)
  | Even_fall_odd_rise (O : odd) (E : even) : In (O,E) (odd_even_neighbors c) -> transitions_FD (* E- → O+ *)
  .
  Instance eqdecFD : eq_dec transitions_FD.
  Proof.
    split. intros t1 t2.
    destruct Heven as [Heven'], Hodd as [Hodd'].
    destruct t1; destruct t2; try (right; inversion 1; fail);
      try (destruct (Dec A A0) as [HA | HA];
        [subst; intuition | right; inversion 1; contradiction]);
      try (destruct (Dec B B0) as [HB | HB];
        [subst; intuition | right; inversion 1; contradiction]).
  Admitted.

  Definition fall_decoupled 
           : marked_graph (event even odd) transitions_FD :=
  {| mg_triples := 
     let eo_f := fun (E : even) (O : odd) pf =>
                     [ (Rise (Even E), Even_fall E, Fall (Even E))
                     ; (Fall (Even E), Even_rise E, Rise (Even E))
                     ; (Rise (Even E), Even_rise_odd_rise E O pf, Rise (Odd O))
                     ; (Fall (Odd O), Odd_fall_even_rise E O pf, Rise (Even E))
                     ; (Rise (Odd O), Odd_fall O, Fall (Odd O))
                     ]
     in
     let oe_f := fun (O : odd) (E : even) pf =>
                     [ (Rise (Odd O), Odd_fall O, Fall (Odd O))
                     ; (Fall (Odd O), Odd_rise O, Rise (Odd O))
                     ; (Rise (Odd O), Odd_rise_even_rise O E pf, Rise (Even E))
                     ; (Fall (Even E), Even_fall_odd_rise O E pf, Rise (Odd O))
                     ; (Rise (Even E), Even_fall E, Fall (Even E))
                     ]
     in flat_map_proof (even_odd_neighbors c) eo_f
     ++ flat_map_proof (odd_even_neighbors c) oe_f
   ; mg_init := fun p => match p with
                | Even_rise_odd_rise _ _ _ => 1
                | Even_fall _ => 1
                | Odd_rise _ => 1
                | _ => 0
                end
   |}.



  Lemma event_rise_invariant_fd : forall t m st st' l,
    {fall_decoupled}⊢ t ↓ m ->
    c ⊢ init_st ⇒t⇒ st ->
    async_step c (transparent t) st (Rise l) st' ->
    forall l', l' <> l -> st'(l') = st(l').
  Admitted.

  Lemma event_invariant_neq : forall t m st st' e,
    {fall_decoupled}⊢ t ↓ m ->
    c ⊢ init_st ⇒t⇒ st ->
    async_step c (transparent t) st e st' ->
    forall l, e <> Rise l -> st'(l) = st(l).
  Proof.
    intros t m st st' e Hm Hst Hstep l Hl.
    destruct e as [l' | l'].
    * eapply event_rise_invariant_fd; eauto.
      inversion 1; subst; contradiction.
    * eapply event_fall_invariant; eauto.
  Qed.



Lemma rise_enabled_even_odd : forall t m O E,
    {fall_decoupled}⊢ t ↓ m ->
    is_enabled fall_decoupled (Rise (Odd O)) m ->
    In (E,O) (even_odd_neighbors c) ->
    num_events (Rise (Even E)) t = num_events (Rise (Odd O)) t.
Admitted.

Lemma rise_enabled_odd_even : forall t m O E,
    {fall_decoupled}⊢ t ↓ m ->
    is_enabled fall_decoupled (Rise (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    num_events (Rise (Odd O)) t = 1+num_events (Rise (Even E)) t.
Admitted.

  Lemma fall_decoupled_strong : 
    forall t,
      forall m, {fall_decoupled}⊢ t ↓ m ->
      forall st, c ⊢ init_st ⇒t⇒ st ->
      (forall O, st(Odd O) = sync_eval c init_st (num_events (Rise (Odd O)) t) (Odd O)) /\
      (forall E, st(Even E) = sync_eval c init_st (1+num_events (Rise (Even E)) t) (Even E)).
  Proof.
    induction t as [P | e t];
      intros m Hm st Heval;
      split; intros l.
    * (* base case, odd *)
      simpl. inversion Heval; subst. rewrite sync_eval_odd_0. reflexivity.
    * (* base case, even *)
      simpl. inversion Heval; subst.
      erewrite eval_transparent; eauto.
      { simpl. rewrite sync_eval_even.
        f_equal.
        unfold odd_state.
        apply functional_extensionality.
        intros [O Ho]. simpl.
        rewrite sync_eval_odd_0. reflexivity.
      }
      { simpl.
        inversion Hm as [P0 Hopaque Htransparent | ]; clear H P0; rewrite <- H2 in *; clear m H2.
        apply Htransparent.

        (* apply is_enabled_fd. *)
        admit (* LEMMA *).
      }
    * (* inductive case, odd *)

      inversion Hm as [ | e0' m0 m0' s' Henabled Hfire Hconsistent']; subst;
        rename m0 into m.
      inversion Heval as [ | ? ? st' ? Heval' Hopaque' Htransparent']; subst.
      simpl in *.

      destruct (Dec (Rise (Odd l)) e).
      (* If e = l+, then l is transparent in (e::t) *)
      { subst. rewrite eqb_eq.
        rewrite Htransparent'.
        2:{ unfold update_transparency_predicate. rewrite eqb_eq. auto. }
        simpl.
        rewrite sync_eval_odd.
        
        f_equal. apply functional_extensionality. 
        unfold even_state. intros [E He].
        simpl.

        rewrite (event_rise_invariant_fd t m st' st (Odd l)); auto.
        2:{ split; auto. }
        2:{ inversion 1. }

        destruct (IHt m Hconsistent' st' Heval') as [_ IH].
        rewrite IH.
        
        assert (Hnum : num_events (Rise (Even E)) t = num_events (Rise (Odd l)) t).
        { eapply rise_enabled_even_odd; eauto.  }

        rewrite Hnum. reflexivity.
      }

      rewrite eqb_neq; auto.
    

      rewrite (event_invariant_neq t m st' st e); eauto.
      2:{ split; auto. }

      destruct (IHt m Hconsistent' st' Heval') as [IH _].
      rewrite IH.
      reflexivity.
      
      

    * (* inductive case, even *)
      inversion Hm as [ | e0' m0 m0' s' Henabled Hfire Hconsistent']; subst;
        rename m0 into m.
      inversion Heval as [ | ? ? st' ? Heval' Hopaque' Htransparent']; subst.
      simpl in *.

      destruct (Dec (Rise (Even l)) e).
      (* If e = l+, then l is transparent in (e::t) *)
      { subst. rewrite eqb_eq.
        rewrite Htransparent'.
        2:{ unfold update_transparency_predicate. rewrite eqb_eq. auto. }
        simpl.
        rewrite sync_eval_even.
        
        f_equal. apply functional_extensionality. 
        unfold odd_state. intros [O He].
        simpl.

        rewrite (event_rise_invariant_fd t m st' st (Even l)); auto.
        2:{ split; auto. }
        2:{ inversion 1. }

        destruct (IHt m Hconsistent' st' Heval') as [IH _].
        rewrite IH.
        
        assert (Hnum : num_events (Rise (Odd O)) t = 1+num_events (Rise (Even l)) t).
        { eapply rise_enabled_odd_even; eauto. }

        rewrite Hnum. reflexivity.
      }

      rewrite eqb_neq; auto.
    
      rewrite (event_invariant_neq t m st' st e); eauto.
      2:{ split; auto. }
      destruct (IHt m Hconsistent' st' Heval') as [_ IH].
      rewrite IH.
      reflexivity.
  Admitted.
      

Lemma num_events_odd_opaque : forall t st m O,
    c ⊢ init_st ⇒t⇒ st ->
    {fall_decoupled}⊢ t ↓ m ->
    transparent t (Odd O) = false ->
    num_events (Rise (Odd O)) t = num_events (Fall (Odd O)) t.
Admitted.
Lemma num_events_even_opaque : forall t st m E,
    c ⊢ init_st ⇒t⇒ st ->
    {fall_decoupled}⊢ t ↓ m ->
    transparent t (Even E) = false ->
    num_events (Fall (Even E)) t = 1 + num_events (Rise (Even E)) t.
Admitted. 

        
  Theorem fall_decoupled_flow_equivalence :
    flow_equivalence fall_decoupled c init_st.
  Proof.
    intros t [m Hm] st Hst l Hopaque.
    destruct (fall_decoupled_strong t m Hm st Hst) as [HO HE].
    destruct l as [O | E].
    + rewrite HO.
      erewrite num_events_odd_opaque; eauto.
    + rewrite HE.
      erewrite num_events_even_opaque; eauto.
  Qed.


End FallDecoupled.
