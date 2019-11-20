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
  | Even_rise_odd_rise (E : even) (O : odd) : (*In (E,O) (even_odd_neighbors c) ->*) transitions_FD (* E+ → O+ *)
  | Odd_fall_even_rise (E : even) (O : odd) : (*In (E,O) (even_odd_neighbors c) ->*) transitions_FD (* O- → E+ *)
  | Odd_rise_even_rise (O : odd) (E : even) : (*In (O,E) (odd_even_neighbors c) ->*) transitions_FD (* O+ → E+ *)
  | Even_fall_odd_rise (O : odd) (E : even) : (*In (O,E) (odd_even_neighbors c) ->*) transitions_FD (* E- → O+ *)
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

  Require Import Monad.

  Definition fall_decoupled 
           : marked_graph (event even odd) transitions_FD :=
  {| mg_triples := 
     let eo_f := fun (EO : even * odd) => let (E,O) := EO in
                     [ (Rise (Even E), Even_fall E, Fall (Even E))
                     ; (Fall (Even E), Even_rise E, Rise (Even E))
                     ; (Rise (Even E), Even_rise_odd_rise E O (*pf*), Rise (Odd O))
                     ; (Fall (Odd O), Odd_fall_even_rise E O (*pf*), Rise (Even E))
                     ; (Rise (Odd O), Odd_fall O, Fall (Odd O))
                     ]
     in
     let oe_f := fun (OE : odd * even) => let (O,E) := OE in
                     [ (Rise (Odd O), Odd_fall O, Fall (Odd O))
                     ; (Fall (Odd O), Odd_rise O, Rise (Odd O))
                     ; (Rise (Odd O), Odd_rise_even_rise O E (*pf*), Rise (Even E))
                     ; (Fall (Even E), Even_fall_odd_rise O E (*pf*), Rise (Odd O))
                     ; (Rise (Even E), Even_fall E, Fall (Even E))
                     ]
     in flat_map eo_f (even_odd_neighbors c)
     ++ flat_map oe_f (odd_even_neighbors c)
   ; mg_init := fun p => match p with
                | Even_rise_odd_rise _ _ => 1
                | Even_fall _ => 1
                | Odd_rise _ => 1
                | _ => 0
                end
   |}.


Inductive is_enabled_FD : event even odd -> marking transitions_FD -> Prop :=
| Even_fall_enabled E m :
  0 < m (Even_fall E) ->
  is_enabled_FD (Fall (Even E)) m
| Even_rise_enabled E m :
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Odd_rise_even_rise O E)) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Even_rise E)) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Odd_fall_even_rise E O)) ->
  is_enabled_FD (Rise (Even E)) m
| Odd_fall_enabled O m :
  0 < m (Odd_fall O) ->
  is_enabled_FD (Fall (Odd O)) m
| Odd_rise_enabled O m :
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Even_rise_odd_rise E O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Odd_rise O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_fall_odd_rise O E)) ->
  is_enabled_FD (Rise (Odd O)) m
.



Lemma FD_is_enabled_equiv : forall e m,
    is_enabled_FD e m -> is_enabled fall_decoupled e m.
Proof.
  destruct e as [[O | E] | [O | E]];
    intros m; inversion 1; subst;
    apply forallb_forall; intros T pf_in;
    apply PeanoNat.Nat.ltb_lt;

    unfold preset in pf_in;
    inversion_In; simpl in *.

  * compare e (Rise (Odd O) : event even odd); inversion_In. 
    repeat case_In; eauto.
  * compare e (Rise (Even E) : event even odd); inversion_In. 
    repeat case_In; eauto.
  * compare e (Fall (Odd O) : event even odd); inversion_In. 
    repeat case_In; eauto.
  * compare e (Fall (Even E) : event even odd); inversion_In. 
    repeat case_In; eauto.
Qed.
  
Lemma is_enabled_RD_equiv : forall e m,
    is_enabled fall_decoupled e m ->
    is_enabled_FD e m.
Proof.
  intros e m Henabled.
  unfold is_enabled, enabled in Henabled.
  destruct e as [[O | E] | [O | E]].
  * constructor; intros E pfE.
    + apply PeanoNat.Nat.ltb_lt.
      destruct (forallb_forall (fun t => 0 <? m t) (preset _ fall_decoupled (Rise (Odd O))))
        as [Hforall _].
      specialize (Hforall Henabled).
      apply Hforall.
      unfold preset. unfold fall_decoupled. simpl.
      apply in_flat_map.
      exists (Rise (Even E), Even_rise_odd_rise E O, Rise (Odd O)).
      split.
      2:{ simpl. rewrite eqb_eq. simpl. auto. }
      apply in_or_app.
      left.
      apply in_flat_map.
      exists (E,O). split; auto.
      simpl. auto.
  (* good *)
Admitted.




  Lemma sync_eval_S : forall n l st,
    (forall l', neighbor _ _ c l' l ->
                 st l' = match l with
                        | Even _ => sync_eval c init_st n l'
                        | Odd _  => sync_eval c init_st (S n) l'
                        end) ->
    sync_eval c init_st (S n) l = next_state c st l.
  Proof.
    intros n [O | E] st Hst; subst.
      + simpl. apply f_equal. apply functional_extensionality. intros [E HE]. simpl.
        unfold even_state. simpl. rewrite Hst; auto. constructor; auto.
      + simpl. apply f_equal. apply functional_extensionality. intros [O HO]. simpl.
        unfold odd_state. simpl. rewrite Hst; auto. constructor; auto.
  Qed.

  Lemma fall_decoupled_strong : forall l b t v,
    async_rel c init_st l b t v ->
      forall m, {fall_decoupled}⊢ t ↓ m ->
      forall n,
      n = match l with
          | Odd o => num_events (Rise (Odd o)) t
          | Even e => 1 + num_events (Rise (Even e)) t
          end ->
      v = sync_eval c init_st n l.
  Proof.
    intros l b t v Hrel.
    induction Hrel; intros m Hm n Hn.
    * (* Because l is opaque in the initial marking, l must be odd. *)
      inversion Hm; subst.
      destruct l as [O | E].
      2:{ contradict H. rewrite H2; [inversion 1 | ].
          apply FD_is_enabled_equiv.
          constructor; auto.
      }
      simpl. reflexivity.
    * (* l is transparent *)
      rewrite H2.

    (* n > 0 *)
    destruct n as [|n].
    { subst. destruct l as [O | E].
        2:{ inversion Hn. }
        (* since the initial state of odd latches are opaque *)
        admit.
    }

    erewrite sync_eval_S; auto.
    intros l' Hl'. 
    erewrite H1; eauto.
    
    inversion Hl'; subst.
    { assert (Hfact : transparent t (Odd O) = true ->
                      num_events (Rise (Odd O)) t = 1+ num_events (Rise (Even E)) t)
        by admit.
      rewrite Hfact in Hn; auto.
      inversion Hn.
      reflexivity.
    }
    { assert (Hfact : transparent t (Even E) = true ->
                      num_events (Rise (Even E)) t = num_events (Rise (Odd O)) t)
        by admit.
      inversion Hn.
      rewrite Hfact; auto.
    }

  * inversion Hm; subst.
    simpl in H. compare (Rise l) e.
    erewrite IHHrel; eauto.
    { destruct l; simpl; reduce_eqb; reflexivity. }

  * 
    destruct n as [|n].
    { simpl in Hn. subst. destruct l as [O | E].
        2:{ inversion Hn. }
        (* since the initial state of odd latches are opaque *)
        simpl in Hn.
        rewrite sync_eval_odd_0.

        inversion Hm; subst.
        (* O- is enabled, but O+ has not yet occurred, this is a contradiction since O starts out low. *)
        admit.
    }

    erewrite sync_eval_S; eauto.
    intros l' Hl'.

    inversion Hm; subst.

    erewrite H1; eauto.
    
    (* since Fall l is enabled *)
     inversion Hl'; subst.
     { rewrite Hn.
       f_equal. simpl.
       assert (Hfact : transparent t (Odd O) = true ->
                      num_events (Rise (Odd O)) t = 1+ num_events (Rise (Even E)) t)
        by admit.
       rewrite Hfact; auto.
       { (* since O- is enabled in t, O must be transparent in t *) admit. }
     }
    { inversion Hn; subst.
      assert (Hfact : transparent t (Even E) = true ->
                      num_events (Rise (Even E)) t = num_events (Rise (Odd O)) t)
        by admit.
      rewrite <- Hfact; auto.
      { (* since E- is enabled in t, E must be transparent in t *) admit. }
Admitted.    



(*

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

Lemma async_rel_transparent : forall l b t v,
    async_rel c init_st l b t v ->
    forall e,
    e <> Rise l ->
    e <> Fall l ->
    transparent (next_trace e t) l = true ->
    async_rel c init_st l true (next_trace e t) v.
Proof.
  intros l b t v Hrel.
Import FE_Tactics.
  induction Hrel; intros e0 Hrise Hfall Ht; reduce_transparent.
  + econstructor; eauto.
    { reduce_transparent. auto. }
    intros l' [ | ] Hneighbor.
    ++ (* true *)
      compare e0 (Rise l').
  Admitted.    
*)


(*

Lemma event_fall_invariant_fd : forall l b t v,
    async_rel c init_st l b t v ->
    forall e,
    e <> Rise l ->
    forall m, {fall_decoupled}⊢ next_trace e t ↓ m ->
    async_rel c init_st l (transparent (next_trace e t) l) (next_trace e t) v.
Proof.
    intros.
    simpl. unfold update_transparency_predicate.
    reduce_eqb.
    compare (Fall l) e.
    { (* e = Fall l *)
      econstructor; eauto.
      simpl. unfold update_transparency_predicate.
      reduce_eqb. auto.
    }

    compare (transparent t l) false.
    { rewrite e0. econstructor; eauto.
      simpl. unfold update_transparency_predicate.
      reduce_eqb; auto.
    }


Qed.

    *)



Proof.
  intros l e t v Hrel.
Require Import Coq.Program.Equality.
  remember (next_trace e t) as t'.
  revert e t Heqt'.
  induction Hrel as [? ? Hopaque | ? ? ? ? Htransparent ? | ? ? ? ? Hopaque ?];
    intros e' t' Heqt' Hneq m Hm; subst.
  * inversion Heqt'.
  * inversion Hm; subst.
    simpl in Htransparent.
    unfold update_transparency_predicate in Htransparent.
    reduce_eqb.
    compare (Fall l) e'.
    eapply async_transparent; auto.
    intros l' Hneighbor.
    assert (transparent (next_trace e' t') l' = false).
    { simpl. unfold update_transparency_predicate.
      (* since e' is enabled in m0 ~ t', if e' = Rise l', then l must have been
      opaque, which is a contradiction. *)
      (* if e' = Fall l', then we're good. *)
      compare (Rise l') e'.
      { contradict Htransparent. admit. }
      compare (Fall l') e'; [auto | ].
      admit (* induction? *).
    }
    

    eapply H0; eauto.



    apply Htransparent.

 as [? ? Hopaque | ? ? ? Htransparent ? | ? ? ? ? Hopaque Hrel]; intros e0 He0.
  + 

(*    
Inductive sync_rel : nat -> latch even odd -> value -> Prop :=
| Sync_odd_0 (O : odd) :  sync_rel 0 (Odd O) (init_st (Odd O)) (* Odd O ⇓^{0} init_st(Odd O)*)
| Sync_odd_S (O : odd) (n : nat) (st0 : state (latch even odd)) :
    (forall (E : even) (pf : In (E,O) (even_odd_neighbors c)), 
            sync_rel (S n) (Even E) (st0(Even E))) ->
    sync_rel (S n) (Odd O) (next_state c st0 (Odd O))
| Sync_even_S (E : even) (n : nat) (st0 : state (latch even odd)) :
    (forall (O : odd) (pf : In (O,E) (odd_even_neighbors c)), 
            sync_rel n (Odd O) (st0(Odd O))) ->
    sync_rel (S n) (Even E) (next_state c st0 (Even E))
.

Fixpoint length_trace (t : trace even odd) : nat :=
  match t with
  | empty_trace _ => 0
  | next_trace _ t' => 1 + length_trace t'
  end.
*)

 Lemma event_fall_invariant_fd : forall n l v,
    sync_rel n l v ->
    forall t st st' e,
    c ⊢ init_st ⇒t⇒ st ->
    async_step c (transparent t) st e st' ->
    e <> Rise l ->
    transparent (next_trace e t) l = true ->
    st'(l) = st(l).
  Proof.
    intros n l v Hrel.
    induction Hrel; intros t st st' e Hst Hstep He Htransparent.
    * simpl in Htransparent. unfold update_transparency_predicate in *.
      reduce_eqb.
      compare (Fall (Odd O) : event even odd) e; [contradict Htransparent; auto | ].
      destruct Hstep.
      

    * simpl in Htransparent. unfold update_transparency_predicate in *.
      reduce_eqb.
      

  Lemma event_disjoint_fd : forall n l v,
    sync_rel n l v ->
    forall t m st st',
    {fall_decoupled}⊢ t ↓ m ->
    n <= length_trace t ->
    c ⊢ st ⇒t⇒st' ->
    disjoint l t ->
    transparent t l = true ->
    st'(l) = st(l).
  Proof.
    intros n l v Hsync.
    induction Hsync; intros t m st st' Hm Hlen Hst Hdisjoint Htransparent.
    * contradict Htransparent. Search transparent Odd. admit (* true *).
    * erewrite eval_transparent; eauto.
      admit (* because O is disjoint from t and transaprent in t, it must also be transparent in the initial marking, which is a contradiction. *).
    * erewrite eval_transparent; eauto.
      transitivity (next_state c st (Even E)).
      2:{ (* because E is disjoint from t and transaprent in t, it must also be transaprent in the initial marking. *) admit. }

      simpl. apply f_equal. unfold odd_state.
      apply functional_extensionality. intros [O Hpf]. simpl.

      assert (


    {fall_decoupled}⊢ t ↓ m ->
    c ⊢ st ⇒t⇒ st' ->
    disjoint l t ->
    st'(l) = st(l).
  Proof.
    intros t m st st' l Hm Hst Hdisjoint.
    revert m st st' Hm Hst.
    induction Hdisjoint; intros m st st' Hm Hst.
    *  inversion Hst; auto.
    * 

    induction t as [P | e t]; intros m st st' l Hm Hst Hdisjoint.
    * inversion Hst. reflexivity.
    * inversion Hst as [ | e0 t0  st0 st'0 Hst' Hopaque Htransparent]; subst.
      inversion Hdisjoint as [ | l0 e0 t0 e_neq_l Hpred Hdisjoint']; subst.
      inversion Hm as [ | e0 m' m0' t0 Henabled Hfire Hm']; subst.
      

  Admitted.

  Lemma event_fall_invariant_fd : forall t st l st',
    c ⊢ init_st ⇒t⇒ st ->
    async_step c (transparent t) st (Fall l) st' ->
    forall l', st'(l') = st(l').
  Proof.
(*
    induction t as [P | e t]; intros st l st' Hst [Hopaque Htransparent] l'.
    * (* t = [] *)
      inversion Hst as [P0 Htransparencies | ]; subst.
     

    destruct ((update_transparency_predicate (Fall l) P) l')
      eqn:Hl';
      unfold update_transparency_predicate in Hl';
      simpl in Hl'.
    + (* l is transparent *)
      compare l l'; [contradict Hl'; auto | ].
      rewrite eqb_neq in Hl'; [ | inversion 1; subst; contradiction].
      
     

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
      unfold next_state.

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
*)
  Admitted.


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
    * eapply event_fall_invariant_fd; eauto.
  Qed.




Opaque sync_eval.
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
      simpl. inversion Heval; subst. reflexivity.
    * (* base case, even *)
      simpl. inversion Heval; subst.
      erewrite eval_transparent; eauto.
      { simpl. rewrite sync_eval_even. reflexivity.
      }
      { simpl.
        inversion Hm as [P0 Hopaque Htransparent | ]; clear H P0; rewrite <- H2 in *; clear m H2.
        apply Htransparent.

        apply FD_is_enabled_equiv.
        constructor; auto.
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
  Qed.
      

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
