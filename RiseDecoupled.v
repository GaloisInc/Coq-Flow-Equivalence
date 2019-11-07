Require Import FlowEquivalence.
Require Import List.
Import ListNotations.
Open Scope list_scope.



Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.

Section RiseDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.


  Inductive transitions_RD : Set :=
  | Even_fall (A : even) : transitions_RD
  | Even_rise (A : even) : transitions_RD
  | Odd_fall  (B : odd) : transitions_RD
  | Odd_rise  (B : odd) : transitions_RD
  | Even_odd_fall (A : even) (B : odd) : In (A,B) (even_odd_neighbors c) -> transitions_RD (* A- → B- *)
  | Odd_even_rise (A : even) (B : odd)  : In (A,B) (even_odd_neighbors c) -> transitions_RD (* B- → A+ *)
  | Even_odd_rise (A : odd)  (B : even) : In (A,B) (odd_even_neighbors c) -> transitions_RD (* B- → A+ *)
  | Odd_even_fall (A : odd)  (B : even) : In (A,B) (odd_even_neighbors c) -> transitions_RD (* A- → B- *)
  .

  Import Coq.Logic.ProofIrrelevance.

  Instance eqdecRD : eq_dec transitions_RD.
  Proof.
    split. intros t1 t2.
    destruct Heven as [Heven'], Hodd as [Hodd'].
    destruct t1; destruct t2; try (right; inversion 1; fail);
      try (destruct (Dec A A0) as [HA | HA];
        [subst; intuition | right; inversion 1; contradiction]);
      try (destruct (Dec B B0) as [HB | HB];
        [subst; intuition | right; inversion 1; contradiction]).
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
  Qed.


  Definition rise_decoupled 
           : marked_graph (event even odd) transitions_RD :=
  {| input_event_output := 
     let eo_f := fun (A : even) (B : odd) pf =>
                     [ (Pos (Even A), Even_fall A, Neg (Even A))
                     ; (Neg (Even A), Even_odd_fall A B pf, Neg (Odd B))
                     ; (Neg (Odd B), Odd_even_rise A B pf, Pos (Even A))
                     ; (Pos (Odd B), Odd_fall B, Neg (Odd B))
                     ; (Neg (Odd B), Odd_rise B, Neg (Odd B))
                     ]
     in
     let oe_f := fun (A : odd) (B : even) pf =>
                     [ (Pos (Odd A), Odd_fall A, Neg (Odd A))
                     ; (Neg (Odd A), Odd_even_fall A B pf, Neg (Even B))
                     ; (Neg (Even B), Even_odd_rise A B pf, Pos (Odd A))
                     ; (Pos (Even B), Even_fall B, Neg (Even B))
                     ; (Neg (Even B), Even_rise B, Pos (Even B))
                     ]
     in flat_map_proof (even_odd_neighbors c) eo_f
     ++ flat_map_proof (odd_even_neighbors c) oe_f
   |}.

  Definition rise_decoupled_init  : marking transitions_RD :=
    fun t => match t with
             | Even_fall e => 1
             | Odd_even_fall _ _ _ => 1
             | Odd_rise _  => 1
             | _ => 0
             end.


Lemma fall_enabled_transparent : forall s m l,
    ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
    is_enabled rise_decoupled (Neg l) m ->
    is_transparent s l = true.
Admitted.

Lemma rise_enabled_opaque : forall s m l,
    ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
    is_enabled rise_decoupled (Pos l) m ->
    is_transparent s l = false.
Admitted.

Lemma fall_enabled_even_opaque : forall s m O E,
    ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
    is_enabled rise_decoupled (Neg (Odd O)) m ->
    In (E,O) (even_odd_neighbors c) ->
    is_transparent s (Even E) = false.
Admitted.

Lemma fall_enabled_odd_opaque : forall s m O E,
    ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
    is_enabled rise_decoupled (Neg (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    is_transparent s (Odd O) = false.
Admitted.

Lemma fall_enabled_even_odd : forall s m O E,
    ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
    is_enabled rise_decoupled (Neg (Odd O)) m ->
    In (E,O) (even_odd_neighbors c) ->
    num_events (Neg (Even E)) s = 1+num_events (Neg (Odd O)) s.
Admitted.

Lemma fall_enabled_odd_even : forall s m O E,
    ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
    is_enabled rise_decoupled (Neg (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    num_events (Neg (Odd O)) s = num_events (Neg (Even E)) s.
Admitted.


Lemma rise_decoupled_init_even : forall lset E,
    consistent rise_decoupled rise_decoupled_init (ls_empty_async lset) ->
    lset (Even E) = true.
Proof.
  intros lset E [m Hm].
  inversion Hm as [? Hpos Hneg | ]; subst.
  apply Hneg.
  unfold is_enabled, enabled.
  apply forallb_forall.
  intros T HT.
          unfold in_transitions, rise_decoupled in HT. simpl in HT.
          apply in_flat_map in HT.
          destruct HT as [[[e_in t] e_out] [HT H]]. simpl in *.
          destruct (Dec e_out (Neg (Even E))); [subst; rewrite eqb_eq in H| rewrite eqb_neq in H; auto].
          inversion H as [ | H0]; [subst | inversion H0]; clear H.
          apply in_app_or in HT.
          destruct HT as [HT | HT].
          ++ apply in_flat_map_proof' in HT.
             destruct HT as [E0 [O0 [pf0 HT]]].
             simpl in HT.
             repeat (destruct HT as [HT | HT]; [ inversion HT; subst; auto | ]); inversion HT.
          ++ apply in_flat_map_proof' in HT.
             destruct HT as [E0 [O0 [pf0 HT]]].
             simpl in HT.
             repeat (destruct HT as [HT | HT]; [ inversion HT; subst; auto | ]); inversion HT.
Qed.

  Theorem rise_decoupled_flow_equivalence :
    flow_equivalence rise_decoupled rise_decoupled_init c.
  Proof.
    unfold flow_equivalence.
    induction s as [lset | e s];
      intros Hconsistent st Heval l Hopaque.
    * simpl. 
      inversion Heval as [lset' Htransparent | ]; subst.

      (* Since l is opaque in the initial rise_decoupled state, it must be odd. *)
      destruct l as [O | E].
      + (* Odd case *) simpl. reflexivity.
      + (* Even case *) 
      contradict Hopaque. 
      { rewrite rise_decoupled_init_even; [inversion 1 | auto]. }
    * simpl.
      inversion Hconsistent as [ m Hm];
        inversion Hm as [ | e0' m0 m0' s' Henabled Hfire Hconsistent']; subst;
        rename m0 into m.
      inversion Heval as [ | ? ? st' ? Heval' Hopaque' Htransparent']; subst.
      simpl in *.

      (* Hconsistent' : ls_consistent_with_MG rise_decoupled rise_decoupled_init s m
         Henabled : is_enabled rise_decoupled e m
         Heval : c ⊢ init_state ⇒ e :: s ⇒ st
         Heval' : c ⊢ init_state ⇒ s ⇒ st'
       *)
    
      (* 1. test if e=l- *)
      destruct (Dec (Neg l) e). 
      { (* e = l-, so l is opaque in st, but transparent in st'. *)
        subst. 
        rewrite eqb_eq.
        rewrite Hopaque'.
        2:{ simpl. unfold step_latch_set. simpl. rewrite eqb_eq. reflexivity. }
        rewrite (eval_transparent _ _ _ _ _ _ Heval').
        2:{ eapply fall_enabled_transparent; eauto. }
        unfold get_latch_value.

        destruct l as [O | E].
        ++ (* l = O *)
           rewrite sync_eval_odd_opp; auto. (* OPPOSITE *)
           apply f_equal. unfold even_state.
           apply functional_extensionality.
           intros [E H_EO].

           rewrite sync_eval_even_opp; auto. (* OPPOSITE *) 
           simpl.

           rewrite IHs; [ |eexists; eauto | assumption |].
           2:{ eapply fall_enabled_even_opaque; eauto. (* LEMMA *) }

           assert (H : num_events (Neg (Even E)) s = 1+num_events (Neg (Odd O)) s).
           { eapply fall_enabled_even_odd; eauto. (* LEMMA *) }
           rewrite H.

           rewrite sync_eval_even_opp; [ | auto | auto]. (* OPPOSITE *)
           reflexivity.

         ++ (* l = E *)
           rewrite sync_eval_even_opp; auto. (* OPPOSITE *)

           apply f_equal. unfold odd_state. apply functional_extensionality.
           intros [O H_OE].

           rewrite sync_eval_odd_opp; auto. (* OPPOSITE *) 
           simpl.

           rewrite IHs; [ |eexists; eauto | assumption |].
           2:{ eapply fall_enabled_odd_opaque; eauto. (* LEMMA *) }

           assert (H : num_events (Neg (Odd O)) s = num_events (Neg (Even E)) s).
           { eapply fall_enabled_odd_even; eauto. (* LEMMA *) }
           rewrite H.

           rewrite sync_eval_odd_opp; [ | auto | auto]. (* OPPOSITE *)
           reflexivity.
      } 

      rewrite eqb_neq; [ | assumption].

      (* 2. Test if e = l+ *)
      destruct (Dec (Pos l) e).
      { (* e = l+, so l is not opaque in st, contradiction. *)
        contradict Hopaque.
        subst.
        unfold step_latch_set. simpl.
        rewrite eqb_eq.
        inversion 1.
      }

      (* 3. e <> l+ and e <> l- *)
      assert (He : event_refers_to_latch  _ _ e l = false).
      { unfold event_refers_to_latch. 
        destruct e; rewrite eqb_neq; auto; intro; subst; intuition.
      }
      unfold step_latch_set in Hopaque.
      rewrite He in *.
      (* Then l is opaque in both s and (e::s) *)
      rewrite Hopaque'.
      2:{ simpl. unfold step_latch_set. rewrite He. apply Hopaque. }
      rewrite IHs; [ | eexists; eauto | auto | apply Hopaque].
      reflexivity.
  Qed.

End RiseDecoupled.
