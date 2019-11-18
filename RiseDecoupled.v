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


Section RiseDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive transitions_RD : Set :=
  | Even_fall (E : even) : transitions_RD
  | Even_rise (E : even) : transitions_RD
  | Odd_fall  (O : odd) : transitions_RD
  | Odd_rise  (O : odd) : transitions_RD
  (* E- → O- *)
  | Even_odd_fall (E : even) (O : odd) : In (E,O) (even_odd_neighbors c) -> transitions_RD
  (* O- → E+ *)
  | Odd_even_rise (E : even) (O : odd)  : In (E,O) (even_odd_neighbors c) -> transitions_RD
  (* E- → O+ *)
  | Even_odd_rise (O : odd)  (E : even) : In (O,E) (odd_even_neighbors c) -> transitions_RD
  (* O- → E- *)
  | Odd_even_fall (O : odd)  (E : even) : In (O,E) (odd_even_neighbors c) -> transitions_RD
  .


  Instance eqdecRD : eq_dec transitions_RD.
  Proof.
    split. intros t1 t2.
    destruct Heven as [Heven'], Hodd as [Hodd'].
    destruct t1; destruct t2; try (right; inversion 1; fail);
      try (destruct (Dec E E0) as [HA | HA];
        [subst; intuition | right; inversion 1; contradiction]);
      try (destruct (Dec O O0) as [HB | HB];
        [subst; intuition | right; inversion 1; contradiction]).
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
  Qed.


  Definition rise_decoupled 
           : marked_graph (event even odd) transitions_RD :=
  {| mg_triples := 
     let eo_f := fun (A : even) (B : odd) pf =>
                     [ (Rise (Even A), Even_fall A, Fall (Even A))
                     ; (Fall (Even A), Even_odd_fall A B pf, Fall (Odd B))
                     ; (Fall (Odd B), Odd_even_rise A B pf, Rise (Even A))
                     ; (Rise (Odd B), Odd_fall B, Fall (Odd B))
                     ; (Fall (Odd B), Odd_rise B, Rise (Odd B))
                     ]
     in
     let oe_f := fun (A : odd) (B : even) pf =>
                     [ (Rise (Odd A), Odd_fall A, Fall (Odd A))
                     ; (Fall (Odd A), Odd_even_fall A B pf, Fall (Even B))
                     ; (Fall (Even B), Even_odd_rise A B pf, Rise (Odd A))
                     ; (Rise (Even B), Even_fall B, Fall (Even B))
                     ; (Fall (Even B), Even_rise B, Rise (Even B))
                     ]
     in flat_map_proof (even_odd_neighbors c) eo_f
     ++ flat_map_proof (odd_even_neighbors c) oe_f
   ; mg_init := fun p => match p with 
                         | Odd_even_fall _ _ _ => 1
                         | Even_fall _ => 1
                         | Odd_rise _ => 1
                         | _ => 0
                         end
   |}.



Open Scope nat_scope.
Inductive is_enabled_RD : event even odd -> marking transitions_RD -> Prop :=
| Even_fall_enabled E m :
  0 < m (Even_fall E) ->
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_odd_rise O E pf)) ->
  is_enabled_RD (Fall (Even E)) m
| Even_rise_enabled E m :
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_rise E)) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m  (Odd_even_rise E O pf)) ->
  is_enabled_RD (Rise (Even E)) m
| Odd_fall_enabled O m :
  0 < m (Odd_fall O) ->
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0%nat < m (Even_odd_fall E O pf)) ->
  is_enabled_RD (Fall (Odd O)) m
| Odd_rise_enabled O m :
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Odd_rise O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_odd_rise O E pf)) ->
  is_enabled_RD (Rise (Odd O)) m
.
Lemma RD_is_enabled_equiv : forall e m,
    is_enabled_RD e m -> is_enabled rise_decoupled e m.
Proof.
  destruct e as [[O | E] | [O | E]];
    intros m; intros H.
  * unfold is_enabled. unfold enabled. apply forallb_forall.
    intros T pf_in.
    inversion H; subst.
    apply PeanoNat.Nat.ltb_lt.
    unfold preset in pf_in.
    unfold rise_decoupled in pf_in. simpl in pf_in.
    apply in_flat_map in pf_in.
    destruct pf_in as [[[e1 T0] e2] [pf_in1 pf_in2]].
    simpl in pf_in2.
    destruct (Dec e2 (Rise (Odd O)));
      [ subst; rewrite eqb_eq in pf_in2; inversion pf_in2;
        [ subst; clear pf_in2 | contradiction]
        | rewrite eqb_neq in pf_in2; [contradiction | assumption] ].
    apply in_app_or in pf_in1.
    destruct pf_in1 as [pf_in1 | pf_in1].
    ** apply in_flat_map_proof' in pf_in1.
       destruct pf_in1 as [E1 [O1 [pf1 pf]]].
       simpl in pf.
       destruct pf as [pf | [pf | [pf | [pf | [pf | pf]]]]];
         try (inversion pf); subst; clear pf.
       eapply H1; eauto.
    ** apply in_flat_map_proof' in pf_in1.
       destruct pf_in1 as [E1 [O1 [pf1 pf]]].
       simpl in pf.
       destruct pf as [pf | [pf | [pf | [pf | [pf | pf]]]]];
         try (inversion pf).
       subst.
       apply H2.
(* good *)
Admitted.
  
Lemma is_enabled_RD_equiv : forall e m,
    is_enabled rise_decoupled e m ->
    is_enabled_RD e m.
Admitted.

Lemma rise_decoupled_init_even : forall P E m,
    {rise_decoupled}⊢ empty_trace P ↓ m ->
    P (Even E) = true.
Proof.
  intros P E m Hm.
  inversion Hm as [? Hpos Hneg | ]; subst.
  apply Hneg.
  unfold is_enabled, enabled.
  apply forallb_forall.
  intros T HT.
          unfold preset, rise_decoupled in HT. simpl in HT.
          apply in_flat_map in HT.
          destruct HT as [[[e_in t] e_out] [HT H]]. simpl in *.
          destruct (Dec e_out (Fall (Even E))); [subst; rewrite eqb_eq in H| rewrite eqb_neq in H; auto].
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


Lemma fall_enabled_even_opaque : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    is_enabled rise_decoupled (Fall (Odd O)) m ->
    In (E,O) (even_odd_neighbors c) ->
    transparent s (Even E) = false.
Admitted.

Lemma fall_enabled_odd_opaque : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    is_enabled rise_decoupled (Fall (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    transparent s (Odd O) = false.
Admitted.

Lemma fall_enabled_even_odd : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    is_enabled rise_decoupled (Fall (Odd O)) m ->
    In (E,O) (even_odd_neighbors c) ->
    num_events (Fall (Even E)) s = 1 + num_events (Fall (Odd O)) s.
Admitted.

Lemma fall_enabled_odd_even : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    is_enabled rise_decoupled (Fall (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    num_events (Fall (Odd O)) s = num_events (Fall (Even E)) s.
Admitted.



  Theorem rise_decoupled_flow_equivalence :
    flow_equivalence rise_decoupled c init_st.
  Proof.
    unfold flow_equivalence. 
    (* need to strengthen the IH with the value of n *)

    induction t as [lset | e s];
      intros [m Hm] st Heval l Hopaque.
    * simpl. 
      inversion Heval as [lset' Htransparent | ]; subst.

      (* Since l is opaque in the initial rise_decoupled state, it must be odd. *)
      destruct l as [O | E].
      + (* Odd case *) rewrite sync_eval_odd_0. reflexivity.
      + (* Even case *) contradict Hopaque.
        erewrite rise_decoupled_init_even; eauto.
        inversion 1.

    * simpl.
      inversion Hm as [ | e0' m0 m0' s' Henabled Hfire Hconsistent']; subst;
        rename m0 into m.
      inversion Heval as [ | ? ? st' ? Heval' Hopaque' Htransparent']; subst.
      simpl in *.

      (* Hconsistent' : ls_consistent_with_MG rise_decoupled rise_decoupled_init s m
         Henabled : is_enabled rise_decoupled e m
         Heval : c ⊢ init_state ⇒ e :: s ⇒ st
         Heval' : c ⊢ init_state ⇒ s ⇒ st'
       *)
    
      unfold update_transparency_predicate in Hopaque.
      (* 1. test if e=l- *)
      destruct (Dec (Fall l) e). 
      { (* e = l-, so l is opaque in st, but transparent in st'. *)
        subst. 
        rewrite eqb_eq.
        rewrite Hopaque'.
        2:{ simpl. unfold update_transparency_predicate. simpl. rewrite eqb_eq. reflexivity. }
        rewrite (eval_transparent _ _ _ _ _ _ Heval').
        2:{ eapply fall_enabled_transparent; eauto. (* LEMMA*) }
        unfold next_state.

        destruct l as [O | E].
        ++ (* l = O *)
           rewrite sync_eval_odd. (* OPPOSITE *)
           apply f_equal. unfold even_state.
           apply functional_extensionality.
           intros [E H_EO].
           simpl.

           rewrite IHs; [ |eexists; eauto | assumption |].
           2:{ eapply fall_enabled_even_opaque; eauto. (* LEMMA *) }

           assert (H : num_events (Fall (Even E)) s = 1 + num_events (Fall (Odd O)) s).
           { eapply fall_enabled_even_odd; eauto. (* LEMMA *) }
           rewrite H.

           reflexivity.

         ++ (* l = E *)
           rewrite sync_eval_even. (* OPPOSITE *)

           apply f_equal. unfold odd_state. apply functional_extensionality.
           intros [O H_OE].
           simpl.

           rewrite IHs; [ |eexists; eauto | assumption |].
           2:{ eapply fall_enabled_odd_opaque; eauto. (* LEMMA *) }

           assert (H : num_events (Fall (Odd O)) s = num_events (Fall (Even E)) s).
           { eapply fall_enabled_odd_even; eauto. (* LEMMA *) }
           rewrite H.
           reflexivity.
      } 

      rewrite eqb_neq; [ | assumption].

      (* 2. Test if e = l+ *)
      destruct (Dec (Rise l) e).
      { (* e = l+, so l is not opaque in st, contradiction. *)
        contradict Hopaque.
        subst.
        unfold update_transparency_predicate. simpl.
        rewrite eqb_eq.
        inversion 1.
      }

      (* 3. e <> l+ and e <> l- *)
      (* Then l is opaque in both s and (e::s) *)
      repeat (rewrite eqb_neq in Hopaque; [ | assumption]).

      rewrite Hopaque'.
      2:{ simpl. unfold update_transparency_predicate.
          repeat (rewrite eqb_neq; [ | assumption]).          
          apply Hopaque.
      }
      rewrite IHs; [ | eexists; eauto | auto | ].
      2:{ apply Hopaque. }
      reflexivity.
  Qed.

End RiseDecoupled.
