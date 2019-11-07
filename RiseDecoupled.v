Require Import FlowEquivalence.
Require Import List.
Import ListNotations.
Open Scope list_scope.



Section RiseDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd. Print circuit.


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

  Fixpoint flat_map_proof {A B C : Type}
                          (ls : list (A*B))
                        : (forall (a : A) (b : B), In (a,b) ls -> list C)
                       -> list C :=
    match ls with
    | [] => fun _ => []
    | (a,b) :: ls' => fun f => f a b (in_eq _ _) ++ flat_map_proof ls' (fun a' b' pf' => f a' b' (in_cons _ _ _ pf'))
    end.

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


(*
  Definition even_neighbors_left (c : circuit even odd) (e : even) : list odd :=
    let f := fun oe => if snd oe =? e then [fst oe] else [] in
    flat_map f (odd_even_neighbors c).
  Definition even_neighbors_right (c : circuit even odd) (e : even) : list odd :=
    let f := fun eo => if fst eo =? e then [snd eo] else [] in
    flat_map f (even_odd_neighbors c).
  Definition odd_neighbors_left (c : circuit even odd) (o : odd) : list even :=
    let f := fun eo => if snd eo =? o then [fst eo] else [] in
    flat_map f (even_odd_neighbors c).
  Definition odd_neighbors_right (c : circuit even odd) (o : odd) : list even :=
    let f := fun oe => if fst oe =? o then [snd oe] else [] in
    flat_map f (odd_even_neighbors c).
*)

  Require Import Monad.

(*
  Definition rise_decoupled 
           : marked_graph (event even odd) transitions_RD :=
  {| in_transitions := fun (E : event even odd) =>
    match E with
    | Pos (Even e) => [Even_rise e] ++ fmap (Odd_even_rise e) (even_neighbors_right e)
    | Neg (Even e) => [Even_fall e] ++ fmap (Odd_even_fall e) (even_neighbors_left e)
    | Pos (Odd o)  => [Odd_rise o]  ++ fmap (Even_odd_rise o) (odd_neighbors_right o)
    | Neg (Odd o)  => [Odd_fall o] ++ fmap (Even_odd_fall o) (odd_neighbors_left o)
    end
  ; out_transitions := fun (E : event even odd) =>
    match E with
    | Pos (Even e) => [Even_fall e]
    | Neg (Even e) => fmap (fun o => Even_odd_fall o e) (even_neighbors_right e)
    | Pos (Odd o)  => [Odd_fall o]
    | Neg (Odd o)  => [Odd_rise o] 
                   ++ fmap (fun e => Odd_even_rise e o) (odd_neighbors_left o)
                   ++ fmap (fun e => Odd_even_fall e o) (odd_neighbors_right o)
    end
  |}.
*)

  Definition rise_decoupled_init  : marking transitions_RD :=
    fun t => match t with
             | Even_fall e => 1
             | Odd_even_fall _ _ _ => 1
             | Odd_rise _  => 1
             | _ => 0
             end.



    Lemma find_ith_occurrence_empty_async :
      forall (i : nat) (e : event even odd) (lset : latch_set even odd),
             find_ith_occurrence e (ls_empty_async lset) i = None.
    Proof.
      induction i; intros e lset; auto.
    Qed. 

Existing Instance event_eq_dec.

  Require Import Program.



  Lemma flat_map_app : forall {A B} (f : A -> list B) (ls1 ls2 : list A),
    flat_map f (ls1 ++ ls2) = flat_map f ls1 ++ flat_map f ls2.
  Admitted.

(*
Lemma eval_cons : forall st e s,
    eval c st (ls_async e s) = let st' := eval c st s in
                               eval_async_1 _ _ c st' e.
Proof.
  intros. reflexivity.
Qed.
*)

Arguments num_events {even odd Heven Hodd}.
Arguments consistent {even odd Heven Hodd transitions Htrans}.
About is_enabled.
Arguments is_enabled {even odd Heven Hodd transitions}.
Existing Instance latch_eq_dec.


Lemma num_events_cons : forall (e e' : event even odd) s,
    num_events e (ls_async e' s) = if e =? e' then 1 + num_events e s else num_events e s.
Proof. intros. reflexivity. Qed.




Lemma in_flat_map_proof : forall {A B C} (a : A) (b : B) (ls : list (A*B))
                                 (f : forall a' b', In (a',b') ls -> list C)
                                 (x : C)
    (pf : In (a,b) ls),
    In x (f a b pf) ->
    In x (flat_map_proof ls f).
Admitted.

Lemma in_flat_map_proof' : forall {A B C} (ls : list (A*B))
                                 (f : forall a' b', In (a',b') ls -> list C)
                                 (x : C),
    In x (flat_map_proof ls f) ->
    exists a b (pf : In (a,b) ls), In x (f a b pf).
Admitted.


Arguments ls_consistent_with_MG {even odd Heven Hodd transitions Htrans}.
Print consistent.


(*
  Lemma num_transparent_events_odd_even : forall s o e m,
      ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
      In (o,e) (odd_even_neighbors c) ->
      num_events (Neg (Even e)) s = num_events (Pos (Odd o)) s
    \/ num_events (Neg (Even e)) s = 1 + num_events (Pos (Odd o)) s.
Proof.
    dependent induction s; [ | rename e into e0];
    intros o e m Hconsistent Hin.
    * simpl. intuition.

  * specialize (IHs s eq_refl JMeq_refl).
    inversion Hconsistent as [ | e1 m1 m1' s' Henabled Hfire Hconsistent']; subst.
    unfold num_events.
    fold (num_events (Pos (Odd o)) s).
    fold (num_events (Neg (Even e)) s).

       assert (Henabled' : forall x, In x (in_transitions _ rise_decoupled e0) ->
                                     (PeanoNat.Nat.ltb 0 (m x)) = true)
          by (apply forallb_forall; apply Henabled).
        destruct (Pos (Odd o) =? e0) as [o0_eq_e | o0_neq_e]. 
        { subst. simpl. (* Since (Pos (Odd o0)) is enabled, it must be the case that num_events (Neg (Even e0)) = Pos (Odd o0)+1 *)
          assert (Heo : num_events (Neg (Even e0)) s = 1 + num_events (Pos (Odd o0)) s)
            by admit.
          rewrite Heo. simpl. intuition.
        }
        destruct (Neg (Even e0) =? e) as [e0_eq_e | e0_neq_e].
        { subst.
          (* Since (Neg (Even e0)) is enabled, it must be the case that num_events (Pos (Odd o0)) = num_events (Neg (Even e0)) *)
          assert (Heo : num_events (Neg (Even e0)) s = num_events (Pos (Odd o0)) s)
            by admit.
          rewrite Heo. intuition.
        }
        { apply (IHs s eq_refl JMeq_refl o0 e0); [eexists; eauto | auto].

    * 
*)  

About in_transitions.
Arguments in_transitions {events transitions Hevents}.

(* maybe it's not about is_enabled or not, it's "does this particular transition have a marking? *)
Print enabled.
Notation "m <? n" := (PeanoNat.Nat.ltb m n) (no associativity, at level 90).

(*
Lemma neg_even_enabled_even_odd_rise_0 : forall e o (Hin : In (o,e) (odd_even_neighbors c)) m,
    is_enabled rise_decoupled (Neg (Even e)) m ->
    m (Even_odd_rise o e Hin) = 0.
Proof.
  intros e o Hin m Henabled.
  unfold is_enabled,enabled in *.
  admit (*???*).
Admitted.
*)


Lemma in_dec_fmap : forall {A B} `{eq_dec A} `{eq_dec B} (x : A) (y : B) f ls,
    x ∈ ls ->
    y = f x ->
    y ∈ fmap f ls.
Admitted.


(*
Lemma fire_even_odd_rise : forall e o (Hin : In (o,e) (odd_even_neighbors c)) m,
    is_enabled rise_decoupled (Neg (Even e)) m ->
    fire (Neg (Even e)) rise_decoupled m (Even_odd_rise o e Hin)
    = 1.
Proof.
  intros e o Hin m Henabled.
  unfold fire.
Existing Instance prod_eq_dec.
  rewrite neg_even_enabled_even_odd_rise_0. Print output_event.
  assert (in_list_dec (Even_odd_rise o e Hin, Neg (Even e)) (output_event _ transitions_RD rise_decoupled) = false).
  { admit. }
  unfold in_dec'. 
Admitted.  
*)  



(*
Print marking.
  Definition RD_odd_even_invariant (o : odd) (e : even) (t : transitions_RD) s m :=
    num_events (Neg (Even e)) s = if 0 <? m t
                                  then S (num_events (Pos (Odd o)) s)
                                  else (num_events (Pos (Odd o)) s).


  Lemma num_transparent_events_odd_even : forall s m m',
(*      ls_consistent_with_MG rise_decoupled s m m' -> *)
      forall o e (pf : In (o,e) (odd_even_neighbors c)) E,
      RD_odd_even_invariant o e (Even_odd_rise o e pf) s m ->
      RD_odd_even_invariant o e (Even_odd_rise o e pf) (ls_async E s) m'.
  Proof.
    intros s m m' o e pf E Hinv.
    unfold RD_odd_even_invariant in *.


    dependent induction Hconsistent; [ | rename e into e0];
      intros o e pf E Hbase.
    * apply Hbase.
    * unfold RD_odd_even_invariant in *.
      specialize (IHHconsistent o e pf).
      unfold num_events.
      fold (num_events (Pos (Odd o)) s').
      fold (num_events (Neg (Even e)) s').
      rewrite IHHconsistent.
      2:{ 
    
*)

(*
  Lemma num_transparent_events_odd_even : forall s m,
      ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
      forall o e (pf : In (o,e) (odd_even_neighbors c)),
      num_events (Neg (Even e)) s = if 0 <? m (Even_odd_rise o e pf) 
                                    then S (num_events (Pos (Odd o)) s)
                                    else (num_events (Pos (Odd o)) s).
  Proof.
    dependent induction s;
      intros m Hconsistent O E Hin.
    * simpl.
      inversion Hconsistent; subst.
      simpl. reflexivity.

  * inversion Hconsistent as [ | e1 m1 m1' s' Henabled Hfire Hconsistent']; subst.
    rename m1 into m.
    unfold num_events.
    fold (num_events (Pos (Odd O)) s).
    fold (num_events (Neg (Even E)) s).

    rewrite (IHs _ Hconsistent' _ _ Hin).
Print eq_dec.

    destruct (Dec (Neg (Even E)) e) as [e0_eq_e | e0_neq_e].
    { subst.
      simpl.
      assert (H_m : m (Even_odd_rise _ _ Hin) = 0) by admit.
(*      { apply neg_even_enabled_even_odd_rise_0. auto. } *)
      rewrite H_m. simpl.


      assert (H_m' :
        fire (Neg (Even E)) rise_decoupled m (Even_odd_rise _ _ Hin)
      = 1)
        by admit.
      rewrite H_m'. rewrite eqb_eq. simpl.
      reflexivity.
    }
    rewrite eqb_neq; auto.
    destruct (Pos (Odd O) =? e) as [o0_eq_e | o0_neq_e]. 
    { subst. simpl.
      assert (H_m : m (Even_odd_rise _ _ Hin) = 1) by admit.
      assert (H_m' : fire (Pos (Odd O)) rise_decoupled m (Even_odd_rise _ _ Hin)
                   = 0) by admit.

      admit.

    }
    { assert (H_m : fire e rise_decoupled m (Even_odd_rise _ _ Hin) = m (Even_odd_rise _ _ Hin)) by admit.
      rewrite H_m.
      reflexivity.
    }
  Admitted.


About get_latch_value.
Arguments get_latch_value {even odd}.
Lemma get_latch_value_eq : forall st1 st2,
      st1 = st2 ->
      forall l,
      get_latch_value c st1 l = get_latch_value c st2 l.
Proof. intros. subst. reflexivity. Qed.




  Lemma num_transparent_events_even_odd : forall s o e m,
      ls_consistent_with_MG rise_decoupled rise_decoupled_init s m ->
      forall (pf : In (e,o) (even_odd_neighbors c)),
      num_events (Neg (Odd o)) s = if 0 <? m (Odd_even_rise e o pf)
                                   then S (num_events (Pos (Even e)) s)
                                   else (num_events (Pos (Even e)) s).
  Proof.
    dependent induction s;
      intros O E m Hconsistent Hin.
    * simpl.
      inversion Hconsistent; subst.
      simpl. reflexivity.

  * inversion Hconsistent as [ | e1 m1 m1' s' Henabled Hfire Hconsistent']; 
      subst; rename m1 into m.
    unfold num_events.
    fold (num_events (Pos (Even E)) s).
    fold (num_events (Neg (Odd O)) s).

    rewrite (IHs O E _ Hconsistent' Hin).

    destruct (Dec (Neg (Odd O)) e) as [e0_eq_e | e0_neq_e].
    { subst. rewrite eqb_eq.
      simpl.
      assert (H_o_enabled_m : m (Odd_even_rise _ _ Hin) = 0)
        by admit.
      rewrite H_o_enabled_m. simpl.
      assert (H_o_enabled_m' :
        fire (Neg (Odd O)) rise_decoupled m (Odd_even_rise E O Hin)
        = 1)
        by admit.
      rewrite H_o_enabled_m'. simpl.
      reflexivity.
    }
    rewrite eqb_neq; [ | assumption].
    destruct (Pos (Even E) =? e) as [o0_eq_e | o0_neq_e]. 
    { subst. simpl.
      assert (H_m : m (Odd_even_rise E O Hin) = 1) by admit.
      assert (H_m' : fire (Pos (Even E)) rise_decoupled m (Odd_even_rise E O Hin)
                   = 0) by admit.
      admit.
    }
    { assert (H_m : fire e rise_decoupled m (Odd_even_rise E O Hin)
                  = m (Odd_even_rise E O Hin)) by admit.
      rewrite H_m.
      reflexivity.
    }
  Admitted.


  Lemma opaque_neq_transparent_event : forall (l : latch even odd),
    opaque_event l <> transparent_event l.
  Proof.
    destruct l; inversion 1.
  Qed.

*)

Print consistent. 
Print ls_consistent_with_MG.


(*
  Lemma init_even_transparent : forall st E lset,
    st = marking_to_state rise_decoupled rise_decoupled_init ->
    is_transparent (ls_empty_async lset) (Even E) = true.
*)

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
      simpl in *. unfold step_latch_set in *.

      (* Hconsistent' : ls_consistent_with_MG rise_decoupled rise_decoupled_init s m
         Henabled : is_enabled rise_decoupled e m
         Heval : c ⊢ init_state ⇒ e :: s ⇒ st
         Heval' : c ⊢ init_state ⇒ s ⇒ st'
       *)
    
      (* 1. test if e=l- *)
      destruct (Dec (Neg l) e). 
      { (* e = l-, so l is opaque in st, but transparent in st'. *)
        subst. rewrite eqb_eq.
        rewrite Hopaque'.
        2:{ simpl. rewrite eqb_eq. destruct l; reflexivity. }
        rewrite (eval_transparent _ _ _ _ _ _ Heval').
        2:{ eapply fall_enabled_transparent; eauto. }
        unfold get_latch_value.

        destruct l as [O | E].
        ++ (* l = O *)
           rewrite sync_eval_odd_opp; auto. (* OPPOSITE *)
           apply f_equal. unfold even_state. apply functional_extensionality.
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
        subst. simpl in Hopaque.
        rewrite eqb_eq in Hopaque.
        destruct l; inversion Hopaque.
      }

      (* 3. e <> l+ and e <> l- *)
      assert (He : event_refers_to_latch  _ _ e l = false).
      { unfold event_refers_to_latch. 
        destruct e; rewrite eqb_neq; auto; intro; subst; intuition.
      }
      rewrite He in *.
      (* Then l is opaque in both s and (e::s) *)
      rewrite Hopaque'.
      2:{ rewrite He. apply Hopaque. }
      rewrite IHs; [ | eexists; eauto | auto | apply Hopaque].
      reflexivity.
  Qed.

End RiseDecoupled.
