Require Import Base.
Require Import FlowEquivalence.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.

Require Import PeanoNat.

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Equality.



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
  | Even_odd_fall (E : even) (O : odd) : (*In (E,O) (even_odd_neighbors c) ->*) transitions_RD
  (* O- → E+ *)
  | Odd_even_rise (E : even) (O : odd)  : (*In (E,O) (even_odd_neighbors c) ->*) transitions_RD
  (* E- → O+ *)
  | Even_odd_rise (O : odd)  (E : even) : (*In (O,E) (odd_even_neighbors c) ->*) transitions_RD
  (* O- → E- *)
  | Odd_even_fall (O : odd)  (E : even) : (*In (O,E) (odd_even_neighbors c) ->*) transitions_RD
  .


  Definition input_RD (t : transitions_RD) : event even odd :=
    match t with
    | Even_fall E => Rise (Even E)
    | Even_rise E => Fall (Even E)
    | Odd_fall o => Rise  (Odd o)
    | Odd_rise o => Fall (Odd o)
    | Even_odd_fall E o => Fall (Even E)
    | Odd_even_rise E o => Fall (Odd o)
    | Even_odd_rise o E => Fall (Even E)
    | Odd_even_fall o E => Fall (Odd o)
    end.
  Definition output_RD (t : transitions_RD) : event even odd :=
    match t with
    | Even_fall E => Fall (Even E)
    | Even_rise E => Rise (Even E)
    | Odd_fall o =>  Fall (Odd o)
    | Odd_rise o =>  Rise (Odd o)
    | Even_odd_fall E o => Fall (Odd o)
    | Odd_even_rise E o => Rise (Even E)
    | Even_odd_rise o E => Rise (Odd o)
    | Odd_even_fall o E => Fall (Even E)
    end.



  Instance eqdecRD : eq_dec transitions_RD.
  Proof.
    split. intros t1 t2.
    destruct Heven as [Heven'], Hodd as [Hodd'].
    destruct t1; destruct t2; try (right; inversion 1; fail);
      try (destruct (Dec E E0) as [HA | HA];
        [subst; intuition | right; inversion 1; contradiction]);
      try (destruct (Dec O O0) as [HB | HB];
        [subst; intuition | right; inversion 1; contradiction]).
(*    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
    * rewrite (proof_irrelevance _ i i0). intuition.
*)
  Qed.


  Definition rise_decoupled 
           : marked_graph (event even odd) transitions_RD :=
  {| mg_triples := 
     let eo_f := fun (eo : even * odd) => let (E,O) := eo in
                     [ (Rise (Even E), Even_fall E, Fall (Even E))
                     ; (Fall (Even E), Even_odd_fall E O, Fall (Odd O))
                     ; (Fall (Odd O), Odd_even_rise E O, Rise (Even E))
                     ; (Rise (Odd O), Odd_fall O, Fall (Odd O))
                     ; (Fall (Odd O), Odd_rise O, Rise (Odd O))
                     ]
     in
     let oe_f := fun (oe : odd * even) => let (O,E) := oe in
                     [ (Rise (Odd O), Odd_fall O, Fall (Odd O))
                     ; (Fall (Odd O), Odd_even_fall O E, Fall (Even E))
                     ; (Fall (Even E), Even_odd_rise O E, Rise (Odd O))
                     ; (Rise (Even E), Even_fall E, Fall (Even E))
                     ; (Fall (Even E), Even_rise E, Rise (Even E))
                     ]
     in flat_map eo_f (even_odd_neighbors c)
     ++ flat_map oe_f (odd_even_neighbors c)
   ; mg_init := fun p => match p with 
                         | Odd_even_fall _ _ => 1
                         | Even_fall _ => 1
                         | Odd_rise _ => 1
                         | _ => 0
                         end
   |}.

About input_RD.
Lemma rd_triples : forall e1 p e2,
      In (e1, p, e2) (mg_triples rise_decoupled) <->
      e1 = input_RD p /\ e2 = output_RD p.
Admitted.



Open Scope nat_scope.
Inductive is_enabled_RD : event even odd -> marking transitions_RD -> Prop :=
| Even_fall_enabled E m :
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Even_fall E)) ->
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_fall E)) ->
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Odd_even_fall O E)) ->
  is_enabled_RD (Fall (Even E)) m
| Even_rise_enabled E m :
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_rise E)) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m  (Odd_even_rise E O)) ->
  is_enabled_RD (Rise (Even E)) m
| Odd_fall_enabled O m :
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Odd_fall O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Odd_fall O)) ->
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Even_odd_fall E O)) ->
  is_enabled_RD (Fall (Odd O)) m
| Odd_rise_enabled O m :
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Odd_rise O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_odd_rise O E)) ->
  is_enabled_RD (Rise (Odd O)) m
.
Lemma RD_is_enabled_equiv : forall e m,
    is_enabled_RD e m -> is_enabled rise_decoupled e m.
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
  

  Ltac in_preset := 
  match goal with
  | [ |- In ?t (preset _ rise_decoupled ?e) ] => apply in_flat_map; exists (input_RD t, t, e);
    split; [ | simpl; reduce_eqb; simpl; auto ];
    apply in_or_app
  end;
  try (left;
       repeat match goal with
       | [ |- In (_, ?t _, _) (flat_map _ _) ] => apply in_flat_map
       | [ E : even , O : odd |- exists x : even * odd, _ ] => exists (E,O)
       | [ E : even , O : odd |- exists x : odd * even, _ ] => exists (E,O)
       end; intuition; fail);
  try (right;
       repeat match goal with
       | [ |- In (_, ?t _, _) (flat_map _ _) ] => apply in_flat_map
       | [ E : even , O : odd |- exists x : even * odd, _ ] => exists (E,O)
       | [ E : even , O : odd |- exists x : odd * even, _ ] => exists (O,E)
       end; intuition; fail).

Lemma is_enabled_RD_equiv : forall e m,
    is_enabled rise_decoupled e m ->
    is_enabled_RD e m.
Proof.
  intros e m Henabled.
  unfold is_enabled, enabled in *.
  assert (H : forall t, In t (preset _ rise_decoupled e) -> 0 <? m t = true).
  { apply forallb_forall; auto. }
  clear Henabled.
  assert (Henabled : forall t, In t (preset _ rise_decoupled e) -> 0 < m t).
  { intros.
    apply Nat.ltb_lt.
    apply H. auto.
  }
  clear H.
  
  destruct e as [[O | E] | [O | E]].
  * constructor; intros E pfE;
      apply Henabled; in_preset.
  * constructor; intros O pfO;
      apply Henabled; in_preset.
  * constructor; intros E pfE;
      apply Henabled; in_preset.
  * constructor; intros O pfO;
      apply Henabled; in_preset.
Qed.


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
          ++ inversion_In. repeat (case_In; auto).
          ++ inversion_In. repeat (case_In; auto). 
Qed.



  Ltac simplify_in_FE :=
      repeat match goal with
      | [ H : In ?x (output_event rise_decoupled) |- _ ] => eapply in_output_event in H; eauto;
                                                            destruct H as [? H]
      | [ H : In ?x (input_event rise_decoupled) |- _ ] => eapply in_input_event in H; eauto;
                                                            destruct H as [? H]
      | [ H : In ?x (mg_triples rise_decoupled) |- _ ] => apply rd_triples in H; destruct H; subst; simpl in *
      | [ |- In (?p, _) (output_event rise_decoupled) ] => eapply in_output_event; eauto;
                                                           exists (input_RD p)
      | [ |- In (_,?p) (input_event rise_decoupled) ] => eapply in_input_event; eauto;
                                                           exists (output_RD p)
      | [ |- In (_,_,_) (mg_triples rise_decoupled) ] => apply rd_triples; split; auto
      end.

  Ltac compare_in x l := 
    let H := fresh "Heq" in
    destruct (in_dec' x l) as [H | ?];
    simplify_in_FE;
      try match goal with
      | [ H : Fall _ = Rise _ |- _ ] => inversion H 
      | [ H : Fall (Even _) = Fall (Odd _) |- _ ] => inversion H
      | [ H : Fall (Odd _) = Fall (Even _) |- _ ] => inversion H
      | [ H : Rise _ = Fall _ |- _ ] => inversion H
      | [ H : Rise (Even _) = Rise (Odd _) |- _ ] => inversion H
      | [ H : Rise (Odd _) = Rise (Even _) |- _ ] => inversion H
      end.

  Ltac compare_next :=
    match goal with
    | [ |- context[ in_dec' ?x ?l ] ] => compare_in x l
    | [ H : context[ in_dec' ?x ?l ] |- _ ] => compare_in x l
    end;
    repeat match goal with
      | [ H : ~ In (_, _) (output_event rise_decoupled) |- _ ] => contradict H; simplify_in_FE; fail
      | [ H : ~ In (_, _) (input_event rise_decoupled) |- _ ] => contradict H; simplify_in_FE; fail
    end.



Ltac specialize_enabled_constraints :=
  repeat match goal with
  | [ HEO : In (_,_) (even_odd_neighbors c)
    , H : forall x, In _ (even_odd_neighbors c) -> _
    |- _] => specialize (H _ HEO)
  | [ HEO : In (_,_) (even_odd_neighbors c)
    , H : forall x y, In _ (even_odd_neighbors c) -> _
    |- _] => specialize (H _ _ HEO)
  | [ HOE : In (_,_) (odd_even_neighbors c)
    , H : forall x, In _ (odd_even_neighbors c) -> _
    |- _] => specialize (H _ HOE)
  | [ HOE : In (_,_) (odd_even_neighbors c)
    , H : forall x y, In _ (odd_even_neighbors c) -> _
    |- _] => specialize (H _ _ HOE)
  end.

Ltac get_enabled_constraints :=
  try match goal with
  | [ H : is_enabled rise_decoupled _ _ |- _ ] => apply is_enabled_RD_equiv in H; inversion H; subst
  end; specialize_enabled_constraints.



Lemma rd_loop_eo : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall E O, In (E,O) (even_odd_neighbors c) ->
        m (Even_fall E) + m (Even_odd_fall E O) + m (Odd_even_rise E O) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros E O pfEO.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next;
      get_enabled_constraints; omega.
Qed.

Lemma rd_loop_odd : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall E O, In (E,O) (even_odd_neighbors c) ->
    m (Odd_fall O) + m (Odd_rise O) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros E O pfEO.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next; get_enabled_constraints; omega.
Qed.

Lemma rd_loop_oe : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall O E, In (O,E) (odd_even_neighbors c) ->
        m (Odd_fall O) + m (Odd_even_fall O E) + m (Even_odd_rise O E) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros O E pfOE.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next;
      get_enabled_constraints; omega.
Qed.

Lemma rd_loop_even : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall O E, In (O,E) (odd_even_neighbors c) ->
    m (Even_fall E) + m (Even_rise E) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros O E pfOE.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next; get_enabled_constraints; omega.
Qed.

Lemma enabled_input_0 : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall p, is_enabled_RD (input_RD p) m ->
    (forall p' : transitions_RD, m p' = 0 \/ m p' = 1) ->
    m p = 0.
Proof.
  intros t m Hm. induction Hm; intros p Henabled IH.
  + admit.
  + subst. unfold fire.
    compare_next. admit (*?*).
    compare_next. admit.
Abort.


Lemma rd_safe : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall p, m(p) = 0 \/ m(p) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros p.
  * destruct p; simpl; auto.
  * apply is_enabled_RD_equiv in H.
    subst.
    unfold fire.
    compare_next.
    { destruct (IHHm p) as [Hp | Hp]; rewrite Hp; auto. }
    compare_next.
    { destruct (IHHm p) as [Hp | Hp]; rewrite Hp; auto.
      contradict Hp. (* based on the fact that (input_RD p) is enabled in m *) admit.
    }
    { apply IHHm. }
Abort.


Lemma fall_enabled_even_opaque : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
(*    is_enabled rise_decoupled (Fall (Odd O)) m -> *)
    0 < m (Even_odd_fall E O) ->
    In (E,O) (even_odd_neighbors c) ->
    transparent s (Even E) = false.
Proof.
  intros t; induction t as [P | e t]; intros m O E Hm Henabled Hneighbor.
  * simpl in *.
    inversion Hm; subst.

    apply H0.
    apply RD_is_enabled_equiv.
    constructor; intros O' HO'; auto.

  * simpl.
    inversion Hm; subst.
    unfold fire in Henabled.
    assert (Rise (Even E) <> e).
    { inversion 1; subst. 
      repeat get_enabled_constraints.
      (* if it were, then (E+) is enabled, meaning that m0(O- -> E+) = 1, which further means that
        m0(E+ -> E-) = 0 and m0(E- -> O-) = 0. *)
      unfold fire in *.
      repeat compare_next.
      set (loop := rd_loop_eo _ _ H4 _ _ Hneighbor).
      omega.
    }
    reduce_eqb.
    compare (Fall (Even E) : event even odd) e; auto.
    (* e is enabled in m0=t. e <> E+, e <> E-. *)
    (* Since O- is enabled in (e::t), e must be equal to O+. *)

    repeat compare_next; find_contradiction.
    { contradict Henabled. 
      set (Hloop := rd_loop_eo _ _ H4 _ _ Hneighbor).
      omega.
      (* since m0(E- → O-) = 0 or 1, it cannot be the case that 0 < m0(E- → O-)-1 *)
    }
    { eapply IHt; eauto. }
Qed.

Lemma fall_enabled_odd_opaque : forall t m O E,
    {rise_decoupled}⊢ t ↓ m ->
    0 < m (Odd_even_fall O E) ->
(*    is_enabled rise_decoupled (Fall (Even E)) m ->*)
    In (O,E) (odd_even_neighbors c) ->
    transparent t (Odd O) = false.
Proof.
  intros t; induction t as [P | e t]; intros m O E Hm Henabled Hneighbor.

  * simpl in *.
    inversion Hm; subst.
    (* I think the precondition of H0 is not enough to know that P(Odd O) = false, since neither O+ nor O- are enabled in the initial state. *)
(*    apply H0.*)
    admit.

  * simpl.
    inversion Hm; subst.
    unfold fire in Henabled.
    assert (Rise (Odd O) <> e).
    { inversion 1; subst. 
      repeat get_enabled_constraints.
      unfold fire in *.
      repeat compare_next.
      set (loop := rd_loop_oe _ _ H4 _ _ Hneighbor).
      omega.
    }
    reduce_eqb.
    compare (Fall (Odd O) : event even odd) e; auto.
    (* e is enabled in m0=t. e <> O+, e <> O-. *)
    (* Since E- is enabled in (e::t), e must be equal to E+. *)

    repeat compare_next; find_contradiction.
    { contradict Henabled. 
      set (Hloop := rd_loop_oe _ _ H4 _ _ Hneighbor).
      omega.
    }
    { eapply IHt; eauto. }
Admitted.

Lemma fall_enabled_even_odd_strong : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
(*    is_enabled rise_decoupled (Fall (Odd O)) m -> *)
    In (E,O) (even_odd_neighbors c) ->
     (0 < m (Even_odd_fall E O) -> num_events (Fall (Even E)) s = 1 + num_events (Fall (Odd O)) s)
  /\ (0 < m (Odd_even_rise E O) -> num_events (Fall (Even E)) s = num_events (Fall (Odd O)) s)
  /\ (0 < m (Even_fall E) -> num_events (Fall (Even E)) s = num_events (Fall (Odd O)) s).
Proof.
  intros t; induction t as [P | e t]; intros m O E Hm  Hneighbor; repeat split; intros Henabled.

  * inversion Hm; subst.
    simpl in Henabled.
    find_contradiction.


  * inversion Hm; subst.
    unfold fire in Henabled.
    simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { specialize (IHt _ _ _ H4 Hneighbor).
      destruct IHt as [IH1 [IH2 IH3]].
      rewrite IH3; auto.
      get_enabled_constraints; auto.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb.
      contradict Henabled.
      set (Hloop := rd_loop_eo _ _ H4 _ _ Hneighbor).
      omega.
    }
    repeat compare_next; reduce_eqb.
    { specialize (IHt _ _ _ H4 Hneighbor).
      destruct IHt as [IH1 [IH2 IH3]].
      apply IH1; auto.
    }


  * inversion Hm; subst.
    unfold fire in Henabled.
    specialize (IHt _ _ _ H4 Hneighbor).
    destruct IHt as [IH1 [IH2 IH3]].
    set (Hloop := rd_loop_eo _ _ H4 _ _ Hneighbor).
    simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb. 
      get_enabled_constraints.
      contradict Henabled.
      omega.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next.
      get_enabled_constraints.
      apply IH1; auto.
    }
    repeat compare_next; find_contradiction.
    { contradict Henabled.
      omega.
    }
    { apply IH2; auto. }

  * inversion Hm; subst.
    unfold fire in Henabled.
    specialize (IHt _ _ _ H4 Hneighbor).
    destruct IHt as [IH1 [IH2 IH3]].
    set (Hloop := rd_loop_eo _ _ H4 _ _ Hneighbor).

    simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb.
      get_enabled_constraints.
      contradict Henabled.
      omega.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next.
      get_enabled_constraints.
      contradict Henabled.
      omega.
    }
    repeat compare_next; find_contradiction.
    { get_enabled_constraints.
      apply IH2; auto.
    }
    { apply IH3; auto. }
Qed.

Lemma fall_enabled_even_odd : forall t m O E,
    {rise_decoupled}⊢ t ↓ m ->
    is_enabled rise_decoupled (Fall (Odd O)) m ->
    In (E,O) (even_odd_neighbors c) ->
    num_events (Fall (Even E)) t = 1 + num_events (Fall (Odd O)) t.
Proof.
  intros t m O E Hm Henabled Hneighbors.
  set (H := fall_enabled_even_odd_strong t m O E Hm Hneighbors).
  destruct H as [H1 [H2 H3]].
  apply H1.
  get_enabled_constraints; auto.
Qed.


Lemma fall_enabled_odd_even : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    is_enabled rise_decoupled (Fall (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    num_events (Fall (Odd O)) s = num_events (Fall (Even E)) s.
Admitted.




Theorem rise_decoupled_flow_equivalence_rel : flow_equivalence_rel _ _ rise_decoupled c init_st.
Proof.
  intros l t v Hrel.
  dependent induction Hrel; intros [m Hm].
  * destruct l as [O | E].
    (* l must be odd *)
    2:{ assert (P (Even E) = true).
        { inversion Hm as [P' Htransparent Hopaque | ].
          rewrite Hopaque; [auto | ].
          apply RD_is_enabled_equiv.
          constructor; intros; auto.
        }
        find_contradiction.
    }
    simpl. reflexivity.
  * inversion Hm as [ | e0 m0 ? t' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    compare (Rise l) e.
    eapply IHHrel; eauto.

  * inversion Hm as [ | e0 m0 ? t' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    reduce_eqb. Search sync_eval S.
    erewrite sync_eval_S; eauto.
    intros l' Hl'.
    erewrite H1; eauto.
    2:{ inversion Hl'; subst. 
        { eapply fall_enabled_even_opaque; eauto. 
          get_enabled_constraints.
          auto.
        }
        { eapply fall_enabled_odd_opaque; eauto.
          get_enabled_constraints.
          auto.
        }
    }

    { inversion Hl'; subst.
      { erewrite fall_enabled_even_odd; eauto. }
      { erewrite fall_enabled_odd_even; eauto. }
    }
        
  Qed.

(*

  Lemma fall_enabled_transparent : forall (t : trace even odd)
                                          (m : marking transitions_RD),
    {rise_decoupled}⊢ t ↓ m ->
    forall l, is_enabled rise_decoupled (Fall l) m ->
              transparent t l = true.
  Proof.
    intros t m pf.
    induction pf as [lset Htransparent Hopaque | ]; intros l Henabled.
    * simpl. apply Hopaque.
      assumption.
    * apply is_enabled_RD_equiv in Henabled.
      inversion Henabled; subst.
      + (* Even case *)
        simpl in *. unfold update_transparency_predicate.

        compare (Rise (Even E) : event even odd) e; auto.
        compare (Fall (Even E) : event even odd) e; auto.
        { absurd (0 < fire (Fall (Even E)) rise_decoupled m (Even_fall E)); auto.
          unfold fire.
          destruct (in_dec' (Even_fall E, Fall (Even E)) (output_event rise_decoupled))
            as [Hin | Hin].
          2:{ contradict Hin.
              eapply in_output_event; eauto.
              exists (Rise (Even E)).
              simpl.
              apply in_or_app.
              left.
              apply in_flat_map.
              eexists. split.
              2:{ admit. }
              admit.
            }
          admit (*?*). admit.
        }

        unfold fire in H2. 
        destruct (in_dec' (Even_fall E, e) (output_event rise_decoupled)) as [H2' | H2'].
        { admit (*contradiction.*). }
        destruct (in_dec' (e,Even_fall E) (input_event rise_decoupled)) as [H2'' | H2''].
        { admit (* contradiction *). }

        
        apply IHpf.
        apply RD_is_enabled_equiv.
        constructor; auto.
        intros O pfO.
        specialize (H3 O pfO).

        unfold fire in H3.

        destruct (in_dec' (Even_odd_rise O E, e) (output_event rise_decoupled)) as [H3' | H3'].
        { admit (*contradiction.*). }
        destruct (in_dec' (e,Even_odd_rise O E) (input_event rise_decoupled)) as [H3'' | H3''].
        { admit (* contradiction *). }
Admitted.

Lemma rise_enabled_opaque :  forall {places : Set} `{Hplaces : eq_dec places}
                                          (M : marked_graph (event even odd) places)
                                          (t : trace even odd)
                                          (m0 m : marking places)
                                          (l : latch even odd),
    {M}⊢ t ↓ m ->
    is_enabled M (Rise l) m ->
    transparent t l = false.
Abort.



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
*)

End RiseDecoupled.
