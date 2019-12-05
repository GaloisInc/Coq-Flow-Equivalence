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
Require Import Coq.Program.Equality.



Section RiseDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive rd_place : event even odd -> event even odd -> Set :=
  | Even_fall (E : even) : rd_place (Rise (Even E)) (Fall (Even E))
  | Even_rise (E : even) : rd_place (Fall (Even E)) (Rise (Even E))
  | Odd_fall  (O : odd) : rd_place (Rise (Odd O)) (Fall (Odd O))
  | Odd_rise  (O : odd) : rd_place (Fall (Odd O)) (Rise (Odd O))
  (* E- → O- *)
  | Even_odd_fall (E : even) (O : odd) : In (E,O) (even_odd_neighbors c) ->
                                         rd_place (Fall (Even E)) (Fall (Odd O))
  (* O- → E+ *)
  | Odd_even_rise (E : even) (O : odd)  : In (E,O) (even_odd_neighbors c) ->
                                          rd_place (Fall (Odd O)) (Rise (Even E))
  (* E- → O+ *)
  | Even_odd_rise (O : odd)  (E : even) : In (O,E) (odd_even_neighbors c) ->
                                          rd_place (Fall (Even E)) (Rise (Odd O))
  (* O- → E- *)
  | Odd_even_fall (O : odd)  (E : even) : In (O,E) (odd_even_neighbors c) ->
                                          rd_place (Fall (Odd O)) (Fall (Even E))
  .


(*
  Definition input_RD (t : rd_place) : event even odd :=
    match t with
    | Even_fall E => Rise (Even E)
    | Even_rise E => Fall (Even E)
    | Odd_fall o => Rise  (Odd o)
    | Odd_rise o => Fall (Odd o)
    | Even_odd_fall E o => Fall (Even E)
    | Odd_even_rise E o => Fall (Odd o)
⟨    | Even_odd_rise o E => Fall (Even E)
    | Odd_even_fall o E => Fall (Odd o)
    end.
  Definition output_RD (t : rd_place) : event even odd :=
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
*)

(*

  Instance eqdecRD : eq_dec rd_place.
  Proof.
    split. intros t1 t2.
    destruct Heven as [Heven'], Hodd as [Hodd'].
    destruct t1; destruct t2; try (right; inversion 1; fail);
      try (destruct (Dec E E0) as [HA | HA];
        [subst; intuition | right; inversion 1; contradiction]);
      try (destruct (Dec O O0) as [HB | HB];
        [subst; intuition | right; inversion 1; contradiction]).
  Qed.

*)


(*
Inductive triples_RD : event even odd -> rd_place -> event even odd -> Prop :=

| RD_odd_rise O : triples_RD (Fall (Odd O)) (Odd_rise O) (Rise (Odd O))
| RD_odd_fall O : triples_RD (Rise (Odd O)) (Odd_fall O) (Fall (Odd O))
| RD_even_rise E : triples_RD (Fall (Even E)) (Even_rise E) (Rise (Even E))
| RD_even_fall E : triples_RD (Rise (Even E)) (Even_fall E) (Fall (Even E))


| RD_even_odd_fall E O : In (E,O) (even_odd_neighbors c) ->
                         triples_RD (Fall (Even E)) (Even_odd_fall E O) (Fall (Odd O))
| RD_odd_even_rise E O : In (E,O) (even_odd_neighbors c) ->
                     triples_RD (Fall (Odd O)) (Odd_even_rise E O) (Rise (Even E))
| RD_odd_even_fall O E : In (O,E) (odd_even_neighbors c) ->
                         triples_RD (Fall (Odd O)) (Odd_even_fall O E) (Fall (Even E))
| RD_even_odd_rise O E : In (O,E) (odd_even_neighbors c) ->
                     triples_RD (Fall (Even E)) (Even_odd_rise O E) (Rise (Odd O))
.
*)


  Definition rise_decoupled : marked_graph (event even odd) :=
    {| place := rd_place
     ; init_marking := fun t1 t2 p => match p with
                                      | Even_fall _ => 1
                                      | Odd_rise  _ => 1
                                      | Odd_even_fall _ _ _ => 1
                                      | _ => 0
                                      end
    |}.
                                    
  Definition P_RD : tstate even odd :=
    fun l => match l with
             | Even _ => Transparent
             | Odd _  => Opaque
             end.

Open Scope nat_scope.

(*Definition get_rd_marking m {t1 t2} (p : place rise_decoupled t1 t2) := get_marking rise_decoupled m p.*)

Inductive is_enabled_RD : event even odd -> marking rise_decoupled -> Prop :=
| Even_fall_enabled E (m : marking rise_decoupled) :
         0 < m _ _ (Even_fall E) ->
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m _ _ (Odd_even_fall O E pf)) ->
  is_enabled_RD (Fall (Even E)) m
| Even_rise_enabled E (m : marking rise_decoupled) :
         0 < m _ _ (Even_rise E) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m _ _ (Odd_even_rise E O pf)) ->
  is_enabled_RD (Rise (Even E)) m
| Odd_fall_enabled O (m : marking rise_decoupled) :
         0 < m _ _ (Odd_fall O) ->
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m _ _ (Even_odd_fall E O pf)) ->
  is_enabled_RD (Fall (Odd O)) m
| Odd_rise_enabled O (m : marking rise_decoupled) :
          0 < m _ _ (Odd_rise O) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m _ _ (Even_odd_rise O E pf)) ->
  is_enabled_RD (Rise (Odd O)) m
.
Lemma RD_is_enabled_equiv : forall e m,
    is_enabled_RD e m -> is_enabled rise_decoupled e m.
Proof.
  destruct e as [[O | E] | [O | E]];
    intros m; inversion 1; subst;
    intros e0 p;
    simpl in p;
    dependent destruction p;
    auto.
Qed.
 

Lemma is_enabled_RD_equiv : forall e m,
    is_enabled rise_decoupled e m ->
    is_enabled_RD e m.
Proof.
  intros e m Henabled.
  unfold is_enabled in *.
  destruct e as [[O | E] | [O | E]];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.



Ltac test_dec :=
      try (right; intros [t' H]; inversion H; subst; find_contradiction; fail);
      try (left; eexists; econstructor; eauto; fail).


  Ltac find_event_contradiction :=
    try match goal with
      | [ H : Fall _ = Rise _ |- _ ] => inversion H 
      | [ H : Fall (Even _) = Fall (Odd _) |- _ ] => inversion H
      | [ H : Fall (Odd _) = Fall (Even _) |- _ ] => inversion H
      | [ H : Rise _ = Fall _ |- _ ] => inversion H
      | [ H : Rise (Even _) = Rise (Odd _) |- _ ] => inversion H
      | [ H : Rise (Odd _) = Rise (Even _) |- _ ] => inversion H
    end.
(*
  Ltac compare_input M p t := 
    let H := fresh "Heq" in
    destruct (input_dec M p t) as [[? H] | H];
    [ inversion H; subst | try (contradict H; eexists; econstructor; eauto; fail)];
    find_event_contradiction.

  Ltac compare_output M p t := 
    let H := fresh "Heq" in
    destruct (output_dec M p t) as [[? H] | H];
    [ inversion H; subst | ];
    find_event_contradiction.

  Ltac compare_next :=
    match goal with
    | [ |- context[ output_dec ?M ?p ?t ] ] => compare_output M p t
    | [ |- context[ input_dec ?M ?t ?p ] ] => compare_input M t p
    | [ H : context[ output_dec ?M ?p ?t ] |- _ ] => compare_output M p t
    | [ H : context[ input_dec ?M ?t ?p ] |- _ ] => compare_input M t p

    end.
  Ltac find_triple_contradiction :=
    repeat match goal with
      | [ H : ~ exists t', mg_triples rise_decoupled t' ?p ?e |- _ ] =>
          contradict H; eexists; econstructor; eauto
      | [ H : ~ exists t', mg_triples rise_decoupled ?e ?p t' |- _ ] =>
          contradict H; eexists; econstructor; eauto
    end.
   *)


(*
Ltac unfold_rd_marking :=
  repeat match goal with
  | [ H : context [ get_rd_marking ] |- _ ] => unfold get_rd_marking, get_marking in *
  | [ |- context[ get_rd_marking ] ] => unfold get_rd_marking, get_marking
  | [ H : context [ get_marking ] |- _ ] => unfold get_marking in *
  | [ |- context[ get_marking ] ] => unfold get_marking

  end.
*)


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
  | [ O : odd , HO : forall (o' : odd), _ = _ |- _ ] => specialize (HO O)
  | [ E : even , HE : forall (e' : even), _ = _ |- _ ] => specialize (HE E)
  | [ O : odd , HO : forall (o' : odd), _ < _ |- _ ] => specialize (HO O)
  | [ E : even , HE : forall (e' : even), _ < _ |- _ ] => specialize (HE E)

  end.

Ltac get_enabled_constraints :=
  try match goal with
  | [ H : is_enabled rise_decoupled _ _ |- _ ] => apply is_enabled_RD_equiv in H; inversion H; subst
  end; specialize_enabled_constraints.


Lemma rd_loop_eo : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall E O (pf : In (E,O) (even_odd_neighbors c)),
        m _ _ (Even_fall E) + m _ _ (Even_odd_fall E O pf) + m _ _ (Odd_even_rise E O pf) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros E O pfEO.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next; get_enabled_constraints; simpl in *; try omega.
Qed.

Lemma rd_loop_odd : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall O,
    m _ _ (Odd_fall O) + m _ _ (Odd_rise O) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros O.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next; get_enabled_constraints; try omega.
Qed.

Lemma rd_loop_oe : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall O E (pf : In (O,E) (odd_even_neighbors c)),
        m _ _ (Odd_fall O) + m _ _ (Odd_even_fall O E pf)
                           + m _ _ (Even_odd_rise O E pf) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros O E pfOE.
  + reflexivity.
  + subst. unfold fire. 
    repeat compare_next;
      get_enabled_constraints; try omega.
Qed.

Lemma rd_loop_even : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall E,
    m _ _ (Even_fall E) + m _ _ (Even_rise E) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros E.
  + reflexivity.
  + subst. unfold fire. 
    repeat compare_next; get_enabled_constraints; try omega.
Qed.

(*
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
*)


Lemma fall_enabled_even_opaque : forall t m O E
    (pf : In (E,O) (even_odd_neighbors c)),
    {rise_decoupled}⊢ t ↓ m ->
    0 < m _ _ (Even_odd_fall E O pf) ->
    transparent t P_RD (Even E) = Opaque.
Proof.
  induction t as [ | t ? e]; intros m O E Hneighbor Hm Henabled.
  * simpl in *.
    inversion Hm; subst.
    simpl in Henabled.
    find_contradiction.

  * simpl.
    inversion Hm; subst.
    unfold fire in Henabled.
    set (loop := rd_loop_eo _ _ H4 _ _ Hneighbor).
 
    assert (Rise (Even E) <> e).
    { inversion 1; subst. 
      repeat get_enabled_constraints.
      (* if it were, then (E+) is enabled, meaning that m0(O- -> E+) = 1, which further means that
        m0(E+ -> E-) = 0 and m0(E- -> O-) = 0. *)
      unfold fire in *.
      repeat compare_next.
      omega.
    }
    reduce_eqb.

    repeat compare_next; auto.
    { contradict Henabled. 
      omega.
      (* since m0(E- → O-) = 0 or 1, it cannot be the case that 0 < m0(E- → O-)-1 *)
    }
    { eapply IHt; eauto. }
Qed.

Lemma fall_enabled_odd_opaque : forall t m O E
    (pf : In (O,E) (odd_even_neighbors c)),
    {rise_decoupled}⊢ t ↓ m ->
    0 < m _ _ (Odd_even_fall O E pf) ->
    transparent t P_RD (Odd O) = Opaque.
Proof.
  intros t; induction t as [ | t ? e]; intros m O E Hneighbor Hm Henabled.
  * reflexivity.
  * simpl.
    inversion Hm; subst.
    unfold fire in Henabled.
    set (loop := rd_loop_oe _ _ H4 _ _ Hneighbor).

    assert (Rise (Odd O) <> e).
    { inversion 1; subst. 
      repeat get_enabled_constraints.
      unfold fire in *.
      repeat compare_next.
      omega.
    }
    reduce_eqb.
    compare (Fall (Odd O) : event even odd) e; auto.
    (* e is enabled in m0=t. e <> O+, e <> O-. *)
    (* Since E- is enabled in (e::t), e must be equal to E+. *)

    repeat compare_next; find_contradiction.
    { contradict Henabled. 
      omega.
    }
    { eapply IHt; eauto. }
Qed.

Lemma fall_enabled_even_odd_strong : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    forall (pf : In (E,O) (even_odd_neighbors c)),
     (0 < m _ _ (Even_odd_fall E O pf) -> num_events (Fall (Even E)) s = 1 + num_events (Fall (Odd O)) s)
  /\ (0 < m _ _ (Odd_even_rise E O pf) -> num_events (Fall (Even E)) s = num_events (Fall (Odd O)) s)
  /\ (0 < m _ _ (Even_fall E) -> num_events (Fall (Even E)) s = num_events (Fall (Odd O)) s).
Proof.
  intros t; induction t as [ | t ? e];
    intros m O E Hm  Hneighbor; repeat split; intros Henabled;
    inversion Hm; subst;
    unfold fire in Henabled;
    try (simpl in Henabled; find_contradiction; fail);
    simpl;

    match goal with
    | [ H : In (_, _) (even_odd_neighbors _)
      , H' : {rise_decoupled}⊢ _ ↓ _ |- _ ] =>
      set (Hloop := rd_loop_eo _ _ H' _ _ H);
      specialize (IHt _ _ _ H' H);
      destruct IHt as [IH1 [IH2 IH3]]
    | [ H : In (_, _) (odd_even_neighbors _)
      , H' : {rise_decoupled}⊢ _ ↓ _ |- _ ] =>
      set (Hloop := rd_loop_oe _ _ H' _ _ H);
      specialize (IHt _ _ _ H' H);
      destruct IHt as [IH1 [IH2 IH3]]
    end;
    repeat compare_next; auto;
    try ( get_enabled_constraints; contradict Henabled; omega).
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


Lemma fall_enabled_odd_even_strong : forall t m O E,
    {rise_decoupled}⊢ t ↓ m ->
    forall (pf : In (O,E) (odd_even_neighbors c)),

     (0 < m _ _ (Odd_even_fall O E pf) -> num_events (Fall (Even E)) t = num_events (Fall (Odd O)) t)
  /\ (0 < m _ _ (Even_odd_rise O E pf) -> num_events (Fall (Even E)) t = 1 + num_events (Fall (Odd O)) t)
  /\ (0 < m _ _ (Odd_fall O) -> num_events (Fall (Even E)) t = 1 + num_events (Fall (Odd O)) t).
Proof.
  induction t as [| t ? e];
    intros m O E Hm  Hneighbor; repeat split; intros Henabled;
    inversion Hm; subst;
    unfold fire in Henabled;
    try ( simpl in Henabled; find_contradiction; fail);
    match goal with
    | [ H : In (_, _) (even_odd_neighbors _)
      , H' : {rise_decoupled}⊢ _ ↓ _ |- _ ] =>
      set (Hloop := rd_loop_eo _ _ H' _ _ H);
      specialize (IHt _ _ _ H' H);
      destruct IHt as [IH1 [IH2 IH3]]
    | [ H : In (_, _) (odd_even_neighbors _)
      , H' : {rise_decoupled}⊢ _ ↓ _ |- _ ] =>
      set (Hloop := rd_loop_oe _ _ H' _ _ H);
      specialize (IHt _ _ _ H' H);
      destruct IHt as [IH1 [IH2 IH3]]
    end;    
    simpl;
    repeat compare_next; auto;
    try ( get_enabled_constraints; contradict Henabled; omega).
Qed.

Lemma fall_enabled_odd_even : forall s m O E,
    {rise_decoupled}⊢ s ↓ m ->
    is_enabled rise_decoupled (Fall (Even E)) m ->
    In (O,E) (odd_even_neighbors c) ->
    num_events (Fall (Odd O)) s = num_events (Fall (Even E)) s.
Proof.
  intros t m O E Hm Henabled Hneighbors.
  set (H := fall_enabled_odd_even_strong t m O E Hm Hneighbors).
  destruct H as [H1 [H2 H3]].
  rewrite H1; auto.
Qed.




Theorem rise_decoupled_flow_equivalence_rel : flow_equivalence rise_decoupled c init_st P_RD.
Proof.
  intros l t v [m Hm] Hrel.
  revert m Hm.
  dependent induction Hrel; intros m Hm.
  * destruct l as [O | E]; auto.
    find_contradiction.
  * inversion Hm as [ | e0 m0 ? t0' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    repeat compare_next.
    eapply IHHrel; eauto.

  * inversion Hm as [ | e0 m0 ? t0' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    reduce_eqb.
    erewrite sync_eval_S; eauto.
    intros l' Hl'.
    erewrite H1; eauto.
    2:{ inversion Hl'; subst. 
        { eapply fall_enabled_even_opaque; eauto.
        }
        { eapply fall_enabled_odd_opaque; eauto.
        }
    }

    { inversion Hl'; subst.
      { erewrite fall_enabled_even_odd; eauto. }
      { erewrite fall_enabled_odd_even; eauto. }
    }
    Unshelve.
    auto. auto.
  Qed.

End RiseDecoupled.
