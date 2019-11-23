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


  Inductive places_RD : Set :=
  | Even_fall (E : even) : places_RD
  | Even_rise (E : even) : places_RD
  | Odd_fall  (O : odd) : places_RD
  | Odd_rise  (O : odd) : places_RD
  (* E- → O- *)
  | Even_odd_fall (E : even) (O : odd) : (*In (E,O) (even_odd_neighbors c) ->*) places_RD
  (* O- → E+ *)
  | Odd_even_rise (E : even) (O : odd)  : (*In (E,O) (even_odd_neighbors c) ->*) places_RD
  (* E- → O+ *)
  | Even_odd_rise (O : odd)  (E : even) : (*In (O,E) (odd_even_neighbors c) ->*) places_RD
  (* O- → E- *)
  | Odd_even_fall (O : odd)  (E : even) : (*In (O,E) (odd_even_neighbors c) ->*) places_RD
  .


  Definition input_RD (t : places_RD) : event even odd :=
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
  Definition output_RD (t : places_RD) : event even odd :=
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



  Instance eqdecRD : eq_dec places_RD.
  Proof.
    split. intros t1 t2.
    destruct Heven as [Heven'], Hodd as [Hodd'].
    destruct t1; destruct t2; try (right; inversion 1; fail);
      try (destruct (Dec E E0) as [HA | HA];
        [subst; intuition | right; inversion 1; contradiction]);
      try (destruct (Dec O O0) as [HB | HB];
        [subst; intuition | right; inversion 1; contradiction]).
  Qed.



Inductive triples_RD : event even odd -> places_RD -> event even odd -> Prop :=

| RD_odd_rise O : triples_RD (Fall (Odd O)) (Odd_rise O) (Rise (Odd O))
| RD_odd_fall O : triples_RD (Rise (Odd O)) (Odd_fall O) (Fall (Odd O))
| RD_even_rise E : triples_RD (Fall (Even E)) (Even_rise E) (Rise (Even E))
| RD_even_fall E : triples_RD (Rise (Even E)) (Even_fall E) (Fall (Even E))


(*
| RD_even_fall_EO E O : In (E,O) (even_odd_neighbors c) ->
                     triples_RD (Rise (Even E)) (Even_fall E) (Fall (Even E))
*)
| RD_even_odd_fall E O : In (E,O) (even_odd_neighbors c) ->
                         triples_RD (Fall (Even E)) (Even_odd_fall E O) (Fall (Odd O))
| RD_odd_even_rise E O : In (E,O) (even_odd_neighbors c) ->
                     triples_RD (Fall (Odd O)) (Odd_even_rise E O) (Rise (Even E))
(*
| RD_odd_fall_EO E O : In (E,O) (even_odd_neighbors c) ->
                    triples_RD (Rise (Odd O)) (Odd_fall O) (Fall (Odd O))
| RD_odd_rise E O : In (E,O) (even_odd_neighbors c) ->
                    triples_RD (Fall (Odd O)) (Odd_rise O) (Rise (Odd O))
*)


(*
| RD_odd_fall_OE O E : In (O,E) (odd_even_neighbors c) ->
                       triples_RD (Rise (Odd O)) (Odd_fall O) (Fall (Odd O))
*)
| RD_odd_even_fall O E : In (O,E) (odd_even_neighbors c) ->
                         triples_RD (Fall (Odd O)) (Odd_even_fall O E) (Fall (Even E))
| RD_even_odd_rise O E : In (O,E) (odd_even_neighbors c) ->
                     triples_RD (Fall (Even E)) (Even_odd_rise O E) (Rise (Odd O))
(*
| RD_even_fall_OE O E : In (O,E) (odd_even_neighbors c) ->
                    triples_RD (Rise (Even E)) (Even_fall E) (Fall (Even E))
| RD_even_rise O E : In (O,E) (odd_even_neighbors c) ->
                    triples_RD (Fall (Even E)) (Even_rise E) (Rise (Even E))
*)
.


  Definition rise_decoupled 
           : marked_graph (event even odd) places_RD :=
  {| mg_triples := triples_RD
(*
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
*)
   ; mg_init := fun p => match p with 
                         | Odd_even_fall _ _ => 1
                         | Even_fall _ => 1
                         | Odd_rise _ => 1
                         | _ => 0
                         end
   |}.



(*

Lemma rd_triples : forall e1 p e2,
      In (e1, p, e2) (mg_triples rise_decoupled) ->
      e1 = input_RD p /\ e2 = output_RD p.
Proof.
  intros e1 p e2.
  { intros Hin.
    simpl in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_flat_map in Hin.
      destruct Hin as [[E O] [Hneighbors Hin]].
      simpl in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; auto | ]).
      contradiction.
    + apply in_flat_map in Hin.
      destruct Hin as [[E O] [Hneighbors Hin]].
      simpl in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; auto | ]).
      contradiction.
  }
Qed.


Lemma rd_triples_inv : forall e1 p e2,
      e1 = input_RD p ->
      e2 = output_RD p -> 
      In (e1, p, e2) (mg_triples rise_decoupled) ->

Proof.
  intros e1 p e2.
  { intros Hin.
    simpl in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_flat_map in Hin.
      destruct Hin as [[E O] [Hneighbors Hin]].
      simpl in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; auto | ]).
      contradiction.
    + apply in_flat_map in Hin.
      destruct Hin as [[E O] [Hneighbors Hin]].
      simpl in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; auto | ]).
      contradiction.
  }
Qed.
*)



Open Scope nat_scope.
Inductive is_enabled_RD : event even odd -> marking places_RD -> Prop :=
| Even_fall_enabled E m :
(*  (forall O (pf : In (E,O) (even_odd_neighbors c)),*)
         ( 0 < m (Even_fall E)) ->
(*  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_fall E)) ->*)
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Odd_even_fall O E)) ->
  is_enabled_RD (Fall (Even E)) m
| Even_rise_enabled E m :
(*  (forall O (pf : In (O,E) (odd_even_neighbors c)),*)
         ( 0 < m (Even_rise E)) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m  (Odd_even_rise E O)) ->
  is_enabled_RD (Rise (Even E)) m
| Odd_fall_enabled O m :
(*  (forall E (pf : In (E,O) (even_odd_neighbors c)),*)
         ( 0 < m (Odd_fall O)) ->
(*  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Odd_fall O)) ->*)
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m (Even_odd_fall E O)) ->
  is_enabled_RD (Fall (Odd O)) m
| Odd_rise_enabled O m :
(*  (forall E (pf : In (E,O) (even_odd_neighbors c)),*)
       (   0 < m (Odd_rise O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m (Even_odd_rise O E)) ->
  is_enabled_RD (Rise (Odd O)) m
.
Lemma RD_is_enabled_equiv : forall e m,
    is_enabled_RD e m -> is_enabled rise_decoupled e m.
Proof.
  destruct e as [[O | E] | [O | E]];
    intros m; inversion 1; subst;
    intros p [e0 Htriples];
    inversion Htriples; subst; eauto.
Qed.
  
(*
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
*)

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


Instance input_dec_RD : mg_input_dec rise_decoupled.
Proof.
  split.
  intros e p.
  destruct p;
    destruct e as [[? | E'] | [? | ?]]; test_dec;
  match goal with
  | [ E : even , E' : even |- _ ] =>
    destruct (Dec E E'); subst; test_dec
  | [ O : odd , O' : odd |- _ ] =>
    destruct (Dec O O'); subst; test_dec
  end;
  match goal with
  | [ E : even, O : odd |- _ ] =>
    destruct (in_dec' (E,O) (even_odd_neighbors c)); test_dec; fail
  | [ E : even, O : odd |- _ ] =>
    destruct (in_dec' (O,E) (odd_even_neighbors c)); test_dec; fail
  end.
Defined.

Instance output_dec_RD : mg_output_dec rise_decoupled.
Proof.
  split.
  intros p e.
  destruct p;
    destruct e as [[? | E'] | [? | ?]]; test_dec;
  match goal with
  | [ E : even , E' : even |- _ ] =>
    destruct (Dec E E'); subst; test_dec
  | [ O : odd , O' : odd |- _ ] =>
    destruct (Dec O O'); subst; test_dec
  end;
  match goal with
  | [ E : even, O : odd |- _ ] =>
    destruct (in_dec' (E,O) (even_odd_neighbors c)); test_dec; fail
  | [ E : even, O : odd |- _ ] =>
    destruct (in_dec' (O,E) (odd_even_neighbors c)); test_dec; fail
  end.
Defined.



(*
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
*)
Arguments input_dec {transition place} M {Houtput} : rename.
Arguments output_dec {transition place} M {Houtput} : rename.

  Ltac find_event_contradiction :=
    try match goal with
      | [ H : Fall _ = Rise _ |- _ ] => inversion H 
      | [ H : Fall (Even _) = Fall (Odd _) |- _ ] => inversion H
      | [ H : Fall (Odd _) = Fall (Even _) |- _ ] => inversion H
      | [ H : Rise _ = Fall _ |- _ ] => inversion H
      | [ H : Rise (Even _) = Rise (Odd _) |- _ ] => inversion H
      | [ H : Rise (Odd _) = Rise (Even _) |- _ ] => inversion H
    end.

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
(*    | [ |- context [ eqb ?x1 ?x2 ] ] => compare x1 x2; auto*)
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


Lemma rd_init_even : forall P E m,
    {rise_decoupled}⊢ empty_trace P ↓ m ->
    P (Even E) = Transparent.
Proof.
  intros P E m Hm.
  inversion Hm as [? Hconsistent | ]; subst.
  specialize (Hconsistent (Even E)).
  inversion Hconsistent; subst; auto.
  * get_enabled_constraints; simpl in *; find_contradiction.
  * contradict H0.
    apply RD_is_enabled_equiv.
    constructor; auto.
Qed.


Lemma has_right_neighbor_dec :
    forall l, sumbool (exists l', neighbor c l l') (~ exists l', neighbor c l l').
Admitted.

Lemma rd_init_odd : forall P O m,
    {rise_decoupled}⊢ empty_trace P ↓ m ->
    P (Odd O) = Opaque.
Proof.
  intros P O m Hm.
  inversion Hm as [? Hconsistent | ]; subst.
  specialize (Hconsistent (Odd O)).
  inversion Hconsistent; subst; auto.
  * get_enabled_constraints. simpl in *. find_contradiction.
  * destruct (has_right_neighbor_dec (Odd O)) as [[l' Hneighbor] | Hneighbor].
    + inversion Hneighbor; subst.
      (* OK, e- can fire, but what about other right neighbors? We need to do induction on the number of right neighbors?? *)
      admit.
    + admit.
Admitted.


Lemma rd_loop_eo : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall E O, In (E,O) (even_odd_neighbors c) ->
        m (Even_fall E) + m (Even_odd_fall E O) + m (Odd_even_rise E O) = 1.
Proof.
  intros t m Hm.
  induction Hm; intros E O pfEO.
  + reflexivity.
  + subst. unfold fire.
    repeat compare_next; get_enabled_constraints; try omega; find_triple_contradiction.
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
    repeat compare_next; get_enabled_constraints; try omega; find_triple_contradiction.
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
      get_enabled_constraints; try omega; find_triple_contradiction.
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
    repeat compare_next; get_enabled_constraints; try omega; find_triple_contradiction.
Qed.

(*
Lemma enabled_input_0 : forall t m,
    {rise_decoupled}⊢ t ↓ m ->
    forall p, is_enabled_RD (input_RD p) m ->
    (forall p' : places_RD, m p' = 0 \/ m p' = 1) ->
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
*)


Lemma fall_enabled_even_opaque : forall t m O E,
    {rise_decoupled}⊢ t ↓ m ->
(*    is_enabled rise_decoupled (Fall (Odd O)) m -> *)
    0 < m (Even_odd_fall E O) ->
    In (E,O) (even_odd_neighbors c) ->
    transparent t (Even E) = Opaque.
Proof.
  induction t as [P | t IH e]; intros m O E Hm Henabled Hneighbor.
  * simpl in *.
    inversion Hm; subst.

    specialize (H0 (Even E)).
    inversion H0; subst; auto; get_enabled_constraints; simpl in *; find_contradiction.

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

    compare (Fall (Even E) : event even odd) e; auto.
    (* e is enabled in m0=t. e <> E+, e <> E-. *)
    (* Since O- is enabled in (e::t), e must be equal to O+. *)

    repeat compare_next; find_contradiction.
    { contradict Henabled. 
      omega.
      (* since m0(E- → O-) = 0 or 1, it cannot be the case that 0 < m0(E- → O-)-1 *)
    }
    { eapply IH; eauto. }
Qed.

Lemma fall_enabled_odd_opaque : forall t m O E,
    {rise_decoupled}⊢ t ↓ m ->
    0 < m (Odd_even_fall O E) ->
(*    is_enabled rise_decoupled (Fall (Even E)) m ->*)
    In (O,E) (odd_even_neighbors c) ->
    transparent t (Odd O) = Opaque.
Proof.
  intros t; induction t as [P | t IHt e]; intros m O E Hm Henabled Hneighbor.

  * simpl in *.
    eapply rd_init_odd; eauto.

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
    In (E,O) (even_odd_neighbors c) ->
     (0 < m (Even_odd_fall E O) -> num_events (Fall (Even E)) s = 1 + num_events (Fall (Odd O)) s)
  /\ (0 < m (Odd_even_rise E O) -> num_events (Fall (Even E)) s = num_events (Fall (Odd O)) s)
  /\ (0 < m (Even_fall E) -> num_events (Fall (Even E)) s = num_events (Fall (Odd O)) s).
Proof.
  intros t; induction t as [P | t IHt e];
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
    end.

  * compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { 
      rewrite IH3; auto.
      get_enabled_constraints; auto.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb; find_triple_contradiction.
      contradict Henabled.
      omega.
    }
    repeat compare_next; reduce_eqb.
    { apply IH1; auto. }

  * simpl.
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

  * simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb; find_triple_contradiction.
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


Lemma fall_enabled_odd_even_strong : forall t m O E,
    {rise_decoupled}⊢ t ↓ m ->
    In (O,E) (odd_even_neighbors c) ->

     (0 < m (Odd_even_fall O E) -> num_events (Fall (Even E)) t = num_events (Fall (Odd O)) t)
  /\ (0 < m (Even_odd_rise O E) -> num_events (Fall (Even E)) t = 1 + num_events (Fall (Odd O)) t)
  /\ (0 < m (Odd_fall O) -> num_events (Fall (Even E)) t = 1 + num_events (Fall (Odd O)) t).
Proof.
  induction t as [P | t IHt e];
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
    end.

  * simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb; find_triple_contradiction.
      contradict Henabled.
      omega.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { 
      rewrite IH3; auto.
      get_enabled_constraints; auto.
    }
    repeat compare_next; reduce_eqb.
    { apply IH1; auto.
    }

  * simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { rewrite IH1; auto.
      get_enabled_constraints; auto.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb.
      get_enabled_constraints.
      contradict Henabled.
      omega.
    }
    repeat compare_next; reduce_eqb.
    { contradict Henabled. omega. }
    { rewrite IH2; auto. }

  * simpl.
    compare (Fall (Even E) : event even odd) e; simpl; reduce_eqb.
    { rewrite IH1; auto.
      get_enabled_constraints; auto.
    }
    compare (Fall (Odd O) : event even odd) e; simpl; reduce_eqb.
    { repeat compare_next; reduce_eqb; find_triple_contradiction.
      get_enabled_constraints.
      contradict Henabled.
      omega.
    }
    repeat compare_next; reduce_eqb.
    { get_enabled_constraints.
      rewrite IH2; auto.
    }
    { rewrite IH3; auto. }
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
  get_enabled_constraints; auto.
Qed.




Theorem rise_decoupled_flow_equivalence_rel : flow_equivalence rise_decoupled c init_st.
Proof.
  intros l t v Hrel.
  dependent induction Hrel; intros [m Hm].
  * destruct l as [O | E].
    (* l must be odd *)
    2:{ assert (P (Even E) = Transparent) by (eapply rd_init_even; eauto).
        find_contradiction.
    }
    reflexivity.
  * inversion Hm as [ | e0 m0 ? t' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    compare (Rise l) e.
    eapply IHHrel; eauto.

  * inversion Hm as [ | e0 m0 ? t' Henabled Hfire Hm']; subst; rename m0 into m.
    simpl in *.
    reduce_eqb.
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

End RiseDecoupled.
