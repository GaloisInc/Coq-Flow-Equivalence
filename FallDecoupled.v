Require Import FlowEquivalence.
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


Section FallDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive fd_place : event even odd -> event even odd -> Set :=
  | Even_fall (E : even) : fd_place (Rise (Even E)) (Fall (Even E))
  | Even_rise (E : even) : fd_place (Fall (Even E)) (Rise (Even E))
  | Odd_fall  (O : odd) : fd_place (Rise (Odd O)) (Fall (Odd O))
  | Odd_rise  (O : odd) : fd_place (Fall (Odd O)) (Rise (Odd O))
    (* E+ → O+ *)
  | Even_rise_odd_rise (E : even) (O : odd) : In (E,O) (even_odd_neighbors c) ->
                                              fd_place (Rise (Even E)) (Rise (Odd O))
    (* O- → E+ *)
  | Odd_fall_even_rise (E : even) (O : odd) : In (E,O) (even_odd_neighbors c) ->
                                              fd_place (Fall (Odd O)) (Rise (Even E))
    (* O+ → E+ *)
  | Odd_rise_even_rise (O : odd) (E : even) : In (O,E) (odd_even_neighbors c) ->
                                              fd_place (Rise (Odd O)) (Rise (Even E))
    (* E- → O+ *)
  | Even_fall_odd_rise (O : odd) (E : even) : In (O,E) (odd_even_neighbors c) ->
                                              fd_place (Fall (Even E)) (Rise (Odd O))
  .


  Definition fall_decoupled 
           : marked_graph (event even odd) :=
    {| place := fd_place
     ; init_marking := fun t1 t2 p => match p with
                                      | Even_rise_odd_rise _ _ _ => 1
                                      | Even_fall _ => 1
                                      | Odd_rise _ => 1
                                      | _ => 0
                                      end
   |}.

  Definition P_FD : tstate even odd :=
    fun l => match l with
             | Even _ => Transparent
             | Odd _  => Opaque
             end.


Inductive is_enabled_FD : event even odd -> marking fall_decoupled -> Prop :=
| Even_fall_enabled E (m : marking fall_decoupled) :
  0 < m _ _ (Even_fall E) ->
  is_enabled_FD (Fall (Even E)) m
| Even_rise_enabled E (m : marking fall_decoupled) :
  (forall O (pf : In (O,E) (odd_even_neighbors c)),
          0 < m _ _ (Odd_rise_even_rise O E pf)) ->
  (0 < m _ _ (Even_rise E)) ->
  (forall O (pf : In (E,O) (even_odd_neighbors c)),
          0 < m _ _ (Odd_fall_even_rise E O pf)) ->
  is_enabled_FD (Rise (Even E)) m
| Odd_fall_enabled O (m : marking fall_decoupled) :
  0 < m _ _ (Odd_fall O) ->
  is_enabled_FD (Fall (Odd O)) m
| Odd_rise_enabled O (m : marking fall_decoupled) :
  (forall E (pf : In (E,O) (even_odd_neighbors c)),
          0 < m _ _ (Even_rise_odd_rise E O pf)) ->
  (0 < m _ _ (Odd_rise O)) ->
  (forall E (pf : In (O,E) (odd_even_neighbors c)),
          0 < m _ _ (Even_fall_odd_rise O E pf)) ->
  is_enabled_FD (Rise (Odd O)) m
.



Lemma FD_is_enabled_equiv : forall e m,
    is_enabled_FD e m -> is_enabled fall_decoupled e m.
Proof.
  destruct e as [[O | E] | [O | E]];
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
  destruct e as [[O | E] | [O | E]];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.
  


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
  | [ H : is_enabled fall_decoupled _ _ |- _ ] => apply is_enabled_FD_equiv in H; inversion H; subst
  end; specialize_enabled_constraints.


Section loop_lemmas.

  Variable t : trace even odd.
  Variable m : marking fall_decoupled.

  Hypothesis fd_t_m : {fall_decoupled}⊢ t ↓ m.

  Lemma odd_loop : forall O, m _ _ (Odd_rise O) + m _ _ (Odd_fall O) = 1.
  Proof.
    intros O.
    induction fd_t_m; auto.
    subst; simpl; unfold fire.
    repeat compare_next.
    { get_enabled_constraints. 
      rewrite <- IHm0 at 3; auto.
      omega.
    }
    { get_enabled_constraints. 
      rewrite <- IHm0 at 3; auto.
      omega.
    }
    { apply IHm0; auto. }
  Qed.


  Lemma even_loop : forall E, m _ _ (Even_rise E) + m _ _ (Even_fall E) = 1.
  Proof.
    intros E. induction fd_t_m; auto.
    subst; simpl; unfold fire.
    repeat compare_next.
    { get_enabled_constraints. etransitivity; [ | apply IHm0; auto]. omega. }
    { get_enabled_constraints. etransitivity; [ | apply IHm0; auto]. omega. } 
    { apply IHm0; auto. }
  Qed.

  Lemma even_odd_loop : forall E O (Hin : In (E,O) (even_odd_neighbors c)),
        m _ _ (Even_rise_odd_rise E O Hin)
      + m _ _ (Odd_fall O)
      + m _ _ (Odd_fall_even_rise E O Hin)
      = 1.
  Proof.
    intros E O  Hin.
    induction fd_t_m; auto.
    subst. unfold fire.
    repeat compare_next.
    { get_enabled_constraints.
      etransitivity; [ | apply IHm0; auto].
      omega.
    }
    { get_enabled_constraints.
      etransitivity; [ | apply IHm0; auto].
      omega.
    }
    { get_enabled_constraints.
      etransitivity; [ | apply IHm0; auto].
      omega.
    }
    { apply IHm0; auto. }
  Qed.

  Lemma odd_even_loop : forall O E (Hin : In (O,E) (odd_even_neighbors c)),
        m _ _ (Odd_rise_even_rise O E Hin)
      + m _ _ (Even_fall E)
      + m _ _ (Even_fall_odd_rise O E Hin)
      = 1.
  Proof.
    intros O E Hin.
    induction fd_t_m; auto.
    subst. unfold fire.
    repeat compare_next.
    { get_enabled_constraints.
      etransitivity; [ | apply IHm0; auto].
      omega.
    }
    { get_enabled_constraints.
      etransitivity; [ | apply IHm0; auto].
      omega.
    }
    { get_enabled_constraints.
      etransitivity; [ | apply IHm0; auto].
      omega.
    }
    { apply IHm0; auto. }
  Qed.


End loop_lemmas.

Section fd_lemmas.

  Variable t : trace even odd.
  Variable m : marking fall_decoupled.

  Hypothesis fd_t_m : {fall_decoupled}⊢ t ↓ m.

  Lemma marking_odd_fall : forall O,
    m _ _ (Odd_fall O) = match transparent t P_FD (Odd O) with
                         | Opaque => 0
                         | Transparent => 1
                         end.
  Proof.
    induction fd_t_m; intros O; auto.
    simpl.
    set (loop := odd_loop t' m m0 O).
    subst. unfold fire. 
    repeat compare_next.
    { get_enabled_constraints. omega. }
    { get_enabled_constraints. omega. }
    { rewrite IHm0; auto. }
  Qed.


  Lemma marking_odd_rise : forall O,
    m _ _ (Odd_rise O) = match transparent t P_FD (Odd O) with
                         | Opaque => 1
                         | Transparent => 0
                         end.
  Proof.
    induction fd_t_m; intros O; auto.
    simpl.
    set (loop := odd_loop t' m m0 O).
    subst. unfold fire. 
    repeat compare_next.
    { get_enabled_constraints. omega. }
    { get_enabled_constraints. omega. }
    { rewrite IHm0; auto. }
  Qed.

  Lemma marking_even_fall : forall E,
    m _ _ (Even_fall E) = match transparent t P_FD (Even E) with
                         | Opaque => 0
                         | Transparent => 1
                         end.
  Proof.
    induction fd_t_m; intros E; auto.
    simpl.
    set (loop := even_loop t' m m0 E).
    subst. unfold fire. 
    repeat compare_next.
    { get_enabled_constraints. omega. }
    { get_enabled_constraints. omega. }
    { rewrite IHm0; auto. }
  Qed.

  Lemma marking_even_rise : forall E,
    m _ _ (Even_rise E) = match transparent t P_FD (Even E) with
                         | Opaque => 1
                         | Transparent => 0
                         end.
  Proof.
    induction fd_t_m; intros E; auto.
    simpl.
    set (loop := even_loop t' m m0 E).
    subst. unfold fire. 
    repeat compare_next.
    { get_enabled_constraints. omega. }
    { get_enabled_constraints. omega. }
    { rewrite IHm0; auto. }
  Qed.

  Lemma odd_num_events : forall O,
    ( m _ _ (Odd_rise O) > 0 ->
      num_events (Rise (Odd O)) t = num_events (Fall (Odd O)) t)
    /\
    ( m _ _ (Odd_fall O) > 0 ->
      num_events (Rise (Odd O)) t = 1 + num_events (Fall (Odd O)) t).
  Proof.
    induction fd_t_m; intros O; split; intros Hrise; auto.
    { contradict Hrise. simpl. inversion 1. }
    { simpl in *.
      set (loop := odd_loop t' m m0 O).
      specialize (IHm0 m0 O).
      destruct IHm0 as [IH1 IH2].
      repeat compare_next; try unfold fire in Hrise; reduce_eqb.
      { contradict Hrise. omega. }
      { apply IH2; auto. }
      { apply IH1; auto. }
    }
    { simpl in *.
      set (loop := odd_loop t' m m0 O).
      specialize (IHm0 m0 O).
      destruct IHm0 as [IH1 IH2].
      repeat compare_next; try unfold fire in Hrise; reduce_eqb.
      { rewrite IH1; auto. }
      { contradict Hrise. omega. }
      { apply IH2; auto. }
    }
  Qed.

  Lemma odd_rise_num_events : forall O,
    m _ _ (Odd_rise O) > 0 ->
    num_events (Rise (Odd O)) t = num_events (Fall (Odd O)) t.
  Proof.
    intros O HO.
    destruct (odd_num_events O) as [H _].
    auto.      
  Qed.

  Lemma odd_fall_num_events : forall O,
    m _ _ (Odd_fall O) > 0 ->
    num_events (Rise (Odd O)) t = 1 + num_events (Fall (Odd O)) t.
    intros O HO.
    destruct (odd_num_events O) as [_ H].
    auto.      
  Qed.

  Lemma even_num_events : forall E,
    ( m _ _ (Even_rise E) > 0 ->
      num_events (Fall (Even E)) t = 1 + num_events (Rise (Even E)) t)
    /\
    ( m _ _ (Even_fall E) > 0 ->
      num_events (Fall (Even E)) t = num_events (Rise (Even E)) t).
  Proof.
    induction fd_t_m; intros E; split; intros Hrise; auto.
    { contradict Hrise. simpl. inversion 1. }
    { simpl in *.
      set (loop := even_loop t' m m0 E).
      specialize (IHm0 m0 E).
      destruct IHm0 as [IH1 IH2].
      repeat compare_next; try unfold fire in Hrise; reduce_eqb.
      { rewrite IH2; auto. }
      { contradict Hrise. omega. }
      { rewrite IH1; auto. }
    }
    { simpl in *.
      set (loop := even_loop t' m m0 E).
      specialize (IHm0 m0 E).
      destruct IHm0 as [IH1 IH2].
      repeat compare_next; try unfold fire in Hrise; reduce_eqb.
      { contradict Hrise. omega. }
      { rewrite IH1; auto. }
      { apply IH2; auto. }
    }
  Qed.


  Lemma even_rise_num_events : forall E,
    m _ _ (Even_rise E) > 0 ->
    num_events (Fall (Even E)) t = 1 + num_events (Rise (Even E)) t.
  Proof.
    intros E HE.
    destruct (even_num_events E) as [H H'].
    auto.      
  Qed.

  Lemma even_fall_num_events : forall E,
    m _ _ (Even_fall E) > 0 ->
    num_events (Fall (Even E)) t = num_events (Rise (Even E)) t.
  Proof.
    intros E HE.
    destruct (even_num_events E) as [H H'].
    auto.      
  Qed.

  Section even_odd.
    Variable E : even.
    Variable O : odd.
    Hypothesis Hin : In (E,O) (even_odd_neighbors c).
    
    Lemma even_odd_num_events : 
       (m _ _ (Odd_fall O) > 0 ->
        num_events (Rise (Odd O)) t = 1 + num_events (Rise (Even E)) t)
    /\ (m _ _ (Odd_fall_even_rise E O Hin) > 0 ->
        num_events (Rise (Odd O)) t = 1 + num_events (Rise (Even E)) t)
    /\ (m _ _ (Even_rise_odd_rise E O Hin) > 0 ->
        num_events (Rise (Odd O)) t = num_events (Rise (Even E)) t).
    Proof.
      induction fd_t_m; repeat split; intros Hgt; simpl in *; auto; find_contradiction.
      { set (Hloop := even_odd_loop t' m m0 E O Hin).
        destruct (IHm0 m0) as [IH1 [IH2 IH3]].
        subst; unfold fire in Hgt.
        repeat compare_next; auto.
        { get_enabled_constraints.
          contradict Hgt.
          omega.
        }
      }
      { set (Hloop := even_odd_loop t' m m0 E O Hin).
        destruct (IHm0 m0) as [IH1 [IH2 IH3]].
        subst; unfold fire in Hgt.
        repeat compare_next; auto.
        { get_enabled_constraints.
          contradict Hgt.
          omega.
        }
      } 
      { set (Hloop := even_odd_loop t' m m0 E O Hin).
        destruct (IHm0 m0) as [IH1 [IH2 IH3]].
        subst; unfold fire in Hgt.
        repeat compare_next; auto.
        { get_enabled_constraints.
          contradict Hgt.
          omega.
        }
      }
    Qed.
  End even_odd.

  Section odd_even.
    Variable O : odd.
    Variable E : even.
    Hypothesis Hin : In (O,E) (odd_even_neighbors c).
    
    Lemma odd_even_num_events : 
       (m _ _ (Even_fall E) > 0 ->
        num_events (Rise (Odd O)) t = num_events (Rise (Even E)) t)
    /\ (m _ _ (Even_fall_odd_rise O E Hin) > 0 ->
        num_events (Rise (Odd O)) t = num_events (Rise (Even E)) t)
    /\ (m _ _ (Odd_rise_even_rise O E Hin) > 0 ->
        num_events (Rise (Odd O)) t = 1 + num_events (Rise (Even E)) t).
    Proof.
      induction fd_t_m; repeat split; intros Hgt; simpl in *; auto; find_contradiction.
      { set (Hloop := odd_even_loop t' m m0 O E Hin).
        destruct (IHm0 m0) as [IH1 [IH2 IH3]].
        subst; unfold fire in Hgt.
        repeat compare_next; auto.
        { get_enabled_constraints.
          contradict Hgt.
          omega.
        }
      }
      { set (Hloop := odd_even_loop t' m m0 O E Hin).
        destruct (IHm0 m0) as [IH1 [IH2 IH3]].
        subst; unfold fire in Hgt.
        repeat compare_next; auto.
        { get_enabled_constraints.
          contradict Hgt.
          omega.
        }
      } 
      { set (Hloop := odd_even_loop t' m m0 O E Hin).
        destruct (IHm0 m0) as [IH1 [IH2 IH3]].
        subst; unfold fire in Hgt.
        repeat compare_next; auto.
        { get_enabled_constraints.
          contradict Hgt.
          omega.
        }
      }
    Qed.
  End odd_even.
    

End fd_lemmas.


  Lemma fall_decoupled_strong : forall l t o v,
    ⟨ c , init_st , P_FD ⟩⊢ t ↓ l ↦{ o } v ->
      forall m, {fall_decoupled}⊢ t ↓ m ->
      forall n,
      n = match l with
          | Odd o' => num_events (Rise (Odd o')) t
          | Even e' => 1 + num_events (Rise (Even e')) t
          end ->
      v = sync_eval c init_st n l.
  Proof.
    intros l t O v Hrel.
    induction Hrel; intros m Hm n Hn.
    * (* Because l is opaque in the initial marking, l must be odd. *)
      inversion Hm; subst.
      destruct l as [O | E].
      2:{ inversion H. }
      simpl. reflexivity.
    * (* l is transparent *)
      rewrite H2.

      erewrite sync_eval_gt; eauto.
      { (* n > 0 *)
        subst.
        destruct l as [O | E]; try omega.

        erewrite odd_fall_num_events; eauto; try omega.
        erewrite marking_odd_fall; eauto.
        rewrite H. omega.
      }

    intros l' Hl'. 
    erewrite H1; eauto.
    
    inversion Hl'; subst; f_equal.
    { edestruct (even_odd_num_events t m Hm E O) as [HEO1 [HEO2 HEO3]]; eauto.
      rewrite HEO1; auto.
      erewrite marking_odd_fall; eauto.
      rewrite H.
      omega.
    }
    { edestruct (odd_even_num_events t m Hm O E) as [HOE1 [HOE2 HOE3]]; eauto.
      rewrite HOE1; eauto; try omega.

      erewrite marking_even_fall; eauto.
      rewrite H; auto.
   }

  * inversion Hm; subst.
    simpl in H. compare (Rise l) e.
    erewrite IHHrel; eauto.
    { destruct l; simpl; reduce_eqb; reflexivity. }

  * inversion Hm.
    assert (n > 0).
    { subst. destruct l; try omega.
      simpl.
      erewrite odd_fall_num_events; eauto; try omega.
    }

    erewrite sync_eval_gt; eauto.
    intros l' Hl'.

    inversion Hm; subst.

    erewrite H1; eauto.
    
    (* since Fall l is enabled *)
     inversion Hl'; subst.
     { f_equal. simpl.
       get_enabled_constraints.
       edestruct (even_odd_num_events) as [HEO1 [HEO2 HEO3]]; eauto.
       erewrite HEO1; auto.
     }
    { f_equal. simpl. get_enabled_constraints. 
      edestruct (odd_even_num_events t' m0 H8 O E) as [HOE1 [HOE2 HOE3]]; eauto.
      erewrite HOE1; auto; try omega.
    }
    Unshelve. all:auto.
Qed.


  Theorem fall_decoupled_flow_equivalence :
    flow_equivalence fall_decoupled c init_st P_FD.
  Proof.
    intros l t v [m Hm] Heval.
    erewrite (fall_decoupled_strong l t Opaque v Heval m Hm); eauto.
    
    destruct l as [O | E].
    + erewrite odd_rise_num_events; eauto.
      erewrite marking_odd_rise; eauto.
      erewrite async_b; eauto.
      auto.
    + erewrite even_rise_num_events; eauto.
      erewrite marking_even_rise; eauto.
      erewrite async_b; eauto.
      auto.
  Qed.
    



End FallDecoupled.
