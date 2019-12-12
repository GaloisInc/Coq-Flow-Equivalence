Require Import Base.
Require Import FlowEquivalence.
Import FE_Tactics.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.

Require Import PeanoNat.

Existing Instance event_eq_dec.
Existing Instance latch_eq_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Section Desynchronization.


  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Variable c : circuit even odd.
  Variable init_st : state (latch even odd).


  Inductive desync_place : event even odd -> event even odd -> Set :=
  | latch_fall (l : latch even odd) : desync_place (Rise l) (Fall l)
  | latch_rise (l : latch even odd) : desync_place (Fall l) (Rise l)
  | neighbor_fall : forall l l', neighbor c l l' -> desync_place (Rise l) (Fall l')
  | neighbor_rise : forall l l', neighbor c l l' -> desync_place (Fall l') (Rise l).

  Definition desynchronization : marked_graph (event even odd) :=
    {| place := desync_place
     ; init_marking := fun t1 t2 p => match p with
                                      | latch_rise _ => 1
                                      | neighbor_fall (Even _) (Odd _) _ => 1
                                      | neighbor_rise (Odd _) (Even _) _ => 1
                                      | _ => 0
                                      end
    |}.

  Definition P_D : tstate even odd :=
    fun l => match l with
             | Even _ => Opaque
             | Odd _  => Opaque
             end.

Inductive is_enabled_desync : event even odd -> marking desynchronization -> Prop :=
| latch_fall_enbled l (m : marking desynchronization) :
    0 < m _ _ (latch_fall l) ->
    (forall l0 (pf : neighbor c l0 l), 0 < m _ _ (neighbor_fall l0 l pf)) ->
    is_enabled_desync (Fall l) m
| latch_rise_enabled l (m : marking desynchronization) :
    0 < m _ _ (latch_rise l) ->
    (forall l' (pf : neighbor c l l'), 0 < m _ _ (neighbor_rise l l' pf)) ->
    is_enabled_desync (Rise l) m
.


Lemma desync_is_enabled_equiv : forall e m,
    is_enabled_desync e m -> is_enabled desynchronization e m.
Proof.
  destruct e as [[O | E] | [O | E]];
    intros m; inversion 1; subst;
    intros e0 p;
    simpl in p;
    dependent destruction p;
    auto.
Qed.


Lemma is_enabled_desync_equiv : forall e m,
    is_enabled desynchronization e m ->
    is_enabled_desync e m.
Proof.
  intros e m Henabled.
  unfold is_enabled in *.
  destruct e as [[O | E] | [O | E]];
    constructor; intros; apply Henabled; eexists; try (econstructor; eauto; fail).
Qed.


End Desynchronization.

Arguments P_D {even odd}.
Arguments desynchronization {even odd}.

  Lemma exists_not_forall : forall A (P : A -> Prop),
    (exists x, ~P x) ->
    ~ forall x, P x.
  Proof.
    intros A P [x H] contr.
    specialize (contr x).
    contradiction.
  Qed.

Section OpenPipeline. (* Pipeline A -> B -> C *)

  Inductive o_even := oA | oC.
  Inductive o_odd := oB.
  Instance o_even_eq_dec : eq_dec o_even.
  Proof. 
    split. intros [ | ] [ | ];
      try (left; reflexivity); try (right; discriminate).
  Defined.
  Instance d_odd_eq_dec : eq_dec o_odd.
  Proof. 
    split. intros [ ] [ ];
      try (left; reflexivity).
  Defined.
  Let A : latch o_even o_odd := Even oA.
  Let B : latch o_even o_odd := Odd oB.
  Let C : latch o_even o_odd := Even oC.

  Variable next_state_A : value.
  Variable next_state_B : value -> value.
  Variable next_state_C : value -> value.
  Variable init1 : state (latch o_even o_odd).


  Program Definition c1 : circuit o_even o_odd :=
    {| even_odd_neighbors := [ (oA,oB) ]
     ; odd_even_neighbors := [ (oB,oC) ]
     ; next_state_e := fun e =>
        match e with
        | oA => fun _ => next_state_A
        | oC => fun st => next_state_C (st (existT _ oB _))
        end
     ; next_state_o := fun o =>
        match o with
        | oB => fun st => next_state_B (st (existT _ oA _))
        end
     |}.


  Hypothesis sync_1_2_neq :
    sync_eval c1 init1 1 C <> sync_eval c1 init1 2 C.

(*
  Lemma c_odd_even_neighbors : forall O E,
    In (O,E) (odd_even_neighbors c) ->
    O = B /\ E = C.
  Proof.
    intros O E [H | []].
    inversion H.
    auto.
  Qed.
  Lemma c_even_odd_neighbors : forall E O,
    In (E,O) (even_odd_neighbors c) ->
    E = A /\ O = B.
  Proof.
    intros E O [H | []].
    inversion H.
    auto.
  Qed.
*)

  Definition counter_trace1 : trace o_even o_odd :=
    t_empty ▷ Rise B
            ▷ Rise C
            ▷ Fall B
            ▷ Fall C
            ▷ Rise C
            ▷ Rise B
            ▷ Fall C
(* should be an error here *)
(*
            ▷ Rise A
            ▷ Fall B
            ▷ Fall A
            ▷ Rise A
            ▷ Rise B
            ▷ Fall A
            ▷ Fall B
            ▷ Rise C
            ▷ Rise A
            ▷ Fall C
            ▷ Fall A
*).

    
    

  Lemma counter_trace_well_formed : exists m, 
    { desynchronization c1 }⊢ counter_trace1 ↓ m.
  Proof.
    eexists.
    unfold counter_trace1.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);
    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors;
       try (repeat (unfold fire at 1; simpl; auto); fail).
    simpl. auto. 
  Qed.


 Lemma counter_eval :
    ⟨c1,init1,P_D⟩⊢ counter_trace1 ↓ C ↦{Opaque}
        sync_eval c1 init1 1 C.
  Proof.
    unfold counter_trace1.
    repeat async_constructor; reflexivity.
  Qed.

  Theorem desynchronization_not_flow_equivalent :
    ~ flow_equivalence (desynchronization c1) c1 init1 P_D.
  Proof.
    unfold flow_equivalence.
    apply exists_not_forall.
    exists C.
    apply exists_not_forall.
    exists counter_trace1.
    apply exists_not_forall.
    exists (sync_eval c1 init1 1 C).
    apply exists_not_forall.
    exists (counter_trace_well_formed).
    apply exists_not_forall.
    exists counter_eval.

    replace (num_events (Fall C) counter_trace1) with 2 by reflexivity.
    apply sync_1_2_neq.
  Qed.


End OpenPipeline.

Section EnvPipeline. (* Pipeline ENV <-> A -> B -> C *)

  Inductive e_even := eA | eC.
  Inductive e_odd := eENV | eB.
  Instance e_even_eq_dec : eq_dec e_even.
  Proof. 
    split. intros [ | ] [ | ];
      try (left; reflexivity); try (right; discriminate).
  Defined.
  Instance e_odd_eq_dec : eq_dec e_odd.
  Proof. 
    split. intros [ ] [ ];
      try (left; reflexivity); try (right; discriminate).
  Defined.

  Let ENV : latch e_even e_odd := Odd eENV.
  Let A : latch e_even e_odd := Even eA.
  Let B : latch e_even e_odd := Odd eB.
  Let C : latch e_even e_odd := Even eC.

  (* The environment is a source, and increments the value passed down the
  pipeline every time. *)
  Definition next_state_ENV (vA : value) : value :=
    match vA with
    | X => Int 0
    | Bit false => Int 1
    | Bit true => Int 2
    | Int n => Int (n+1)
    end.

  (* Each pipeline stage simply forwards its value down the pipeline. *)
  Let next_state_A (vENV : value) : value := vENV.
  Let next_state_B (vA : value) : value := vA.
  Let next_state_C (vB : value) : value := vB.

  Program Definition c2 : circuit e_even e_odd :=
    {| even_odd_neighbors := [ (eA,eENV); (eA,eB) ]
     ; odd_even_neighbors := [ (eENV,eA); (eB,eC) ]
     ; next_state_e := fun e =>
        match e with
        | eA => fun st => next_state_A (st (existT _ eENV _))
        | eC => fun st => next_state_C (st (existT _ eB _))
        end
     ; next_state_o := fun o =>
        match o with
        | eENV => fun st => next_state_ENV (st (existT _ eA _))
        | eB => fun st => next_state_B (st (existT _ eA _))
        end
     |}.
  Definition init2 : state (latch e_even e_odd) := fun l =>
    match l with
    | Odd eENV => X
    | Even eA => Int 0
    | Odd eB => X
    | Even eC => X
    end.


  Lemma sync_A : forall n,
    sync_eval c2 init2 n A = Int (Z_of_nat n).
  Proof.
    induction n; auto.
    * simpl; unfold odd_state; simpl; unfold even_state; simpl.
      unfold A in IHn.
      rewrite IHn.
      simpl.
      unfold next_state_A.
      f_equal. 

      replace 1%Z with (Z.of_nat 1) by reflexivity.
      rewrite <- Nat2Z.inj_add.
      replace (n+1) with (1+n) by omega.
      unfold Z.of_nat. simpl.
      reflexivity.
  Qed.

  Lemma sync_B : forall n,
    sync_eval c2 init2 (S n) B = sync_eval c2 init2 n A.
  Proof.
    induction n; auto. 
  Qed.

  Lemma sync_C : forall n,  
    sync_eval c2 init2 n C = sync_eval c2 init2 n B.
  Proof.
    induction n; auto.
  Qed.


  Lemma Pos_n_neq_S : forall (p : positive), p <> (p+1)%positive.
  Proof.
    induction p; simpl; try discriminate.
  Qed.
  Lemma Pos_n_neq_minus : forall (p : positive), Zneg p <> (Z.pos_sub 1 p)%Z.
  Proof.
    intros.
    induction p; simpl; try discriminate.
    destruct p; simpl; try discriminate.
  Qed.

  Lemma Z_n_neq_S : forall (z : Z), z <> (z+1)%Z.
  Proof.
    destruct z; auto.
    discriminate.
    { simpl. inversion 1. apply (Pos_n_neq_S p). auto. }
    { simpl. inversion 1. apply (Pos_n_neq_minus p). auto. }
  Qed.

  Lemma sync_neq : forall n, sync_eval c2 init2 n C <> sync_eval c2 init2 (S n) C.
  Proof.
    induction n; auto.
    * simpl.
      unfold odd_state; simpl; unfold even_state; simpl;
      unfold next_state_C, next_state_B.
      discriminate.
    * simpl.
      unfold odd_state; simpl; unfold even_state; simpl;
      unfold odd_state; simpl; unfold even_state; simpl;
      unfold next_state_C, next_state_B, next_state_A, next_state_ENV.
      rewrite sync_A.


      inversion 1.
      apply (Z_n_neq_S (Z_of_nat n)).
      auto.
  Qed.


  Definition counter_trace2 : trace e_even e_odd :=
    t_empty ▷ Rise B
            ▷ Rise C
            ▷ Fall B
            ▷ Fall C
            ▷ Rise C
            ▷ Rise B
            ▷ Fall C
(*
            ▷ Rise A
            ▷ Fall B
            ▷ Fall A
            ▷ Rise A
            ▷ Rise B
            ▷ Fall A
            ▷ Fall B
            ▷ Rise C
            ▷ Rise A
            ▷ Fall C
            ▷ Fall A.
*).


    
    

  Lemma counter_trace2_well_formed : exists m, 
    { desynchronization c2 }⊢ counter_trace2 ↓ m.
  Proof.
    eexists.
    unfold counter_trace2.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);
    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors;
       try (repeat (unfold fire at 1; simpl; auto); fail).
    simpl. auto. 
  Qed.


 Lemma counter_eval2 :
    ⟨c2,init2,P_D⟩⊢ counter_trace2 ↓ C ↦{Opaque}
        sync_eval c2 init2 1 C.
  Proof.
    unfold counter_trace2.
    repeat async_constructor; reflexivity.
  Qed.

  Theorem desynchronization_not_flow_equivalent2 :
    ~ flow_equivalence (desynchronization c2) c2 init2 P_D.
  Proof.
    unfold flow_equivalence.
    apply exists_not_forall.
    exists C.
    apply exists_not_forall.
    exists counter_trace2.
    apply exists_not_forall.
    exists (sync_eval c2 init2 1 C).
    apply exists_not_forall.
    exists (counter_trace2_well_formed).
    apply exists_not_forall.
    exists counter_eval2.

    replace (num_events (Fall C) counter_trace2) with 2 by reflexivity.
    apply sync_neq.
  Qed.


End EnvPipeline.

