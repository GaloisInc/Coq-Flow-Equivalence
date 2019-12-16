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
                                      | latch_rise (Even _) => 1
                                      | latch_fall (Odd _) => 1
                                      | neighbor_fall _ _ _ => 1
                                      | _ => 0
                                      end
    |}.

  Definition P_D : tstate even odd :=
    fun l => match l with
             | Even _ => Opaque
             | Odd _  => Transparent
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


  Definition counter_trace1 : trace o_even o_odd :=
    t_empty ▷ Rise C
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
Reset OpenPipeline.


Section EnvPipeline. (* Pipeline ENV <-> A -> B -> C *)

  Inductive e_even := A | C.
  Inductive e_odd := ENV | B.


  Definition eEven : e_even -> latch e_even e_odd := Even.
  Coercion eEven : e_even >-> latch.
  Definition eOdd : e_odd -> latch e_even e_odd := Odd.
  Coercion eOdd : e_odd >-> latch.

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

(*
  Let ENV : latch e_even e_odd := Odd ENV.
  Let A : latch e_even e_odd := Even A.
  Let B : latch e_even e_odd := Odd B.
  Let C : latch e_even e_odd := Even C.
*)

  (* The environment is a source, and increments the value passed down the
  pipeline every time. *)
  Definition next_state_ENV (vA : value) : value :=
    match vA with
    | X => Num 0
    | Num n => Num (n+1)
    end.

  (* Each pipeline stage simply forwards its value down the pipeline. *)
  Let next_state_A (vENV : value) : value := vENV.
  Let next_state_B (vA : value) : value := vA.
  Let next_state_C (vB : value) : value := vB.

  Program Definition c : circuit e_even e_odd :=
    {| even_odd_neighbors := [ (A,ENV); (A,B) ]
     ; odd_even_neighbors := [ (ENV,A); (B,C) ]
     ; next_state_e := fun e =>
        match e with
        | A => fun st => next_state_A (st (existT _ ENV _))
        | C => fun st => next_state_C (st (existT _ B _))
        end
     ; next_state_o := fun o =>
        match o with
        | ENV => fun st => next_state_ENV (st (existT _ A _))
        | B => fun st => next_state_B (st (existT _ A _))
        end
     |}.
  Definition st0 : state (latch e_even e_odd) := fun l =>
    match l with
    | ENV => X
    | A => Num 0
    | B => X
    | C => X
    end.


  Lemma sync_A : forall n,
    sync_eval c st0 n A = Num n.
  Proof.
    induction n; auto.
    * simpl; unfold odd_state; simpl; unfold even_state; simpl.
      unfold eEven in IHn.
      rewrite IHn.
      simpl.
      unfold next_state_A. 
      f_equal. omega.
  Qed.

  Lemma sync_B : forall n,
    sync_eval c st0 (S n) B = sync_eval c st0 n A.
  Proof.
    induction n; auto. 
  Qed.

  Lemma sync_C : forall n,  
    sync_eval c st0 n C = sync_eval c st0 n B.
  Proof.
    induction n; auto.
  Qed.

(*
  (* facts about Z *)
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
*)

  Lemma sync_neq : forall n, sync_eval c st0 n C <> sync_eval c st0 (S n) C.
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

      inversion 1. omega.
  Qed.


  Definition counter_trace : trace e_even e_odd :=
    t_empty ▷ Rise C
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


    
    

  Lemma counter_trace_well_formed : exists m, 
    { desynchronization c }⊢ counter_trace ↓ m.
  Proof.
    eexists.
    unfold counter_trace.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);
    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors;
       try (repeat (unfold fire at 1; simpl; auto); fail).
  Qed.


 Lemma counter_eval :
    ⟨c,st0,P_D⟩⊢ counter_trace ↓ C ↦{Opaque}
        sync_eval c st0 1 C.
  Proof.
    unfold counter_trace.
    repeat async_constructor; reflexivity.
  Qed.

  Theorem desynchronization_not_flow_equivalent2 :
    ~ flow_equivalence (desynchronization c) c st0 P_D.
  Proof.
    unfold flow_equivalence.
    apply exists_not_forall.
    exists C.
    apply exists_not_forall.
    exists counter_trace.
    apply exists_not_forall.
    exists (sync_eval c st0 1 C).
    apply exists_not_forall.
    exists (counter_trace_well_formed).
    apply exists_not_forall.
    exists counter_eval.

    replace (num_events (Fall C) counter_trace) with 2 by reflexivity.
    apply sync_neq.
  Qed.


End EnvPipeline.
Reset EnvPipeline.

Section EnvPipeline. (* Pipeline SRC <-> A -> B -> C <-> SNK *)

  Inductive even := A | C.
  Inductive odd := SRC | B | SNK.


  Definition eEven : even -> latch even odd := Even.
  Coercion eEven : even >-> latch.
  Definition eOdd : odd -> latch even odd := Odd.
  Coercion eOdd : odd >-> latch.

  Instance even_eq_dec : eq_dec even.
  Proof. 
    split. intros [ | ] [ | ];
      try (left; reflexivity); try (right; discriminate).
  Defined.
  Instance odd_eq_dec : eq_dec odd.
  Proof. 
    split. intros [ ] [ ];
      try (left; reflexivity); try (right; discriminate).
  Defined.

  (* The environment is a source, and increments the value passed down the
  pipeline every time. *)
  Definition next_state_SRC (vA : value) : value :=
    match vA with
    | X => Num 0
    | Num n => Num (1+n)
    end.
  Definition next_state_SNK : value := Num 0.
  Definition inc_value (v : value) : value :=
    match v with
    | Num n => Num (1+n)
    | X => Num 0
    end.
  Lemma inc_value_inj : forall v1 v2,
    inc_value v1 = inc_value v2 ->
    v1 = v2.
  Proof.
    intros [x | ] [y | ] Heq; auto; simpl in *;
      inversion Heq; auto.
  Qed.
    

  

  Program Definition c : circuit even odd :=
    {| even_odd_neighbors := [ (A,SRC); (A,B); (C,SNK) ]
     ; odd_even_neighbors := [ (SRC,A); (B,C); (SNK,C) ]
     ; next_state_e := fun e =>
        match e with
        | A => fun st => st (existT _ SRC _)
        | C => fun st => inc_value (st (existT _ B _))
        end
     ; next_state_o := fun o =>
        match o with
        | SRC => fun st => inc_value (st (existT _ A _))
        | B => fun st => inc_value (st (existT _ A _))
        | SNK => fun st => Num 0
        end
     |}.
  Definition st0 : state (latch even odd) := fun l => X.
(*    match l with
    | SRC => Num 0
    | _ => X
    end.*)

  Lemma sync_A : forall n,
    sync_eval c st0 n A = match n with
                          | 0 => X
                          | S n' => Num n'
                          end.
  Proof.
    induction n; auto.
    * simpl; unfold odd_state; simpl; unfold even_state; simpl.
      unfold eEven in IHn.
      rewrite IHn.
      unfold inc_value.
      destruct n; auto. 
  Qed.

  Lemma sync_B : forall n,
    sync_eval c st0 (S n) B = inc_value (sync_eval c st0 n A).
  Proof.
    induction n; auto. 
  Qed.

  Lemma sync_C : forall n, n > 0 ->
    sync_eval c st0 n C = inc_value (sync_eval c st0 n B).
  Proof.
    induction n; intros Hn; auto.
    find_contradiction.
  Qed.

  Lemma sync_neq : forall n, sync_eval c st0 n C <> sync_eval c st0 (S n) C.
  Proof.
    induction n; auto.
    * simpl. discriminate.
    * repeat (rewrite sync_C; [ | omega]).
      repeat rewrite sync_B.
      repeat rewrite sync_A.

      intros H.
      repeat apply inc_value_inj in H.
      destruct n; [discriminate | ].
      inversion H. omega.
  Qed.


  Definition counter_trace : trace even odd :=
    t_empty ▷ Fall SNK ▷ Rise C
            ▷ Fall B
            ▷ Fall C
            ▷ Rise SNK ▷ Fall SNK ▷ Rise C
            ▷ Rise B
            ▷ Fall C
(*
            (* could stop here *)
            ▷ Rise SRC ▷ Fall SRC ▷ Rise A
            ▷ Fall B
            ▷ Fall A
            ▷ Rise SRC ▷ Fall SRC ▷ Rise A
            ▷ Rise B
            ▷ Fall A
            ▷ Fall B
            ▷ Rise SNK ▷ Fall SNK ▷ Rise C
            ▷ Rise SRC ▷ Fall SRC ▷ Rise A
            ▷ Fall C
            ▷ Fall A.
*).


  Lemma counter_trace_well_formed : exists m, 
    { desynchronization c }⊢ counter_trace ↓ m.
  Proof.
    eexists.
    unfold counter_trace.
  
    repeat (try (econstructor; [ | reflexivity | ])); try (econstructor; fail);
    apply desync_is_enabled_equiv; constructor; auto; intros;
    inversion_neighbors;
       try (repeat (unfold fire at 1; simpl; auto); fail).
  Qed.


 Lemma counter_eval :
    ⟨c,st0,P_D⟩⊢ counter_trace ↓ C ↦{Opaque}
        sync_eval c st0 1 C.
  Proof.
    unfold counter_trace. unfold eEven. unfold eOdd.
    repeat async_constructor; reflexivity.
  Qed.

  Theorem desynchronization_not_flow_equivalent2 :
    ~ flow_equivalence (desynchronization c) c st0 P_D.
  Proof.
    unfold flow_equivalence.
    apply exists_not_forall.
    exists C.
    apply exists_not_forall.
    exists counter_trace.
    apply exists_not_forall.
    exists (sync_eval c st0 1 C).
    apply exists_not_forall.
    exists (counter_trace_well_formed).
    apply exists_not_forall.
    exists counter_eval.

    replace (num_events (Fall C) counter_trace) with 2 by reflexivity.
    apply sync_neq.
  Qed.


End EnvPipeline.

