Require Import Base.
Require Import FlowEquivalence.
Require Import Monad.


Require Import List.
Import ListNotations.
Open Scope list_scope.



Section state_space.

Variable name : Set.
Context `{name_eq_dec : eq_dec name}.
Import EnsembleNotation.
Open Scope ensemble_scope.

(*Definition e_state {X} (S : Ensemble X) := forall (x : X), x ∈ S -> value.
Definition update {X} `{eq_dec X}
                  {S : Ensemble X} (σ : e_state S) (x : X) (v : value) : e_state S :=
    fun y pf_y =>
      if x =? y then v
      else σ y pf_y.
*)

Definition fin_state (X : Set) := X -> option value.
Definition fin_update {X : Set} `{eq_dec X} (σ : fin_state X) (x : X) (v : value) : fin_state X :=
  fun y => if x =? y then Some v
           else σ y.
Definition restrict {X : Set} (S : Ensemble X) `{in_dec _ S} (σ : fin_state X) : fin_state X :=
  fun y => if y ∈? S
           then σ y
           else None.
Definition in_fin_state {X} (σ : fin_state X) (x : X) :=
  match σ x with
  | Some _ => True
  | None => False
  end.


(*
Inductive e_event {X} (I O : Ensemble X) :=
| Input_Event x : x ∈ I -> value -> e_event I O
| Output_Event x : x ∈ O -> value -> e_event I O
.
Arguments Input_Event {X I O}.
Arguments Output_Event {X I O}.
Inductive is_input_event {X} {I O : Ensemble X} : option (e_event I O) -> Prop :=
| Is_Input_Event x (pf : x ∈ I) v : is_input_event (Some (Input_Event x pf v)).
Inductive event_in {X} {I O : Ensemble X} (S : Ensemble X) : option (e_event I O) -> Prop :=
| Input_Event_In x (pf : x ∈ I) v : x ∈ S -> event_in S (Some (Input_Event x pf v))
| Output_Event_In x (pf : x ∈ O) v : x ∈ S -> event_in S (Some (Output_Event x pf v))
.
*)

Inductive event :=
| Eps : event
| Value : name -> value -> event.

Inductive event_in (I : Ensemble name) : event -> Prop :=
| Event_In i (pf : i ∈ I) v : event_in I (Value i v).

(* css_space should be called state *)
Definition update {X : Set} `{eq_dec X} (σ : state X) (x : X) (v : value) : state X :=
  fun y => if x =? y then v
           else σ y.

Record StateSpace :=
  { space_input : Ensemble name
  ; space_output : Ensemble name
  ; space_internal : Ensemble name
  ; space_step  : state name -> event -> option (state name) -> Prop
  }.
Notation "C ⊢ σ →{ e } τ" := (space_step C σ e τ) (no associativity, at level 70).
Definition space_domain (S : StateSpace) := space_input S ∪ space_output S ∪ space_internal S.

Record well_formed (S : StateSpace) (σ : state name) :=
  { (*space_dom : forall x, x ∈ space_domain S <-> in_fin_state σ x*)
    space_input_output : space_input S ⊥ space_output S
  ; space_input_internal : space_input S ⊥ space_internal S
  ; space_output_internal : space_output S ⊥ space_internal S
  }.
Record stable (S : StateSpace) (σ : state name) :=
  { stable_wf : well_formed S σ
  ; stable_step : forall e τ, S ⊢ σ →{e} τ -> event_in (space_input S) e }.

Class stable_dec (S : StateSpace) :=
  { space_stable_dec : forall σ, stable S σ + ~ stable S σ }.

Section FuncStateSpace.

  (* Define a circuit state space from a combinational logic function *)

  Variable I : Ensemble name.
  Variable x : name.
  Variable f : state name -> value.
  Hypothesis x_notin_I : ~ (x ∈ I).

  Let dom := I ∪ singleton x ∪ ∅.
  Hint Unfold dom.
  Lemma x_in_dom : x ∈ dom. unfold dom. auto with sets. Qed.
  Lemma I_subset_dom : forall i, i ∈ I -> i ∈ dom.
  Proof. unfold dom. auto with sets. Qed.

  Let func_stable (σ : state name) := σ x = f σ.
  Hint Unfold func_stable.
  
  Inductive func_step (σ : state name) :
                      event ->
                      option (state name) ->
                      Prop :=
  | func_input_stable i (pf_i : i ∈ I) v :
    func_stable σ ->
    σ i <> v ->
    func_step σ (Value i v)
                (Some (update σ i v))

  | func_input_unstable i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
(*    ~ (func_stable (update σ i v)) -> (* in a binary system, this is ok *)*)
    f σ = f (update σ i v) -> (* ok to update input in an unstable system if the output doesn't change *)
    func_step σ (Value i v) (Some (update σ i v))


  | func_err i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
    f σ <> f (update σ i v) -> (* if input updates in an unstable system causes output to change, go to error state*)
    func_step σ (Value i v) None

  | func_output v :
    ~ (func_stable σ) ->
    σ x = v ->
    func_step σ (Value x v)
                (Some (update σ x v))
  .
    
  Program Definition func_space : StateSpace :=
  {| space_input := I
   ; space_output := singleton x
   ; space_internal := ∅
   ; space_step := func_step
   |}.

  (* This just depends on the enumerability of I *)
  Hypothesis space_wf_decidable : forall σ, well_formed func_space σ + ~(well_formed func_space σ).

  Lemma func_stable_equiv : forall σ, well_formed func_space σ ->
        func_stable σ <-> stable func_space σ.
  Proof.
    intros σ Hwf. split; intros Hstable.
    * (*destruct Hstable as [H_x_stable H_I_stable].*)
      split; [assumption | ].
      intros e τ Hstep.
      inversion Hstep; subst.
      + constructor. auto.
      + contradiction.
      + contradiction.
      + contradiction.
    * compare (σ x) (f σ); auto.
      absurd (event_in (space_input func_space) (Value x (σ x))).
      { inversion 1; subst. simpl in *.
        contradiction. }
      { eapply Hstable.
        apply func_output; auto.
      }
  Qed.


  Instance func_stable_dec : stable_dec func_space.
  Proof.
    split.
    intros σ.
    destruct (space_wf_decidable σ) as [Hwf | Hwf].
    2:{ right. inversion 1. contradiction. }
    {
    compare (f σ) (σ x).
    * left. apply func_stable_equiv; auto.

    * right. intros Hstable. 
      apply func_stable_equiv in Hstable; auto.
    }
  Defined.

End FuncStateSpace.

Section UnionStateSpace.

  Variable S1 S2 : StateSpace.
  Hypothesis output_dec1 : in_dec (space_output S1).
  Hypothesis output_dec2 : in_dec (space_output S2).

  Hypothesis output_disjoint : space_output S1 ⊥ space_output S2.
  Hypothesis wires1_disjoint : space_internal S1 ⊥ space_domain S2.
  Hypothesis wires2_disjoint : space_domain S1 ⊥ space_internal S2.

  Let union_input := (space_input S1 ∖ space_output S2) ∪ (space_input S2 ∖ space_output S1).
  Let union_output := space_output S1 ∪ space_output S2.
  Let union_internal := space_internal S1 ∪ space_internal S2.
  Hint Unfold union_input union_output union_internal.

  Inductive union_input_event e :=
  | driven_by_1 : event_in (space_output S1) e ->
              event_in (space_input S2) e ->
              union_input_event e
  | driven_by_2 : event_in (space_input S1) e ->
              event_in (space_output S2) e ->
              union_input_event e
  | driven_by_env : event_in (space_input S1) e ->
                event_in (space_input S2) e ->
                union_input_event e.

  Context `{in_dec _ (space_domain S1)} `{in_dec _ (space_domain S2)}.

  Definition state_equiv_on (X : Ensemble name) (τ1 τ2 : option (state name)) :=
      match τ1, τ2 with
      | Some σ1, Some σ2 => forall x, x ∈ X -> σ1 x = σ2 x
      | None, None => True
      | _, _ => False
      end.


  Inductive union_step (σ : state name)
                     : event ->
                       option (state name) ->
                       Prop :=
  | union_step_1 e τ :
    ~ (event_in (space_domain S2) e) ->
    S1 ⊢ σ →{e} τ ->
    state_equiv_on (space_domain S2) (Some σ) τ ->
    union_step σ e τ

  | union_step_2 e τ :
    ~ (event_in (space_domain S1) e) ->
    S2 ⊢ σ →{e} τ ->
    state_equiv_on (space_domain S1) (Some σ) τ ->
    union_step σ e τ

  | union_communicate e τ :
    union_input_event e ->
    S1 ⊢ σ →{e} τ ->
    S2 ⊢ σ →{e} τ ->
    (* e must be consistent with both e1 and e2 *)
    union_step σ e τ
    .

    
  Definition union : StateSpace :=
    {| space_input := union_input
     ; space_output := union_output
     ; space_internal := union_internal
     ; space_step := union_step
    |}.


  Instance union_stable_dec `{stable_dec S1} `{stable_dec S2} : stable_dec union.
  Proof. split.
    intros σ.
    destruct (@space_stable_dec S1 _ σ) as [stable1 | stable1];
    destruct (@space_stable_dec S2 _ σ) as [stable2 | stable2].
    
  Abort.



  Definition union_stable (σ : state name) := 
    stable S1 σ /\ stable S2 σ.


  Lemma wf_union : forall σ,
    well_formed S1 σ ->
    well_formed S2 σ ->
    well_formed union σ.
  Proof.
  intros σ [disjoint_in_out1 disjoint_in_int1 disjoint_out_int1]
           [disjoint_in_out2 disjoint_in_int2 disjoint_out_int2].
  constructor;
    simpl in *;
      unfold union_input, union_output, union_internal in *;
    constructor; intros x Hintersect;
    decompose_set_structure.
  - assert (x ∈ space_domain S2).
    { unfold space_domain. auto with sets. }
    find_contradiction.
  - assert (x ∈ space_domain S1).
    { unfold space_domain. auto with sets. }
    find_contradiction.
  - assert (x ∈ space_domain S2).
    { unfold space_domain. auto with sets. }
    find_contradiction.
  - assert (x ∈ space_domain S1).
    { unfold space_domain. auto with sets. }
    find_contradiction.
  Qed.

  (** Note: I'm not sure the other direction actually is true, as written *)
  Lemma union_stable_implies : forall σ, 
        stable S1 σ ->
        stable S2 σ ->
        stable union σ.
  Proof.
    intros σ Hstable1 Hstable2.
    * split; auto.
      + destruct Hstable1, Hstable2.
        apply wf_union; auto.
      + intros e τ Hstep.
           destruct Hstable1 as [Hwf1 Hstable1];
           destruct Hstable2 as [Hwf2 Hstable2].
        destruct Hstep.
        ++ assert (He : event_in (space_input S1) e).
           { eapply Hstable1; eauto. }
           inversion He; subst.
           constructor. simpl. unfold union_input.
           assert (Hi' : ~(i ∈ space_output S2)).
           { intros He'. apply H1.
             constructor. simpl. unfold space_domain. auto with sets. }
           auto with sets.
        ++ assert (He : event_in (space_input S2) e).
           { eapply Hstable2; eauto. }
           inversion He; subst.
           constructor. simpl. unfold union_input.
           assert (Hi' : ~(i ∈ space_output S1)).
           { intros He'. apply H1.
             constructor. simpl. unfold space_domain. auto with sets. }
           auto with sets.
        ++ assert (He1 : event_in (space_input S1) e).
           { eapply Hstable1; eauto. }
           assert (He2 : event_in (space_input S2) e).
           { eapply Hstable2; eauto. }
           inversion He1; subst.
           inversion He2; subst.
           constructor. simpl. unfold union_input.
           left. constructor; auto.
           intro.
           inversion Hwf2 as [[Hwf2']].
           apply (Hwf2' i).
           auto with sets.
  Qed.
        

End UnionStateSpace.

Section HideStateSpace.

  Variable x : name.
  Variable S : StateSpace.

  Hypothesis x_output : x ∈ space_output S.

  Let hide_input := space_input S.
  Let hide_output := space_output S ∖ singleton x.
  Let hide_internal := space_internal S ∪ singleton x.

  Inductive hide_step (σ : state name) :
                      event ->
                      option (state name) ->
                      Prop :=
  | Hide_Eq v τ:
    S ⊢ σ →{Value x v} τ ->
    hide_step σ Eps τ
  | Hide_Neq e τ :
    S ⊢ σ →{e} τ ->
    ~(event_in (singleton x) e) ->
    hide_step σ e τ
  .

  Definition ss_hide : StateSpace :=
    {| space_input := hide_input
     ; space_output := hide_output
     ; space_internal := hide_internal
     ; space_step := hide_step
    |}.


End HideStateSpace.

Section Flop.

  Variable dp_reset : name.
  Variable clk old_clk : name.
  Variable state0 : name.
  Variable reset_value : value (* the value to set state0 when dp_reset=0 *).

  Context (disjoint : all_disjoint [dp_reset;clk;old_clk; state0]).
  Let flop_input := Couple _ dp_reset clk.
  Let flop_output := singleton state0.
  Let flop_internal := singleton old_clk.

  Let flop_stable σ := (σ dp_reset = Num 0 -> σ state0 = Num 0)
                    /\ (σ dp_reset = Num 1 -> σ clk = σ old_clk).


  Definition neg_value (v : value) : value :=
    match v with 
    | Num 0 => Num 1
    | Num 1 => Num 0
    | _ => v
    end.

  Inductive flop_step (σ : state name) :
                      event ->
                      option (state name) ->
                      Prop :=
  | Flop_Input_Stable i v :
    flop_stable σ ->
    i ∈ flop_input ->
    σ i <> v ->
    flop_step σ (Value i v) (Some (update σ i v))

  | Flop_Input_Unstable i v :
    ~ flop_stable σ ->
    i ∈ flop_input ->
    flop_step σ (Value i v) None

  | Flop_Reset :
    ~ flop_stable σ ->
    σ dp_reset = Num 0 ->
    flop_step σ (Value state0 reset_value) (Some (update σ state0 reset_value))

  | Flop_clk1 new_state0 :
    ~ flop_stable σ ->
    σ dp_reset = Num 1 ->
    σ clk = Num 1 ->
    new_state0 = neg_value (σ state0) ->
    flop_step σ (Value state0 new_state0) (Some (update (update σ state0 new_state0) old_clk (Num 1)))

  | Flop_clk0 :
    ~ flop_stable σ ->
    σ dp_reset = Num 1 ->
    σ clk <> Num 1 ->
    flop_step σ Eps (Some (update σ old_clk (σ clk)))
  .


  Definition flop : StateSpace :=
    {| space_input := flop_input
     ; space_output := flop_output
     ; space_internal := flop_internal
     ; space_step := flop_step
    |}.

  Lemma flop_stable_implies_stable : forall σ, 
    flop_stable σ -> stable flop σ.
  Proof.
    intros σ Hstable.
    constructor.
    * (* well-formed *)
      constructor; simpl in *; unfold flop_input, flop_output, flop_internal in *.
      + constructor.
        intros x Hx.
        decompose_set_structure.
      + constructor.
        intros x Hx.
        decompose_set_structure.
      + constructor.
        intros x Hx.
        decompose_set_structure.
    * intros e τ Hstep.
      destruct Hstep;
        try contradiction;
        try (constructor; auto; fail).
  Qed.

  Lemma stable_implies_flop_stable : forall σ,
    stable flop σ ->
    flop_stable σ.
  Proof.
    intros σ Hstable. constructor; intros Hdp_reset.
    + (* dp_reset = 0 *)
      compare (σ state0) (Num 0); auto.
      (* derive a contradiction, since we can have σ -> σ[state0 ↦ 0] *)
      assert (Hstep : flop ⊢ σ →{Value state0 reset_value} Some (update σ state0 reset_value)).
      { apply Flop_Reset; auto.
        intros [Hreset0 _].
        specialize (Hreset0 Hdp_reset).
        contradiction.
      }
      destruct Hstable as [_ Hstable].
      specialize (Hstable _ _ Hstep).
      (*contradict Hstable.*)
      inversion Hstable; subst.
        simpl in pf. unfold flop_input in pf. 
      decompose_set_structure.
      inversion pf; find_contradiction.

    + (* dp_reset = 1 *)
      compare (σ clk) (σ old_clk); auto.
      (* derive a contradiction, since σ is no longer flop_stable *)
      assert (Hstable' : ~ flop_stable σ).
      { intros [Hreset0 Hreset1].
        specialize (Hreset1 Hdp_reset).
        contradiction.
      }
      compare (σ clk) (Num 1).
      { assert (Hstep : flop ⊢ σ →{Value state0 (neg_value (σ state0))}
                                  Some (update (update σ state0 (neg_value (σ state0))) old_clk (Num 1))).
        { eapply Flop_clk1; auto. }
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        contradict Hstable.
        inversion 1; subst.
          decompose_set_structure. 
          simpl in pf. inversion pf; find_contradiction.
      }
      { assert (Hstep : flop ⊢ σ →{Eps} (Some (update σ old_clk (σ clk)))).
        { eapply Flop_clk0; auto. }
        
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        contradict Hstable.
        inversion 1; subst.
      }
  Qed.

End Flop.





Section Celem.

  Variable x1 x2 y : name.
  Let C_input := Couple _ x1 x2.
  Let C_output := singleton y.
  
  Let C_stable σ := (σ x1 = Num 0 /\ σ x2 = Num 0 -> σ y = Num 0)
                 /\ (σ x1 = Num 1 /\ σ x2 = Num 1 -> σ y = Num 1).

  Inductive C_step (σ : state name) :
                      event ->
                      option (state name) ->
                      Prop :=
  | C_input1_stable v :
    C_stable σ ->
    σ x1 <> v ->
    C_step σ (Value x1 v) (Some (update σ x1 v))
  | C_input2_stable v :
    C_stable σ ->
    σ x2 <> v ->
    C_step σ (Value x2 v) (Some (update σ x2 v))


  | C_input1_unstable v :
    ~ C_stable σ ->
    σ x1 <> v ->
    C_step σ (Value x1 v) None
  | C_input2_unstable v :
    ~ C_stable σ ->
    σ x2 <> v ->
    C_step σ (Value x2 v) None

  | C_output0 :
    σ x1 = Num 0 ->
    σ x2 = Num 0 ->
    σ y <> Num 0 ->
    C_step σ (Value y (Num 0)) (Some (update σ y (Num 0)))
  | C_output1 :
    σ x1 = Num 1 ->
    σ x2 = Num 1 ->
    σ y <> Num 1 ->
    C_step σ (Value y (Num 1)) (Some (update σ y (Num 1)))
  .

  Definition C_elem : StateSpace :=
    {| space_input := C_input
     ; space_output := C_output
     ; space_internal := ∅
     ; space_step := C_step
    |}.

  Lemma C_stable_implies_stable : forall σ, C_stable σ -> stable C_elem σ.
  Abort.
  Lemma stable_implies_C_stable : forall σ, stable C_elem σ -> C_stable σ.
  Abort.

End Celem.

End state_space.

Arguments space_input {name}.
Arguments space_output {name}.
Arguments space_internal {name}.
Arguments space_domain {name}.
Arguments stable {name}.
Arguments Value {name}.
Arguments Eps {name}.
Arguments func_space {name name_eq_dec}.
Arguments C_elem {name name_eq_dec}.
Arguments flop {name name_eq_dec}.
Notation "C ⊢ σ →{ e } τ" := (space_step _ C σ e τ) (no associativity, at level 70).
Notation "S1 ∥ S2" := (union _ S1 S2) (left associativity, at level 91).
