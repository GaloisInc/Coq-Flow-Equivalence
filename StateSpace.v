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


Arguments Value {latch val}.
Inductive event_in {val} (I : Ensemble name) : option (event name val) -> Prop :=
| Event_In i (pf : i ∈ I) v : event_in I (Some (Value i v)).

(* css_space should be called state *)
Definition update {X : Set} `{eq_dec X} (σ : state X) (x : X) (v : value) : state X :=
  fun y => if x =? y then v
           else σ y.

Record StateSpace :=
  { space_input : Ensemble name
  ; space_output : Ensemble name
  ; space_internal : Ensemble name
  ; space_step  : state name -> option (event name value) -> option (state name) -> Prop
  }.
Print option.
(* C : StateSpace *)
(* space_step C : state name -> option (event name value) -> option (state name) -> Prop *)
Notation "C ⊢ σ →{ e } τ" := (space_step C σ e τ) (no associativity, at level 70).

Reserved Notation "C ⊢ σ →*{ t } τ" (no associativity, at level 70).
Inductive space_steps (C : StateSpace) (σ : state name)
          : trace name value -> option (state name) -> Prop :=
| steps0 : C ⊢ σ →*{t_empty} Some σ
| steps1 σ' t e τ :
    C ⊢ σ →*{t} Some σ' ->
    C ⊢ σ' →{Some e} τ ->
    C ⊢ σ →*{t ▶ e} τ
| stepsEps σ' t τ :
    C ⊢ σ →*{t} Some σ' ->
    C ⊢ σ' →{None} τ ->
    C ⊢ σ →*{t} τ
where "C ⊢ σ →*{ t } τ" := (space_steps C σ t τ).

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
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  | func_input_stable i (pf_i : i ∈ I) v :
    func_stable σ ->
(*    σ i <> v -> *)
    func_step σ (Some (Value i v))
                (Some (update σ i v))

  | func_input_unstable i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
(*    ~ (func_stable (update σ i v)) -> (* in a binary system, this is ok *)*)
    f σ = f (update σ i v) -> (* ok to update input in an unstable system if the output doesn't change *)
    func_step σ (Some (Value i v)) (Some (update σ i v))


  | func_err i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
    f σ <> f (update σ i v) -> (* if input updates in an unstable system causes output to change, go to error state*)
    func_step σ (Some (Value i v)) None

  | func_output v :
    ~ (func_stable σ) ->
    σ x = v ->
    func_step σ (Some (Value x v))
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
      absurd (event_in (space_input func_space) (Some (Value x (σ x)))).
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

  Inductive union_input_event (e : option (event name value)) :=
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
                     : option (event name value) ->
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
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  | Hide_Eq v τ:
    S ⊢ σ →{Some (Value x v)} τ ->
    hide_step σ None τ
  | Hide_Neq e τ :
    S ⊢ σ →{e} τ ->
    ~(event_in (singleton x) e) ->
    hide_step σ e τ
  .

  Definition hide : StateSpace :=
    {| space_input := hide_input
     ; space_output := hide_output
     ; space_internal := hide_internal
     ; space_step := hide_step
    |}.


End HideStateSpace.

Section Flop.

  (* the set and reset lines can be optional*)
  Variable set reset : name.
  Variable clk old_clk : name.
  Variable D Q : name.

  Context (disjoint : all_disjoint [set; reset;clk;old_clk;D;Q]).
  Let flop_input := from_list [set;reset;clk;D].
  Let flop_output := singleton Q.
  Let flop_internal := singleton old_clk.

(*
  Let Q_output σ :=
    match σ set with
    | Num 0 => Num 1
    | Num 1 => match σ reset with
               | Num 0 => Num 0
               | Num 1 => σ D
               | _     => X
               end
    | _     => X
    end.
*)
  Let Q_output σ :=
    if σ set =? Num 0 then Num 1
    else if σ reset =? Num 0 then Num 0
    else σ D.

  Let flop_stable σ :=
    σ Q = Q_output σ /\ σ clk = σ old_clk.
    

  Definition neg_value (v : value) : value :=
    match v with 
    | Num 0 => Num 1
    | Num 1 => Num 0
    | _ => v
    end.

  Inductive flop_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
    (* an input is allowed when, either (1) the flip-flop is stable aka any
    possible clock changes have been registered; or (2) when the input would not
    actually be observable on the outputs of the circuit. *)
  | Flop_input i v σ' :
    flop_stable σ \/ Q_output σ = Q_output (update σ i v) ->
    i ∈ flop_input ->
    σ' = update σ i v ->
    flop_step σ (Some (Value i v)) (Some σ')

    (* other inputs lead to the error state *)
  | Flop_input_err i v :
    ~ flop_stable σ ->
    Q_output σ <> Q_output (update σ i v) ->
    i ∈ flop_input ->
    flop_step σ (Some (Value i v)) None

    (* if the set line is high, raise Q *)
  | Flop_set σ' :
    σ set = Num 0 ->
    σ Q  <> Num 1 ->
    σ' = update σ Q (Num 1) ->
    flop_step σ (Some (Value Q (Num 1))) (Some σ')

    (* if the reset line is high, lower Q *)
  | Flop_reset σ' :
    σ set   = Num 1 ->
    σ reset = Num 0 ->
    σ Q    <> Num 0 ->
    σ' = update σ Q (Num 0) ->
    flop_step σ (Some (Value Q (Num 0))) (Some σ')

    (* if the clock has fallen (i.e. input changed and clk is no longer 1), do
    nothing to the outputs, but propogate thd change to the old_clk. *)
  | Flop_clk_fall σ' :
    σ clk <> Num 1 ->
    σ clk <> σ old_clk ->
    σ' = update σ old_clk (σ clk) ->
    flop_step σ None (Some σ')

    (* if the clock has risen (i.e. input changed and clk is now equal to 1),
    update Q and old_clk to their proper values. The result will now be stable *)
  | Flop_clk_rise v σ' :
    σ set      = Num 1 ->
    σ reset    = Num 1 ->
    σ clk      = Num 1 ->
    σ old_clk <> Num 1 ->

    v = σ D ->
    σ' = update (update σ Q v) old_clk (σ clk) ->

    flop_step σ (Some (Value Q v)) (Some σ')
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
      + absurd (σ Q = Num 1); auto.
        destruct Hstable as [Hstable _].
        rewrite Hstable; unfold Q_output.
        rewrite H; auto.
      + absurd (σ Q = Num 0); auto.
        destruct Hstable as [Hstable _].
        rewrite Hstable; unfold Q_output.
        rewrite H, H0; auto.
      + absurd (σ clk = σ old_clk); auto.
        destruct Hstable as [_ Hstable]; auto.
      + absurd (σ clk = σ old_clk); try congruence.
        destruct Hstable as [_ Hstable]; auto.
  Qed.

(* Not true as is; flop_stable would need to be more precise as to how we handle when set and reset lines are X *)
(*
  Lemma stable_implies_flop_stable : forall σ,
    stable flop σ ->
    flop_stable σ.
  Proof.
    intros σ Hstable. constructor.
    + unfold Q_output.
      destruct (σ set) as [ [ | [ | ?]] | ] eqn:Hset.
      { (* σ set = Num 0 *)
        compare (σ Q) (Num 1); auto.
        (* if these are not equal, we can take a step *)
        assert (Hstep : flop ⊢ σ →{Value Q (Num 1)} Some (update σ Q (Num 1))).
        { apply Flop_set; auto. }
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        (*contradict Hstable.*)
        inversion Hstable; subst.
        simpl in pf. unfold flop_input in pf. 
        decompose_set_structure.
      }
      destruct (σ reset) as [ [ | [ | ?]] | ] eqn:Hreset.
      { compare (σ Q) (Num 0); auto.
        assert (Hstep : flop ⊢ σ →{Value Q (Num 0)} Some (update σ Q (Num 0))).
        { apply Flop_reset; auto. }
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        (*contradict Hstable.*)
        inversion Hstable; subst.
        simpl in pf. unfold flop_input in pf. 
        decompose_set_structure.
      }
      { compare (σ Q) (σ D); auto.
        compare (σ clk) (σ old_clk)
        compare (σ clk) (Num 1).
        { set (σ' := update (update σ Q (σ D)) old_clk (σ clk)). 
          assert (Hstep : flop ⊢ σ →{Value Q (σ D)} Some σ').
          { apply Flop_clk_rise; auto.
        { apply Flop_reset; auto. }
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        (*contradict Hstable.*)
        inversion Hstable; subst.
        simpl in pf. unfold flop_input in pf. 
        decompose_set_structure.

        destruct (σ 
          

      ++ compare (σ reset) (Num 0).

         simpl in pf.
         decompose_set_structure.

         inversion pf; find_contradiction.
          
         inversion H14. clear H14. contradiction.
         inversion H14. clea

         


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
*)

End Flop.





Section Celem.

  Variable x1 x2 y : name.
  Let C_input := Couple _ x1 x2.
  Let C_output := singleton y.
  
  Let y_output σ := 
    match σ x1, σ x2 with
    | Num 0, Num 0 => Num 0
    | Num 1, Num 1 => Num 1
    | Num 0, Num 1 => σ y
    | Num 1, Num 0 => σ y
    | _, _ => X
    end.
  Definition C_elem : StateSpace := func_space C_input y y_output.

End Celem.

End state_space.

Arguments space_input {name}.
Arguments space_output {name}.
Arguments space_internal {name}.
Arguments space_domain {name}.
Arguments stable {name}.
Arguments Value {latch val}.
Definition Eps {latch val} : option (event latch val) := None.
Arguments func_space {name name_eq_dec}.
Arguments C_elem {name name_eq_dec}.
Arguments hide {name}.
Arguments flop {name name_eq_dec}.
Notation "C ⊢ σ →{ e } τ" := (space_step _ C σ e τ) (no associativity, at level 70).
 Notation "C ⊢ σ →*{ t } τ" := (space_steps _ C σ t τ) (no associativity, at level 70).
Notation "S1 ∥ S2" := (union _ S1 S2) (left associativity, at level 91).
