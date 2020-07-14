Require Import Base.
Require Import Circuit.
Require Import Monad.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Import EnsembleNotation.
Open Scope ensemble_scope.

(** * Define a state space for modeling asynchronous controllers, based loosely
on trace theory *)
Section state_space.


(** In this section we will use Ensembles heavily, and for the sake of
consistency we will assume there is an abstract type [name] that all the
Ensembles will quantify over. *)
Variable name : Set.
Context `{name_eq_dec : eq_dec name}.


(** An event is an element of an ensemble exactly if its underlying key is in the ensemble. *)
Inductive event_in {val} (I : Ensemble name) : option (event name val) -> Prop :=
| Event_In i (pf : i ∈ I) v : event_in I (Some (Event i v)).

Lemma not_event_in : forall {val} x (v : val) I, ~ event_in I (Some (Event x v)) -> x ∉ I.
Proof.
 intros. intro. apply H. constructor. auto.
Qed.

(** A state space consists of 

1. a set of input wires
2. a set of output wires
3. a set of internal wires (not visible in the events of the transition relation
4. a transition relation

The transition relation for a state space [C] holds of the triple ([σ],[e],[τ]),
also written [C ⊢ σ →{e} τ], if the state [σ] transitions to the state [τ] via
the event [e]. In this case, [e] may be either an actual event ([Some e']) or an
epsilon transition ([None]), and [τ] may be an actual state ([Some σ']) or the
error state ([None]).

The transition relation is a relation and not a function primarily because of
the presence of epsilon transitions.

*)
Record StateSpace :=
  { space_input : Ensemble name
  ; space_output : Ensemble name
  ; space_internal : Ensemble name
  ; space_step  : state name -> option (event name value) -> option (state name) -> Prop
  }.

(** The domain of a state space is the union of its input, output, and internal wires *)
Definition space_domain (S : StateSpace) := space_input S ∪ space_output S ∪ space_internal S.

Notation "C ⊢ σ →{ e } τ" := (space_step C σ e τ) (no associativity, at level 70).

(** The multi-step relation [C ⊢ σ →*{t} τ] is the closure of the step relation
over a trace of events. Note that epsilon transitions are not present in the
trace. *)
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

Definition traces_of (S : StateSpace) (σ0 : state name) : Ensemble (trace name value) :=
  fun t => exists σ, S ⊢ σ0 →*{t} Some σ.



(** A state space is well-formed if several properties hold. There may be other
properties that also hold not included here, such as the condition that each
input/output/internal set are individually all_disjoint, or that the transition
relation is only valid for events in [space_input S ∪ space_outupt S]. *)
Record well_formed (S : StateSpace) :=
  { (*space_dom : forall x, x ∈ space_domain S <-> in_fin_state σ x*)
    space_input_output : space_input S ⊥ space_output S
  ; space_input_internal : space_input S ⊥ space_internal S
  ; space_output_internal : space_output S ⊥ space_internal S
  ; wf_space : forall σ x v σ',
    S ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_input S ∪ space_output S
  ; wf_scoped : forall σ e σ',
    S ⊢ σ →{e} Some σ' ->
    forall x, (forall v, e <> Some (Event x v)) ->
              x ∉ space_internal S ->
              σ' x = σ x
  ; wf_update : forall σ x v σ',
    S ⊢ σ →{Some (Event x v)} Some σ' ->
    σ' x = v
  }.

(** A state [σ] in the state space [S] is stable if the only events that are
enabled in σ are input events. That is, S will not take any more steps except
those prompted by the environment. *)
Record stable (S : StateSpace) (σ : state name) :=
  { stable_wf : well_formed S
  ; stable_step : forall e τ, S ⊢ σ →{e} τ -> event_in (space_input S) e }.

Class stable_dec (S : StateSpace) :=
  { space_stable_dec : forall σ, stable S σ + ~ stable S σ }.



Section RelateTrace.

  Variable S1 S2 : StateSpace.
  Variable σ1_0 σ2_0 : state name.
  Hypothesis init_domain_consistent :
    forall x, x ∈ space_domain S1 ->
              x ∈ space_domain S2 ->
              σ1_0 x = σ2_0 x.

  (* input(SS1)=input(SS2)
     output(SS1)=output(SS2) *)
  Inductive relate_trace : state name -> trace name value -> state name -> Prop :=
  | relate_trace_nil :
    relate_trace σ1_0 t_empty σ2_0

  | relate_trace_left σ1 σ1' σ2 t :
    relate_trace σ1 t σ2 ->
    S1 ⊢ σ1 →{None} Some σ1' ->
    relate_trace σ1' t σ2

  | relate_trace_right σ1 σ2 σ2' t :
    relate_trace σ1 t σ2 ->
    S2 ⊢ σ2 →{None} Some σ2' ->
    relate_trace σ1 t σ2'

  | relate_trace_sync σ1 σ1' σ2 σ2' t e :
    relate_trace σ1 t σ2 ->
    S1 ⊢ σ1 →{Some e} Some σ1' ->
    S2 ⊢ σ2 →{Some e} Some σ2' ->
    relate_trace σ1' (t ▶ e) σ2'.

  Hypothesis internal_disjoint_1 : space_internal S1 ⊥ space_domain S2.
  Hypothesis internal_disjoint_2 : space_internal S2 ⊥ space_domain S1.

  Lemma relate_trace_domain : forall σ1 σ2 t,
    well_formed S1 ->
    well_formed S2 ->
    relate_trace σ1 t σ2 ->
    forall x, x ∈ space_domain S1 ->
              x ∈ space_domain S2 ->
              σ1 x = σ2 x.
  Proof.
    intros σ1 σ2 t Hwf1 Hwf2 Hrelate x Hx1 Hx2.
    assert (x ∉ space_internal S1).
    { (* if it were, it would be disjoint from dom(S2) *)
      intro Hx.
      find_contradiction.
    }
    assert (x ∉ space_internal S2).
    { (* if it were, it would be disjoint from dom(S1) *)
      intros Hx.
      find_contradiction.
    }

    induction Hrelate.
    * apply init_domain_consistent; auto.
    * assert (Hσ1' : σ1' x = σ1 x).
      { (* Since σ1 →{None} Some σ1', it must be the case that σ1 and σ1' only
        differ on internal wires *)
        eapply (wf_scoped _ Hwf1); eauto.
        { intros v; inversion 1. }
      }
      congruence.
    * assert (Hσ2' : σ2' x = σ2 x).
      { (* Since σ2 →{None} Some σ2', it must be the case that σ2 and σ2' only
        differ on internal wires *)
        eapply (wf_scoped _ Hwf2); eauto.
        { intros v; inversion 1. }
      }
      congruence.
    * destruct e as [y v].
      compare x y.
      + (* x = y *)
        assert (σ1' y = v).
        { (* another feature of well-formed step relations *) 
          eapply (wf_update _ Hwf1); eauto. 
        }
        assert (σ2' y = v).
        { (* another feature of well-formed step relations *)
          eapply (wf_update _ Hwf2); eauto.
        }
        congruence.
      + (* x <> y *)
        assert (σ1' x = σ1 x).
        { (* σ1 and σ1' must only vary on interal wires and y *) 
          eapply (wf_scoped _ Hwf1); eauto.
          intros v'; inversion 1; subst; find_contradiction.
        }
        assert (σ2' x = σ2 x).
        { (* σ2 and σ2' must only vary on interal wires and y *)
          eapply (wf_scoped _ Hwf2); eauto.
          intros v'; inversion 1; subst; find_contradiction.
        }
        congruence.
  Qed.

  Definition relate_trace_step_lemma := forall σ1 σ1' σ2 e t,
    S1 ⊢ σ1 →{Some e} Some σ1' ->
    relate_trace σ1 t σ2 ->
    exists σ2', S2 ⊢ σ2 →{Some e} Some σ2'.


  Theorem relate_trace_subset_lemma :
    relate_trace_step_lemma ->
    forall (σ1 : state name) t,
      S1 ⊢ σ1_0 →*{t} Some σ1 ->
      exists σ2, relate_trace σ1 t σ2.
  Proof.
    intros Hlemma σ1 t Hstep.
    remember (Some σ1) as τ1 eqn:Heqτ.
      generalize dependent σ1.
    induction Hstep as [ | | ]; intros σ1 Heqτ; subst.
    * inversion Heqτ; subst. rewrite <- H0.
      exists σ2_0. constructor.
    * unfold relate_trace_step_lemma in Hlemma.
      rename σ' into σ1'.
      destruct (IHHstep σ1' eq_refl) as [σ2' IH].
      specialize (Hlemma _ _ _ _ _ H IH).
      destruct Hlemma as [σ2 Hstep2].
      exists σ2.
      eapply relate_trace_sync; eauto.
    * rename σ' into σ1'.
      destruct (IHHstep σ1' eq_refl) as [σ2' IH].
      exists σ2'.
      eapply relate_trace_left; eauto.
  Qed.

  Lemma relate_trace_project_left : forall σ1 t σ2,
      relate_trace σ1 t σ2 ->
      S1 ⊢ σ1_0 →*{t} Some σ1.
  Proof.
    intros σ1 t σ2 Hrelate.
    induction Hrelate.
    * constructor.
    * eapply stepsEps; eauto.
    * apply IHHrelate.
    * eapply steps1; eauto.
  Qed.

  Lemma relate_trace_project_right : forall σ1 t σ2,
      relate_trace σ1 t σ2 ->
      S2 ⊢ σ2_0 →*{t} Some σ2.
  Proof.
    intros σ1 t σ2 Hrelate.
    induction Hrelate.
    * constructor.
    * apply IHHrelate.
    * eapply stepsEps; eauto.
    * eapply steps1; eauto.
  Qed.


  Theorem relate_trace_step_subset :
    relate_trace_step_lemma ->
    traces_of S1 σ1_0 ⊆ traces_of S2 σ2_0.
  Proof.
    intros Hlemma t H1.
    destruct H1 as [σ1 H1].
    destruct (relate_trace_subset_lemma Hlemma _ _ H1) as [σ2 Hrelate].
    exists σ2.
    eapply relate_trace_project_right; eauto.
  Qed.

End RelateTrace.

(** * Define a circuit state space from a combinational logic function *)
Section FuncStateSpace.

  Variable I : Ensemble name.
  Variable x : name.
  Variable f : state name -> value.
  Hypothesis x_notin_I : ~ (x ∈ I).

  Let dom := I ∪ singleton x ∪ ∅.
  Hint Unfold dom.
  Lemma x_in_dom : x ∈ dom. unfold dom. auto with sets. Qed.
  Lemma I_subset_dom : forall i, i ∈ I -> i ∈ dom.
  Proof. unfold dom. auto with sets. Qed.

  (** The definition of func_step requires a notion of stability of the state
  space, which in this case corresponds to [x] being equal to the value of
  [f(I)] in [σ]. Below we will prove that this condition exactly correlates with
  the stability of the state space. *)
  Let func_stable (σ : state name) := σ x = f σ.
  Hint Unfold func_stable.
  
  Inductive func_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  | func_input_stable i (pf_i : i ∈ I) v :
    func_stable σ ->
(*    σ i <> v -> *) (* Question: what happens if an event occurs that doesn't change the value of the variable? Is it allowed? Is it a no-op? *)
    func_step σ (Some (Event i v))
                (Some (update σ i v))

  | func_input_unstable i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
(*    ~ (func_stable (update σ i v)) -> (* in a binary system, this is ok *)*)
    f σ = f (update σ i v) -> (* ok to update input in an unstable system if the output doesn't change *)
    func_step σ (Some (Event i v)) (Some (update σ i v))


  (* if input updates in an unstable system causes output to change, go to error state*)
  | func_err i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
    f σ <> f (update σ i v) -> 
    func_step σ (Some (Event i v)) None

  | func_output v :
    ~ (func_stable σ) ->
    v = f σ ->
    func_step σ (Some (Event x v))
                (Some (update σ x v))
  .
    
  Program Definition func_space : StateSpace :=
  {| space_input := I
   ; space_output := singleton x
   ; space_internal := ∅
   ; space_step := func_step
   |}.

  Lemma func_wf : well_formed func_space.
  Proof.
    split.
    + constructor.
      simpl.
      intros y Hy.
      decompose_set_structure.
    + constructor.
      simpl.
      intros y Hy.
      decompose_set_structure.
    + constructor.
      simpl.
      intros y Hy.
      decompose_set_structure.
    + intros σ y v σ' Hstep.
      inversion Hstep; try (subst; solve_set).
      rewrite <- H. simpl. solve_set.

    + admit (*intros ? z ? ? Hstep y y_neq_z y_not_internal.
      inversion Hstep; try subst; unfold update; reduce_eqb; auto. *)
    + admit (*TODO*).
  Admitted.

  (** ** Decidability of stability for function spaces *)

  (** This just depends on the enumerability of I *)
(*  Hypothesis space_wf_decidable : forall σ, well_formed func_space σ + ~(well_formed func_space σ).*)

  Lemma func_stable_equiv : forall σ, 
        func_stable σ <-> stable func_space σ.
  Proof.
    intros σ. split; intros Hstable.
    * (*destruct Hstable as [H_x_stable H_I_stable].*)
      split; [apply func_wf | ].
      intros e τ Hstep.
      inversion Hstep; subst.
      + constructor. auto.
      + contradiction.
      + contradiction.
      + contradiction.
    * compare (σ x) (f σ); auto.

      inversion Hstable.
      assert (Hstep : func_space ⊢ σ →{Some (Event x (f σ))} Some (update σ x (f σ))).
      { apply func_output; auto. }
      specialize (stable_step0 _ _ Hstep).
      inversion stable_step0; subst.
      simpl in *. find_contradiction.
  Qed.


  Instance func_stable_dec : stable_dec func_space.
  Proof.
    split.
    intros σ.
    {
    compare (f σ) (σ x).
    * left. apply func_stable_equiv; auto.

    * right. intros Hstable. 
      apply func_stable_equiv in Hstable; auto.
    }
  Defined.

End FuncStateSpace.

(** * Composition of two state spaces, written S1 ∥ S2. *)
Section UnionStateSpace.

  Variable S1 S2 : StateSpace.
  Hypothesis output_dec1 : in_dec (space_output S1).
  Hypothesis output_dec2 : in_dec (space_output S2).

  (** The union is only defined for two spaces that are appropriately disjoint. The spaces may share input wires with the others' output wires, however. *)

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


  Definition union_stable (σ : state name) := 
    stable S1 σ /\ stable S2 σ.


  Lemma wf_union : 
    well_formed S1 ->
    well_formed S2 ->
    well_formed union.
  Proof.
  intros [disjoint_in_out1 disjoint_in_int1 disjoint_out_int1 wf1]
         [disjoint_in_out2 disjoint_in_int2 disjoint_out_int2 wf2].
  constructor;
    simpl in *;
      unfold union_input, union_output, union_internal in *.
    
  - constructor; intros x Hintersect; decompose_set_structure.
  - constructor; intros x Hintersect; decompose_set_structure.
    { destruct wires1_disjoint as [Hdisjoint].
      apply (Hdisjoint x). unfold space_domain. solve_set.
    }
    { destruct wires2_disjoint as [Hdisjoint].
      apply (Hdisjoint x). unfold space_domain. solve_set.
    } 
  - constructor; intros x Hintersect; decompose_set_structure.
    { destruct wires1_disjoint as [Hdisjoint].
      apply (Hdisjoint x). unfold space_domain. solve_set.
    }
    { destruct wires2_disjoint as [Hdisjoint].
      apply (Hdisjoint x). unfold space_domain. solve_set.
    } 
  - intros ? ? ? ? Hstep.
    simpl. unfold union_input, union_output.
    inversion Hstep; subst.
    * apply wf1 in H2.
      simpl. unfold union_input, union_output.
      decompose_set_structure.
      { assert (x ∉ space_output S2).
        { intro. apply H1. constructor; auto. unfold space_domain. solve_set. }
        solve_set.
      }
    * apply wf2 in H2.
      decompose_set_structure.
      assert (x ∉ space_output S1).
      { intro. apply H1. constructor; auto. unfold space_domain. solve_set. }
      solve_set.
    * inversion H1.
      + inversion H4; subst. inversion H5; subst.
        solve_set.
      + inversion H4; subst. inversion H5; subst.
        solve_set.
      + inversion H4; subst. inversion H5; subst.
        assert (x ∉ space_output S1).
        { intro. inversion disjoint_in_out1 as [wf].
          apply (wf x).
          solve_set.
        }
        solve_set.

  - intros ? ? ? Hstep x Hx x_not_internal.
    decompose_set_structure.
    inversion Hstep; subst.
    + specialize (wf_scoped0 _ _ _ H4).
      apply wf_scoped0; auto.
    + specialize (wf_scoped1 _ _ _ H4).
      apply wf_scoped1; auto.
    + specialize (wf_scoped1 _ _ _ H5).
      apply wf_scoped1; auto.

  - admit (*TODO*).
  Admitted.


  (** Although this direction ([union_stable_implies]) is true, I don't know if the other direction
  actually is true, e.g. if [S1 ∥ S2] is stable, then both [S1] and [S2] are
  stable. If it is true, I may have to make some subtle arguments about the fact
  that certain (e.g. input events) are always enabled in a state. *)
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

Notation "S1 ∥ S2" := (union S1 S2) (left associativity, at level 91).

Section UnionStateSpaceRefinement.

  Variable S1 S2 S1' S2' : StateSpace.
  Variable σ0 σ0' : state name.

  Theorem union_refinement : 
    traces_of S1 σ0 ⊆ traces_of S1' σ0' ->
    traces_of S2 σ0 ⊆ traces_of S2' σ0' ->
    traces_of (S1 ∥ S2) σ0 ⊆ traces_of (S1' ∥ S2') σ0'.
  Proof.
    intros H1 H2.
    apply relate_trace_step_subset.
    { admit (* need to assert this is true *). }
    unfold relate_trace_step_lemma.
    intros σ σ' σT e t Hstep1 Hrelate.
    inversion Hrelate; subst.
    * (* σ0' = σT ???*)
  Abort.
      
End UnionStateSpaceRefinement.


(** * Move a name from the output of a state space to the input of a state space. *)
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
    S ⊢ σ →{Some (Event x v)} τ ->
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


  Lemma hide_wf : well_formed S -> well_formed hide.
  Proof.
    intros [[wfIO] [wfII] [wfOI] wfStep].
    constructor; simpl; unfold hide_input, hide_output, hide_internal.
    - constructor. intros y Hy.
      decompose_set_structure.
      apply (wfIO y). solve_set.
    - constructor. intros y Hy.
      decompose_set_structure.
      { apply (wfII y). solve_set. }
      { apply (wfIO x). solve_set. }
    - constructor. intros y Hy.
      decompose_set_structure.
      { apply (wfOI y). solve_set. }
    - intros σ y v σ' Hstep.
      inversion Hstep; subst.
      assert (x <> y).
      { intro. apply H0. constructor. subst. auto with sets. }
      specialize (wfStep _ _ _ _ H).
      decompose_set_structure.
      solve_set.
    - intros ? ? ? Hstep y Hy y_not_internal.
      decompose_set_structure.
      inversion Hstep; subst.
      + specialize (wf_scoped0 _ _ _ H1).
        apply wf_scoped0; auto.
        intro. inversion 1; subst. find_contradiction.
      + specialize (wf_scoped0 _ _ _ H1).
        apply wf_scoped0; auto.
    - admit (*TODO*).
  Admitted.
End HideStateSpace.


(** * A state space modeling a D-flip-flop with set and reset lines. *)
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
    | Bit0  => Bit1
    | Bit1  => Bit0
    | _     => v
    end.
  Definition inc_value (v : value) : value :=
    match v with
    | Num n => Num (n+1)
    | _     => v
    end.
  Definition dec_value (v : value) : value :=
    match v with
    | Num n => Num (n-1)
    | _     => v
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
    flop_step σ (Some (Event i v)) (Some σ')

    (* other inputs lead to the error state *)
  | Flop_input_err i v :
    ~ flop_stable σ ->
    Q_output σ <> Q_output (update σ i v) ->
    i ∈ flop_input ->
    flop_step σ (Some (Event i v)) None

    (* if the set line is high, raise Q *)
  | Flop_set σ' :
    σ set = Num 0 ->
    σ Q  <> Num 1 ->
    σ' = update σ Q (Num 1) ->
    flop_step σ (Some (Event Q (Num 1))) (Some σ')

    (* if the reset line is high, lower Q *)
  | Flop_reset σ' :
    σ set   = Num 1 ->
    σ reset = Num 0 ->
    σ Q    <> Num 0 ->
    σ' = update σ Q (Num 0) ->
    flop_step σ (Some (Event Q (Num 0))) (Some σ')

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

    flop_step σ (Some (Event Q v)) (Some σ')
  .

  Definition flop : StateSpace :=
    {| space_input := flop_input
     ; space_output := flop_output
     ; space_internal := flop_internal
     ; space_step := flop_step
    |}.


  Lemma flop_wf : well_formed flop.
  Proof.
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
      + intros ? ? ? ? Hstep.
        inversion Hstep; try subst; try solve_set.
      + intros ? ? ? Hstep y Hy H_not_internal.
        decompose_set_structure.
        inversion Hstep; try subst.
        ++ unfold update. specialize (Hy v).
           assert (i <> y). { inversion 1; subst. apply Hy. auto. }
           reduce_eqb; auto.
           
        ++ unfold update.
           assert (y <> Q). { specialize (Hy (Num 1)).
                              inversion 1; subst. apply Hy. auto. }
           reduce_eqb. auto.
        ++ unfold update.
           compare_next; auto.
           rewrite <- Heq in Hy.
           specialize (Hy (Num 0)).
           contradict Hy; auto.
        ++ unfold update.
           compare_next; auto.
        ++ unfold update.
           compare_next; auto.
           compare_next; auto.
           specialize (Hy (σ D)).
           contradict Hy; rewrite <- Heq; auto.

    + admit (* TODO *).
  Admitted.

  Lemma flop_stable_implies_stable : forall σ, 
    flop_stable σ -> stable flop σ.
  Proof.
    intros σ Hstable.
    constructor.
    * (* well-formed *)
      apply flop_wf.
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

(** The reverse is not true as is; flop_stable would need to be more precise as to how we handle
when set and reset lines are X:

  Lemma stable_implies_flop_stable : forall σ,
    stable flop σ ->
    flop_stable σ.
*)


End Flop.

(** * A state space modeling a C element. *)

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
Definition Eps {latch val} : option (event latch val) := None.
Arguments func_space {name name_eq_dec}.
Arguments C_elem {name name_eq_dec}.
Arguments hide {name}.
Arguments flop {name name_eq_dec}.
Notation "C ⊢ σ →{ e } τ" := (space_step _ C σ e τ) (no associativity, at level 70).
 Notation "C ⊢ σ →*{ t } τ" := (space_steps _ C σ t τ) (no associativity, at level 70).
Notation "S1 ∥ S2" := (union _ S1 S2) (left associativity, at level 91).


Section MG_to_SS.

  Set Implicit Arguments.
  (** ** Convert a marked graph to a state space *)
  Variable name : Set.
  Context `{name_dec : eq_dec name}.

  Variable transition : Set.
  Context `{transition_dec : eq_dec transition}.
  Variable MG : marked_graph transition.

  Import EnsembleNotation.
  Open Scope ensemble_scope.


  Class MG_naming_scheme :=
  { transition_name : transition -> name
  ; place_name : forall {t1 t2} (p : place MG t1 t2), name

  ;  name_is_place_dec : forall (x : name),
     {t1 : transition & {t2 : transition & {p : place MG t1 t2 & x = place_name p}}}
   + {forall t1 t2 (p : place MG t1 t2), x <> place_name p}


  ; transition_update_value : transition -> value -> value

  ; input_transition : Ensemble transition

  ; transition_place_name_disjoint : forall t {t1 t2} (p : place MG t1 t2),
    transition_name t <> place_name p
  }.
  Context `{MG_scheme : MG_naming_scheme}.

  Definition places_set : Ensemble name :=
    fun x => exists t1 t2 (p : place MG t1 t2), x = place_name p.
  Definition state_to_marking (σ : state name) : marking MG :=
    fun t1 t2 p => val_to_nat (σ (place_name p)).

  Definition fire_in_state (t : transition) (σ : state name) : state name :=
    fun x =>
    match name_is_place_dec x with
    (* if x is not a place, do nothing *)
    | inright _ => σ x
    | inleft (existT _ tin (existT _ tout (existT _ p x_is_p))) =>
      (* corner case: do nothing *)
      if tin =? tout then σ x
      (* if x is a place leading into t, increment the value *)
      else if t =? tout then dec_value (σ x)
      (* if x is a place leading out of t, decrement the value *)
      else if t =? tin then inc_value (σ x)
      (* otherwise do nothing *)
      else σ x
    end.

  (* NOTE: this may not be the right relation for all marked graphs--get example from Peter *)
  Inductive MG_SS_step
    : state name -> option (event name value) -> option (state name) -> Prop :=

  | transition_enabled σ σ' x v (t : transition) :
    x = transition_name t ->
    is_enabled MG t (state_to_marking σ) ->
    v = transition_update_value t (σ x) ->
    σ' = update (fire_in_state t σ) x v ->
    MG_SS_step σ (Some (Event x v)) (Some σ')

  | input_not_enabled σ x v t :
    x = transition_name t ->
    t ∈ input_transition ->
    ~ is_enabled MG t (state_to_marking σ) ->
   MG_SS_step σ (Some (Event x v)) None
  .

  Let output_transition : Ensemble transition :=
    fun t => t ∉ input_transition.
  Definition MG_SS : StateSpace name :=
  {| space_input := fmap transition_name input_transition
   ; space_output := fmap transition_name output_transition
   ; space_internal := places_set
   ; space_step := MG_SS_step
   |}.

Arguments well_formed {name}.
  Lemma wf_MG_SS : well_formed MG_SS.
  Proof.
    split.
    * simpl. constructor.
      intros x Hx. decompose_set_structure.
      inversion H; subst. destruct H1.
      inversion H0; subst. destruct H3.
      admit (* need more assumptions about naming scheme *).
    * simpl. constructor.
      intros x Hx. decompose_set_structure.
      inversion H; subst. destruct H1.
      inversion H0; subst. destruct H3.
      destruct H2 as [p H2].
      set (Hdisjoint := transition_place_name_disjoint x0 p).
      find_contradiction.
    * simpl. constructor.
      intros x Hx. decompose_set_structure.
      inversion H; subst. destruct H1.
      inversion H0; subst. destruct H3.
      destruct H2 as [p H2].
      set (Hdisjoint := transition_place_name_disjoint x0 p).
      find_contradiction.
    * admit.
    * admit.
  Abort.

  Unset Implicit Arguments.
End MG_to_SS.

Section Structural_SS.

  Set Implicit Arguments.
  (** ** Convert a marked graph to a state space *)
  Variable name : Set.
  Context `{name_dec : eq_dec name}.


  Inductive structural_state_space :=
  | Prim : StateSpace name -> structural_state_space
  | Union : structural_state_space -> structural_state_space -> structural_state_space
  | Hide  : name -> structural_state_space -> structural_state_space
  .
  Fixpoint interp_S (S : structural_state_space) : StateSpace name :=
    match S with
    | Prim S0 => S0
    | Union S1 S2 => interp_S S1 ∥ interp_S S2
    | Hide x S'    => hide x (interp_S S')
    end.

  

  Ltac reflect_S_constr S :=
  match S with
  | hide ?x ?S' => let SSS' := reflect_S_constr S' in
                   constr:(Hide x SSS')
  | ?S1 ∥ ?S2   => let SS1 := reflect_S_constr S1 in
                   let SS2 := reflect_S_constr S2 in
                   constr:(Union SS1 SS2)
  | _           => constr:(Prim S)
  end.
  Ltac reflect_S S := let S' := reflect_S_constr S in
                      replace S with (interp_S S') by reflexivity.

  Variable x : name.
  Definition S : StateSpace name := C_elem x x x.
  Lemma foo : (C_elem x x x ∥ func_space (singleton x) x (fun _ => X)) = C_elem x x x.
  reflect_S (C_elem x x x ∥ func_space (singleton x) x (fun _ => X)).
  Abort.

End Structural_SS.
