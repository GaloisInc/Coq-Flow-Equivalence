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
              x ∈ space_input S ∪ space_output S ->
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
        { unfold space_domain in *. decompose_set_structure; solve_set. }
      }
      congruence.
    * assert (Hσ2' : σ2' x = σ2 x).
      { (* Since σ2 →{None} Some σ2', it must be the case that σ2 and σ2' only
        differ on internal wires *)
        eapply (wf_scoped _ Hwf2); eauto.
        { intros v; inversion 1. }
        { unfold space_domain in *. decompose_set_structure; solve_set. }
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
          { intros v'; inversion 1; subst; find_contradiction. }
          { unfold space_domain in *. decompose_set_structure; solve_set. }
        }
        assert (σ2' x = σ2 x).
        { (* σ2 and σ2' must only vary on interal wires and y *)
          eapply (wf_scoped _ Hwf2); eauto.
          { intros v'; inversion 1; subst; find_contradiction. }
          { unfold space_domain in *. decompose_set_structure; solve_set. }
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

  Definition state_equiv_on (X : Ensemble name) (τ1 τ2 : option (state name)) :=
      match τ1, τ2 with
      | Some σ1, Some σ2 => forall x, x ∈ X -> σ1 x = σ2 x
      | None, None => True
      | _, _ => False
      end.

  
  Inductive func_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  | func_input_stable i (pf_i : i ∈ I) v σ' :
    func_stable σ ->
(*    σ i <> v -> *) (* Question: what happens if an event occurs that doesn't change the value of the variable? Is it allowed? Is it a no-op? *)
    state_equiv_on (I ∪ singleton x) (Some σ') (Some (update σ i v)) ->
    func_step σ (Some (Event i v))
                (Some σ')

  | func_input_unstable i (pf_i : i ∈ I) v σ' :
    ~ (func_stable σ) ->
(*    ~ (func_stable (update σ i v)) -> (* in a binary system, this is ok *)*)
    f σ = f (update σ i v) -> (* ok to update input in an unstable system if the output doesn't change *)
    state_equiv_on (I ∪ singleton x) (Some σ') (Some (update σ i v)) ->
    func_step σ (Some (Event i v)) (Some σ')


  (* if input updates in an unstable system causes output to change, go to error state*)
  | func_err i (pf_i : i ∈ I) v :
    ~ (func_stable σ) ->
    f σ <> f (update σ i v) -> 
    func_step σ (Some (Event i v)) None

  | func_output v σ' :
    ~ (func_stable σ) ->
    v = f σ ->
    state_equiv_on (I ∪ singleton x) (Some σ') (Some (update σ x v)) ->
    func_step σ (Some (Event x v))
                (Some σ')
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
      rewrite <- H. simpl. solve_set

    + intros ? ? ? Hstep y y_neq_z y_not_internal.
    + intros ? ? ? Hstep y y_neq_z y_not_internal.

      inversion Hstep; try subst; unfold update in *.
      ++ rewrite H2; [ | solve_set].
         assert (i <> y).
         { intro. apply (y_neq_z v). subst; auto. }
         reduce_eqb; auto.
      ++ rewrite H3; [ | solve_set].
         assert (i <> y).
         { intro. apply (y_neq_z v). subst; auto. }
         reduce_eqb; auto.
      ++ rewrite H3; [ | solve_set].
         compare x y; auto.
         { (* x = y *)
            rewrite Heq in y_neq_z.
            specialize (y_neq_z (f σ) eq_refl).
            find_contradiction.
         }

    + intros ? y ? ? Hstep.
      inversion Hstep; try subst; unfold update in *;
        [rewrite H3 | rewrite H4 | rewrite H4];
        try (simpl; reduce_eqb; simpl; auto; fail);
        try solve_set.
      
  Qed.

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
      { apply func_output; auto.
        intros y Hy. unfold update. compare_next; auto. }
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


  Inductive union_state : option (state name) -> option (state name) -> option (state name) -> Prop :=
  | union_None1 τ : union_state None τ None
  | union_None2 τ : union_state τ None None
  | union_Some : forall σ1 σ2 σ,
    (forall y, y ∉ space_internal S2 -> σ y = σ1 y) ->
    (forall y, y ∉ space_internal S1 -> σ y = σ2 y) ->
    union_state (Some σ1) (Some σ2) (Some σ)
  .

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
    decompose_set_structure;
      inversion Hstep; subst;
      try match goal with
      | [ H : ?x ∈ space_input ?S
        , Hstep : ?S ⊢ ?σ →{e} Some ?σ'
        , Hscoped : forall σ e σ', ?S ⊢ σ →{e} Some σ' ->
                    forall x, (forall v, e <> Some (Event x v)) ->
                    x ∈ space_input ?S ∪ space_output ?S -> σ' x = σ x
        |- ?σ' ?x = ?σ ?x ] => apply (Hscoped _ _ _ Hstep); [ auto | solve_set ]; fail
      | [ H : ?x ∈ space_output ?S
        , Hstep : ?S ⊢ ?σ →{e} Some ?σ'
        , Hscoped : forall σ e σ', ?S ⊢ σ →{e} Some σ' ->
                    forall x, (forall v, e <> Some (Event x v)) ->
                    x ∈ space_input ?S ∪ space_output ?S -> σ' x = σ x
        |- ?σ' ?x = ?σ ?x ] => apply (Hscoped _ _ _ Hstep); [ auto | solve_set ]; fail

      | [ H : ?x ∈ space_input ?S
        , Hstep : state_equiv_on (space_domain ?S) (Some ?σ) (Some ?σ')
        |- ?σ' x = σ x ] => rewrite Hstep; unfold space_domain; solve_set; fail
      | [ H : ?x ∈ space_output ?S
        , Hstep : state_equiv_on (space_domain ?S) (Some ?σ) (Some ?σ')
        |- ?σ' x = σ x ] => rewrite Hstep; unfold space_domain; solve_set; fail

      end.

  - intros ? ? ? ? Hstep.
    inversion Hstep; subst.
    + eapply wf_update0; eauto.
    + eapply wf_update1; eauto.
    + erewrite wf_update0; eauto.
  Qed.


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
      decompose_set_structure;
      inversion Hstep; subst;
      repeat match goal with
      | [ H : ?x ∈ space_input ?S
        , Hstep : ?S ⊢ ?σ →{?e} Some ?σ'
        , Hscoped : forall σ e σ', ?S ⊢ σ →{e} Some σ' ->
                    forall x, (forall v, e <> Some (Event x v)) ->
                    x ∈ space_input ?S ∪ space_output ?S -> σ' x = σ x
        |- ?σ' ?x = ?σ ?x ] => apply (Hscoped _ _ _ Hstep);
           [ auto; intro; inversion 1; subst; find_contradiction | solve_set ]
      | [ H : ?x ∈ space_output ?S
        , Hstep : ?S ⊢ ?σ →{?e} Some ?σ'
        , Hscoped : forall σ e σ', ?S ⊢ σ →{e} Some σ' ->
                    forall x, (forall v, e <> Some (Event x v)) ->
                    x ∈ space_input ?S ∪ space_output ?S -> σ' x = σ x
        |- ?σ' ?x = ?σ ?x ] => apply (Hscoped _ _ _ Hstep);
           [ auto; intro; inversion 1; subst; find_contradiction | solve_set ]

      | [ Hinput : ?x ∈ ?A
        , Houtput : ?x ∈ ?B
        , Hwf : forall x, x ∉ ?A ∩ ?B |- _ ] => contradiction (Hwf x); solve_set

      end.


    - intros ? ? ? ? Hstep.
      inversion Hstep; subst; auto.
      eapply wf_update0; eauto.
  Qed.
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
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some σ') (Some (update σ i v)) ->
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
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some σ') (Some (update σ Q (Num 1))) ->
    flop_step σ (Some (Event Q (Num 1))) (Some σ')

    (* if the reset line is high, lower Q *)
  | Flop_reset σ' :
    σ set   = Num 1 ->
    σ reset = Num 0 ->
    σ Q    <> Num 0 ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some σ') (Some (update σ Q (Num 0))) ->
    flop_step σ (Some (Event Q (Num 0))) (Some σ')

    (* if the clock has fallen (i.e. input changed and clk is no longer 1), do
    nothing to the outputs, but propogate thd change to the old_clk. *)
  | Flop_clk_fall σ' :
    σ clk <> Num 1 ->
    σ clk <> σ old_clk ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some σ')
                                                           (Some (update σ old_clk (σ clk))) ->
    flop_step σ None (Some σ')

    (* if the clock has risen (i.e. input changed and clk is now equal to 1),
    update Q and old_clk to their proper values. The result will now be stable *)
  | Flop_clk_rise v σ' :
    σ set      = Num 1 ->
    σ reset    = Num 1 ->
    σ clk      = Num 1 ->
    σ old_clk <> Num 1 ->

    v = σ D ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk])
                   (Some σ')
                   (Some (update (update σ Q v) old_clk (σ clk))) ->

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
        decompose_set_structure;
        inversion Hstep; try subst;
        repeat match goal with
        | [ H : forall v0, Some (Event ?x ?v) <> Some (Event ?x v0)
          |- _ ] => contradiction (H v); auto
        | [ H : state_equiv_on _ (Some ?σ') _
          |- ?σ' _ = _ ] =>
          rewrite H; [ unfold update; repeat compare_next; auto | solve_set]
        end.
    + intros ? ? ? ? Hstep.
      inversion Hstep; try subst; unfold update; reduce_eqb; auto.
      ++ rewrite H4; [ | unfold flop_input in *; decompose_set_structure; solve_set].
          unfold update. reduce_eqb; auto.
      ++ rewrite H4; [ | solve_set]. unfold update. reduce_eqb; auto.
      ++ rewrite H5; [ | solve_set]. unfold update.
         repeat my_subst. reduce_eqb; auto.
      ++ rewrite H7; [ | solve_set]. unfold update.
         repeat my_subst. compare_next; auto.
  Qed.

  Lemma flop_output_is_bit : forall σ v σ',
    val_is_bit (σ D) ->
    flop ⊢ σ →{Some (Event Q v)} Some σ' ->
    val_is_bit v.
  Proof.
    intros ? ? ? ? Hstep.
    inversion Hstep as [? ? ? ? Hi | | | | |]; subst;
      auto; try constructor.
    * contradict Hi. unfold flop_input. solve_set.
  Qed.


  Lemma flop_old_clk : forall σ x v σ',
    val_is_bit v ->
    flop ⊢ σ →{Some (Event x v)} Some σ' ->
    val_is_bit (σ clk) ->
    val_is_bit (σ old_clk) ->
    val_is_bit (σ' old_clk).
  Proof.
    intros ? ? ? ? ? Hstep ? ?.
    inversion Hstep as [? ? ? ? Hi | | | | |]; try subst; unfold update;
      try match goal with
      | [ H : state_equiv_on _ (Some ?σ') _ |- _ ] =>
        rewrite H; [try unfold update; repeat (compare_next; auto) | solve_set]
      end.
  Qed.
    

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

(** * A state space modeling a delay until a guard holds over some sensitive input wires *)
(** Relative timing constraint *)
Section Delay.

  Variable x y : name.
  Variable sensitivities : Ensemble name.
  (** The guard should only depend on the variables in the sensitivites set *)
  Variable guard : state name -> bool.

  Inductive delay_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  | delay_input_unstable : forall v, σ x <> v -> σ y <> σ x ->
                                     delay_step σ (Some (Event x v)) None
  | delay_input_stable : forall v, σ y = σ x -> delay_step σ (Some (Event x v)) (Some (update σ x v))
  (* output only transitions when the guard is true *)
  | delay_output σ' : σ y <> σ x ->
                   guard σ = true ->
                   state_equiv_on (sensitivities ∪ from_list [x;y]) (Some σ')
                                                                    (Some (update σ y (σ x))) ->
                   delay_step σ (Some (Event y (σ x))) (Some σ')
  .

  Definition delay : StateSpace :=
    {| space_input := singleton x ∪ sensitivities
     ; space_output := singleton y
     ; space_internal := ∅
     ; space_step := delay_step
    |}.


    
  Lemma delay_wf : well_formed delay.
  Admitted.

End Delay.

Section DelaySpace.
  Variable S : StateSpace.
  Variable sensitivities : Ensemble name.
  (** The guard should only depend on the variables in the sensitivites set *)
  Variable guard : state name -> Prop.


  Inductive delay_space_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  (* input steps are always valid *)
  | delay_space_input : forall x v τ,
    S ⊢ σ →{Some (Event x v)} τ ->
    state_equiv_on sensitivities (Some σ) τ ->
    x ∈ space_input S ->
    delay_space_step σ (Some (Event x v)) τ

  (* epsilon steps are always valid *)
  | delay_space_internal : forall τ,
    S ⊢ σ →{None} τ ->
    state_equiv_on sensitivities (Some σ) τ ->
    delay_space_step σ None τ

  (* output steps can only happen if the guard is true *)
  | delay_space_output : forall x v τ,
    guard σ ->
    S ⊢ σ →{Some (Event x v)} τ ->
    x ∈ space_output S ->
    state_equiv_on sensitivities (Some σ) τ ->
    delay_space_step σ (Some (Event x v)) τ
  .

  Definition delay_space : StateSpace :=
    {| space_input := space_input S ∪ sensitivities
     ; space_output := space_output S
     ; space_internal := space_internal S
     ; space_step := delay_space_step
    |}.

  Lemma delay_space_wf : well_formed delay_space.
  Admitted.

  Lemma delay_space_inversion : forall σ e τ,
    delay_space ⊢ σ →{e} τ ->
    S ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hstep.
    inversion Hstep; subst; auto.
  Qed.


End DelaySpace.

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
Arguments well_formed {name}.
Arguments delay {name name_eq_dec}.
Arguments delay_space {name}.
Arguments state_equiv_on {name}.

Notation "C ⊢ σ →{ e } τ" := (space_step _ C σ e τ) (no associativity, at level 70).
 Notation "C ⊢ σ →*{ t } τ" := (space_steps _ C σ t τ) (no associativity, at level 70).
Notation "S1 ∥ S2" := (union _ S1 S2) (left associativity, at level 91).

Module Type NameType.
  Parameter name : Set.
  Parameter name_eq_dec : eq_dec name.
  Existing Instance name_eq_dec.
  Export EnsembleNotation.
  Open Scope ensemble_scope.
End NameType.

Module StateSpaceTactics (Export name : NameType).
  Lemma union_inversion_left : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S1 ->
    S1 ⊢ σ →{Some (Event x v)} Some σ'.
  Proof.
    intros ? ? ? ? ? ? Hstep Hdom.
    inversion Hstep; subst; auto.
    (* the only remaining case is when x ∉ dom(S1), a contradiction *)
    { absurd (event_in _ (space_domain S1) (Some (Event x v))); auto.
      constructor; auto.
    }
  Qed.

  Lemma union_inversion_right : forall (S1 S2 : StateSpace name) σ x v σ',
      (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
      x ∈ space_domain S2 ->
      S2 ⊢ σ →{Some (Event x v)} Some σ'.
  Proof.
    intros ? ? ? ? ? ? Hstep Hdom.
    inversion Hstep; subst; auto.
    (* the only remaining case is when x ∉ dom(S2), a contradiction *)
    { absurd (event_in _ (space_domain S2) (Some (Event x v))); auto.
      constructor; auto.
    }
  Qed.

  Lemma union_inversion_lr : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S1 ∩ space_domain S2 ->
    S1 ⊢ σ →{Some (Event x v)} Some σ' /\ S2 ⊢ σ →{Some (Event x v)} Some σ'.
  Proof.
    intros ? ? ? ? ? ? Hstep Hdom.
    split; [eapply union_inversion_left | eapply union_inversion_right];
      eauto; decompose_set_structure.
  Qed.

  Lemma union_inversion : forall (S1 S2 : StateSpace name) e σ σ',
    (S1 ∥ S2) ⊢ σ →{e} Some σ' ->
    S1 ⊢ σ →{e} Some σ' \/ S2 ⊢ σ →{e} Some σ'.
  Proof.
    intros S1 S2 e σ σ' Hstep.
    inversion Hstep; auto.
  Qed.

(*
  Instance internal_in_dec : forall l, in_dec (space_internal (latch_stage_with_env l)).
  Proof.
    intros l. simpl. typeclasses eauto.
  Qed.

  Instance input_in_dec : forall l, in_dec (space_input (latch_stage_with_env l)).
  Admitted.

  Instance output_in_dec : forall l, in_dec (space_output (latch_stage_with_env l)).
  Admitted.
*)
About state_equiv_on.


  Lemma union_internal_inversion_right : forall (S1 S2 : StateSpace name) σ x v σ',
      well_formed S1 ->
      well_formed S2 ->
      space_internal S1 ⊥ space_domain S2 ->
      space_domain S1 ⊥ space_internal S2 ->
      (S1 ∥ S2) ⊢ σ →{ Some (Event x v)} Some σ' ->
      x ∉ space_domain S2 ->
      state_equiv_on (space_internal S2) (Some σ') (Some σ).
  Proof.
    intros ? ? ? ? ? ? Hwf1 Hwf2 Hdisj1 Hdisj2 Hstep Hx y Hy.
    inversion Hstep as [ ? ? H_event_in Hstep' Hequiv
                       | ? ? H_event_in Hstep' Hequiv
                       | ? ? Hevent Hstep1 Hstep2]; subst; auto.
    * unfold state_equiv_on in Hequiv.
      rewrite Hequiv; auto.
      unfold space_domain; solve_set.
    * contradict H_event_in.
      constructor.
      apply wf_space in Hstep; auto.
      2:{ apply wf_union; auto. }
      simpl in Hstep.
      decompose_set_structure; unfold space_domain in *;
        try solve_set;
        try (contradict Hx; solve_set).

    * inversion Hevent as [Hevent1 Hevent2 | Hevent1 Hevent2 | Hevent1 Hevent2];
        inversion Hevent2; subst;
          contradict Hx; unfold space_domain; solve_set.
  Qed.

  Lemma hide_inversion : forall (S : StateSpace name) σ x e σ',
      (hide x S) ⊢ σ →{Some e} Some σ' ->
      S ⊢ σ →{Some e} Some σ'.
  Proof.
    intros ? ? ? ? ? Hstep.
    inversion Hstep; auto.
  Qed.

  Lemma hide_inversion_None : forall (S : StateSpace name) σ x σ',
      (hide x S) ⊢ σ →{None} Some σ' ->
      S ⊢ σ →{None} Some σ' \/ exists v, S ⊢ σ →{Some (Event x v)} Some σ'.
  Proof.
    intros ? ? ? ? Hstep.
    inversion Hstep; subst; auto.
    right. exists v. auto.
  Qed.

  Lemma func_space_output_inversion : forall I (o : name) f (σ : state name) x v σ',
      o ∉ I ->
      func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
      x = o ->
      v = f σ.
  Proof.
    intros ? ? ? ? ? ? ? Ho Hstep ?. subst.
    inversion Hstep; try find_contradiction.
    subst. auto.
  Qed.


  Lemma func_space_output_unstable : forall I (o : name) f σ x v σ',
      o ∉ I ->
      func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
      x = o ->
      σ x <> v.
  Proof.
    intros ? ? ? ? ? ? ? ? Hstep Heq.
    subst.
    inversion Hstep; subst; try find_contradiction; auto.
  Qed.

  Lemma func_space_output_neq : forall I (o : name) f σ v σ' y,
      o ∉ I ->
      func_space I o f ⊢ σ →{Some (Event o v)} Some σ' ->
      y ∈ I ->
      σ' y = σ y.
  Proof.
    intros ? ? ? ? ? ? ? ? Hstep Hneq.
    inversion Hstep; subst;
    match goal with
    | [ H : state_equiv_on _ (Some ?σ') _ |- ?σ' _ = _ ] => rewrite H; [unfold update | try solve_set]
    end;
      compare_next; auto.
  Qed.

  Lemma func_space_inversion_None : forall I (o : name) f (σ : state name) σ',
      func_space I o f ⊢ σ →{None} Some σ' ->
      False.
  Proof.
    intros. inversion H.
  Qed.

About union_inversion_lr.
  Ltac step_inversion_1 :=
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_lr in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S1) *)
      [ let Hstep' := fresh "Hstep" in destruct Hstep as [Hstep Hstep']
      | unfold space_domain; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_left in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S1) *)
      [ | unfold space_domain; left; right; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_right in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S2) *)
      [ | unfold space_domain; left; right; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply hide_inversion in Hstep
  | [ Hstep : _ ⊢ _ →{ _ } Some _ |- _ ] =>
      apply delay_space_inversion in Hstep
  | [ Hstep : _ ⊢ _ →{None} Some _ |- _ ] =>
      apply func_space_inversion_None in Hstep; inversion Hstep
  | [ Hstep : _ ⊢ _ →{None} Some _ |- _ ] =>
      apply union_inversion in Hstep; destruct Hstep as [Hstep | Hstep]
  | [ Hstep : _ ⊢ _ →{None} Some _ |- _ ] =>
      apply hide_inversion_None in Hstep; destruct Hstep as [Hstep | [? Hstep]]
  | [ Hstep : flop _ _ _ _ _ _ ⊢ _ →{ None } Some _ |- _ ] => inversion Hstep; subst; clear Hstep

  end.
  Ltac step_inversion_eq :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply func_space_output_inversion in Hstep;
        [ | simpl; solve_set; fail | simpl; solve_set; fail]
  end.
  Ltac step_inversion_unstable :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      eapply func_space_output_unstable in Hstep; eauto;
        [ | simpl; solve_set; fail ]
  end.

  Ltac step_inversion_neq :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some ?σ' |- context[?σ' ?y] ] =>
      apply (func_space_output_neq _ _ _ _ _ _ y) in Hstep;
      [ | simpl; solve_set; fail | simpl; solve_set; fail];
      rewrite Hstep
  end.

End StateSpaceTactics.

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

  Inductive place_eq : forall {t1 t2 t1' t2' : transition}, place MG t1 t2 -> place MG t1' t2' -> Prop :=
  | place_refl : forall t1 t2 (p : place MG t1 t2), place_eq p p.


  Class MG_naming_scheme :=
  { transition_name : transition -> name
  ; place_name : forall {t1 t2} (p : place MG t1 t2), name

  ;  name_is_place_dec : forall (x : name),
     {t1 : transition & {t2 : transition & {p : place MG t1 t2 & x = place_name p}}}
   + {forall t1 t2 (p : place MG t1 t2), x <> place_name p}


  ; transition_update_value : transition -> value -> value

  ; input_transition : Ensemble transition
  ; input_transition_dec : `{in_dec input_transition}

  ; transition_place_name_disjoint : forall t {t1 t2} (p : place MG t1 t2),
    transition_name t <> place_name p

    (* I'm not sure if t ∈ input_transition is the right restriction here, but
    we need this fact for proving well_formed, and it does not hold without this
    transition for click, e.g. with CLK+ and CLK-. On the other hand, what about
    4 phase handshake protocols? *)
  ; transition_name_injective : forall t t', t ∈ input_transition ->
    t <> t' -> transition_name t <> transition_name t'

   ; places_all_disjoint : forall {t1 t2 t1' t2' : transition}
                                        (p : place MG t1 t2) (p' : place MG t1' t2'),
      place_name p = place_name p' ->
      place_eq p p'

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
  Let transition_set : Ensemble name := fmap transition_name (fun (t : transition) => True).

  Inductive MG_SS_step
    : state name -> option (event name value) -> option (state name) -> Prop :=

  | transition_enabled σ σ' x v (t : transition) :
    x = transition_name t ->
    is_enabled MG t (state_to_marking σ) ->
    v = transition_update_value t (σ x) ->
    state_equiv_on (transition_set ∪ places_set)
                   (Some σ') 
                   (Some (update (fire_in_state t σ) x v)) ->
    MG_SS_step σ (Some (Event x v)) (Some σ')

  | input_not_enabled σ x v t :
    x = transition_name t ->
    t ∈ input_transition ->
    ~ is_enabled MG t (state_to_marking σ) ->
   MG_SS_step σ (Some (Event x v)) None
  .

  Let output_transition : Ensemble transition :=
    (fun t => True) ∖ input_transition.
(*    fun t => t ∉ input_transition.*)
  Definition MG_SS : StateSpace name :=
  {| space_input := fmap transition_name input_transition
   ; space_output := fmap transition_name output_transition
   ; space_internal := places_set
   ; space_step := MG_SS_step
   |}.

  Arguments well_formed {name}.
  Lemma wf_MG_SS : well_formed MG_SS.
  Proof.
    set (Hdec := input_transition_dec).
    constructor;
    try match goal with
    | [ |- _ ⊥ _ ] =>
      simpl; constructor;
      intros x Hx; deep_decompose_set_structure;
      match goal with
      | [ H : transition_name ?t1 = transition_name ?t2 |- _ ] =>
        compare t1 t2;
        try (eapply transition_name_injective; eauto; fail)

      | [ H : transition_name ?t = place_name ?p |- _ ] =>
        let Hdisjoint := fresh "Hdisjoint" in
        set (Hdisjoint := transition_place_name_disjoint t p);
        find_contradiction
      end
    end.

    * intros ? ? ? ? Hstep.
      inversion Hstep; subst; simpl.
      destruct (t ∈? input_transition).
      + left. econstructor; eauto.
      + right. econstructor; split; eauto.
        unfold output_transition. solve_set.
    * intros ? ? ? Hstep ? He Hexternal.
      inversion Hstep; subst.
      unfold update. unfold fire_in_state.
      destruct (name_is_place_dec x) as [[t1 [t2 [p Hp]]] | ].
      { (*contradiction *)
        contradict Hexternal. subst.
        simpl. inversion 1 as [? [t' [Ht' Hp']] | x [? [? Hp']]]; subst;
          apply transition_place_name_disjoint in Hp'; auto.
      }
      compare x (transition_name t); auto.
      { contradiction (He (transition_update_value t (σ (transition_name t)))); auto. }
      { assert (Hx : exists t', x = transition_name t').
        { inversion Hexternal as [? Hex | ? Hex]; subst;
           inversion Hex as [t' [Ht Hx]]; subst;
           eexists; split; auto; constructor.
        }
        destruct Hx as [t' Ht']; subst.
        rewrite H5. 2:{ left. exists t'; split; auto; constructor. }
        unfold update. compare_next. unfold fire_in_state.
        destruct (name_is_place_dec (transition_name t'))
          as [[t1 [t2 [p Hp]]] | ]; auto.
        { contradict Hp. apply transition_place_name_disjoint. }
      }
        

    * intros ? ? ? ? Hstep.
      inversion Hstep; subst.
      rewrite H6.
      2:{ left. exists t; split; auto; constructor. }
      unfold update; simpl.
      reduce_eqb. auto.
  Qed.



  Lemma MG_SS_val_not_X : forall σ0 tr σ,
    MG_SS ⊢ σ0 →*{tr} Some σ ->
    forall {t1 t2} (p : place MG t1 t2), 
    σ0 (place_name p) <> X ->
    σ (place_name p) <> X.
  Proof.
    intros σ0 tr σ Hstep.
    remember (Some σ) as τ; generalize dependent σ.
    induction Hstep; intros σ Hτ t1 t2 p Hwf; inversion Hτ; subst; auto.
    * specialize (IHHstep σ' eq_refl t1 t2 p Hwf).
      inversion H; subst.
      rewrite H7.
      2:{ right. eexists. eexists. exists p. reflexivity. }
      unfold update. compare_next.
      { Search transition_name place_name.
        apply transition_place_name_disjoint in Heq; contradiction.
      }
      unfold fire_in_state.
      destruct (name_is_place_dec (place_name p)) as [[t1' [t2' [p' Heq']]] | Hneq'].
      2:{ specialize (Hneq' _ _ p); find_contradiction. }
      Search place_name place_eq.
      apply places_all_disjoint in Heq'.
Require Import Coq.Program.Equality.
      dependent destruction Heq'.
      compare_next; auto.
      compare_next. { destruct (σ' (place_name p)); try (inversion 1; fail); find_contradiction. }
      compare_next. { destruct (σ' (place_name p)); try (inversion 1; fail); find_contradiction. }
      auto.

    * specialize (IHHstep σ' eq_refl t1 t2 p Hwf).
      inversion H; subst.
  Qed.



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
