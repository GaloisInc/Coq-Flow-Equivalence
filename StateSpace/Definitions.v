Require Import Base.
Require Import Circuit.
Require Import Monad.
Require Import Setoid.

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
Lemma in_implies_event_in : forall (x : name) X (v : value),
  x ∈ X ->
  event_in X (Some (Event x v)).
Proof.
  intros. econstructor. auto.
Qed.
Lemma not_in_implies_event_not_in : forall (x : name) X (v : value),
  x ∉ X ->
  ~ event_in X (Some (Event x v)).
Proof.
  intros. inversion 1; subst. contradiction.
Qed.

Add Parametric Morphism : event_in
  with signature Same_set name ==> @eq (option (event name value)) ==> iff as event_in_equiv.
Proof.
  intros X Y Hequiv e.
  split; intros Hin; inversion Hin; subst; constructor; rewrite Hequiv in *; auto.
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

  Definition state_equiv_on (X : Ensemble name) (τ1 τ2 : option (state name)) :=
      match τ1, τ2 with
      | Some σ1, Some σ2 => forall x, x ∈ X -> σ1 x = σ2 x
      | None, None => True
      | _, _ => False
      end.


  Add Parametric Morphism : state_equiv_on
    with signature (Same_set name) ==> (@eq (option (state name)))
                                   ==> (@eq (option (state name))) ==> iff
    as state_equiv_on_equiv.
  Proof.
    intros X Y HXY τ τ'.
    split; intros Hequiv.
    * destruct τ as [σ | ]; destruct τ' as [σ' | ]; try inversion Hequiv.
      { simpl in *.
        intros x Hx.
        rewrite <- HXY in Hx.
        apply Hequiv; auto.
      }
      { constructor. }
    * destruct τ as [σ | ]; destruct τ' as [σ' | ]; try inversion Hequiv.
      { simpl in *.
        intros x Hx.
        rewrite HXY in Hx.
        apply Hequiv; auto.
      }
      { constructor. }
  Qed.

  Ltac rewrite_state_equiv_on :=
  match goal with
  | [ Hequiv : state_equiv_on _ (Some ?σ) _ |- context[?σ _] ] =>
    rewrite Hequiv; [ | try solve_set; try (decompose_set_structure; solve_set); fail]
  | [ Hequiv : state_equiv_on _ _ (Some ?σ) |- context[?σ _] ] =>
    rewrite <- Hequiv; [ | try solve_set; try (decompose_set_structure; solve_set); fail]
  end.


(** A state space is well-formed if several properties hold. There may be other
properties that also hold not included here, such as the condition that each
input/output/internal set are individually all_disjoint, or that the transition
relation is only valid for events in [space_input S ∪ space_outupt S]. *)
Record well_formed (S : StateSpace) :=
  { (*space_dom : forall x, x ∈ space_domain S <-> in_fin_state σ x*)
    space_input_output : space_input S ⊥ space_output S
  ; space_input_internal : space_input S ⊥ space_internal S
  ; space_output_internal : space_output S ⊥ space_internal S
  ; wf_space : forall σ x v τ,
    S ⊢ σ →{Some (Event x v)} τ ->
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



(** * Define a circuit state space from a combinational logic function *)
Section FuncStateSpace.

  Variable I : list name.
  Variable x : name.
  Variable f : state name -> value.
  Hypothesis x_notin_I : ~ (x ∈ from_list I).

  Let dom := from_list I ∪ singleton x ∪ ∅.
  Hint Unfold dom.
  Lemma x_in_dom : x ∈ dom. unfold dom. auto with sets. Qed.
  Lemma I_subset_dom : forall i, i ∈ from_list I -> i ∈ dom.
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
  | func_input_stable i (pf_i : i ∈ from_list I) v σ' :
    func_stable σ ->
    σ i <> v -> (* Question: what happens if an event occurs that doesn't change the value of the variable? Is it allowed? Is it a no-op? *)
    state_equiv_on (from_list I ∪ singleton x) (Some (update σ i v)) (Some σ') ->
    func_step σ (Some (Event i v))
                (Some σ')

  | func_input_unstable i (pf_i : i ∈ from_list I) v σ' :
    ~ (func_stable σ) ->
    σ i <> v ->
(*    ~ (func_stable (update σ i v)) -> (* in a binary system, this is ok *)*)
    f σ = f (update σ i v) -> (* ok to update input in an unstable system if the output doesn't change *)
    state_equiv_on (from_list I ∪ singleton x) (Some (update σ i v))  (Some σ') ->
    func_step σ (Some (Event i v)) (Some σ')


  (* if input updates in an unstable system causes output to change, go to error state*)
  | func_err i (pf_i : i ∈ from_list I) v :
    ~ (func_stable σ) ->
    f σ <> f (update σ i v) \/ σ i = v -> 
    func_step σ (Some (Event i v)) None

  | func_output v σ' :
    ~ (func_stable σ) ->
    v = f σ ->
    state_equiv_on (from_list I ∪ singleton x) (Some (update σ x v)) (Some σ')  ->
    func_step σ (Some (Event x v))
                (Some σ')
  .

  Program Definition func_space : StateSpace :=
  {| space_input := from_list I
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
      ++ rewrite_state_equiv_on.
         assert (i <> y).
         { intro. apply (y_neq_z v). subst; auto. }
         reduce_eqb; auto.
      ++ rewrite_state_equiv_on.
         assert (i <> y).
         { intro. apply (y_neq_z v). subst; auto. }
         reduce_eqb; auto.
      ++ rewrite_state_equiv_on.
         compare x y; auto.
         { (* x = y *)
            rewrite Heq in y_neq_z.
            specialize (y_neq_z (f σ) eq_refl).
            find_contradiction.
         }

    + intros ? y ? ? Hstep.
      inversion Hstep; try subst; unfold update in *;
        rewrite_state_equiv_on;
        reduce_eqb; auto.
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
    (* Flops treat clk inputs different than other inputs. Flop_input only
      covers set, reset, and D inputs. This is because clk- operations should *)

    (* an input is allowed when, either (1) the flip-flop is stable aka any
    possible clock changes have been registered; or (2) when the input would not
    actually be observable on the outputs of the circuit. *)
    (* Note: I am modifying condition 2 because, for clocks, that would enable
    the clocks to get out of sync. *)
  | Flop_input i v σ' :
    σ clk = σ old_clk ->
    (σ Q = Q_output σ \/ Q_output σ = Q_output (update σ i v)) ->
    i ∈ from_list [set;reset;D] ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ i v)) (Some σ') ->
    flop_step σ (Some (Event i v)) (Some σ')

  | Flop_input_clk_fall v σ' :
    σ clk = σ old_clk ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update (update σ clk v)
                                                                     old_clk v))
                                                       (Some σ') ->
    v <> Bit1 ->
    flop_step σ (Some (Event clk v)) (Some σ')

  | Flop_input_clk_rise σ' :
    σ clk = σ old_clk ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk])
                   (Some (update σ clk Bit1))
                   (Some σ') ->
    flop_step σ (Some (Event clk Bit1)) (Some σ')

    (* other inputs lead to the error state *)
  | Flop_input_err_clk i v :
    σ clk <> σ old_clk ->
    i ∈ flop_input ->
    flop_step σ (Some (Event i v)) None
  | Flop_input_err_val i v :
    σ Q <> Q_output σ ->
    Q_output σ <> Q_output (update σ i v) ->
    i ∈ flop_input ->
    flop_step σ (Some (Event i v)) None

    (* if the set line is high, raise Q *)
  | Flop_set σ' :
    σ set = Num 0 ->
    σ Q  <> Num 1 ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ Q (Num 1))) (Some σ') ->
    flop_step σ (Some (Event Q (Num 1))) (Some σ')

    (* if the reset line is high, lower Q *)
  | Flop_reset σ' :
    σ set   = Num 1 ->
    σ reset = Num 0 ->
    σ Q    <> Num 0 ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ Q (Num 0))) (Some σ') ->
    flop_step σ (Some (Event Q (Num 0))) (Some σ')

(*
    (* if the clock has fallen (i.e. input changed and clk is no longer 1), do
    nothing to the outputs, but propogate thd change to the old_clk. *)
  | Flop_clk_fall σ' :
    σ clk <> Num 1 ->
    σ clk <> σ old_clk ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ old_clk (σ clk)))
                                                           (Some σ')
                                                            ->
    flop_step σ None (Some σ')
*)

    (* if the clock has risen (i.e. input changed and clk is now equal to 1),
    update Q and old_clk to their proper values. The result will now be stable *)
  | Flop_clk_rise v σ' :
    σ set      = Num 1 ->
    σ reset    = Num 1 ->
    σ clk      = Num 1 ->
    σ old_clk <> Num 1 ->

    v = σ D ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk])
                   (Some (update (update σ Q v) old_clk (σ clk)))
                   (Some σ') ->

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
        decompose_set_structure; try solve_set.
      + intros ? ? ? Hstep y Hy H_not_internal.
        decompose_set_structure;
        inversion Hstep; try subst;
        repeat match goal with
        | [ H : forall v0, Some (Event ?x ?v) <> Some (Event ?x v0)
          |- _ ] => contradiction (H v); auto
        | [ H : state_equiv_on _ _ (Some ?σ')
          |- ?σ' _ = _ ] =>
          rewrite <- H; [ unfold update; repeat compare_next; auto | solve_set]
        end.
    + intros ? ? ? ? Hstep.
      inversion Hstep; try subst; unfold update; reduce_eqb; auto.
      ++ unfold flop_input in *. rewrite_state_equiv_on. 
         unfold update. reduce_eqb; auto.
      ++ rewrite_state_equiv_on; auto.
         unfold update.
         rewrite <- H (* clk = x *).
         reduce_eqb.
         compare_next; auto.
      ++ rewrite_state_equiv_on; auto.
         unfold update.
         reduce_eqb.
         reflexivity.
      ++ rewrite_state_equiv_on.
         unfold update.
         reduce_eqb; auto.
      ++ rewrite_state_equiv_on.
         unfold update.
         reduce_eqb; auto.
      ++ rewrite_state_equiv_on.
         unfold update.
         reduce_eqb; auto.
         compare_next; auto.
  Qed.

  Lemma flop_output_is_bit : forall σ v σ',
    val_is_bit (σ D) ->
    flop ⊢ σ →{Some (Event Q v)} Some σ' ->
    val_is_bit v.
  Proof.
    intros ? ? ? ? Hstep.
    inversion Hstep as [? ? ? ? ? Hi | | | | | | |]; try subst;
      auto; try constructor.
    * contradict Hi. unfold flop_input. solve_set.
    * find_contradiction.
  Qed.


  Lemma flop_old_clk : forall σ x v σ',
    val_is_bit v ->
    flop ⊢ σ →{Some (Event x v)} Some σ' ->
    val_is_bit (σ clk) ->
    val_is_bit (σ old_clk) ->
    val_is_bit (σ' old_clk).
  Proof.
    intros ? ? ? ? ? Hstep ? ?.
    inversion Hstep as [? ? ? ? ? Hi | | | | | | |]; try subst; unfold update;
      try match goal with
      | [ H : state_equiv_on _ _ (Some ?σ') |- _ ] =>
        rewrite <- H; [try unfold update; repeat (compare_next; auto) | solve_set]
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
      + constructor. simpl. unfold flop_input.
        decompose_set_structure; try solve_set.
      + constructor. simpl. unfold flop_input.
        solve_set.
      + constructor. simpl. unfold flop_input.
        solve_set.
      + absurd (σ Q = Num 1); auto.
        destruct Hstable as [Hstable _].
        rewrite Hstable; unfold Q_output.
        rewrite H; auto.
      + absurd (σ Q = Num 0); auto.
        destruct Hstable as [Hstable _].
        rewrite Hstable; unfold Q_output.
        rewrite H, H0; auto.
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
  
  Definition C_elem_output σ := 
    match σ x1, σ x2 with
    | Num 0, Num 0 => Num 0
    | Num 1, Num 1 => Num 1
    | Num 0, Num 1 => σ y
    | Num 1, Num 0 => σ y
    | _, _ => X
    end.
  Definition C_elem : StateSpace := func_space [x1;x2] y C_elem_output.

End Celem.

(** * A state space modeling a delay until a guard holds over some sensitive input wires *)
(** Relative timing constraint *)
Section Delay.

  Variable x y : name.
  Variable sensitivities : list name.
  (** The guard should only depend on the variables in the sensitivites set *)
  Variable guard : state name -> Prop.
  Variable guardb : state name -> bool.
  Hypothesis guardb_equiv : forall σ, guard σ <-> guardb σ = true.

  Inductive delay_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  | delay_input_unstable : forall v, σ x <> v -> σ y <> σ x ->
                                     delay_step σ (Some (Event x v)) None
  | delay_input_stable : forall v, σ y = σ x -> delay_step σ (Some (Event x v)) (Some (update σ x v))
  (* output only transitions when the guard is true *)
  | delay_output σ' : σ y <> σ x ->
                   guard σ ->
                   state_equiv_on (from_list sensitivities ∪ from_list [x;y]) (Some σ')
                                                                    (Some (update σ y (σ x))) ->
                   delay_step σ (Some (Event y (σ x))) (Some σ')
  .

  Definition delay : StateSpace :=
    {| space_input := singleton x ∪ from_list sensitivities
     ; space_output := singleton y
     ; space_internal := ∅
     ; space_step := delay_step
    |}.

  Lemma delay_wf : well_formed delay.
  Admitted.

End Delay.


Section DelaySpace.
  Variable S : StateSpace.
  Variable sensitivities : list name.
  (** The guard should only depend on the variables in the sensitivites set *)
  Variable guard : state name -> Prop.

  Inductive delay_space_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
  (* sensitivity steps are always valid *)
  | delay_space_sensitivity : forall x v σ',
    x ∈ from_list sensitivities ->
    state_equiv_on (space_domain S ∪ from_list sensitivities) (Some (update σ x v)) (Some σ') ->
    delay_space_step σ (Some (Event x v)) (Some σ')

  (* input steps are always valid *)
  | delay_space_input : forall x v τ,
    S ⊢ σ →{Some (Event x v)} τ ->
    state_equiv_on (from_list sensitivities) (Some σ) τ ->
    x ∈ space_input S ->
    delay_space_step σ (Some (Event x v)) τ

  (* epsilon steps are always valid *)
  | delay_space_internal : forall τ,
    S ⊢ σ →{None} τ ->
    state_equiv_on (from_list sensitivities) (Some σ) τ ->
    delay_space_step σ None τ

  (* output steps can only happen if the guard is true *)
  | delay_space_output : forall x v τ,
    guard σ ->
    S ⊢ σ →{Some (Event x v)} τ ->
    x ∈ space_output S ->
    state_equiv_on (from_list sensitivities) (Some σ) τ ->
    delay_space_step σ (Some (Event x v)) τ
  .

  Definition delay_space (guardb : state name -> bool) : StateSpace :=
    {| space_input := space_input S ∪ from_list sensitivities
     ; space_output := space_output S
     ; space_internal := space_internal S
     ; space_step := delay_space_step
    |}.

  Variable guardb : state name -> bool.
  Lemma delay_space_wf :
    well_formed S ->
    from_list sensitivities ⊥ space_domain S ->
    well_formed (delay_space guardb).
  Proof.
    intros Hwf Hdisjoint.
    destruct Hwf.
    unfold space_domain in Hdisjoint.
    assert (Hdisjoint1 : from_list sensitivities ⊥ space_input S).
    { destruct Hdisjoint as [Hdisjoint]. constructor. intros x Hx.
      apply (Hdisjoint x).
      decompose_set_structure; solve_set.
    }
    assert (Hdisjoint2 : from_list sensitivities ⊥ space_output S).
    { destruct Hdisjoint as [Hdisjoint]. constructor. intros x Hx.
      apply (Hdisjoint x).
      decompose_set_structure; solve_set.
    }
    assert (Hdisjoint3 : from_list sensitivities ⊥ space_internal S).
    { destruct Hdisjoint as [Hdisjoint]. constructor. intros x Hx.
      apply (Hdisjoint x).
      decompose_set_structure; solve_set.
    }
    split.
    * simpl. solve_set.
    * simpl. solve_set.
    * simpl. solve_set.
    * intros σ x v τ Hstep.
      simpl.
      inversion Hstep; subst.
      + solve_set.
      + solve_set.
      + solve_set.
    * intros ? ? ? Hstep x Hv Hx.
      simpl in Hx.
      decompose_set_structure.
      { (* x ∈ input *) inversion Hstep; subst;
        try (eapply wf_scoped0; eauto; try solve_set; fail).
        assert (x0 <> x).
        { intros Hx. subst. apply (Hv v). auto. }
        unfold space_domain in *. rewrite_state_equiv_on.
        unfold update. reduce_eqb. auto.
      }
      { (* x ∈ sens *) inversion Hstep; subst; try (rewrite_state_equiv_on; auto; fail).
        assert (x0 <> x).
        { intros Hx. subst. apply (Hv v). auto. }
        unfold space_domain in *. rewrite_state_equiv_on.
        unfold update. reduce_eqb. auto.
      }
      { (* x ∈ output *) inversion Hstep; subst;
        try (eapply wf_scoped0; eauto; solve_set; fail).
        assert (x0 <> x).
        { intros Hx. subst. apply (Hv v). auto. }
        unfold space_domain in *. rewrite_state_equiv_on.
        unfold update. reduce_eqb. auto.
      }
    * intros ? ? ? ? Hstep.
      inversion Hstep; subst;
      try (eapply wf_update0; eauto; fail).
      rewrite_state_equiv_on. unfold update. reduce_eqb. auto.
  Qed.

  Lemma delay_space_inversion_sens : forall σ x v τ,
    delay_space guardb ⊢ σ →{Some (Event x v)} τ ->
    from_list sensitivities ⊥ space_domain S ->
    x ∈ from_list sensitivities ->
    state_equiv_on (space_domain S ∪ from_list sensitivities) (Some (update σ x v)) τ.
  Proof.
    intros σ x v τ Hstep [Hwf] Hx.
    inversion Hstep; subst; auto.
    * contradiction (Hwf x). unfold space_domain. solve_set.
    * contradiction (Hwf x); unfold space_domain.
      solve_set.
  Qed.

  Lemma delay_space_inversion_step : forall σ e τ,
    delay_space guardb ⊢ σ →{e} τ ->
    ~ (event_in (from_list sensitivities) e) ->
    S ⊢ σ →{e} τ /\ state_equiv_on (from_list sensitivities) (Some σ) τ.
  Proof.
    intros ? ? ? Hstep Hin.
    inversion Hstep; subst.
    * (* contradiction *)
      contradict Hin. constructor. solve_set.
    * split; auto.
    * split; auto.
    * split; auto.
  Qed.

  Lemma delay_space_inversion_output : forall σ e τ,
    delay_space guardb ⊢ σ →{e} τ ->
    from_list sensitivities ⊥ space_domain S ->
    space_input S ⊥ space_output S ->
    event_in (space_output S) e ->
    guard σ.
  Proof.
    intros ? ? ? Hstep [Hwf1] [Hwf2] Hin.
    inversion Hstep; subst; auto.
    * inversion Hin; subst. contradiction (Hwf1 x). unfold space_domain; solve_set.
    * inversion Hin; subst. contradiction (Hwf2 x). unfold space_domain; solve_set.
    * inversion Hin; subst.
  Qed.


End DelaySpace.


End state_space.

Arguments event_in {name val}.
Arguments Event_In {name val}.
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
Arguments delay {name name_eq_dec}.
Arguments delay_space {name name_eq_dec}.
Arguments state_equiv_on {name}.
Arguments traces_of {name}.

Arguments well_formed {name}.
Arguments space_input_output {name}.
Arguments space_input_internal {name}.
Arguments space_output_internal {name}.
Arguments wf_space {name}.
Arguments wf_scoped {name}.
Arguments wf_update {name}.

Arguments union_input_event {name}.

Notation "C ⊢ σ →{ e } τ" := (space_step _ C σ e τ) (no associativity, at level 70).
Notation "C ⊢ σ →*{ t } τ" := (space_steps _ C σ t τ) (no associativity, at level 70).
Notation "S1 ∥ S2" := (union _ S1 S2) (left associativity, at level 91).
