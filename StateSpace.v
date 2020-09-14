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
  ; wf_space : forall σ x v τ,
    S ⊢ σ →{Some (Event x v)} τ ->
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

Class enumerable {A} (X : Ensemble A) :=
    { enumerate : list A
    ; as_list_equiv : X == from_list enumerate
    }.
  Instance singleton_enumerable : forall (x : name), enumerable (singleton x).
  Proof. intros x. exists [x]. simpl.
    split; intros y Hy; decompose_set_structure; solve_set.
  Defined.
  Instance from_list_enumerable : forall (l : list name), enumerable (from_list l).
  Proof.
    intros l. exists l. reflexivity.
  Defined.
  Lemma from_list_app : forall (l1 l2 : list name),
    from_list (l1 ++ l2) == from_list l1 ∪ from_list l2.
  Proof.
    induction l1; intros; simpl.
    * split; intros x Hx. solve_set. decompose_set_structure; solve_set.
    * rewrite IHl1.
      split; intros x Hx; decompose_set_structure; solve_set.
  Qed.

  Instance union_enumerable (X Y : Ensemble name) :
    enumerable X ->
    enumerable Y ->
    enumerable (X ∪ Y).
  Proof.
    intros [Xl HX] [Yl HY].
    exists (Xl ++ Yl).
    rewrite HX, HY.
    rewrite from_list_app.
    reflexivity.
  Defined.

Print filter.
Print in_list_dec.


  Lemma intersection_emptyset : forall {X} (A : Ensemble X),
    ∅ ∩ A == ∅.
  Proof.
    intros. split; intros x Hx; decompose_set_structure.
  Qed.
  Lemma union_emptyset : forall {X} (A : Ensemble X),
    ∅ ∪ A == A.
  Proof.
    intros. split; intros x Hx; decompose_set_structure; solve_set.
  Qed.
  Lemma setminus_emptyset : forall {X} (A : Ensemble X),
    ∅ ∖ A == ∅.
  Proof.
    intros. split; intros x Hx; decompose_set_structure; solve_set.
  Qed.


  Lemma union_intersect_distr : forall {X} (A B C : Ensemble X),
    (A ∪ B) ∩ C == (A ∩ C) ∪ (B ∩ C).
  Proof.
    intros. split; intros x Hx; decompose_set_structure; solve_set.
  Qed.

  Lemma union_setminus_distr : forall {X} (A B C : Ensemble X),
    (A ∪ B) ∖ C == (A ∖ C) ∪ (B ∖ C).
  Proof.
    intros; split; intros x Hx; decompose_set_structure; solve_set.
  Qed.

  Lemma singleton_intersection_in : forall {X} (A : Ensemble X) a,
    a ∈ A ->
    singleton a ∩ A == singleton a.
  Proof.
    intros X A a Ha; split; intros x Hx;
    decompose_set_structure.
  Qed.
  Lemma singleton_intersection_not_in : forall {X} (A : Ensemble X) a,
    a ∉ A ->
    singleton a ∩ A == ∅.
  Proof.
    intros X A a Ha; split; intros x Hx;
    decompose_set_structure.
  Qed.
  Lemma singleton_setminus_in : forall {X} (A : Ensemble X) a,
      a ∈ A ->
      singleton a ∖ A == ∅.
    intros X A a Ha; split; intros x Hx;
    decompose_set_structure.
  Qed.
  Lemma singleton_setminus_not_in : forall {X} (A : Ensemble X) a,
      a ∉ A ->
      singleton a ∖ A == singleton a.
    intros X A a Ha; split; intros x Hx;
    decompose_set_structure.
  Qed.

Lemma in_list_dec_t : forall (x : name) (X : list name),
    in_list_dec x X = true <-> x ∈ from_list X.
Proof.
    induction X; split; simpl; intros H; try (inversion H; fail).
    * compare_next; try solve_set.
      right. apply IHX. auto.
    * compare_next; auto.
      apply IHX.
      decompose_set_structure.
Qed.
Lemma in_list_dec_f : forall (x : name) X,
    in_list_dec x X = false <-> x ∉ from_list X.
Proof.
    induction X; split; simpl; intros H; auto; try solve_set.
    * compare_next.
      apply IHX in H.
      solve_set.
    * decompose_set_structure.
      compare_next.
      apply IHX; auto.
Qed.

Ltac from_in_list_dec :=
  repeat match goal with
  | [ H : in_list_dec ?x ?X = true |- _] => apply in_list_dec_t in H
  | [ |- in_list_dec ?x ?X = true ] => apply in_list_dec_t
  | [ H : in_list_dec ?x ?X = false |- _] => apply in_list_dec_f in H
  | [ |- in_list_dec ?x ?X = false ] => apply in_list_dec_f
  end.
Ltac to_in_list_dec :=
  repeat match goal with
  | [ H : ?x ∈ ?X |- _] => apply in_list_dec_t in H
  | [ |- ?x ∈ ?X ] => apply in_list_dec_t
  | [ H : ?x ∉ ?X |- _] => apply in_list_dec_f in H
  | [ |- ?x ∉ ?X ] => apply in_list_dec_f
  end.
  Lemma filter_false : forall {X} (l : list X),
    filter (fun _ => false) l = nil.
  Proof.
    induction l; auto.
  Qed.


  Section IntersectionEnumerable.

    Variable X Y : Ensemble name.
    Context `{enumX : enumerable _ X} `{enumY : enumerable _ Y}.
    Let list_intersection := filter (fun x => in_list_dec x (@enumerate _ Y _)) (@enumerate _ X _).
    Lemma list_intersection_equiv :
      X ∩ Y == from_list list_intersection.
    Proof.
      destruct enumX as [Xl HX]; destruct enumY as [Yl HY].
      unfold list_intersection; clear list_intersection.
      simpl.
      rewrite HX, HY; clear HX HY.
      induction Xl.
      * simpl. rewrite intersection_emptyset.
        reflexivity.
      * simpl.
        destruct (in_list_dec a Yl) eqn:Ha;
          from_in_list_dec.
        + (* a ∈ Yl *) simpl.
          rewrite union_intersect_distr.
          rewrite singleton_intersection_in; auto.
          rewrite IHXl.
          reflexivity.
        + (* a ∉ Yl *)
          rewrite union_intersect_distr.
          rewrite singleton_intersection_not_in; auto.
          rewrite union_emptyset.
          rewrite IHXl; reflexivity.
    Qed.

    Instance intersection_enumerable :
      enumerable (X ∩ Y).
    Proof.
      exists list_intersection.
      apply list_intersection_equiv.
    Defined.
  End IntersectionEnumerable.

  Section SetminusEnumerable.
    Variable X Y : Ensemble name.
    Context `{enumX : enumerable _ X} `{enumY : enumerable _ Y}.
    Let list_setminus := filter (fun x => negb (in_list_dec x (@enumerate _ Y _))) (@enumerate _ X _).
    Lemma list_setminus_equiv :
      X ∖ Y == from_list list_setminus.
    Proof.
      destruct enumX as [Xl HX]; destruct enumY as [Yl HY].
      unfold list_setminus; clear list_setminus.
      simpl.
      rewrite HX, HY; clear HX HY.
      induction Xl.
      * simpl.
        rewrite setminus_emptyset.
        reflexivity.
      * simpl.
        rewrite union_setminus_distr.
        rewrite IHXl.
        destruct (in_list_dec a Yl) eqn:Ha;
          from_in_list_dec;
          simpl.
        + (* a ∈ Y *)
          rewrite singleton_setminus_in; auto.
          rewrite union_emptyset.
          reflexivity.
        + (* a ∉ Y *)
          rewrite singleton_setminus_not_in; auto.
          reflexivity.
  Qed.
  Instance setminus_enumerable : enumerable (X ∖ Y).
    exists list_setminus.
    apply list_setminus_equiv.
  Defined.
  End SetminusEnumerable.

  Instance empty_enumerable : forall {A}, @enumerable A ∅.
  Proof.
    intros A.
    exists nil. simpl. reflexivity.
  Defined.
  Existing Instance union_enumerable.
  Existing Instance setminus_enumerable.


Class functional_step_relation (S : StateSpace) :=
  { fun_step : state name -> option (event name value) -> Ensemble (option (state name))
  ; fun_step_in : forall σ e τ,
    S ⊢ σ →{e} τ -> τ ∈ fun_step σ e
  ; fun_in_step : forall σ e τ,
    τ ∈ fun_step σ e -> S ⊢ σ →{e} τ
  ; input_list : enumerable (space_input S)
  ; output_list : enumerable (space_output S)
  ; internal_list : enumerable (space_internal S)
  }.
Arguments fun_step S {rel} : rename.
Arguments input_list S {rel} : rename.
Arguments output_list S {rel} : rename.
Arguments internal_list S {rel} : rename.


Instance functional_step_relation_enumerable_domain S `{functional_step_relation S}
    : enumerable (space_domain S).
Proof.
    destruct H. unfold space_domain. typeclasses eauto.
Defined.
    

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

    + intros ? ? ? Hstep y y_neq_z y_not_internal.

      inversion Hstep; try subst; unfold update.
      ++ assert (i <> y).
         { intro. apply (y_neq_z v). subst; auto. }
         reduce_eqb; auto.
      ++ assert (i <> y).
         { intro. apply (y_neq_z v). subst; auto. }
         reduce_eqb; auto.
      ++ compare x y; auto.
         (* x = y *)
            rewrite Heq in y_neq_z.
            specialize (y_neq_z (f σ) eq_refl).
            find_contradiction.

    + intros ? y ? ? Hstep.
      inversion Hstep; try subst; unfold update; simpl;
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

Definition Success {A} (a : A) := Some (Some a).
Definition Failure {A} : option (option A) := Some None.
Definition ERROR {A} : option (option A) := None.
  Context `{decI : in_dec _ I}.
  Definition func_step_fun (σ : state name) (e : option (event name value)) : option (option (state name)) :=
    match e with
    | None => (* No eps transitions *) ERROR
    | Some (Event z v) =>
      if z ∈? I
      then if σ x =? f σ
           then (* func_input_stable *) Success (update σ z v)
           else if f σ =? f (update σ z v)
           then (* func_input_unstable *) Success (update σ z v)
           else (* func_err *) Failure
      else if z =? x
      then if σ x =? f σ
           then (* output cannot transition on stable input *) ERROR
           else if v =? f σ
           then (* func_output *) Success (update σ z v)
           else (* v does not have the correct form *) ERROR
      else (* event ∉ domain(func_space) *) ERROR
      
    end.

  Lemma func_step_equiv : forall σ e τ,
    func_space ⊢ σ →{e} τ <-> func_step_fun σ e = Some τ.
  Proof.
    intros σ e τ. unfold func_step_fun.
    split; intros Hstep.
    * inversion Hstep; subst.
      + destruct (i ∈? I). 2:{ find_contradiction. }
        unfold func_stable in *.
        compare_next.
        reflexivity.
      + destruct (i ∈? I). 2:{ find_contradiction. }
        unfold func_stable in *.
        compare_next.
        reflexivity.
      + destruct (i ∈? I). 2:{ find_contradiction. }
        unfold func_stable in *.
        compare_next.
        reflexivity.
      + destruct (x ∈? I). 1:{ find_contradiction. }
        unfold func_stable in *.
        reduce_eqb.
        reflexivity.
    * destruct e as [[z v] | ]; [ | inversion Hstep].
      destruct (z ∈? I).
      { compare_next.
        { rewrite Heq in Hstep. reduce_eqb.
          inversion Hstep; subst.
          apply func_input_stable; auto.
        }
        compare_next.
        { rewrite Heq in Hstep. reduce_eqb.
          inversion Hstep; subst.
          apply func_input_unstable; auto.
        }
        inversion Hstep; subst.
        { apply func_err; auto. }
      }
      compare_next.
      compare_next.
      { rewrite Heq in Hstep; reduce_eqb. }
      compare_next.
      inversion Hstep.
      apply func_output; auto.
  Qed.


  Variable EnumerableI : enumerable I.

Print functional_step_relation.
  Program Instance func_step_functional : functional_step_relation func_space :=
    {| fun_step := fun σ e =>
        match func_step_fun σ e with
        | None => ∅
        | Some τ => singleton τ
        end
(*     ; fun_step_equiv := func_step_equiv *)
     ; input_list := EnumerableI
     ; output_list := singleton_enumerable x
     ; internal_list := empty_enumerable
    |}.
  Next Obligation.
    apply func_step_equiv in H.
    rewrite H.
    solve_set.
  Qed.
  Next Obligation.
    apply func_step_equiv.
    destruct (func_step_fun σ e); decompose_set_structure.
  Qed.

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

  - intros ? ? ? ? Hstep.
    inversion Hstep; subst.
    + eapply wf_update0; eauto.
    + eapply wf_update1; eauto.
    + eapply wf_update0; eauto.
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

  Print union_step.

  Definition event_in_b (X : Ensemble name) `{in_dec _ X} (e : option (event name value)) :=
    match e with
    | None => false
    | Some (Event x v) => if x ∈? X then true else false
    end.
Print functional_step_relation.


  Context `{S1_functional : functional_step_relation S1}
          `{S2_functional : functional_step_relation S2}
          `{S_enumerable : enumerable _ (space_domain S1 ∩ space_domain S2)}.
(*
  Context `{S1_input_dec : in_dec _ (space_input S1)}.
  Context `{S2_input_dec : in_dec _ (space_input S2)}.
  Context `{S1_output_dec : in_dec _ (space_output S1)}.
  Context `{S2_output_dec : in_dec _ (space_output S2)}.
  Context `{S1_internal_dec : in_dec _ (space_internal S1)}.
  Context `{S2_intneral_dec : in_dec _ (space_internal S2)}.
*)
  Context `{S1_wf : well_formed S1} `{S2_wf : well_formed S2}.


  Fixpoint states_equiv_on (l : list name) (σ1 σ2 : state name) : bool :=
    match l with
    | nil => true
    | x  :: l' => if σ1 x =? σ2 x then states_equiv_on l' σ1 σ2
                  else false
    end.
About enumerable.
  Arguments enumerate {A} X.

  Definition join_option_state (τ1 τ2 : option (option (state name))) : option (option (state name)) :=
    match τ1, τ2 with
    | None, _ => None
    | _, None => None
    | Some None, _ => Some None
    | _, Some None => Some None
    | Some (Some σ1), Some (Some σ2) =>
      if states_equiv_on (enumerate (space_domain S1 ∩ space_domain S2) S_enumerable) σ1 σ2
      then Some (Some (fun x => if x ∈? space_domain S1
                                then σ1 x
                                else σ2 x))
      else None (* failure if not consistent across states *)
    end.


Ltac solve_event_in :=
  match goal with
  | [ H : in_list_dec ?x (enumerate (space_input ?S) (input_list ?S)) = true
    , S_functional : functional_step_relation ?S
    |- event_in (space_input ?S) (Some (Event ?x _)) ] =>
    constructor;
    from_in_list_dec;
    rewrite <- (@as_list_equiv _ (space_input S)) in *;
    auto
  | [ H : in_list_dec ?x (enumerate (space_output ?S) (output_list ?S)) = true
    , S_functional : functional_step_relation ?S
    |- event_in (space_output ?S) (Some (Event ?x _)) ] =>
    constructor;
    from_in_list_dec;
    rewrite <- (@as_list_equiv _ (space_output S) ) in *;
    auto
  end.

(*
  Definition dec_union_input_event : forall e,
    union_input_event e + {~ event_in (space_domain S1) e} + {~ event_in (space_domain S2) e}.
  Proof.
    destruct e as [[x v] | ].
    2:{ right. inversion 1. }
      assert (decompose1 : x ∈ space_input S1 ∪ space_output S1 ->
              x ∉ space_input S2 ∪ space_output S2 ->
              ~ event_in (space_domain S2) (Some (Event x v))).
      { intros H1 H2.
        inversion 1; subst.
        unfold space_domain in *.
        decompose_set_structure;
          contradict wires2_disjoint;
          intros [Hdisjoint];
          apply (Hdisjoint x);
          solve_set.
      }
     assert (decompose2 : x ∉ space_input S1 ∪ space_output S1 ->
              x ∈ space_input S2 ∪ space_output S2 ->
              ~ event_in (space_domain S1) (Some (Event x v))).
      { intros H1 H2.
        inversion 1; subst.
        unfold space_domain in *.
        decompose_set_structure;
          contradict wires1_disjoint;
          intros [Hdisjoint];
          apply (Hdisjoint x);
          solve_set.
      }
    destruct (in_list_dec x (enumerate (space_input S1) (input_list S1)))
      eqn:Hin1;
    destruct (in_list_dec x (enumerate (space_input S2) (input_list S2)))

      eqn:Hin2.
    { (* x ∈ input(S1) ∩ input(S2) *)
      left. left. apply driven_by_env; solve_event_in. 
    }
    { (* x ∈ input S1, x ∉ input S2 *)
      destruct (in_list_dec x (enumerate (space_output S2) (@output_list S2 S2_functional)))
        eqn:Hout2.
      { (* x ∈ output S2 *)
        left. left. apply driven_by_2; solve_event_in.
      }
      { (* x ∉ dom S2 *)
        right. 
        from_in_list_dec;
        erewrite <- as_list_equiv in Hin1;
        erewrite <- as_list_equiv in Hin2;
        erewrite <- as_list_equiv in Hout2.

        apply decompose1; solve_set.
      }
    }
    { (* x ∉ input S1, x ∈ input S2 *)
      destruct (in_list_dec x (enumerate (space_output S1) (@output_list S1 S1_functional)))
        eqn:Hout1.
      { (* x ∈ output S1 *)
        left. left. apply driven_by_1; solve_event_in.
      }
      { (* x ∉ dom S1 *)
        left. right. 
        from_in_list_dec;
        erewrite <- as_list_equiv in Hin1;
        erewrite <- as_list_equiv in Hin2;
        erewrite <- as_list_equiv in Hout1.
        apply decompose2; solve_set.
      }
    }
    (* x ∉ input S1, x ∉ input S2 *)
    destruct (in_list_dec x (enumerate (space_output S1) (@output_list S1 S1_functional)))
        eqn:Hout1.
    { (* x ∈ output S1, so x ∉ dom S2 *)
      right.
        from_in_list_dec;
        erewrite <- as_list_equiv in Hin1;
        erewrite <- as_list_equiv in Hin2;
        erewrite <- as_list_equiv in Hout1;
        apply decompose1; try solve_set.
        intros Hout2. decompose_set_structure.
    }
    destruct (in_list_dec x (enumerate (space_output S2) (@output_list S2 S2_functional)))
        eqn:Hout2.
    { (* x ∈ output S2, so x ∉ dom S1 *)
      left. right.
        from_in_list_dec;
        erewrite <- as_list_equiv in Hin1;
        erewrite <- as_list_equiv in Hin2;
        erewrite <- as_list_equiv in Hout1;
        erewrite <- as_list_equiv in Hout2;
        apply decompose2; try solve_set.
    }
    destruct (in_list_dec x (enumerate (space_internal S1) (@internal_list S1 S1_functional)))
        eqn:Hint1.
    { (* x ∈ internal S1, so x ∉ dom S2 *)
      right.
        from_in_list_dec;
        erewrite <- as_list_equiv in Hin1;
        erewrite <- as_list_equiv in Hin2;
        erewrite <- as_list_equiv in Hout1;
        erewrite <- as_list_equiv in Hout2;
        erewrite <- as_list_equiv in Hint1.
        unfold space_domain. inversion 1; subst.
        find_contradiction.
    }
    { (* x ∉ dom S1 *)
      left. right.
        from_in_list_dec;
        erewrite <- as_list_equiv in Hin1;
        erewrite <- as_list_equiv in Hin2;
        erewrite <- as_list_equiv in Hout1;
        erewrite <- as_list_equiv in Hout2;
        erewrite <- as_list_equiv in Hint1.
        unfold space_domain. inversion 1; subst.
        decompose_set_structure.
    }        
  Defined.
*)

  Fixpoint equiv_on_list' (l : list name) (σ : state name) : Ensemble (state name) :=
    match l with
    | nil => fun σ' => True
    | x :: l' => fun σ' => if σ' x =? σ x
                           then equiv_on_list' l' σ σ'
                           else False
    end.
  Definition equiv_on_list l σ (τ : option (state name)) : Prop :=
             match τ with
             | None => False
             | Some σ' => equiv_on_list' l σ σ'
             end.

  Lemma state_equiv_on_implies_list : forall (A : list name) σ τ,
    state_equiv_on (from_list A) (Some σ) τ ->
    τ ∈ equiv_on_list A σ.
  Proof.
    induction A as [ | a A];
      intros σ τ Hequiv.
    * simpl in Hequiv.
      destruct τ; find_contradiction.
      constructor.
    * simpl in Hequiv.
      unfold equiv_on_list, equiv_on_list'. fold equiv_on_list'.
      unfold Coq.Sets.Ensembles.In.
      destruct τ as [ σ' | ]; find_contradiction.
      rewrite Hequiv; [ | solve_set].
      reduce_eqb.
      assert (IH : Some σ' ∈ equiv_on_list A σ).
      { apply IHA.
        unfold state_equiv_on.
        intros x Hx.
        apply Hequiv. solve_set.
      }
      apply IH.
  Qed.

  Lemma equiv_on_list_implies_state_equiv_on : forall (A : list name) σ τ,
    τ ∈ equiv_on_list A σ ->
    state_equiv_on (from_list A) (Some σ) τ.
  Proof.
    induction A; intros σ τ Hequiv;
      unfold Coq.Sets.Ensembles.In in Hequiv.
    * destruct τ as [σ' | ].
      2:{ inversion Hequiv. }
      { simpl. intros x Hx. find_contradiction. }
    * destruct τ as [σ' | ]; [ | inversion Hequiv].
      simpl in Hequiv.
      intros x Hx. simpl in Hx.
      compare_next. rewrite Heq in Hequiv. reduce_eqb.
      decompose_set_structure.
      specialize (IHA σ (Some σ')).
      unfold state_equiv_on in IHA.
      apply IHA; auto.
  Qed.


  Definition union_step_fun (σ : state name) (e : option (event name value))
        : Ensemble (option (state name)) :=
    match e with
    | None =>
       (fun_step S1 σ None ∩ equiv_on_list (enumerate (space_domain S2) _) σ)
    ∪ (fun_step S2 σ None ∩ equiv_on_list (enumerate (space_domain S1) _) σ) 
    | Some (Event x v) =>
      (* NOTE: we can make assumptions about the well-formedness of S1 ∪ S2
         because we have assumed these facts. *)
      if andb (in_list_dec x (enumerate (space_domain S1) _))
              (in_list_dec x (enumerate (space_domain S2) _))
      then fun_step S1 σ e ∩ fun_step S2 σ e
      else if in_list_dec x (enumerate (space_domain S1) _)
      then (fun_step S1 σ e) ∩ (equiv_on_list (enumerate (space_domain S2) _) σ)
      else if in_list_dec x (enumerate (space_domain S2) _)
      then (fun_step S2 σ e) ∩ (equiv_on_list (enumerate (space_domain S1) _) σ)
      else (* singleton None *) ∅
    end.

Require Export Setoid.
About state_equiv_on.
  Add Parametric Morphism : state_equiv_on
    with signature (Same_set name) ==> (@eq (option (state name)))
                                   ==> (@eq (option (state name))) ==> iff
    as state_equiv_on_equiv.
  Proof.
    intros X Y HXY τ τ'.
    split; intros Hequiv.
    * Print state_equiv_on. 
      destruct τ as [σ | ]; destruct τ' as [σ' | ]; try inversion Hequiv.
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

Ltac compare_next_in_list_dec :=
  match goal with
  | [ Hstep : ?S ⊢ _ →{Some (Event ?x _)} _
    |- context[ in_list_dec ?x (enumerate (space_domain ?S) _) ] ]=>
    let Hin := fresh "Hin" in
    assert (Hin : x ∈ space_domain S)
      by (apply wf_space in Hstep;
           [unfold space_domain; solve_set | auto]);
    rewrite as_list_equiv in Hin;
    to_in_list_dec;
    rewrite Hin;
    clear Hin;
    simpl
  | [ Hevent : ~ event_in ?X (Some (Event ?x _))
    |- context[ in_list_dec ?x (enumerate ?X _) ] ] =>
    let Hin := fresh "Hin" in
    assert (Hin : x ∉ X)
      by (intro; contradict Hevent; constructor; auto);
    rewrite as_list_equiv in Hin;
    to_in_list_dec;
    rewrite Hin;
    clear Hin;
    simpl
  end.

  Lemma union_implies_union_step_fun : forall σ e τ,
    union ⊢ σ →{e} τ -> τ ∈ union_step_fun σ e.
  Proof.
    intros σ e τ Hstep.
    inversion Hstep; subst;
      repeat match goal with
      | [ H : S1 ⊢ _ →{_} _ |- _ ] => rename H into Hstep1
      | [ H : S2 ⊢ _ →{_} _ |- _ ] => rename H into Hstep2
      end;
      try match goal with
      | [ H : state_equiv_on (space_domain _) (Some _) ?τ |- _ ] =>
        let σ' := fresh "σ'" in
        destruct τ as [ σ' | ]; [ | find_contradiction]
      end.

    * unfold union_step_fun.

      destruct e as [[x v] | ].
      2:{ left.
          constructor.
          { apply (@fun_step_in _ S1_functional); auto. }
          { apply state_equiv_on_implies_list.
            rewrite <- as_list_equiv; auto.
          }
      }
      { 
    
        compare_next_in_list_dec.
        compare_next_in_list_dec.
        split.
        { apply fun_step_in; auto. }
        { apply state_equiv_on_implies_list.
          rewrite <- as_list_equiv; auto.
        }
      }


    * unfold union_step_fun.
      destruct e as [[x v] | ].
      2:{ right.
          split.
          { apply fun_step_in; auto. }
          { apply state_equiv_on_implies_list.
            rewrite <- as_list_equiv; auto.
          }
      }
      compare_next_in_list_dec.
      compare_next_in_list_dec.
      split.
      { apply fun_step_in; auto. }
      { apply state_equiv_on_implies_list.
        rewrite <- as_list_equiv; auto.
      }

    * (*rename H3 into Hstep2.*)

      destruct e as [[x v] | ]; simpl.
      2:{ (* contradiction *)
          repeat match goal with
          | [ H : union_input_event None |- _ ] => inversion H; clear H
          | [ H : event_in _ None |- _ ] => inversion H; fail
          end.
      }
      compare_next_in_list_dec.
      compare_next_in_list_dec.
      split; apply fun_step_in; auto.
  Qed.

  Lemma in_join_domain_implies_union_input_event : forall x v,
    x ∈ space_domain S1 ->
    x ∈ space_domain S2 ->
    union_input_event (Some (Event x v)).
  Proof.
    intros x v Hx1 Hx2.
    unfold space_domain in Hx1, Hx2.
    destruct (x ∈? from_list (enumerate (space_output S1) (output_list S1)))
      as  [Houtput1 | Houtput1];
    rewrite <- as_list_equiv in Houtput1.
    { (* x ∈ output S1 *)
      (* it must also be the case that x ∈ input S2 *)
      apply driven_by_1; constructor; auto.
      decompose_set_structure.
    }
    assert (Hx1' : x ∈ space_input S1).
    { decompose_set_structure; auto.
      { contradict wires1_disjoint.
        intros [Hdisjoint].
        apply (Hdisjoint x).
        unfold space_domain.
        solve_set.
      }
      { contradict wires1_disjoint.
        intros [Hdisjoint].
        apply (Hdisjoint x).
        unfold space_domain.
        solve_set.
      }
    }
    destruct (x ∈? from_list (enumerate (space_output S2) (output_list S2)))
      as  [Houtput2 | Houtput2];
    rewrite <- as_list_equiv in Houtput2.
    { (* x ∈ output S2 *)
      (* it must also be the case that x ∈ input S1 *)
      apply driven_by_2; constructor; auto.
    }
    assert (Hx2' : x ∈ space_input S2).
    { decompose_set_structure; auto. }

    apply driven_by_env; constructor; auto.
  Qed.

  Lemma union_step_fun_implies_union : forall σ e τ,
    τ ∈ union_step_fun σ e ->
    union ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hstep.
    unfold union_step_fun in Hstep.
    destruct e as [[x v] | ].
    2:{ decompose_set_structure.
        + apply union_step_1.
          { inversion 1. }
          { apply fun_in_step; auto. }
          { Search state_equiv_on.
            rewrite as_list_equiv.
            apply equiv_on_list_implies_state_equiv_on; auto.
          }
            
        + apply union_step_2.
          { inversion 1. }
          { apply fun_in_step; auto. }
          { rewrite as_list_equiv.
            apply equiv_on_list_implies_state_equiv_on; auto.
          }

    }
    { destruct (in_list_dec x
                 (enumerate (space_domain S1) (functional_step_relation_enumerable_domain S1)))
        eqn:Hx1;
      destruct (in_list_dec x
                 (enumerate (space_domain S2) (functional_step_relation_enumerable_domain S2)))
        eqn:Hx2;
      from_in_list_dec;
      rewrite <- as_list_equiv in Hx1;
      rewrite <- as_list_equiv in Hx2;
      simpl in Hstep.
      + decompose_set_structure.
        Print union_step.
        apply union_communicate; try (apply fun_in_step; auto; fail).
        { apply in_join_domain_implies_union_input_event; auto. }

      + decompose_set_structure.
        apply union_step_1.
        { inversion 1; subst. find_contradiction. }
        { apply fun_in_step; auto. }
        { rewrite as_list_equiv.
          apply equiv_on_list_implies_state_equiv_on; auto.
        }
      + decompose_set_structure.
        apply union_step_2.
        { inversion 1; subst. find_contradiction. }
        { apply fun_in_step; auto. }
        { rewrite as_list_equiv.
          apply equiv_on_list_implies_state_equiv_on; auto.
        }
      + find_contradiction.

  }
  Qed.

(*
  Lemma dec_union_input_event3 : forall 
    ~ event_in (space_domain S2) e ->
    dec_union_input_event e = inright pf.
  Admitted.
  Lemma union_step_fun_implies_union : forall σ e τ,
    union_step_fun σ e = Some τ ->
    union ⊢ σ →{e} τ.
  Admitted.
*)


  Instance union_functional : functional_step_relation union :=
  {| fun_step := union_step_fun |}.
  3:{ destruct S1_functional, S2_functional.
      typeclasses eauto.
    }
  3:{ destruct S1_functional, S2_functional.
      typeclasses eauto. }
  3:{ destruct S1_functional, S2_functional.
      typeclasses eauto. }
  { apply union_implies_union_step_fun. }
  { apply union_step_fun_implies_union. }
  Defined.


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

    + intros ? ? ? ? Hstep.
      inversion Hstep; try subst; unfold update; reduce_eqb; auto.
      ++ rewrite H4. unfold update. reduce_eqb; auto.
      ++ rewrite H5. unfold update. reduce_eqb; auto.
      ++ rewrite H7. unfold update.
         repeat my_subst. reduce_eqb.
         compare_next; auto.
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

  Lemma union_internal_inversion_right : forall (S1 S2 : StateSpace name) σ x v σ',
      well_formed S1 ->
      well_formed S2 ->
      space_internal S1 ⊥ space_domain S2 ->
      space_domain S1 ⊥ space_internal S2 ->
      (S1 ∥ S2) ⊢ σ →{ Some (Event x v)} Some σ' ->
      x ∉ space_domain S2 ->
      forall y, y ∈ space_internal S2 ->
                σ' y = σ y.
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
      y <> o ->
      σ' y = σ y.
  Proof.
    intros ? ? ? ? ? ? ? ? Hstep Hneq.
    inversion Hstep; subst; unfold update;
      compare_next; auto.
  Qed.

  Ltac step_inversion_1 :=
  match goal with
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
        simpl. econstructor; eauto.
      }
      compare x (transition_name t); auto.
      contradiction (He (transition_update_value t (σ (transition_name t)))); auto.

    * intros ? ? ? ? Hstep.
      inversion Hstep; subst.
      unfold update; simpl.
      reduce_eqb. auto.
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
