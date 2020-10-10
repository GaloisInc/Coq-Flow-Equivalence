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

  Definition state_equiv_on (X : Ensemble name) (τ1 τ2 : option (state name)) :=
      match τ1, τ2 with
      | Some σ1, Some σ2 => forall x, x ∈ X -> σ1 x = σ2 x
      | None, None => True
      | _, _ => False
      end.


  Require Export Setoid.
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

  Ltac decompose_state_equiv_on :=
  match goal with
  | [ H : ?τ ∈ state_equiv_on _ (Some _) |- _ ] =>
    let σ' := fresh "σ'" in
    destruct τ as [σ' | ];
    [ | inversion H; fail]
  | [ H : ?τ ∈ state_equiv_on _ None |- _ ] =>
    let σ' := fresh "σ'" in
    destruct τ as [σ' | ];
    [ inversion H; fail | ]
  | [ H : ?τ ∈ singleton None |- _ ] => inversion H

  | [ H :  state_equiv_on _ (Some _) ?τ |- _ ] =>
    let σ' := fresh "σ'" in
    destruct τ as [σ' | ];
    [ | inversion H; fail]
  | [ H : state_equiv_on _ None ?τ |- _ ] =>
    let σ' := fresh "σ'" in
    destruct τ as [σ' | ];
    [ inversion H; fail | ]

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

  Class enumerable {A} (X : Ensemble A) :=
    { enumerate : list A
    ; rewrite_enumerate : X == from_list enumerate
    }.
  Arguments enumerate {A} X {enumX} : rename.
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

About enumerate.


  Ltac rewrite_in_list_dec :=
    match goal with
    | [ H : ?x ∈ from_list ?l |- context[ in_list_dec ?x ?l ] ] =>
      replace (in_list_dec x l) with true in *
      by (to_in_list_dec; rewrite H; auto)
    | [ H : ?x ∈ from_list ?l, H' : context[ in_list_dec ?x ?l ] |- _ ] =>
      replace (in_list_dec x l) with true in *
      by (to_in_list_dec; rewrite H; auto)
    | [ H : ?x ∈ ?X |- context[ in_list_dec ?x (enumerate ?X) ] ] =>
      replace (in_list_dec x (enumerate X)) with true in *
      by (rewrite (@rewrite_enumerate _ X) in H;
          to_in_list_dec;
          rewrite H;
          auto)
    | [ H : ?x ∈ ?X, H' : context[ in_list_dec ?x (enumerate ?X) ] |- _ ] =>
      replace (in_list_dec x (enumerate X)) with true in *
      by (rewrite (@rewrite_enumerate _ X) in H;
          to_in_list_dec;
          rewrite H;
          auto)

    | [ H : ?x ∉ from_list ?l |- context[ in_list_dec ?x ?l ] ] =>
      replace (in_list_dec x l) with false in *
      by (to_in_list_dec; rewrite H; auto)
    | [ H : ?x ∉ from_list ?l, H' : context[ in_list_dec ?x ?l ] |- _ ] =>
      replace (in_list_dec x l) with false in *
      by (to_in_list_dec; rewrite H; auto)
    | [ H : ?x ∉ ?X |- context[ in_list_dec ?x (enumerate ?X) ] ] =>
      replace (in_list_dec x (enumerate X)) with false in *
      by (rewrite (@rewrite_enumerate _ X) in H;
          to_in_list_dec;
          rewrite H;
          auto)
    | [ H : ?x ∉ ?X, H' : context[ in_list_dec ?x (enumerate ?X) ] |- _ ] =>
      replace (in_list_dec x (enumerate X)) with false in *
      by (rewrite (@rewrite_enumerate _ X) in H;
          to_in_list_dec;
          rewrite H;
          auto)
    end.

Ltac deduce_in_domain S :=
  match goal with
  | [ Hstep : S ⊢ _ →{ Some (Event ?x _)} _ |- _ ] =>
    assert (x ∈ space_domain S)
      by (unfold space_domain;
          apply wf_space in Hstep; auto;
          solve_set)
  | [ He : ~ event_in (space_domain S) (Some (Event ?x _)) |- _ ] =>
    assert (x ∉ space_domain S)
      by (intro; apply He; constructor; assumption)
  | [ He : event_in (space_domain S) (Some (Event ?x _)) |- _ ] =>
    assert (x ∈ space_domain S)
      by (inversion He; auto)
  end.

  Ltac compare_next_in_list_dec :=
  match goal with
  | [ Hstep : ?S ⊢ _ →{Some (Event ?x _)} _
    |- context[ in_list_dec ?x (enumerate (space_domain ?S) _) ] ]=>
    let Hin := fresh "Hin" in
    assert (Hin : x ∈ space_domain S)
      by (apply wf_space in Hstep;
           [unfold space_domain; solve_set | auto]);
    rewrite rewrite_enumerate in Hin;
    to_in_list_dec;
    rewrite Hin;
    clear Hin;
    simpl
  | [ Hevent : ~ event_in ?X (Some (Event ?x _))
    |- context[ in_list_dec ?x (enumerate ?X _) ] ] =>
    let Hin := fresh "Hin" in
    assert (Hin : x ∉ X)
      by (intro; contradict Hevent; constructor; auto);
    rewrite rewrite_enumerate in Hin;
    to_in_list_dec;
    rewrite Hin;
    clear Hin;
    simpl
  end.



  Section IntersectionEnumerable.

    Variable X Y : Ensemble name.
    Context `{enumX : enumerable _ X} `{enumY : enumerable _ Y}.
    Definition list_intersection (A B : list name) := filter (fun x => in_list_dec x B) A.
    Lemma list_intersection_equiv :
      X ∩ Y == from_list (list_intersection (enumerate X) (enumerate Y)).
    Proof.
      destruct enumX as [Xl HX]; destruct enumY as [Yl HY].
      unfold list_intersection.
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
      exists (list_intersection (enumerate X) (enumerate Y)).
      apply list_intersection_equiv.
    Defined.
  End IntersectionEnumerable.

  Section SetminusEnumerable.
    Variable X Y : Ensemble name.
    Context `{enumX : enumerable _ X} `{enumY : enumerable _ Y}.

Print filter.
    Fixpoint better_filter {A : Type} (f : A -> bool) (l : list A) :=
      match l with
      | nil => nil
      | x :: l0 => (if f x then x::nil else nil) ++ better_filter f l0
      end.
  Lemma filter_false : forall {X} (l : list X),
    better_filter (fun _ => false) l = nil.
  Proof.
    induction l; auto.
  Qed.

    Definition list_setminus lX lY :=
      better_filter (fun x => negb (in_list_dec x lY)) lX.
    Lemma list_setminus_equiv :
      X ∖ Y == from_list (list_setminus (enumerate X) (enumerate Y)).
    Proof.
      destruct enumX as [Xl HX]; destruct enumY as [Yl HY].
      unfold list_setminus.
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
    exists (list_setminus (enumerate X) (enumerate Y)).
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
  ; input_list : enumerable (space_input S)
  ; output_list : enumerable (space_output S)
  ; internal_list : enumerable (space_internal S)
  }.
Arguments fun_step S {functional_step_relation}.
Class functional_step_relation_correct (S : StateSpace) `{functional_step_relation S} :=
  { fun_step_in : forall σ e τ,
    S ⊢ σ →{e} τ -> τ ∈ fun_step S σ e
  ; fun_in_step : forall σ e τ,
    τ ∈ fun_step S σ e -> S ⊢ σ →{e} τ
  }.
Arguments fun_step S {rel} : rename.
Arguments input_list S {rel} : rename.
Arguments output_list S {rel} : rename.
Arguments internal_list S {rel} : rename.


Instance functional_step_relation_enumerable_domain S `{H : functional_step_relation S}
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
(*    σ i <> v -> *) (* Question: what happens if an event occurs that doesn't change the value of the variable? Is it allowed? Is it a no-op? *)
    state_equiv_on (from_list I ∪ singleton x) (Some (update σ i v)) (Some σ') ->
    func_step σ (Some (Event i v))
                (Some σ')

  | func_input_unstable i (pf_i : i ∈ from_list I) v σ' :
    ~ (func_stable σ) ->
(*    ~ (func_stable (update σ i v)) -> (* in a binary system, this is ok *)*)
    f σ = f (update σ i v) -> (* ok to update input in an unstable system if the output doesn't change *)
    state_equiv_on (from_list I ∪ singleton x) (Some (update σ i v))  (Some σ') ->
    func_step σ (Some (Event i v)) (Some σ')


  (* if input updates in an unstable system causes output to change, go to error state*)
  | func_err i (pf_i : i ∈ from_list I) v :
    ~ (func_stable σ) ->
    f σ <> f (update σ i v) -> 
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

Definition Success {A} (a : A) := Some (Some a).
Definition Failure {A} : option (option A) := Some None.
Definition ERROR {A} : option (option A) := None.

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
        intros y Hy.
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
      { simpl. intros y Hx. find_contradiction. }
    * destruct τ as [σ' | ]; [ | inversion Hequiv].
      simpl in Hequiv.
      intros y Hx. simpl in Hx.
      compare_next. rewrite Heq in Hequiv. reduce_eqb.
      decompose_set_structure.
      specialize (IHA σ (Some σ')).
      unfold state_equiv_on in IHA.
      apply IHA; auto.
  Qed.



(*
  Definition update_on D σ x v : Ensemble (option (state name)) :=
    state_equiv_on D (Some (update σ x v)).
*)


  Definition func_step_fun (σ : state name) (e : option (event name value))
    : Ensemble (option (state name)) :=
    match e with
    | None => (* No eps transitions *) ∅
    | Some (Event z v) =>
      if in_list_dec z I
      then if σ x =? f σ
           then (* func_input_stable *) equiv_on_list (x::I) (update σ z v)
           else if f σ =? f (update σ z v)
           then (* func_input_unstable *) equiv_on_list (x::I) (update σ z v)
           else (* func_err *) singleton None
      else if z =? x
      then if σ x =? f σ
           then (* output cannot transition on stable input *) ∅
           else if v =? f σ
           then (* func_output *) equiv_on_list (x::I) (update σ z v)
           else (* v does not have the correct form *) ∅
      else (* event ∉ domain(func_space) *) ∅
      
    end.

Require Import Coq.Logic.FunctionalExtensionality.

  Lemma func_step_in : forall σ e τ,
    func_space ⊢ σ →{e} τ ->
    τ ∈ func_step_fun σ e.
  Proof.
    intros σ e τ Hstep.
    unfold func_step_fun.
    assert (Heq : from_list I ∪ singleton x == from_list (x::I)).
    { simpl. split; intros y Hy; decompose_set_structure; solve_set. }

    inversion Hstep; subst.
    * rewrite_in_list_dec.
      compare_next; auto.
      apply state_equiv_on_implies_list.
      rewrite <- Heq; auto.
    * rewrite_in_list_dec.
      compare_next; auto.
      apply state_equiv_on_implies_list.
      rewrite <- Heq; auto.
    * rewrite_in_list_dec.
      compare_next; auto.
      solve_set.
    * destruct (x ∈? from_list I) as [pf_i | pf_i ].
      { find_contradiction. }
      { rewrite_in_list_dec. reduce_eqb. compare_next; auto. 
        apply state_equiv_on_implies_list.
        rewrite <- Heq; auto.
      }
  Qed.

Ltac compare_next_in :=
  match goal with
  | [ |- context[ ?x ∈? ?X ] ] => destruct (x ∈? X)
  | [ H : context[ ?x ∈? ?X ] |- _ ] => destruct (x ∈? X)
  end.




  Lemma func_in_step : forall σ e τ,
    τ ∈ func_step_fun σ e ->
    func_space ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hin.
    unfold func_step_fun in Hin.
    assert (HxI : from_list I ∪ singleton x == from_list (x::I)).
    { simpl. split; intros y Hy; decompose_set_structure; solve_set. }
    destruct e as [[y v] | ]; [ | find_contradiction].
    destruct (y ∈? from_list I) as [Hy | Hy].
    { rewrite_in_list_dec.
      compare_next.
      { rewrite Heq in Hin. reduce_eqb.
        apply equiv_on_list_implies_state_equiv_on in Hin.
        decompose_state_equiv_on.
        apply func_input_stable; auto.
        rewrite HxI; auto.
      }
      compare_next.
      { rewrite Heq in Hin. reduce_eqb.
        apply equiv_on_list_implies_state_equiv_on in Hin.
        decompose_state_equiv_on.
        apply func_input_unstable; auto.
        rewrite HxI; auto.
      }
      { decompose_state_equiv_on. 
        apply func_err; auto.
      }
    }
    { rewrite_in_list_dec.
      compare_next.
      compare_next.
      { rewrite Heq in Hin; reduce_eqb. }
      compare_next.
      apply equiv_on_list_implies_state_equiv_on in Hin.
      decompose_state_equiv_on.
      apply func_output; auto.
      rewrite HxI; auto.
    }
  Qed.


  Program Instance func_functional : functional_step_relation func_space :=
    {| fun_step := func_step_fun |}.
  Instance func_functional_correct : functional_step_relation_correct func_space :=
  {| fun_step_in := func_step_in
   ; fun_in_step := func_in_step
   |}.

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


  Definition event_in_b (X : Ensemble name) `{in_dec _ X} (e : option (event name value)) :=
    match e with
    | None => false
    | Some (Event x v) => if x ∈? X then true else false
    end.


  Context `{S1_functional : functional_step_relation S1}
          `{S2_functional : functional_step_relation S2}
          `{S_enumerable : enumerable _ (space_domain S1 ∩ space_domain S2)}.
  Context `{S1_wf : well_formed S1} `{S2_wf : well_formed S2}.


  Fixpoint states_equiv_on (l : list name) (σ1 σ2 : state name) : bool :=
    match l with
    | nil => true
    | x  :: l' => if σ1 x =? σ2 x then states_equiv_on l' σ1 σ2
                  else false
    end.
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
    rewrite <- (@rewrite_enumerate _ (space_input S)) in *;
    auto
  | [ H : in_list_dec ?x (enumerate (space_output ?S) (output_list ?S)) = true
    , S_functional : functional_step_relation ?S
    |- event_in (space_output ?S) (Some (Event ?x _)) ] =>
    constructor;
    from_in_list_dec;
    rewrite <- (@rewrite_enumerate _ (space_output S) ) in *;
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
        erewrite <- rewrite_enumerate in Hin1;
        erewrite <- rewrite_enumerate in Hin2;
        erewrite <- rewrite_enumerate in Hout2.

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
        erewrite <- rewrite_enumerate in Hin1;
        erewrite <- rewrite_enumerate in Hin2;
        erewrite <- rewrite_enumerate in Hout1.
        apply decompose2; solve_set.
      }
    }
    (* x ∉ input S1, x ∉ input S2 *)
    destruct (in_list_dec x (enumerate (space_output S1) (@output_list S1 S1_functional)))
        eqn:Hout1.
    { (* x ∈ output S1, so x ∉ dom S2 *)
      right.
        from_in_list_dec;
        erewrite <- rewrite_enumerate in Hin1;
        erewrite <- rewrite_enumerate in Hin2;
        erewrite <- rewrite_enumerate in Hout1;
        apply decompose1; try solve_set.
        intros Hout2. decompose_set_structure.
    }
    destruct (in_list_dec x (enumerate (space_output S2) (@output_list S2 S2_functional)))
        eqn:Hout2.
    { (* x ∈ output S2, so x ∉ dom S1 *)
      left. right.
        from_in_list_dec;
        erewrite <- rewrite_enumerate in Hin1;
        erewrite <- rewrite_enumerate in Hin2;
        erewrite <- rewrite_enumerate in Hout1;
        erewrite <- rewrite_enumerate in Hout2;
        apply decompose2; try solve_set.
    }
    destruct (in_list_dec x (enumerate (space_internal S1) (@internal_list S1 S1_functional)))
        eqn:Hint1.
    { (* x ∈ internal S1, so x ∉ dom S2 *)
      right.
        from_in_list_dec;
        erewrite <- rewrite_enumerate in Hin1;
        erewrite <- rewrite_enumerate in Hin2;
        erewrite <- rewrite_enumerate in Hout1;
        erewrite <- rewrite_enumerate in Hout2;
        erewrite <- rewrite_enumerate in Hint1.
        unfold space_domain. inversion 1; subst.
        find_contradiction.
    }
    { (* x ∉ dom S1 *)
      left. right.
        from_in_list_dec;
        erewrite <- rewrite_enumerate in Hin1;
        erewrite <- rewrite_enumerate in Hin2;
        erewrite <- rewrite_enumerate in Hout1;
        erewrite <- rewrite_enumerate in Hout2;
        erewrite <- rewrite_enumerate in Hint1.
        unfold space_domain. inversion 1; subst.
        decompose_set_structure.
    }        
  Defined.
*)


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

  Instance union_functional : functional_step_relation union :=
  {| fun_step := union_step_fun |}.
  { set (enum_in_1 := input_list S1).
    set (enum_in_2 := input_list S2).
    set (enum_out_1 := output_list S1).
    set (enum_out_2 := output_list S2).
    typeclasses eauto.
  }
  { set (enum_out_1 := output_list S1).
    set (enum_out_2 := output_list S2).
    typeclasses eauto.
  }
  { set (enum_int_1 := internal_list S1).
    set (enum_int_2 := internal_list S2).
    typeclasses eauto.
  }
  Defined.

  Context `{S1_functional_correct : @functional_step_relation_correct S1 S1_functional}
          `{S2_functional_correct : @functional_step_relation_correct S2 S2_functional}.



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
            rewrite <- rewrite_enumerate; auto.
          }
      }
      { assert (x ∈ space_domain S1).
        { unfold space_domain.
          apply wf_space in Hstep1; auto.
          solve_set.
        }
        rewrite_in_list_dec; simpl.
        assert (x ∉ space_domain S2).
        { intro. contradict H1. constructor; auto. }
        rewrite_in_list_dec; simpl.
        split.
        { apply fun_step_in; auto. }
        { apply state_equiv_on_implies_list.
          rewrite <- rewrite_enumerate; auto.
        }
      }


    * unfold union_step_fun.
      destruct e as [[x v] | ].
      2:{ right.
          split.
          { apply fun_step_in; auto. }
          { apply state_equiv_on_implies_list.
            rewrite <- rewrite_enumerate; auto.
          }
      }
      deduce_in_domain S1; rewrite_in_list_dec.
      deduce_in_domain S2; rewrite_in_list_dec.
      simpl.

      split.
      { apply fun_step_in; auto. }
      { apply state_equiv_on_implies_list.
        rewrite <- rewrite_enumerate; auto.
      }

    * (*rename H3 into Hstep2.*)

      destruct e as [[x v] | ]; simpl.
      2:{ (* contradiction *)
          repeat match goal with
          | [ H : union_input_event None |- _ ] => inversion H; clear H
          | [ H : event_in _ None |- _ ] => inversion H; fail
          end.
      }
      deduce_in_domain S1; rewrite_in_list_dec.
      deduce_in_domain S2; rewrite_in_list_dec.
      simpl.
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
    rewrite <- rewrite_enumerate in Houtput1.
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
    rewrite <- rewrite_enumerate in Houtput2.
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
          { rewrite rewrite_enumerate.
            apply equiv_on_list_implies_state_equiv_on; auto.
          }
            
        + apply union_step_2.
          { inversion 1. }
          { apply fun_in_step; auto. }
          { rewrite rewrite_enumerate.
            apply equiv_on_list_implies_state_equiv_on; auto.
          }

    }
    { destruct (x ∈? space_domain S1) as [Hx1 | Hx1]; rewrite_in_list_dec; simpl in Hstep;
      destruct (x ∈? space_domain S2) as [Hx2 | Hx2]; rewrite_in_list_dec; simpl in Hstep.
      + decompose_set_structure.
        apply union_communicate; try (apply fun_in_step; auto; fail).
        { apply in_join_domain_implies_union_input_event; auto. }

      + decompose_set_structure.
        apply union_step_1.
        { inversion 1; subst. find_contradiction. }
        { apply fun_in_step; auto. }
        { rewrite rewrite_enumerate.
          apply equiv_on_list_implies_state_equiv_on; auto.
        }
      + decompose_set_structure.
        apply union_step_2.
        { inversion 1; subst. find_contradiction. }
        { apply fun_in_step; auto. }
        { rewrite rewrite_enumerate.
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
  Existing Instance union_functional.
  Instance union_functional_correct : functional_step_relation_correct union.
  Proof.
    split.
    * apply union_implies_union_step_fun.
    * apply union_step_fun_implies_union.
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


  Context `{S_functional : functional_step_relation S}.
  Context `{S_functional_correct : @functional_step_relation_correct S S_functional}.
  Definition hide_step_fun (σ : state name) (e : option (event name value)) :=
    match e with
    | None => (* either an epsilong transition from S, or an x transition from S *)
      (fun_step S σ None) ∪ (fun τ => exists v, fun_step S σ (Some (Event x v)) τ)
    | Some (Event y v) =>
      if x =? y
      then ∅
      else fun_step S σ (Some (Event y v))
    end.

  Lemma hide_fun_step_in : forall σ e τ,
    hide ⊢ σ →{e} τ ->
    τ ∈ hide_step_fun σ e.
  Proof.
    intros σ e τ Hstep.
    destruct Hstep as [v τ Hstep | e τ Hstep He].
    * right. exists v.
      apply fun_step_in; auto.
    * destruct e as [[y v] | ].
      + simpl. compare_next.
        { contradict He. constructor. solve_set. }
        apply fun_step_in; auto.
      + left. apply fun_step_in; auto.
  Qed.

  Lemma hide_fun_in_step : forall σ e τ,
    τ ∈ hide_step_fun σ e ->
    hide ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hτ. unfold hide_step_fun in Hτ.
    destruct e as [[y v] | ].
    * compare_next.
      { rewrite Heq in Hτ. reduce_eqb. }
      { apply Hide_Neq.
        { apply fun_in_step; auto. }
        { inversion 1; subst.
          decompose_set_structure. }
      }
    * decompose_set_structure.
      { apply Hide_Neq.
        { apply fun_in_step; auto. }
        { inversion 1. }
      }
      { destruct H as [v Hτ].
        eapply Hide_Eq.
        apply fun_in_step; eauto.
      }
  Qed.


  Instance hide_functional : functional_step_relation hide :=
  {| fun_step := hide_step_fun |}.
    * simpl. unfold hide_input. apply input_list; auto.
    * simpl. unfold hide_output.
      set (Houtput := output_list S).
      typeclasses eauto.
    * simpl. unfold hide_internal.
      set (Houtput := internal_list S).
      typeclasses eauto.
  Defined.
  Instance hide_functional_correct : functional_step_relation_correct hide :=
   {| fun_step_in := hide_fun_step_in
   ; fun_in_step := hide_fun_in_step
   |}.

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
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ i v)) (Some σ') ->
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
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ Q (Num 1))) (Some σ') ->
    flop_step σ (Some (Event Q (Num 1))) (Some σ')

    (* if the reset line is high, lower Q *)
  | Flop_reset σ' :
    σ set   = Num 1 ->
    σ reset = Num 0 ->
    σ Q    <> Num 0 ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ Q (Num 0))) (Some σ') ->
    flop_step σ (Some (Event Q (Num 0))) (Some σ')

    (* if the clock has fallen (i.e. input changed and clk is no longer 1), do
    nothing to the outputs, but propogate thd change to the old_clk. *)
  | Flop_clk_fall σ' :
    σ clk <> Num 1 ->
    σ clk <> σ old_clk ->
    state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ old_clk (σ clk)))
                                                           (Some σ')
                                                            ->
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

About update_on.
  Let update_on_flop σ x v := state_equiv_on (from_list [set;reset;clk;D;Q;old_clk]) (Some (update σ x v)).
  Definition flop_step_fun (σ : state name) (e : option (event name value)) :=
    match e with
    | None => (* must be flop_clk_fall *)
      if σ clk =? Num 1
      then ∅
      else if σ clk =? σ old_clk
      then ∅
      else update_on_flop σ old_clk (σ clk)
    | Some (Event x v) =>

      if x ∈? flop_input
      (* Flop_input *)
      then if (* flop_stable *) ((σ Q =? Q_output σ) && (σ clk =? σ old_clk))%bool
           then update_on_flop σ x v
           else if (* still safe *) Q_output σ =? Q_output (update σ x v)
           then update_on_flop σ x v
           else singleton None
      else if x =? Q
      then if ((σ set =? Num 0) (* Flop_set *)
            && negb (σ Q =? Num 1)
            && (v =? Num 1))%bool
           then update_on_flop σ Q (Num 1)
           else if ((σ set =? Num 1) (* Flop_set *)
                 && (σ reset =? Num 0) (* Flop_reset *)
                 && negb (σ Q =? Num 0)
                 && (v =? Num 0))%bool
                then update_on_flop σ Q (Num 0)
           else if ((σ set =? Num 1) (* Flop_set *)
                 && (σ reset =? Num 1) (* Flop_reset *)
                 && (σ clk =? Num 1) (* Flop_clk_rise *)
                 && negb (σ old_clk =? Num 1)
                 && (v =? σ D))%bool
           then update_on_flop (update σ Q v) old_clk (Num 1)
           else ∅
       else ∅
   end.


  Lemma flop_fun_step_in : forall σ e τ,
    flop ⊢ σ →{e} τ ->
    τ ∈ flop_step_fun σ e.
  Proof.
    intros σ e τ Hstep.
    destruct Hstep.
    * unfold flop_step_fun; subst.
      destruct (i ∈? flop_input); [ | find_contradiction].
      destruct H as [Hstable | Hchange].
      + unfold flop_stable in Hstable.
        destruct Hstable.
        compare_next. simpl.
        unfold update_on_flop.
        auto.
      + repeat compare_next; simpl; solve_set.
    * unfold flop_step_fun.
      destruct (i ∈? flop_input); [ | find_contradiction].
      repeat compare_next; simpl; try solve_set.
      { (* contradiction *) contradict H. unfold flop_stable. auto. }
    * unfold flop_step_fun.
      destruct (Q ∈? flop_input) as [HQ | HQ];
        [ unfold flop_input in HQ; decompose_set_structure | ].
      repeat (compare_next; simpl; try solve_set).
    * subst.  unfold flop_step_fun.
      destruct (Q ∈? flop_input) as [HQ | HQ];
        [ unfold flop_input in HQ; decompose_set_structure | ].
      repeat (compare_next; simpl; try solve_set).
    * subst.  unfold flop_step_fun.
      destruct (Q ∈? flop_input) as [HQ | HQ];
        [ unfold flop_input in HQ; decompose_set_structure | ].
      repeat (compare_next; simpl; try solve_set).
    * subst.  unfold flop_step_fun.
      destruct (Q ∈? flop_input) as [HQ | HQ];
        [ unfold flop_input in HQ; decompose_set_structure | ].
      repeat (compare_next; simpl; try solve_set).
      unfold update_on_flop.
      repeat my_subst; auto.
  Qed.



  Lemma flop_fun_in_step : forall σ e τ,
    τ ∈ flop_step_fun σ e ->
    flop ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hstep.
    unfold flop_step_fun in Hstep.
    destruct e as [[x v] | ].
    2:{ compare_next; [rewrite Heq in Hstep; reduce_eqb | ].
        compare_next; [rewrite Heq in Hstep; reduce_eqb | ].
        destruct τ as [σ' | ]; [ | inversion Hstep].
        apply Flop_clk_fall; auto.
    }
    unfold update_on_flop in *.
    destruct (x ∈? flop_input).
    { repeat (compare_next;
        try match goal with
            | [ H : ?x = ?y 
            , H' : context[ ?x =? ?y ] |- _ ] =>
            rewrite H in H'; reduce_eqb; simpl in H'
            end);
         simpl in Hstep;
         try decompose_state_equiv_on;
         try match goal with
         | [ |- flop ⊢ _ →{_} Some _ ] =>
           apply Flop_input; auto; try (unfold flop_stable; auto)
         | [ |- flop ⊢ _ →{_} None ] =>
           apply Flop_input_err; auto; try (unfold flop_stable; inversion 1; find_contradiction)
         end.
    }
    repeat (compare_next;
        try match goal with
            | [ H : ?x = ?y 
            , H' : context[ ?x =? ?y ] |- _ ] =>
            rewrite H in H'; reduce_eqb; simpl in H'
            end);
        simpl in Hstep;
        decompose_state_equiv_on;
        match goal with
        | [ H : σ set = Num 0 |- _ ] => apply Flop_set; auto
        | [ H : σ reset = Num 0 |- _ ] => apply Flop_reset; auto
        | [ |- _ ] => apply Flop_clk_rise; auto; repeat my_subst; auto
        end.
    { (* easy *) rewrite Heq. inversion 1. }
  Qed.

  
  Instance flop_functional : functional_step_relation flop :=
  {| fun_step := flop_step_fun |}.
  Instance flop_functional_correct : functional_step_relation_correct flop :=
  {| fun_step_in := flop_fun_step_in
   ; fun_in_step := flop_fun_in_step
   |}.


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
  Variable guard : state name -> bool.


  Inductive delay_space_step (σ : state name) :
                      option (event name value) ->
                      option (state name) ->
                      Prop :=
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
    guard σ = true ->
    S ⊢ σ →{Some (Event x v)} τ ->
    x ∈ space_output S ->
    state_equiv_on (from_list sensitivities) (Some σ) τ ->
    delay_space_step σ (Some (Event x v)) τ
  .

  Definition delay_space : StateSpace :=
    {| space_input := space_input S ∪ from_list sensitivities
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

  Context `{S_functional : functional_step_relation S}.


  Existing Instance input_list.
  Existing Instance output_list.
  Existing Instance internal_list.

  Definition delay_space_step_fun σ e : Ensemble (option (state name)) :=
    match e with
    | None => (* must come from epsilon step inside S *)
      fun_step S σ e ∩ equiv_on_list sensitivities σ
    | Some (Event x v) =>
      if in_list_dec x (enumerate (space_input S))
      then fun_step S σ e ∩ equiv_on_list sensitivities σ
      else if andb (in_list_dec x (enumerate (space_output S)))
                   (guard σ)
      then fun_step S σ e ∩ equiv_on_list sensitivities σ
      else ∅
    end.

  Instance delay_space_functional : functional_step_relation delay_space :=
  {| fun_step := delay_space_step_fun |}.
  * simpl. typeclasses eauto.
  * simpl. typeclasses eauto.
  Defined.

  Context `{S_functional_correct : @functional_step_relation_correct S S_functional}.
  
Search in_dec enumerable.
Instance enum_in_dec : forall (X : Ensemble name) `{enumerable _ X}, in_dec X.
Proof.
  intros X [Xl Hl].
  constructor; intros x.
  destruct (x ∈? from_list Xl).
  + left. rewrite Hl; auto.
  + right. rewrite Hl; auto.
Defined.

  Instance delay_space_functional_correct : functional_step_relation_correct delay_space.
  split.
  * intros σ e τ Hstep.
    inversion Hstep; subst; simpl.
    + rewrite_in_list_dec.
      split.
      { eapply fun_step_in; auto. }
      { apply state_equiv_on_implies_list; auto. }
    + split.
      { eapply fun_step_in; auto. }
      { apply state_equiv_on_implies_list; auto. }
    + rewrite_in_list_dec; simpl.
      replace (guard σ) with true by assumption.
      assert (τ ∈ fun_step S σ (Some (Event x v))) by (apply fun_step_in; auto).
      assert (τ ∈ equiv_on_list sensitivities σ).
      { apply state_equiv_on_implies_list; auto. }
      destruct (x ∈? space_input S); rewrite_in_list_dec; constructor; auto.

  * intros σ e τ Hstep.
    simpl in Hstep. unfold delay_space_step_fun in Hstep.
    destruct e as [[x v] | ].
    2:{ Print delay_space_step.
        decompose_set_structure.
        apply delay_space_internal.
        { apply fun_in_step; auto. }
        { rewrite rewrite_enumerate.
          apply equiv_on_list_implies_state_equiv_on; auto.
        }
    }
    destruct (x ∈? space_input S); rewrite_in_list_dec.
    { decompose_set_structure. Print delay_space_step.
      apply delay_space_input; auto.
      { apply fun_in_step; auto. }
      { rewrite rewrite_enumerate.
        apply equiv_on_list_implies_state_equiv_on; auto.
      }
    }
    destruct (x ∈? space_output S); rewrite_in_list_dec.
    { destruct (guard σ) eqn:Hguard; [ simpl in Hstep | inversion Hstep].
      decompose_set_structure. Print delay_space_step.
      apply delay_space_output; auto.
      { apply fun_in_step; auto. }
      { rewrite rewrite_enumerate.
        apply equiv_on_list_implies_state_equiv_on; auto.
      }
    }
    { simpl in Hstep. find_contradiction. }
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

  Lemma union_inversion_left_only : forall (S1 S2 : StateSpace name) σ e σ',
    (S1 ∥ S2) ⊢ σ →{e} Some σ' ->
    event_in _ (space_domain S1) e ->
    ~ event_in _ (space_domain S2) e ->
    S1 ⊢ σ →{e} Some σ'
    /\ state_equiv_on (space_domain S2) (Some σ) (Some σ').
  Proof.
    intros ? ? ? ? ? Hstep H1 H2.
    inversion Hstep; subst; split; auto; 
      try contradiction.
    contradict H2.
    inversion H; subst; auto;
    match goal with
    [ H : event_in _ (_ ?S2) ?e |- event_in _ (space_domain ?S2) ?e ] =>
      inversion H; subst;
      constructor;
      unfold space_domain; solve_set
    end.
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

  Lemma union_inversion_right_only : forall (S1 S2 : StateSpace name) σ e σ',
    (S1 ∥ S2) ⊢ σ →{e} Some σ' ->
    ~ event_in _ (space_domain S1) e ->
    event_in _ (space_domain S2) e ->
    S2 ⊢ σ →{e} Some σ'
    /\ state_equiv_on (space_domain S1) (Some σ) (Some σ').
  Proof.
    intros ? ? ? ? ? Hstep H1 H2.
    inversion Hstep; subst; split; auto; 
      try contradiction.
    contradict H1.
    inversion H; subst; auto;
    match goal with
    [ H : event_in _ (_ ?S2) ?e |- event_in _ (space_domain ?S2) ?e ] =>
      inversion H; subst;
      constructor;
      unfold space_domain; solve_set
    end.
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
      o ∉ from_list I ->
      func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
      x = o ->
      v = f σ.
  Proof.
    intros ? ? ? ? ? ? ? Ho Hstep ?. subst.
    inversion Hstep; try find_contradiction.
    subst. auto.
  Qed.


  Lemma func_space_output_unstable : forall I (o : name) f σ x v σ',
      o ∉ from_list I ->
      func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
      x = o ->
      σ x <> v.
  Proof.
    intros ? ? ? ? ? ? ? ? Hstep Heq.
    subst.
    inversion Hstep; subst; try find_contradiction; auto.
  Qed.

  Lemma func_space_output_neq : forall I (o : name) f σ v σ' y,
      o ∉ from_list I ->
      func_space I o f ⊢ σ →{Some (Event o v)} Some σ' ->
      y ∈ from_list I ->
      σ' y = σ y.
  Proof.
    intros ? ? ? ? ? ? ? ? Hstep Hneq.
(*
    inversion Hstep; subst;
    match goal with
    | [ H : state_equiv_on _ (Some ?σ') _ |- ?σ' _ = _ ] => rewrite H; [unfold update | try solve_set]
    end;
      compare_next; auto.
  Qed.
*)
  Admitted.

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
      { destruct (t ∈? input_transition).
        + left. econstructor; eauto.
        + right. econstructor; split; eauto.
          unfold output_transition. solve_set.
       }
      { destruct (t ∈? input_transition).
        + left. econstructor; eauto.
        + right. econstructor; split; eauto.
          unfold output_transition. solve_set.
       }
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

Module Structural_SS (Export name : NameType).

Print StateSpace.
  Inductive ISpace :=
  | IFunc (I : list name) (x : name) (f : state name -> value) : ISpace
  | IUnion (S1 S2 : ISpace) : ISpace
  | IHide  (x : name) (S : ISpace) : ISpace
  | IFlop (set reset clk old_clk D Q : name) : 
    (*all_disjoint [set;reset;clk;old_clk;D;Q] ->*)
    ISpace
  | IDelaySpace (S : ISpace)
                (sensitivities : list name)
                (guard : state name -> bool) : ISpace
(*  | IPrim : StateSpace name -> ISpace*)
  .

  Fixpoint interp_ISpace (S : ISpace) : StateSpace name :=
    match S with
(*    | IPrim S0     => S0*)
    | IFunc I' x f  => func_space I' x f
    | IUnion S1 S2 => interp_ISpace S1 ∥ interp_ISpace S2
    | IHide x S0   => hide x (interp_ISpace S0)
    | IFlop set reset clk old_clk D Q => flop set reset clk old_clk D Q
    | IDelaySpace S0 sens guard => delay_space (interp_ISpace S0) sens guard
    end.


  Lemma interp_ISpace_wf : forall S,
    well_formed (interp_ISpace S).
  Admitted.


Ltac maybe_do flag tac :=
  match flag with
  | false => idtac
  | true  => tac
  end.

(* unfold_StateSpace_1 := unfold_StateSpace false *)

Ltac replace_with_in x y loc_flag :=
  match loc_flag with
  | false => (* only in conclusion *) replace x with y
  | true  => (* everywhere *) replace x with y in *
  | _ => replace x with y in loc_flag
  end.
Ltac unfold_SS recurse_flag loc_flag S :=
  match S with

  | func_space ?I0 ?x ?f => idtac
  | ?S1 ∥ ?S2            =>
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S1);
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S2)
  | hide ?x ?S'          =>
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S')
  | flop ?set ?reset ?clk ?old_clk ?D ?Q => idtac
  | delay_space ?S0 ?sens ?guard      => 
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S0)

  (* func *)
  | _ => let I := fresh "I" in
         let o := fresh "o" in
         let f := fresh "f" in
         evar (I : list name);
         evar (o : name);
         evar (f : state name -> value);
         replace_with_in S (func_space I o f) loc_flag;
         unfold I, o, f in *;
         clear I o f;
         [ | reflexivity]
                
  (* union *)
  | _ => let S1 := fresh "S1" in
         let S2 := fresh "S2" in
         evar (S1 : StateSpace name);
         evar (S2 : StateSpace name);
         replace_with_in S (S1 ∥ S2) loc_flag;
         unfold S1, S2 in *;
         [ | reflexivity];
         maybe_do recurse_flag ltac:(let S1' := eval unfold S1 in S1 in
                                let S2' := eval unfold S2 in S2 in
                                unfold_SS recurse_flag loc_flag S1';
                                unfold_SS recurse_flag loc_flag S2');
         clear S1 S2
  (* hide *)
  | _ => let x0 := fresh "x0" in
         let S0 := fresh "S0" in
         evar (x0 : name);
         evar (S0 : StateSpace name);
         replace_with_in S (hide x0 S0) loc_flag;
         unfold x0, S0 in *;
         [ | reflexivity];
         maybe_do recurse_flag ltac:(let S0' := eval unfold S0 in S0 in
                                unfold_SS recurse_flag loc_flag S0');
         clear x0 S0

  (* flop *)
  | _ => let set := fresh "set" in
         let reset := fresh "reset" in
         let clk := fresh "clk" in
         let old_clk := fresh "old_clk" in
         let D := fresh "D" in
         let Q := fresh "Q" in
         evar (set : name); evar (reset : name);
         evar (clk : name); evar (old_clk : name);
         evar (D : name); evar (Q : name);
         replace_with_in S (flop set reset clk old_clk D Q) loc_flag;
         unfold set, reset, clk, old_clk, D, Q in *;
         clear set reset clk old_clk D Q;
         [ | reflexivity]

  (* delay space *)
  | _ => let S0 := fresh "S0" in
         let sens := fresh "sens" in
         let guard := fresh "guard" in
         evar (S0 : StateSpace name);
         evar (sens : list name);
         evar (guard : state name -> bool);
         replace_with_in S (delay_space S0 sens guard) loc_flag;
         unfold S0, sens, guard in *;
         [ | reflexivity];
         maybe_do recurse_flag ltac:(let S0' := eval unfold S0 in S0 in
                                unfold_SS recurse_flag loc_flag S0');
         clear S0 sens guard

  end.
  Tactic Notation "unfold_StateSpace" constr(S) :=
    (unfold_SS true false S).
  Tactic Notation "unfold_StateSpace_1" constr(S) :=
    (unfold_SS false false S).
  Tactic Notation "unfold_StateSpace" constr(S) "in" "*" :=
    (unfold_SS true true S).
  Tactic Notation "unfold_StateSpace_1" constr(S) "in" "*" :=
    (unfold_SS false true S).
  Tactic Notation "unfold_StateSpace" constr(S) "in" hyp(H) :=
    (unfold_SS true H S).
  Tactic Notation "unfold_StateSpace_1" constr(S) "in" hyp(H) :=
    (unfold_SS false H S).

  Ltac reflect_ISpace S :=
  match S with
  | func_space ?I0 ?x ?f => constr:(IFunc I0 x f)
  | ?S1 ∥ ?S2            => let SS1 := reflect_ISpace S1 in
                            let SS2 := reflect_ISpace S2 in
                            constr:(IUnion SS1 SS2)
  | hide ?x ?S'          => let SSS' := reflect_ISpace S' in
                            constr:(IHide x SSS')
  | flop ?set ?reset ?clk ?old_clk ?D ?Q => constr:(IFlop set reset clk old_clk D Q)
  | delay_space ?S0 ?sens ?guard      => let SS := reflect_ISpace S0 in
                                      constr:(IDelaySpace SS sens guard)
(*  | _                              => constr:(IPrim S)*)
  end.
  Ltac reflect_S S := 
    let S' := reflect_ISpace S in
    replace S with (interp_ISpace S') by reflexivity.

  Ltac reflect_StateSpace :=
  match goal with
  | [ |- ?S1 = ?S2 ] => unfold_StateSpace S1;
                        unfold_StateSpace S2;
    match goal with
    | [ |- ?S1' = ?S2' ] => reflect_S S1'; reflect_S S2'
    end
  end.

  Section Test.
  Variable x : name.
  Let S : StateSpace name := C_elem x x x.
  Let S' := (S ∥ func_space (x::nil) x (fun _ => X)).
  Lemma foo : S' = S.
    assert (Heq : S' = S') by reflexivity.
    unfold_StateSpace S' in Heq.
  Abort.
  End Test.


  Definition update_oevent (σ : state name) (e : option (event name value)) : state name :=
    match e with
    | None => σ
    | Some (Event x v) => update σ x v
    end.

Print ISpace. Print flop_step.

  Fixpoint ISpace_dom (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => x0 :: I0
    | IUnion S1 S2 => ISpace_dom S1 ++ ISpace_dom S2
    | IHide x0 S0  => ISpace_dom S0
    | IFlop set reset clk old_clk D Q => set::reset::clk::old_clk::D::Q::nil
    | IDelaySpace S0 sens guard => ISpace_dom S0 ++ sens
    end.

  Fixpoint ISpace_output (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => x0 :: nil
    | IUnion S1 S2 => ISpace_output S1 ++ ISpace_output S2
    | IHide x0 S0  => better_filter (fun y => negb (x0 =? y)) (ISpace_output S0)
    | IFlop set reset clk old_clk D Q => Q::nil
    | IDelaySpace S0 sens guard => ISpace_output S0
    end.

  Fixpoint ISpace_input (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => I0
    | IUnion S1 S2 => list_setminus _ (ISpace_input S1) (ISpace_output S2)
                   ++ list_setminus _ (ISpace_input S2) (ISpace_output S1)
    | IHide x0 S0  => ISpace_input S0
    | IFlop set reset clk old_clk D Q => set::reset::clk::D::nil
    | IDelaySpace S0 sens guard => ISpace_input S0 ++ sens
    end.

  Fixpoint ISpace_internal (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => nil
    | IUnion S1 S2 => ISpace_internal S1 ++ ISpace_internal S2
    | IHide x0 S0  => x0 :: ISpace_internal S0
    | IFlop set reset clk old_clk D Q => old_clk::nil
    | IDelaySpace S0 sens guard => ISpace_internal S0
    end.

  Lemma space_domain_ISpace : forall S,
    space_domain (interp_ISpace S) == from_list (ISpace_dom S).
  Proof.
(*
    induction S; unfold space_domain in *; simpl;
      try rewrite from_list_app;
      split; intros z Hz;
      decompose_set_structure; try solve_set;
      try rewrite <- IHS1 in *;
      try rewrite <- IHS2 in *;
      decompose_set_structure;
      try solve_set.
      try rewrite <- IHS1 in *.
      rewrite <- IHS1 in H.
      rewrite 
*)
  Admitted.

  Lemma space_output_ISpace : forall S,
    space_output (interp_ISpace S) == from_list (ISpace_output S).
  Proof.
  Admitted.

  Lemma space_input_ISpace : forall S,
    space_input (interp_ISpace S) == from_list (ISpace_input S).
  Proof.
  Admitted.
  Lemma space_internal_ISpace : forall S,
    space_internal (interp_ISpace S) == from_list (ISpace_internal S).
  Proof.
  Admitted.


 (* Set reflection, with  *)

Inductive SetStructure :=
  | SetEmpty : SetStructure
  | SetSingleton : name -> SetStructure
  | SetList : list name -> SetStructure
  | SetUnion : SetStructure  -> SetStructure -> SetStructure
  | SetIntersection : SetStructure -> SetStructure -> SetStructure
  | SetDifference : SetStructure -> SetStructure -> SetStructure
  | SetSpaceDomain : ISpace -> SetStructure
  | SetSpaceInput : ISpace -> SetStructure
  | SetSpaceOutput : ISpace -> SetStructure
  | SetSpaceInternal : ISpace -> SetStructure
.
Ltac reflect_to_SetStructure S :=
  match S with
  | ∅ => constr:(SetEmpty)
  | singleton ?x => constr:(SetSingleton x)
  | ?S1 ∪ ?S2 => let l1 := reflect_to_SetStructure S1 in
                  let l2 := reflect_to_SetStructure S2 in
                  constr:(SetUnion l1 l2)
  | space_domain ?S0 => let S0' := reflect_ISpace S0 in
                        constr:(SetSpaceDomain S0')
  | space_input ?S0 => let S0' := reflect_ISpace S0 in
                        constr:(SetSpaceInternal S0')
  | space_output ?S0 => let S0' := reflect_ISpace S0 in
                        constr:(SetSpaceOutput S0')
  | space_internal ?S0 => let S0' := reflect_ISpace S0 in
                        constr:(SetSpaceInternal S0')

  | ?S1 ∖ ?S2 =>  let l1 := reflect_to_SetStructure S1 in
                  let l2 := reflect_to_SetStructure S2 in
                  constr:(SetDifference l1 l2)
  | ?S1 ∩ ?S2 =>  let l1 := reflect_to_SetStructure S1 in
                  let l2 := reflect_to_SetStructure S2 in
                  constr:(SetIntersection l1 l2)
  | from_list ?l0 => constr:(SetList l0)
  end.
Fixpoint interpret_SetStructure S :=
  match S with
  | SetEmpty => ∅
  | SetSingleton x => singleton x
  | SetList l => from_list l
  | SetUnion S1 S2 => interpret_SetStructure S1 ∪ interpret_SetStructure S2
  | SetIntersection S1 S2 => (interpret_SetStructure S1)
                           ∩ (interpret_SetStructure S2)
  | SetDifference S1 S2 => (interpret_SetStructure S1)
                         ∖ (interpret_SetStructure S2)
  | SetSpaceDomain S0 => space_domain (interp_ISpace S0)
  | SetSpaceInput S0 => space_input (interp_ISpace S0)
  | SetSpaceOutput S0 => space_output (interp_ISpace S0)
  | SetSpaceInternal S0 => space_internal (interp_ISpace S0)
  end.


Fixpoint SetStructure_to_list S :=
  match S with
  | SetEmpty => nil
  | SetSingleton x => x::nil
  | SetList l => l
  | SetUnion S1 S2 => SetStructure_to_list S1 ++ SetStructure_to_list S2
  | SetIntersection S1 S2 => list_intersection _ (SetStructure_to_list S1)
                                               (SetStructure_to_list S2)
  | SetDifference S1 S2 => list_setminus  _ (SetStructure_to_list S1)
                                          (SetStructure_to_list S2)
  | SetSpaceDomain S0 => ISpace_dom S0
  | SetSpaceInput S0 => ISpace_input S0
  | SetSpaceOutput S0 => ISpace_output S0
  | SetSpaceInternal S0 => ISpace_internal S0
  end.
    
Lemma SetStructure_to_list_correct : forall S,
  interpret_SetStructure S == from_list (SetStructure_to_list S).
Proof.
Admitted.

  Ltac set_to_list HS S :=
    let S0 := reflect_to_SetStructure S in
    let l0 := eval simpl in (SetStructure_to_list S0) in
    assert (HS : S == from_list l0);
    [ transitivity (interpret_SetStructure S0);
      [ reflexivity | rewrite SetStructure_to_list_correct; reflexivity]
    | ].



  (* NO, this doesn't work because of the non-determinism introduced by Union/Eps transitions... *)

  Notation "⊤" := (fun _ => True) : ensemble_notation.
  Open Scope ensemble_notation.


Lemma in_list_dec_equiv_t : forall {A} `{eq_dec A} (x : A) (X : list A),
    in_list_dec x X = true <-> x ∈ from_list X.
Proof.
  induction X; split; inversion 1; subst; auto.
  * compare_next; [left; solve_set | right; apply IHX; auto].
  * simpl. inversion H1; subst. reduce_eqb. auto.
  * simpl. compare_next; auto.
    apply IHX; auto.
Qed.

Lemma in_list_dec_equiv_f : forall {A} `{eq_dec A} (x : A) (X : list A),
    in_list_dec x X = false <-> x ∉ from_list X.
Proof.
  induction X; split; intros Hin; auto.
  * solve_set.
  * simpl in *. compare_next.
    apply IHX in Hin. solve_set.
  * simpl in *. compare_next.
    + contradict Hin. solve_set.
    + apply IHX. solve_set.
Qed.
Lemma from_list_app : forall {A} (l1 l2 : list A),
    from_list (l1 ++ l2) == from_list l1 ∪ from_list l2.
Proof.
  induction l1; intros l2; simpl; constructor; intros x Hx.
  * solve_set.
  * decompose_set_structure.
  * rewrite IHl1 in Hx.
    decompose_set_structure; solve_set.
  * rewrite IHl1.
    decompose_set_structure; solve_set.
Qed.


Print functional_step_relation. Print func_step_fun.
About enumerate.
Arguments enumerate {A} X {HX} : rename.
About fun_step.
Arguments fun_step {name} S {functional_step_relation}.
Print union_step_fun.
Print IFunc.
Print flop_step_fun.
Print hide_step_fun.
Print delay_space_step_fun.
  Fixpoint step_ISpace (S : ISpace) (σ : state name) (e : option (event name value))
           : Ensemble (option (state name)) :=
    match S with
    | IFunc I0 x0 f0 => func_step_fun _ I0 x0 f0 σ e
    | IUnion S1 S2 => 
      match e with
      | Some (Event x _) =>
        if (in_list_dec x (ISpace_dom S1) && in_list_dec x (ISpace_dom S2))%bool
        then step_ISpace S1 σ e ∩ step_ISpace S2 σ e
        else if in_list_dec x (ISpace_dom S1)
        then step_ISpace S1 σ e ∩ equiv_on_list _ (ISpace_dom S2) σ
        else if in_list_dec x (ISpace_dom S2)
        then step_ISpace S2 σ e ∩ equiv_on_list _ (ISpace_dom S1) σ
        else ∅
      | None =>
        (step_ISpace S1 σ None ∩ equiv_on_list _ (ISpace_dom S2) σ)
     ∪ (step_ISpace S2 σ None ∩ equiv_on_list _ (ISpace_dom S1) σ)
      end

    | IHide x0 S0 =>
      match e with
      | Some (Event y v) => if x0 =? y then ∅ else step_ISpace S0 σ e
      | None => step_ISpace S0 σ None ∪ (fun τ => exists v, step_ISpace S0 σ (Some (Event x0 v)) τ)
      end
    | IFlop set reset clk old_clk D Q =>
      flop_step_fun _ set reset clk old_clk D Q σ e
    | IDelaySpace S0 sensitivities guard =>
      match e with
      | Some (Event x _) =>
        if in_list_dec x (ISpace_input S0)
        then step_ISpace S0 σ e ∩ equiv_on_list _ sensitivities σ
        else if (in_list_dec x (ISpace_output S) && guard σ)%bool
        then step_ISpace S0 σ e ∩ equiv_on_list _ sensitivities σ
        else ∅
      | None => step_ISpace S0 σ e ∩ equiv_on_list _ sensitivities σ
      end
    end.

Print functional_step_relation.

  Instance ISpace_functional : forall S, functional_step_relation _ (interp_ISpace S).
  Proof.
    induction S; simpl.
    * apply func_functional.
    * apply union_functional; auto; typeclasses eauto.
    * apply hide_functional; auto; typeclasses eauto.
    * apply flop_functional.
    * apply delay_space_functional; auto. typeclasses eauto.
  Defined.

Print ISpace. About wf_union.
  Inductive ISpace_wf : ISpace -> Prop :=
  | IFunc_wf : forall I x f,
    x ∉ from_list I ->
    ISpace_wf (IFunc I x f)
  | IUnion_wf S1 S2 :
    list_intersection _ (ISpace_internal S1) (ISpace_dom S2) = nil ->
    list_intersection _ (ISpace_internal S2) (ISpace_dom S1) = nil ->
    ISpace_wf S1 ->
    ISpace_wf S2 ->
    ISpace_wf (IUnion S1 S2)
  (* more... *)
  .
  
  (*???*)
  Instance ISpace_functional_correct : forall S,
    ISpace_wf S ->
    functional_step_relation_correct _ (interp_ISpace S).
  Proof.
    induction S; intros wf; simpl.
    * apply func_functional_correct.
      inversion wf; auto.
    * inversion wf; subst.
      admit (*
      apply union_functional_correct; auto. *).

    * apply hide_functional_correct; auto. admit.
      admit.
    * apply flop_functional_correct. auto. admit.
    * apply delay_space_functional_correct; auto.
      admit.
  Admitted.


  Instance ISpace_enumerable : forall S,
    enumerable (space_domain (interp_ISpace S)).
  Proof.
    intros.
    apply functional_step_relation_enumerable_domain.
    apply ISpace_functional.
  Defined.


  Lemma equiv_on_list_equiv : forall l1 l2 σ,
    from_list l1 == from_list l2 ->
    equiv_on_list name l1 σ == equiv_on_list name l2 σ.
  (* proving this is trickier than I thought *)
  Admitted.
  Lemma in_list_dec_equiv : forall l1 l2 x,
    from_list l1 == from_list l2 ->
    in_list_dec x l1 = in_list_dec x l2.
  Admitted.

  Lemma step_ISpace_correct : forall S σ e,
    step_ISpace S σ e == fun_step (interp_ISpace S) σ e.
  Proof.
    induction S; intros σ e.
    * simpl. reflexivity.
    * simpl. unfold union_step_fun.
      destruct e as [[x v] | ].
      2:{ rewrite IHS1. rewrite IHS2.
          rewrite (equiv_on_list_equiv (ISpace_dom S1)).
          2:{ rewrite <- rewrite_enumerate.
              rewrite <- space_domain_ISpace; reflexivity. 
          }
          rewrite (equiv_on_list_equiv (ISpace_dom S2)).
(*                     (@enumerate _ (space_domain (interp_ISpace S2)) (ISpace_enumerable S2))).*)
          2:{ rewrite <- rewrite_enumerate.
              rewrite <- space_domain_ISpace; reflexivity. 
          }
          reflexivity.
      }
      rewrite <- (in_list_dec_equiv (ISpace_dom S1)
                                  (enumerate (space_domain (interp_ISpace S1)))).
      2:{ rewrite <- rewrite_enumerate.
          rewrite <- space_domain_ISpace. reflexivity.
      }
      rewrite <- (in_list_dec_equiv (ISpace_dom S2)
                                  (enumerate (space_domain (interp_ISpace S2)))).
      2:{ rewrite <- rewrite_enumerate.
          rewrite <- space_domain_ISpace. reflexivity.
      }
      destruct (in_list_dec x (ISpace_dom S1));
      destruct (in_list_dec x (ISpace_dom S2));
        simpl;
      try rewrite IHS1; try rewrite IHS2; try reflexivity.
      + rewrite (equiv_on_list_equiv (ISpace_dom S2)).
          2:{ rewrite <- rewrite_enumerate.
              rewrite <- space_domain_ISpace; reflexivity. 
          }
        reflexivity.
      + rewrite (equiv_on_list_equiv (ISpace_dom S1)).
          2:{ rewrite <- rewrite_enumerate.
              rewrite <- space_domain_ISpace; reflexivity. 
          }
        reflexivity.
    * simpl. unfold hide_step_fun.
      destruct e as [[y v] | ].
      { compare_next; auto. reflexivity. }
      rewrite IHS.
      Search Same_set Union.
      apply union_mor; try reflexivity.
      split; intros τ [v Hτ];
        destruct (IHS σ (Some (Event x v))) as [IH1 IH2].
      + exists v. apply IH1; auto.
      + exists v. apply IH2; auto.

    * simpl. reflexivity.

    * simpl. unfold delay_space_step_fun.
      destruct e as [[x v] | ].
      2:{ rewrite IHS. reflexivity. }
      rewrite <- (in_list_dec_equiv (ISpace_input S)
                                  (enumerate (space_input (interp_ISpace S)))).
      2:{ rewrite <- rewrite_enumerate.
          rewrite <- space_input_ISpace. reflexivity.
      }
      rewrite <- (in_list_dec_equiv (ISpace_output S)
                                  (enumerate (space_output (interp_ISpace S)))).
      2:{ rewrite <- rewrite_enumerate.
          rewrite <- space_output_ISpace. reflexivity.
      }
      destruct (in_list_dec x (ISpace_input S)) eqn:Hx.
      { rewrite IHS. reflexivity. }
      destruct (in_list_dec x (ISpace_output S)) eqn:Hx'; simpl.
      2:{ reflexivity. }
      destruct (guard σ) eqn:Hguard.
      { rewrite IHS. reflexivity. }
      { reflexivity. }
  Qed.
      

  Ltac rewrite_state_equiv :=
  match goal with
  | [ H : state_equiv_on ?X (Some ?σ') (Some _) |- context[?σ' _] ] =>
    rewrite H; [ try unfold update | decompose_set_structure]
  | [ H : state_equiv_on ?X (Some _) (Some ?σ') |- context[?σ' _] ] =>
    rewrite <- H; [ try unfold update | decompose_set_structure]
  end.
Ltac compare_in_list :=
  match goal with
  | [ |- context[ in_list_dec ?x ?X ] ] =>
    let Hx := fresh "Hx" in
    destruct (in_list_dec x X) eqn:Hx
  end.
Ltac from_in_list_dec :=
  repeat match goal with
  | [ H : in_list_dec ?x ?X = true |- _ ] => apply in_list_dec_equiv_t in H
  | [ H : in_list_dec ?x ?X = false |- _ ] => apply in_list_dec_equiv_f in H
  | [ |- in_list_dec _ _ = true ] => apply in_list_dec_equiv_t
  | [ |- in_list_dec _ _ = false ] => apply in_list_dec_equiv_f
  end.
Ltac to_in_list_dec :=
  repeat match goal with
  | [ H : ?x ∈ from_list ?X |- _ ] => apply in_list_dec_equiv_t in H
  | [ H : ?x ∉ from_list ?X |- _ ] => apply in_list_dec_equiv_f in H
  | [ |- _ ∈ from_list _ ] => apply in_list_dec_equiv_t
  | [ |- _ ∉ from_list _ ] => apply in_list_dec_equiv_f
  end.


Print functional_step_relation_correct.
  Theorem step_ISpace_in : forall S σ e τ,
    ISpace_wf S ->
    interp_ISpace S ⊢ σ →{e} τ ->
    τ ∈ step_ISpace S σ e.
  Proof.
    intros.
    rewrite step_ISpace_correct.
    apply fun_step_in; auto.
    apply ISpace_functional_correct; auto.
  Qed.
  Theorem step_in_ISpace : forall S σ e τ,
    ISpace_wf S ->
    τ ∈ step_ISpace S σ e ->
    interp_ISpace S ⊢ σ →{e} τ.
  Proof.
    intros S σ e τ Hwf Hτ.
    rewrite step_ISpace_correct in Hτ.
    eapply fun_in_step; auto.
    apply ISpace_functional_correct; auto.
  Qed.


  Definition lookup_in_state_set (x : name) (X : Ensemble (option (state name))) : Ensemble value :=
    fun v => exists σ, (Some σ ∈ X) /\ σ x = v.
  

End Structural_SS.

Section Reflection.

Print func_space. Print flop. Print C_elem. Print delay_space.
  Context {name : Set} `{name_eq_dec : eq_dec name}.
  


End Reflection.
